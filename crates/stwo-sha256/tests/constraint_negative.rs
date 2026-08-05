//! Constraint-layer negative tests for the SHA-256 AIR.
//!
//! Each test builds a valid witness and trace. It changes one cell, evaluates
//! the trace through `Sha256Eval::evaluate`, and checks that the AIR rejects
//! the trace.
//!
//! The driver is a custom `ConstraintCollector` that implements
//! `EvalAtRow` directly against the main trace. The motivation:
//!
//! - `AssertEvaluator` would be the obvious fit, but it `panic!`s on the
//!   first non-zero constraint and requires a finalized interaction trace.
//!   Building one here would duplicate `crate::interaction`'s walk over
//!   the entire trace; the collector keeps the negative-test driver
//!   self-contained and fast.
//! - `InfoEvaluator` only counts constraints; it doesn't actually evaluate
//!   them against trace data.
//!
//! `ConstraintCollector` therefore mirrors `AssertEvaluator`'s
//! `next_interaction_mask` (including the circle-domain coset bit-reverse
//! arithmetic for the `[0, -1]` cross-row reads used by the block-chain
//! copy constraint) but records non-zero residuals instead of
//! panicking, and no-ops `add_to_relation`. The recorded residuals cover
//! every trace constraint `Sha256Eval::evaluate` emits: IV binding,
//! schedule recurrence, T1/T2/e_new/a_new adds, σ-output reassembly,
//! finalization, multi-block chain, and the complete padding-role family.
//! These are the classes that the mutations below break.
//!
//! This driver ignores `add_to_relation` calls, so it does not exercise the
//! four `Range_k` channels. End-to-end lookup tests are in
//! `tests/prove_verify_round_trip.rs`
//! (`rejects_out_of_range_carry_witness_mutation`,
//! `verify_rejects_range_k_claimed_sum_mutations`).

use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, Relation, RelationEntry, ORIGINAL_TRACE_IDX,
};

use stwo_sha256::components::{
    is_first_round_column_id, is_first_row_column_id, round_cyclic_column_ids,
};
use stwo_sha256::constraints::Sha256Eval;
use stwo_sha256::field_exposure::FieldExposure;
use stwo_sha256::relations::Sha256Relations;
use stwo_sha256::trace::{generate_trace, generate_trace_with_fields, min_log_size, Layout};
use stwo_sha256::witness::compute_sha256_witness;

// ---------------------------------------------------------------------------
// Linear-constraint collecting evaluator
// ---------------------------------------------------------------------------

/// A non-zero constraint residual emitted while running `Sha256Eval::evaluate`
/// on a (possibly mutated) trace at one row. All fields are surfaced only
/// through `Debug` — the `dead_code` lint mis-reports them as unread.
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct Residual {
    /// The trace slot (row index) the constraint was evaluated at.
    row: usize,
    /// Per-row constraint counter — increments once per `add_constraint`,
    /// so residual `(row, constraint_idx)` pairs identify the specific
    /// algebraic identity the AIR emitted.
    constraint_idx: usize,
    /// The non-zero constraint value, lifted to `SecureField` (the AIR's
    /// extension type). Stored for diagnostic printing.
    value: SecureField,
}

/// An `EvalAtRow` that reads from a real main trace and records any
/// constraint whose algebraic value is not zero. See file-level docs for
/// the rationale vs. `AssertEvaluator` / `InfoEvaluator`.
struct ConstraintCollector<'a> {
    /// Main trace; one inner `Vec` per column, indexed `[col][row]`.
    trace: &'a [Vec<BaseField>],
    /// `log2` of the trace row count (needed for the cross-row coset math
    /// `AssertEvaluator` uses).
    log_size: u32,
    /// Row this evaluator is evaluating at.
    row: usize,
    /// Next column index for the main trace.
    col_index: usize,
    /// Per-row constraint counter, incremented on each `add_constraint`.
    constraint_idx: usize,
    /// Non-zero residuals captured this row.
    non_zero: Vec<Residual>,
}

impl<'a> ConstraintCollector<'a> {
    fn new(trace: &'a [Vec<BaseField>], log_size: u32, row: usize) -> Self {
        Self {
            trace,
            log_size,
            row,
            col_index: 0,
            constraint_idx: 0,
            non_zero: Vec::new(),
        }
    }
}

impl EvalAtRow for ConstraintCollector<'_> {
    type F = BaseField;
    type EF = SecureField;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        // The SHA-256 AIR's main-trace reads land here; preprocessed-table
        // cells are matched via `add_to_relation` (which this evaluator
        // no-ops) and the `is_first_row` selector is served via the
        // dedicated `get_preprocessed_column` override below. A non-
        // `ORIGINAL_TRACE_IDX` interaction here would mean the AIR has
        // grown a read this evaluator doesn't model — fail loudly rather
        // than silently.
        assert_eq!(
            interaction, ORIGINAL_TRACE_IDX,
            "ConstraintCollector only reads from the main trace",
        );
        let col_index = self.col_index;
        self.col_index += 1;
        offsets.map(|off| {
            if off == 0 {
                return self.trace[col_index][self.row];
            }
            // Cross-row read: walk one step on the bit-reversed
            // circle-domain coset. Mirrors `AssertEvaluator::next_interaction_mask`
            // (constraint-framework/src/prover/assert.rs) so the values
            // line up with what the prover sees.
            let log_size = self.log_size;
            let domain_size = 1isize << log_size;
            let coset_index =
                circle_domain_index_to_coset_index(bit_reverse_index(self.row, log_size), log_size)
                    as isize;
            let next_coset_index = (coset_index + off).rem_euclid(domain_size);
            let next_index = bit_reverse_index(
                coset_index_to_circle_domain_index(next_coset_index as usize, log_size),
                log_size,
            );
            self.trace[col_index][next_index]
        })
    }

    fn get_preprocessed_column(&mut self, column: PreProcessedColumnId) -> Self::F {
        // Serve `is_first_row` and the round-cyclic columns directly,
        // mirroring `crate::preprocessed`'s emission. This does **not**
        // advance `col_index` (preprocessed columns live in a separate
        // commitment tree from the main trace).
        if column == is_first_row_column_id() {
            return if self.row == 0 {
                BaseField::from(1u32)
            } else {
                BaseField::from(0u32)
            };
        }
        let natural = circle_domain_index_to_coset_index(
            bit_reverse_index(self.row, self.log_size),
            self.log_size,
        );
        if column == is_first_round_column_id() {
            return BaseField::from(u32::from(natural == stwo_sha256::trace::STATE_SEED_ROWS));
        }
        let position = natural % stwo_sha256::trace::ROWS_PER_BLOCK;
        let round = position.checked_sub(stwo_sha256::trace::STATE_SEED_ROWS);
        let cyclic = round_cyclic_column_ids();
        let flag = |b: bool| BaseField::from(u32::from(b));
        if column == cyclic[0] {
            BaseField::from(round.map_or(0, |t| stwo_sha256::constants::K[t] & 0xFFFF))
        } else if column == cyclic[1] {
            BaseField::from(round.map_or(0, |t| stwo_sha256::constants::K[t] >> 16))
        } else if column == cyclic[2] {
            flag(round == Some(0))
        } else if column == cyclic[3] {
            flag(round == Some(15))
        } else if column == cyclic[4] {
            flag(round == Some(stwo_sha256::constants::N_ROUNDS - 1))
        } else if column == cyclic[5] {
            flag(round.is_some_and(|t| t >= 16))
        } else if column == cyclic[6] {
            flag(round.is_some())
        } else if column == cyclic[7] {
            BaseField::from(round.unwrap_or(0) as u32)
        } else {
            panic!("ConstraintCollector has no fixture for preprocessed column {column:?}");
        }
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        let value = SecureField::from(constraint);
        if !value.is_zero() {
            self.non_zero.push(Residual {
                row: self.row,
                constraint_idx: self.constraint_idx,
                value,
            });
        }
        self.constraint_idx += 1;
    }

    fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        SecureField::from_m31_array(values)
    }

    fn add_to_relation<R: Relation<Self::F, Self::EF>>(
        &mut self,
        _entry: RelationEntry<'_, Self::F, Self::EF, R>,
    ) {
        // **This collector deliberately no-ops every lookup.** It only
        // records non-zero residuals from `add_constraint`, including IV
        // binding, schedule
        // recurrence, T1/T2/e_new/a_new adds, sigma-output reassembly,
        // finalization, multi-block chain, and the padding-role block. Every
        // mutation class in the suite below is caught by these identities.
        //
        // This evaluator does not model the LogUp layer. The
        // `prove_verify_round_trip` suite tests the range-check lookups.
    }

    /// `Sha256Eval::evaluate` ends with `finalize_logup_batched(LOGUP_BATCH)`
    /// so that real prover/verifier evaluators batch the lookup fractions
    /// into interaction columns. This collector does **not**
    /// model the LogUp interaction trace, so the finalize step is a
    /// no-op here — the recorded `non_zero` residuals stay scoped to the
    /// trace constraints `add_constraint` saw. (`finalize_logup_in_pairs`
    /// routes through this same entry point by default.)
    fn finalize_logup_batched(&mut self, _batch_size: usize) {}
}

/// Run `Sha256Eval::evaluate` against `trace` at every row and return every
/// non-zero residual collected. An empty return value means the AIR's
/// trace constraint layer accepts the trace; a non-empty return means
/// the AIR rejects.
fn collect_constraint_residuals_with_fields(
    trace: &[Vec<BaseField>],
    log_size: u32,
    field_exposure: FieldExposure,
) -> Vec<Residual> {
    let eval = Sha256Eval {
        log_size,
        relations: Sha256Relations::dummy(),
        field_exposure,
        instance_namespace: String::new(),
        claim_mask_beta: None,
    };
    let n_rows = 1usize << log_size;
    let mut all = Vec::new();
    for row in 0..n_rows {
        let collector = ConstraintCollector::new(trace, log_size, row);
        let collector = eval.evaluate(collector);
        all.extend(collector.non_zero);
    }
    all
}

fn collect_constraint_residuals(trace: &[Vec<BaseField>], log_size: u32) -> Vec<Residual> {
    collect_constraint_residuals_with_fields(trace, log_size, FieldExposure::empty())
}

/// Honest-trace sanity: every trace constraint `Sha256Eval::evaluate`
/// emits is zero on an unmutated single-block trace. If this fails, the
/// negative tests below are meaningless — they'd report rejections that
/// the honest baseline already produces.
#[test]
fn honest_single_block_trace_yields_no_residuals() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let trace = generate_trace(&witness, log_size);
    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        residuals.is_empty(),
        "honest abc trace produced {} non-zero residuals: {:?}",
        residuals.len(),
        residuals.first(),
    );
}

/// Honest-trace sanity, multi-block: confirms the block-chain copy
/// constraint and the multi-block padding paths are also clean on an
/// unmutated trace before the mutation tests rely on them.
#[test]
fn honest_multi_block_trace_yields_no_residuals() {
    let witness = compute_sha256_witness(&[0xABu8; 200]);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let trace = generate_trace(&witness, log_size);
    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        residuals.is_empty(),
        "honest multi-block trace produced {} non-zero residuals: {:?}",
        residuals.len(),
        residuals.first(),
    );
}

#[test]
fn honest_full_padded_stream_trace_has_no_constraint_residuals() {
    let message = [0xABu8; 130];
    let witness = compute_sha256_witness(&message);
    assert_eq!(witness.padding.padded.len(), 192);
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_full_padded_stream(77, witness.padding.padded.len());
    let trace = generate_trace_with_fields(&witness, log_size, &exposure);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        residuals.is_empty(),
        "honest full padded stream produced {} residuals: {:?}",
        residuals.len(),
        residuals.first(),
    );
}

#[test]
fn rejects_full_padded_stream_with_wrong_block_total() {
    let message = [0xABu8; 130];
    let witness = compute_sha256_witness(&message);
    assert_eq!(witness.padding.padded.len(), 192);
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_full_padded_stream(77, 128);
    let trace = generate_trace_with_fields(&witness, log_size, &exposure);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "configured padded length must bind the final block counter",
    );
}

#[test]
fn rejects_full_padded_stream_counter_on_disabled_input_row() {
    let message = [0xABu8; 130];
    let witness = compute_sha256_witness(&message);
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_full_padded_stream(77, witness.padding.padded.len());
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);
    let disabled_round_zero = witness.blocks.len() * stwo_sha256::trace::ROWS_PER_BLOCK
        + stwo_sha256::trace::STATE_SEED_ROWS;
    let slot = Layout::row_slot(disabled_round_zero, log_size);
    let counter = Layout::field_byte_col(0);
    assert_eq!(trace[Layout::COL_ENABLER][slot].0, 0);
    assert_eq!(trace[counter][slot].0, 0);
    trace[counter][slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a block counter on a disabled input row",
    );
}

#[test]
fn rejects_full_padded_stream_counter_jump() {
    let message = [0xABu8; 130];
    let witness = compute_sha256_witness(&message);
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_full_padded_stream(77, witness.padding.padded.len());
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);
    let slot = Layout::round_row_slot(1, 5, log_size);
    let counter = Layout::field_byte_col(0);
    trace[counter][slot] = BaseField::from(trace[counter][slot].0 + 1);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a block-counter jump inside a block",
    );
}

/// Mutation class: corrupt a single limb in a single row.
///
/// Picks the `lo` limb of `W[0]` (a schedule word, used as `W[t-16]` in the
/// schedule recurrence at `t=16` and as the `T1` add operand at round 0)
/// and replaces it with a value the algebra cannot satisfy. The schedule
/// recurrence add identity `s1.lo + W[t-7].lo + s0.lo + W[t-16].lo =
/// W[t].lo + 2¹⁶·carry_lo` and the round-0 `T1` identity both go non-zero.
#[test]
fn rejects_corrupted_schedule_word_limb() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    let slot = Layout::round_row_slot(0, 0, log_size);

    // Honest baseline first — confirm the unmutated trace is clean so the
    // post-mutation rejection is solely attributable to the mutation.
    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Flip a single byte's worth of bits in `W[0].lo`. XOR rather than
    // overwrite so a coincidental "the chosen value happened to already be
    // there" no-op cannot happen.
    let (w0_lo, _) = Layout::schedule_word();
    let original = trace[w0_lo][slot].0;
    trace[w0_lo][slot] = BaseField::from(original ^ 0x1234u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a corrupted schedule-word limb (mutated W[0].lo)",
    );
}

/// Mutation class: swap a carry value within a row.
///
/// At round 0, the `T1` add emits a `(carry_lo, carry_hi)` pair. Swapping
/// these two cells inside the same row (no change to any other cell)
/// breaks the limb-add identity unless the two values happen to coincide
/// — and on a real message they almost never do. The assertion below
/// guards against the rare coincidence by asserting the original values
/// differ before swapping.
#[test]
fn rejects_swapped_carry_within_row() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    let slot = Layout::round_row_slot(0, 0, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Round 0 `t1` carry pair lives at offsets [16, 17] of `round_col()`
    // — see the comment block above `Layout::round_col` for the order.
    let round_cols = Layout::round_col();
    let carry_lo_col = round_cols[16];
    let carry_hi_col = round_cols[17];
    let lo = trace[carry_lo_col][slot].0;
    let hi = trace[carry_hi_col][slot].0;
    assert_ne!(
        lo, hi,
        "carry pair coincidentally equal on this message — pick a different mutation site",
    );
    trace[carry_lo_col][slot] = BaseField::from(hi);
    trace[carry_hi_col][slot] = BaseField::from(lo);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a swapped within-row carry pair (round 0, T1 carry)",
    );
}

#[test]
fn rejects_swapped_state_seed_rows() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    let seed_h3 = Layout::seed_row_slot(0, 0, log_size);
    let seed_h2 = Layout::seed_row_slot(0, 1, log_size);
    for lane in 0..2 {
        for bit in 0..stwo_sha256::trace::WORD_BIT_COLS {
            trace[Layout::round_operand_bit(lane, bit)].swap(seed_h3, seed_h2);
        }
    }

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject swapped h3/h2 and h7/h6 seed rows",
    );
}

/// Mutation class: scramble a σ-output column.
///
/// The schedule entry for `W[16]` (i.e. `j = 0`) commits `σ0(W[1])`'s
/// `(lo, hi)` and `σ1(W[14])`'s `(lo, hi)` to the first four cells of
/// `Layout::schedule_entry(0)`. The AIR constrains committed sigma bits to
/// the direct Boolean formula and recomposes those bits into the output
/// limbs. Flipping the σ0 `lo` alone breaks that identity. The matching
/// schedule-recurrence limb-add identity also catches the mutation.
#[test]
fn rejects_scrambled_sigma_output() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    // Schedule entry j = 0 (W[16]) lives on the t = 16 row.
    let slot = Layout::round_row_slot(0, 16, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // schedule_entry(0) layout: [σ0_lo, σ0_hi, σ1_lo, σ1_hi, carry_lo, carry_hi].
    let s0_lo_col = Layout::schedule_entry()[0];
    let original = trace[s0_lo_col][slot].0;
    // XOR with 0x55AA: a 16-bit pattern that flips half the limb's bits,
    // guaranteed to change the value (no aliasing in `[0, 2¹⁶)`).
    let mutated = original ^ 0x55AAu32;
    assert_ne!(original, mutated, "mutation must change the cell");
    trace[s0_lo_col][slot] = BaseField::from(mutated);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a scrambled σ0(W[1]) output limb on the W[16] schedule entry",
    );
}

/// Mutation class: change one continuation seed bit.
///
/// The chain constraint binds the continuation seed to the previous block
/// output.
#[test]
fn rejects_mutated_continuation_seed() {
    let witness = compute_sha256_witness(&[0xABu8; 200]);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Change bit zero of h0 in block one.
    let block_1_slot = Layout::round_row_slot(1, 0, log_size);
    let h0_bit = Layout::round_operand_bit(0, 0);
    trace[h0_bit][block_1_slot] = BaseField::from(1u32 - trace[h0_bit][block_1_slot].0);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a changed h0 seed on block one's continuation row",
    );
}

#[test]
fn rejects_noncanonical_intermediate_output_limb() {
    let witness = compute_sha256_witness(&[0xABu8; 200]);
    assert!(witness.blocks.len() >= 2, "need a continuation block");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    let word = witness.blocks[0]
        .finalization_carries
        .iter()
        .position(|carry| carry.lo == 1)
        .expect("fixture needs a low-limb finalization carry");
    let slot = Layout::round_row_slot(0, stwo_sha256::constants::N_ROUNDS - 1, log_size);
    let (output_lo, _) = Layout::h_out_word(word);
    let (carry_lo, _) = Layout::final_carry(word);

    trace[output_lo][slot] = BaseField::from(trace[output_lo][slot].0 + (1 << 16));
    trace[carry_lo][slot] = BaseField::from(trace[carry_lo][slot].0 - 1);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a noncanonical intermediate output limb",
    );
}

/// Wave C / C10 (2026-08-05): extended from the pre-alias version, which
/// checked only 2 columns (`h_out_word(0).0`, `final_carry(0).0`). Now that
/// `Layout::COL_PADDING_START..COL_PADDING_END` (30 cells) ALIASES onto the
/// finalization-carry/`h_out` region, every one of those 30 cells must
/// reject a planted nonzero value at a row that is neither `r15` (t = 15)
/// nor `r63` (t = 63) — the merged `(1 - r63 - r15) · cell` zero-pin from
/// `Sha256Eval::evaluate`.
#[test]
fn rejects_finalization_cells_outside_round_63() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let slot = Layout::round_row_slot(0, stwo_sha256::constants::N_ROUNDS - 2, log_size);

    for column in Layout::COL_PADDING_START..Layout::COL_PADDING_END {
        let mut trace = generate_trace(&witness, log_size);
        assert_eq!(trace[column][slot].0, 0);
        trace[column][slot] = BaseField::from(1u32);
        assert!(
            !collect_constraint_residuals(&trace, log_size).is_empty(),
            "AIR must reject nonzero aliased column {column} at t = 62 (outside both r15 and r63)",
        );
    }
}

/// t4 (C10 adversarial plan): a padding-shaped value planted in an aliased
/// slot at a REAL block's `t = 63` row must reject via the `gate_r63`
/// finalization mod-add — the merged zero-pin is vacuous there (r63 = 1),
/// so the linear add identity is the only thing standing guard.
#[test]
fn rejects_padding_value_in_aliased_slot_at_real_round_63() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let slot = Layout::round_row_slot(0, stwo_sha256::constants::N_ROUNDS - 1, log_size);
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Perturb one of the 30 aliased cells (here, the first finalization
    // carry, which coincides with `Layout::COL_IS_MARKER_BLOCK`) as if a
    // padding value had been substituted for the honest finalization carry.
    let column = Layout::COL_PADDING_START;
    trace[column][slot] = BaseField::from(trace[column][slot].0 + 1);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a padding-shaped value substituted for a real t = 63 finalization cell",
    );
}

/// t3 (C10 adversarial plan): every aliased slot must reject a lone
/// nonzero plant at a DISABLED block's `t = 15` row too — the merged
/// zero-pin is vacuous there (r15 = 1), so this exercises the r15-gated
/// padding family (P.A/P.A'/P.B/P.D) instead. `bit_length_w14/w15` (4 of
/// the 30 slots) are the one documented exception: they are read only by
/// (P.H), itself gated by `is_length_block` — which (P.A') already pins to
/// 0 here — so a lone plant in just those 4 cells is inert (no other
/// constraint reads them) both before and after this change. See the
/// final report for the file:line trace of this pre-existing property.
#[test]
fn rejects_nonzero_in_aliased_slot_on_disabled_block_round_15() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len()).max(4);
    let n_rows = 1usize << log_size;

    // Second "block" position (k = 1) is disabled padding for a
    // single-block message; its t = 15 row is natural row 67 + 3 + 15.
    let disabled_t15_natural =
        stwo_sha256::trace::ROWS_PER_BLOCK + stwo_sha256::trace::STATE_SEED_ROWS + 15;
    let slot = bit_reverse_index(
        coset_index_to_circle_domain_index(disabled_t15_natural, log_size),
        log_size,
    );
    assert!(slot < n_rows);

    let bit_length_cols = [
        Layout::COL_BIT_LENGTH_W14_LO,
        Layout::COL_BIT_LENGTH_W14_HI,
        Layout::COL_BIT_LENGTH_W15_LO,
        Layout::COL_BIT_LENGTH_W15_HI,
    ];
    for column in Layout::COL_PADDING_START..Layout::COL_PADDING_END {
        if bit_length_cols.contains(&column) {
            continue;
        }
        let mut trace = generate_trace(&witness, log_size);
        assert_eq!(trace[Layout::COL_ENABLER][slot].0, 0);
        assert_eq!(trace[column][slot].0, 0);
        trace[column][slot] = BaseField::from(1u32);
        assert!(
            !collect_constraint_residuals(&trace, log_size).is_empty(),
            "AIR must reject nonzero aliased column {column} on a disabled block's t = 15 row",
        );
    }
}

/// t5 (C10 adversarial plan): `is_marker_block = 1` planted at a DISABLED
/// r15 row (natural `67k + 18`, `k ≥ 1`) must reject via (P.A') — gated by
/// bare `r15`, not `gate_r15 = enabler · r15` (which would vanish on this
/// exact disabled row and silently miss the mutation). No prior test in
/// this suite planted the flag specifically on an `r15 = 1`, `enabler = 0`
/// row (`rejects_padding_role_flag_on_disabled_row` uses a seed row,
/// `r15 = 0`, caught instead by the merged "outside both families" pin).
#[test]
fn rejects_marker_flag_on_disabled_r15_row() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len()).max(4);
    let n_rows = 1usize << log_size;

    let disabled_t15_natural =
        stwo_sha256::trace::ROWS_PER_BLOCK + stwo_sha256::trace::STATE_SEED_ROWS + 15;
    let slot = bit_reverse_index(
        coset_index_to_circle_domain_index(disabled_t15_natural, log_size),
        log_size,
    );
    assert!(slot < n_rows);

    let mut trace = generate_trace(&witness, log_size);
    assert_eq!(trace[Layout::COL_ENABLER][slot].0, 0);
    assert_eq!(trace[Layout::COL_IS_MARKER_BLOCK][slot].0, 0);
    trace[Layout::COL_IS_MARKER_BLOCK][slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject is_marker_block = 1 planted on a disabled r15 row",
    );
}

/// Mutation class: shift the padding's `0x80` marker.
///
/// The padding-role witness in `b"abc"`'s sole block has the marker at
/// byte 3 of `W[0]` (i.e. `W[0].lo = 0x6380` — `'c' = 0x63` followed by
/// the `0x80` marker). Moving the `marker_byte_sel` one-hot to byte 0
/// claims the marker is the MSB instead, while leaving `W[0]` unchanged
/// — the (P.E) `marker_byte_sel[b] · (marker_word_byte[b] − 0x80) = 0`
/// constraint then goes non-zero because `marker_word_byte[0]` is `'a' =
/// 0x61`, not `0x80`.
#[test]
fn rejects_shifted_marker_byte_sel() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    // The padding-role family lives on the t = 15 row.
    let slot = Layout::round_row_slot(0, 15, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Honest: marker is at byte 3 of W[0] (the `0x80` after `'a','b','c'`).
    assert_eq!(trace[Layout::marker_byte_sel(3)][slot].0, 1);
    assert_eq!(trace[Layout::marker_byte_sel(0)][slot].0, 0);

    // Shift the one-hot to byte 0 — claiming `0x80` is the MSB instead.
    trace[Layout::marker_byte_sel(3)][slot] = BaseField::from(0u32);
    trace[Layout::marker_byte_sel(0)][slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a shifted `0x80` marker selector",
    );
}

#[test]
fn rejects_each_iv_seed_mutation() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    for word in 0..8 {
        let mut trace = generate_trace(&witness, log_size);
        let lane = usize::from(word >= 4);
        let position = word % 4;
        let slot = if position == 0 {
            Layout::round_row_slot(0, 0, log_size)
        } else {
            Layout::seed_row_slot(0, stwo_sha256::trace::STATE_SEED_ROWS - position, log_size)
        };
        let column = Layout::round_operand_bit(lane, word);
        trace[column][slot] = BaseField::from(1u32 - trace[column][slot].0);
        assert!(
            !collect_constraint_residuals(&trace, log_size).is_empty(),
            "AIR must reject mutated IV word {word}",
        );
    }
}

/// Mutation class: set `enabler = 0` on a real continuation row.
///
/// The contiguity constraint
/// `(1 - is_first_row) * enabler * (1 - enabler_prev) = 0` rejects a real row
/// after a disabled predecessor. Only block zero is exempt.
#[test]
fn rejects_block_skip_via_disabled_interior_row() {
    // Use enough blocks that we have at least three contiguous real slots
    // — disable the middle one to create a padding-to-real transition at
    // the third.
    let witness = compute_sha256_witness(&[0xABu8; 200]);
    assert!(witness.blocks.len() >= 3, "need ≥3 blocks for block-skip");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Disable an interior real row — its successor then sees a disabled
    // predecessor, tripping the contiguity anchor.
    let interior_slot = Layout::round_row_slot(1, 0, log_size);
    assert_eq!(trace[Layout::COL_ENABLER][interior_slot].0, 1);
    trace[Layout::COL_ENABLER][interior_slot] = BaseField::from(0u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a block-skip (disabled-interior) trace",
    );
}

/// Mutation class: set `is_marker_block = 1` on a disabled padding row.
///
/// The gate `(1 - enabler) * is_marker_block = 0` rejects this mutation.
#[test]
fn rejects_padding_role_flag_on_disabled_row() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len()).max(4);
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Pick the first natural row past the single block's 67 real rows.
    let n_rows = 1usize << log_size;
    let padding_slot = bit_reverse_index(
        coset_index_to_circle_domain_index(stwo_sha256::trace::ROWS_PER_BLOCK, log_size),
        log_size,
    );
    assert!(padding_slot < n_rows);
    assert_eq!(trace[Layout::COL_ENABLER][padding_slot].0, 0);

    // Plant `is_marker_block = 1` on the padding row.
    trace[Layout::COL_IS_MARKER_BLOCK][padding_slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a padding-role flag set on a disabled row",
    );
}

// The tests above cover one SHA instance and its field exposure.
