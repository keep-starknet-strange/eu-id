//! Constraint-layer negative tests for the SHA-256 AIR.
//!
//! Direct response to audit lesson **L4** (docs/research/sha256-air-design.md §11):
//! `../sha256-air`'s suite passes *only because* every test feeds an honest
//! trace — the broken constraints (no range checks, IV not bound) are never
//! exercised. The eu-id component must not repeat that failure mode.
//!
//! Each test below builds an honest witness, generates a trace, mutates a
//! single cell (one mutation class per test), drives the trace through
//! `Sha256Eval::evaluate`, and asserts that **at least one constraint goes
//! non-zero** — i.e. the AIR rejects.
//!
//! The driver is a custom `LinearConstraintCollector` that implements
//! `EvalAtRow` directly against the main trace. The motivation:
//!
//! - `AssertEvaluator` would be the obvious fit, but it `panic!`s on the
//!   first non-zero constraint and requires a finalized interaction trace.
//!   Building one here would duplicate `crate::interaction`'s walk over
//!   the entire trace; the linear collector keeps the negative-test driver
//!   self-contained and fast.
//! - `InfoEvaluator` only counts constraints; it doesn't actually evaluate
//!   them against trace data.
//!
//! `LinearConstraintCollector` therefore mirrors `AssertEvaluator`'s
//! `next_interaction_mask` (including the circle-domain coset bit-reverse
//! arithmetic for the `[0, -1]` cross-row reads used by the §10.3
//! block-chain copy constraint) but records non-zero residuals instead of
//! panicking, and no-ops `add_to_relation`. The recorded residuals cover
//! every linear constraint `Sha256Eval::evaluate` emits: IV binding,
//! schedule recurrence, T1/T2/e_new/a_new adds, σ-output reassembly,
//! O2 chunk-bind, finalization, multi-block chain, and the whole §10.4
//! padding-role family — exactly the classes the mutations below break.
//!
//! **Lookup-side rejection (the complement of this file).** This driver
//! deliberately ignores `add_to_relation` calls, so the four `Range_k`
//! channels, the σ/Σ decode tables, the packed Maj/Ch lookup, the
//! `xor_8` chunk-combine, and the eight split-and-pack lookups are not
//! exercised here. End-to-end coverage of those — including a
//! carry-out-of-range witness mutation that closes L4 from the lookup
//! side — lives in `tests/prove_verify_round_trip.rs`
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

use air_core::relations::field_id;
use stwo_sha256::components::{is_first_row_column_id, round_cyclic_column_ids};
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
struct LinearConstraintCollector<'a> {
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

impl<'a> LinearConstraintCollector<'a> {
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

impl EvalAtRow for LinearConstraintCollector<'_> {
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
            "LinearConstraintCollector only reads from the main trace",
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
        // Round-cyclic columns: functions of `t = natural_row mod 64`.
        let natural = circle_domain_index_to_coset_index(
            bit_reverse_index(self.row, self.log_size),
            self.log_size,
        );
        let t = natural % stwo_sha256::constants::N_ROUNDS;
        let cyclic = round_cyclic_column_ids();
        let flag = |b: bool| BaseField::from(u32::from(b));
        if column == cyclic[0] {
            BaseField::from(stwo_sha256::constants::K[t] & 0xFFFF)
        } else if column == cyclic[1] {
            BaseField::from(stwo_sha256::constants::K[t] >> 16)
        } else if column == cyclic[2] {
            flag(t == 0)
        } else if column == cyclic[3] {
            flag(t == 1)
        } else if column == cyclic[4] {
            flag(t == 2)
        } else if column == cyclic[5] {
            flag(t == 3)
        } else if column == cyclic[6] {
            flag(t == 15)
        } else if column == cyclic[7] {
            flag(t == stwo_sha256::constants::N_ROUNDS - 1)
        } else if column == cyclic[8] {
            flag(t >= 16)
        } else {
            panic!("LinearConstraintCollector has no fixture for preprocessed column {column:?}");
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
        // records non-zero residuals from `add_constraint`, i.e. the
        // *linear* identities the AIR emits — IV binding, schedule
        // recurrence, T1/T2/e_new/a_new adds, σ-output reassembly, O2
        // chunk-bind, finalization, multi-block chain, and the §10.4
        // padding-role block. Every mutation class in the suite below
        // is caught by exactly those identities.
        //
        // Carry range-check lookups (`Range_2`/`4`/`5` per family) and
        // the terminal `Range_16` on `h_out` *are* wired in
        // `crate::constraints` today, but their soundness lives in the
        // LogUp interaction layer this evaluator does not model. The
        // `prove_verify_round_trip` suite exercises that path end-to-end.
        // The follow-up that migrates this driver to `AssertEvaluator`
        // — once the assert backend's interaction-trace setup is wired
        // in — should add a "carry-set-to-out-of-range" mutation class
        // to close L4 on the LogUp side too.
    }

    /// `Sha256Eval::evaluate` ends with `finalize_logup_in_pairs()` so
    /// that real prover/verifier evaluators batch the lookup fractions
    /// into interaction columns. This linear-only collector does **not**
    /// model the LogUp interaction trace, so the finalize step is a
    /// no-op here — the recorded `non_zero` residuals stay scoped to the
    /// linear identities `add_constraint` saw.
    fn finalize_logup_in_pairs(&mut self) {}
}

/// Run `Sha256Eval::evaluate` against `trace` at every row and return every
/// non-zero residual collected. An empty return value means the AIR's
/// linear constraint layer accepts the trace; a non-empty return means
/// the AIR rejects.
fn collect_constraint_residuals_with_fields(
    trace: &[Vec<BaseField>],
    log_size: u32,
    field_exposure: FieldExposure,
) -> Vec<Residual> {
    let eval = Sha256Eval {
        log_size,
        relations: Sha256Relations::dummy(),
        // The digest yield is a LogUp term, not a linear constraint, so it
        // does not affect this linear-residual collector either way; keep it
        // off to mirror the standalone (self-balancing) AIR.
        expose_digest: false,
        field_exposure,
    };
    let n_rows = 1usize << log_size;
    let mut all = Vec::new();
    for row in 0..n_rows {
        let collector = LinearConstraintCollector::new(trace, log_size, row);
        let collector = eval.evaluate(collector);
        all.extend(collector.non_zero);
    }
    all
}

fn collect_constraint_residuals(trace: &[Vec<BaseField>], log_size: u32) -> Vec<Residual> {
    collect_constraint_residuals_with_fields(trace, log_size, FieldExposure::empty())
}

/// Honest-trace sanity: every linear constraint `Sha256Eval::evaluate`
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
fn honest_multi_block_field_exposure_trace_yields_no_residuals() {
    let message = [0xABu8; 200];
    let witness = compute_sha256_witness(&message);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_preimage_windows_multi(&[
        (field_id::DOB, 62, 4),
        (field_id::NATIONALITY, 70, 3),
    ]);
    let trace = generate_trace_with_fields(&witness, log_size, &exposure);
    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        residuals.is_empty(),
        "honest multi-block field trace produced {} non-zero residuals: {:?}",
        residuals.len(),
        residuals.first(),
    );
}

#[test]
fn honest_large_multi_block_field_exposure_trace_yields_no_residuals() {
    // Opaque field tags (2, 3): the SHA producer is agnostic to their meaning.
    // Two 32-byte windows spanning blocks 1 and 2.
    let message = [0xABu8; 220];
    let witness = compute_sha256_witness(&message);
    assert!(witness.blocks.len() >= 3, "need at least three blocks");
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_preimage_windows_multi(&[(2, 96, 32), (3, 128, 32)]);
    let trace = generate_trace_with_fields(&witness, log_size, &exposure);
    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        residuals.is_empty(),
        "honest large multi-block field trace produced {} non-zero residuals: {:?}",
        residuals.len(),
        residuals.first(),
    );
}

#[test]
fn rejects_field_selector_on_wrong_block() {
    let message = [0xABu8; 200];
    let witness = compute_sha256_witness(&message);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_preimage_windows_multi(&[(field_id::NATIONALITY, 70, 2)]);
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);

    assert!(
        collect_constraint_residuals_with_fields(&trace, log_size, exposure.clone()).is_empty(),
        "baseline should be clean before mutation",
    );

    let selector_slot = exposure
        .selector_column_slot(0)
        .expect("nonzero-block exposure has selector columns");
    let selector_col = Layout::field_byte_col(selector_slot);
    let wrong_slot = Layout::round_row_slot(0, 15, log_size);
    trace[selector_col][wrong_slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a field selector enabled on the wrong SHA block",
    );
}

#[test]
fn rejects_frozen_field_block_counter() {
    let message = [0xABu8; 200];
    let witness = compute_sha256_witness(&message);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_preimage_windows_multi(&[(field_id::NATIONALITY, 70, 2)]);
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);

    assert!(
        collect_constraint_residuals_with_fields(&trace, log_size, exposure.clone()).is_empty(),
        "baseline should be clean before mutation",
    );

    let counter_slot = exposure
        .block_counter_column_slot()
        .expect("nonzero-block exposure has a block counter");
    let counter_col = Layout::field_byte_col(counter_slot);
    for t in 0..stwo_sha256::constants::N_ROUNDS {
        let slot = Layout::round_row_slot(1, t, log_size);
        trace[counter_col][slot] = BaseField::from(0u32);
    }

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a block counter that fails to increment at a SHA block boundary",
    );
}

// ---------------------------------------------------------------------------
// Mutation suite (one test per mutation class)
// ---------------------------------------------------------------------------

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

/// Mutation class: flip the `is_first_block` flag (set on a continuation
/// row, unset on the first-block row).
///
/// Post-C1-fix, the rejection path is a single linear identity:
/// `is_first_block − is_first_row = 0` (`constraints.rs`). The
/// `is_first_row` preprocessed selector is `1` only at storage index 0
/// (block 0's slot) and `0` elsewhere, so any cell-level flip on
/// `is_first_block` immediately produces a non-zero residual at that row.
/// The IV-binding / chain-gate consequences the pre-fix version relied on
/// are still present — they just fire downstream of this anchor
/// constraint.
#[test]
fn rejects_flipped_is_first_block_flag() {
    let witness = compute_sha256_witness(&[0xABu8; 200]);
    assert!(
        witness.blocks.len() >= 2,
        "need a continuation row to flip onto"
    );
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Clear is_first_block on the actual first-block row (block 0, t = 0).
    let first_slot = Layout::round_row_slot(0, 0, log_size);
    assert_eq!(trace[Layout::COL_IS_FIRST_BLOCK][first_slot].0, 1);
    trace[Layout::COL_IS_FIRST_BLOCK][first_slot] = BaseField::from(0u32);

    // Set is_first_block on a continuation block's t = 0 row.
    let later_slot = Layout::round_row_slot(1, 0, log_size);
    assert_eq!(trace[Layout::COL_IS_FIRST_BLOCK][later_slot].0, 0);
    trace[Layout::COL_IS_FIRST_BLOCK][later_slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject the flipped is_first_block flags",
    );
}

/// Mutation class: scramble a σ-output column.
///
/// The schedule entry for `W[16]` (i.e. `j = 0`) commits `σ0(W[1])`'s
/// `(lo, hi)` and `σ1(W[14])`'s `(lo, hi)` to the first four cells of
/// `Layout::schedule_entry(0)`. The σ-output reassembly identity emitted
/// by `wire_sigma_decode` (constraints.rs:1064–1080) ties each output to
/// `o_main_s + o_main_s_complement + o2_combined`; flipping the σ0 `lo`
/// alone without touching the decode-block intermediates breaks that
/// identity. The matching schedule-recurrence limb-add identity also
/// catches the mutation.
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

/// Mutation class: mutate `h_in` on a continuation block (chain-break
/// case).
///
/// The §10.3 block-chain copy constraint `(enabler − is_first_block) ·
/// (h_in[block r] − h_out[block r-1]) = 0` rejects exactly this class.
/// `chain_constraint_rejects_h_in_mutation_on_block_1` in constraints.rs
/// already exercises this at the trace-residual level; this version
/// drives it through `Sha256Eval::evaluate` for the L4 audit-lesson
/// closure.
#[test]
fn rejects_mutated_h_in_on_continuation_block() {
    let witness = compute_sha256_witness(&[0xABu8; 200]);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Mutate `h_in[0].lo` of block 1. Block 1 is a continuation row
    // (is_first_block = 0), so the chain gate is `1`, and the identity
    // `h_in[0].lo = h_out[block 0][0].lo` must hold.
    let block_1_slot = Layout::round_row_slot(1, 0, log_size);
    let (h_in_lo, _) = Layout::h_in_word(0);
    let original = trace[h_in_lo][block_1_slot].0;
    trace[h_in_lo][block_1_slot] = BaseField::from(original ^ 0xBEEFu32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a mutated h_in[0].lo on block 1's continuation row",
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

/// Mutation class: C1 IV-anchor exploit — clear `is_first_block` on block 0
/// **and** plant an attacker-chosen `h_out` on the wraparound padding row.
///
/// Pre-fix soundness gap (`docs/research/sha256-air-design.md` §11 L2): with
/// `is_first_block = 0` on the real row, IV binding was vacuous. With the
/// padding-row `h_out` cells unconstrained (Range_16/finalization both
/// gated by `enabler`), the prover could inject any state `X` into block
/// 0's `h_in` via the chain's `[0, -1]` mask wraparound — yielding a
/// "digest" of `compression(X, W)` instead of `SHA-256(W) = compression(IV, W)`.
///
/// Post-fix rejection path: the preprocessed `is_first_row` selector is
/// `1` at storage index 0, so the anchor constraint
/// `is_first_block − is_first_row = 0` fails immediately when the mutator
/// clears `is_first_block`. The mutation that *would* have completed the
/// exploit (setting padding-row `h_out` to a chosen `X`) is preserved here
/// to document the threat model, but the AIR rejects on the anchor before
/// the chain ever reads the planted `h_out`.
#[test]
fn rejects_iv_anchor_exploit_via_padding_h_out_injection() {
    let witness = compute_sha256_witness(b"abc");
    // Single-block message; min_log_size = 4 (the SIMD floor) gives one
    // real slot and 15 padding slots — exactly the layout an attacker
    // would target. The cyclic predecessor of slot 0 wraps to slot N-1.
    let log_size = min_log_size(witness.blocks.len()).max(4);
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // (1) Clear `is_first_block` on block 0's t = 0 row to disable IV binding.
    let first_slot = Layout::round_row_slot(0, 0, log_size);
    assert_eq!(first_slot, 0, "row (0, 0) must live at storage index 0");
    assert_eq!(trace[Layout::COL_IS_FIRST_BLOCK][first_slot].0, 1);
    trace[Layout::COL_IS_FIRST_BLOCK][first_slot] = BaseField::from(0u32);

    // (2) Plant an attacker-chosen `h_out` on the wraparound padding row
    //     (coset N-1 in the chain's [0, -1] mask). Any non-zero pattern
    //     suffices to demonstrate the threat surface.
    let n_rows = 1usize << log_size;
    let wraparound_slot = bit_reverse_index(
        coset_index_to_circle_domain_index(n_rows - 1, log_size),
        log_size,
    );
    for j in 0..8usize {
        let (lo_col, hi_col) = Layout::h_out_word(j);
        trace[lo_col][wraparound_slot] = BaseField::from(0xCAFEu32 + j as u32);
        trace[hi_col][wraparound_slot] = BaseField::from(0xBABEu32 + j as u32);
    }

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject the C1 IV-anchor exploit",
    );
}

/// Mutation class: C1 block-skip exploit — set `enabler = 0` on a real
/// continuation row to splice in a padding-row `h_out` as the next block's
/// `h_in`.
///
/// Pre-fix surface: even with `is_first_block = 1` correctly anchored at
/// block 0, a prover could disable an interior block (`enabler = 0`) so
/// the next real block's chain reads its `h_out_prev` from a now-padding
/// predecessor (`h_out` unconstrained). Compression at that row runs from
/// the planted state — not an honestly chained SHA-256 state.
///
/// Post-fix rejection path: the contiguity constraint
/// `(1 − is_first_row) · enabler · (1 − enabler_prev) = 0` rejects the
/// transition from a disabled predecessor (`enabler_prev = 0`) to a real
/// row (`enabler = 1`). Only block 0's slot is exempt (via
/// `is_first_row = 1`).
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

/// Mutation class: Mn1 padding-flag injection — set `is_marker_block = 1`
/// on a disabled (padding) row.
///
/// Pre-fix: padding-role flags fired unconditionally (no `enabler` gate),
/// so a malicious prover could mark a disabled row as a marker block.
/// While not a direct soundness break in isolation, it interacts with C1
/// and is undesirable defense-in-depth: disabled rows should carry no
/// padding metadata.
///
/// Post-fix rejection path: the gate `(1 − enabler) · is_marker_block = 0`
/// (Mn1) fails immediately on a disabled row with `is_marker_block ≠ 0`.
#[test]
fn rejects_padding_role_flag_on_disabled_row() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len()).max(4);
    let mut trace = generate_trace(&witness, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // Pick a padding slot — the first natural row past the single block's
    // 64 real rows.
    let n_rows = 1usize << log_size;
    let padding_slot =
        bit_reverse_index(coset_index_to_circle_domain_index(64, log_size), log_size);
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
