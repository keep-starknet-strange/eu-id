//! Constraint-layer negative tests for the SHA-256 AIR.
//!
//! Each test constructs a valid trace and changes one class of cell. It sends
//! the changed trace to `Sha256Eval::evaluate`. At least one constraint must
//! have a nonzero residual.
//!
//! `LinearConstraintCollector` implements `EvalAtRow` for the main trace. It
//! records all linear residuals without a full interaction trace. It also
//! reproduces the circle-domain index rules for cross-row masks.
//!
//! This driver ignores `add_to_relation`, so it does not test `Range_k`
//! balance. `tests/prove_verify_round_trip.rs` tests that balance with real
//! proofs and claimed-sum mutations.

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
    /// Main trace. One inner `Vec` per column, indexed `[col][row]`.
    trace: &'a [Vec<BaseField>],
    /// `log2` of the trace row count (needed for the cross-row coset math
    /// `AssertEvaluator` uses).
    log_size: u32,
    /// Row that this evaluator checks.
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
        // The SHA-256 AIR's main-trace reads land here. Preprocessed-table
        // cells are matched via `add_to_relation` (which this evaluator
        // no-ops) and the `is_first_row` selector is served via the
        // dedicated `get_preprocessed_column` override below. A non-
        // `ORIGINAL_TRACE_IDX` interaction here would mean the AIR has
        // grown a read this evaluator does not model — fail loudly rather
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
        // This collector ignores each lookup. It records nonzero residuals
        // only from `add_constraint`. These residuals cover IV binding,
        // schedule recurrence, round additions, bit-plane recomposition,
        // finalization, the block chain, and padding roles.
        //
        // `crate::constraints` wires each family's carry lookups for Range_2,
        // Range_4, and Range_5. It also wires the terminal Range_8 byte checks on
        // `h_out`. Their soundness depends on the LogUp interaction layer, which
        // this evaluator does not model. The `prove_verify_round_trip` suite
        // exercises that path end to end.
    }

    /// `Sha256Eval::evaluate` ends with `finalize_logup_batched(..)`.
    /// Real prover and verifier evaluators batch lookup fractions into
    /// interaction columns. This linear collector does not model the LogUp
    /// interaction trace. Therefore, finalization does nothing here. Recorded
    /// `non_zero` residuals cover only identities passed to `add_constraint`.
    fn finalize_logup_batched(&mut self, _batch_size: usize) {}
    fn finalize_logup_in_pairs(&mut self) {}
}

/// Run `Sha256Eval::evaluate` against `trace` at every row and return every
/// non-zero residual collected. An empty return value means the AIR's
/// linear constraint layer accepts the trace. A non-empty return means
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
        // does not affect this linear-residual collector either way. Keep it
        // off to mirror the standalone (self-balancing) AIR.
        expose_digest: false,
        field_exposure,
        claim_mask_beta: None,
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
/// negative tests below are meaningless — they would report rejections that
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

/// Check the block chain and padding paths on a valid multi-block trace.
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
    let exposure = FieldExposure::from_preimage_windows(&[
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
    let exposure = FieldExposure::from_preimage_windows(&[(2, 96, 32), (3, 128, 32)]);
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
    let exposure = FieldExposure::from_preimage_windows(&[(field_id::NATIONALITY, 70, 2)]);
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);

    assert!(
        collect_constraint_residuals_with_fields(&trace, log_size, exposure.clone()).is_empty(),
        "baseline should be clean before mutation",
    );

    let selector_slot = exposure
        .selector_column_slot(1)
        .expect("nonzero-block exposure has selector columns");
    let selector_col = Layout::field_aux_col(selector_slot);
    let wrong_slot = Layout::round_row_slot(0, 15, log_size);
    trace[selector_col][wrong_slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a field selector enabled on the wrong SHA block",
    );
}

#[test]
fn rejects_field_selector_on_padding_r15_row() {
    let message = [0xABu8; 200];
    let witness = compute_sha256_witness(&message);
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_preimage_windows(&[(field_id::NATIONALITY, 70, 2)]);
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);

    assert!(
        collect_constraint_residuals_with_fields(&trace, log_size, exposure.clone()).is_empty(),
        "baseline should be clean before mutation",
    );

    let selector_slot = exposure
        .selector_column_slot(1)
        .expect("nonzero-block exposure has selector columns");
    let selector_col = Layout::field_aux_col(selector_slot);
    let first_padding_r15 = witness.blocks.len() * stwo_sha256::constants::N_ROUNDS + 15;
    assert!(
        first_padding_r15 < 1usize << log_size,
        "test needs a padding r15 row"
    );
    let padding_slot = Layout::row_slot(first_padding_r15, log_size);
    trace[selector_col][padding_slot] = BaseField::from(1u32);

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a field selector enabled on a periodic padding r15 row",
    );
}

#[test]
fn rejects_virtual_field_byte_w_bit_tamper() {
    let message: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
    let witness = compute_sha256_witness(&message);
    let log_size = min_log_size(witness.blocks.len());
    // Offset 70 = block 1, W[1], big-endian byte 2 = W bits 8..15.
    let exposure = FieldExposure::from_preimage_windows(&[(field_id::NATIONALITY, 70, 1)]);
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);

    assert!(
        collect_constraint_residuals_with_fields(&trace, log_size, exposure.clone()).is_empty(),
        "baseline should be clean before mutation",
    );

    let word_row = Layout::round_row_slot(1, 1, log_size);
    let bit_col = Layout::w_bit(8);
    trace[bit_col][word_row] = BaseField::from(1u32) - trace[bit_col][word_row];

    let residuals = collect_constraint_residuals_with_fields(&trace, log_size, exposure);
    assert!(
        !residuals.is_empty(),
        "AIR must reject tampering with a W bit that feeds a virtual field byte",
    );
}

#[test]
fn rejects_frozen_field_block_counter() {
    let message = [0xABu8; 200];
    let witness = compute_sha256_witness(&message);
    assert!(witness.blocks.len() >= 2, "need multi-block message");
    let log_size = min_log_size(witness.blocks.len());
    let exposure = FieldExposure::from_preimage_windows(&[(field_id::NATIONALITY, 70, 2)]);
    let mut trace = generate_trace_with_fields(&witness, log_size, &exposure);

    assert!(
        collect_constraint_residuals_with_fields(&trace, log_size, exposure.clone()).is_empty(),
        "baseline should be clean before mutation",
    );

    let counter_slot = exposure
        .block_counter_column_slot()
        .expect("nonzero-block exposure has a block counter");
    let counter_col = Layout::field_aux_col(counter_slot);
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
/// Change the low limb of `W[0]`.
///
/// The schedule recurrence at `t = 16` and the `T1` addition at round zero
/// both read this value. At least one identity must have a nonzero residual.
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
/// Swap the two `T1` carry cells at round zero.
///
/// The addition identity fails when the values differ. The test checks this
/// premise before it swaps the cells.
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
/// `is_first_row` is one only at the first storage slot. A change to
/// `is_first_block` gives a nonzero residual at that row.
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
/// The row for `W[16]` contains `σ0(W[1])` and `σ1(W[14])`. Bit recomposition
/// ties these limbs to the lower-sigma output planes. A change to one limb
/// breaks recomposition or the schedule addition.
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
/// already exercises this at the trace-residual level. This version uses
/// `Sha256Eval::evaluate`.
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
/// The only block for `b"abc"` places the marker at byte 3 of `W[0]`.
/// Thus, `W[0].lo = 0x6380`, with `'c' = 0x63` before the marker.
/// Move the `marker_byte_sel` one-hot value to byte 0. This claims the marker is
/// the most significant byte without changing `W[0]`.
/// The constraint is `marker_byte_sel[b] · (marker_word_byte[b] − 0x80) = 0`.
/// It becomes nonzero because byte 0 contains `'a' = 0x61`, not `0x80`.
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
/// This mutation models an IV-anchor attack. It clears `is_first_block` and
/// puts an arbitrary `h_out` state in the cyclic predecessor row. Without the
/// anchor, the chain could read that state as block zero input.
///
/// The AIR requires `is_first_block = is_first_row`. It rejects the changed
/// flag before the chain can use the planted state.
#[test]
fn rejects_iv_anchor_exploit_via_padding_h_out_injection() {
    let witness = compute_sha256_witness(b"abc");
    // A single block uses 64 real rows. `min_log_size = 7` adds 64 padding
    // rows. The cyclic predecessor of row zero wraps to the last row.
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
/// This mutation disables an interior continuation row. The next real row
/// would then read an unchecked predecessor state.
///
/// The contiguity constraint rejects a transition from a disabled predecessor
/// to a real row. Only the first row has an exemption.
#[test]
fn rejects_block_skip_via_disabled_interior_row() {
    // Use at least three contiguous real block slots. Disable the middle slot.
    // This creates a padding-to-real transition at the third slot.
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
/// and is undesirable defense-in-depth. Disabled rows must contain no padding
/// metadata.
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

/// Check that bit recomposition rejects a limb that does not match its bit
/// planes.
#[test]
fn rejects_maj_limb_off_bit_recomposition() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);
    let slot = Layout::round_row_slot(0, 0, log_size);

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // `maj.lo` is round-family column 6. The AIR recomposes it ungated as
    // `maj.lo == Σ maj_bits[i]·2^i` from the committed a/b/c bit-planes.
    // Flipping one bit of the limb (bits unchanged) breaks that identity.
    let maj_lo = Layout::round_col()[6];
    let original = trace[maj_lo][slot].0;
    trace[maj_lo][slot] = BaseField::from(original ^ 0x0001u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "AIR must reject a maj limb that does not match its bit recomposition",
    );
}

/// Check that an inactive row cannot contain a non-Boolean bit-plane value.
///
/// The ungated `constrain_boolean_bits` constraint applies to every row.
#[test]
fn rejects_non_boolean_bit_on_padding_row() {
    let witness = compute_sha256_witness(b"abc");
    let log_size = min_log_size(witness.blocks.len());
    let mut trace = generate_trace(&witness, log_size);

    let real_rows = witness.blocks.len() * 64;
    let padding_slot = Layout::row_slot(real_rows, log_size);
    assert_eq!(
        trace[Layout::COL_ENABLER][padding_slot].0,
        0,
        "must target a disabled (padding) row",
    );

    assert!(
        collect_constraint_residuals(&trace, log_size).is_empty(),
        "baseline should be clean before mutation",
    );

    // `a`-operand bit 0 on the disabled row → set to a non-boolean value.
    let bit_col = Layout::round_operand_bit(0, 0);
    trace[bit_col][padding_slot] = BaseField::from(2u32);

    let residuals = collect_constraint_residuals(&trace, log_size);
    assert!(
        !residuals.is_empty(),
        "ungated booleanity must reject a non-boolean bit-plane cell even on a padding row",
    );
}
