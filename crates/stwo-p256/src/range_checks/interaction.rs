//! LogUp interaction trace for the range-check providers.

use stwo::{
    core::{channel::Channel, fields::qm31::SecureField, ColumnVec},
    prover::backend::simd::{m31::LOG_N_LANES, qm31::PackedQM31},
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use super::{ColumnEval, RangeCheckRelation};

/// Prover-side claim for the LogUp interaction trace contributed by a
/// range-check provider.
///
/// Both [`super::RangeCheckEval`] and [`super::SignedCarryRangeEval`] emit
/// the same LogUp shape — `−multiplicity / (z − value)` per row — so a
/// single claim type covers both. The `value` column is the preprocessed
/// `0..2^log_size` table for plain range checks, or the centered
/// signed-carry value column for the signed-carry provider.
#[derive(Clone, Debug)]
pub struct RangeCheckInteractionClaim {
    pub claimed_sum: SecureField,
}

impl RangeCheckInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }

    /// Build the LogUp interaction column from the multiplicity column and
    /// the column of values being looked up.
    ///
    /// Returns the interaction trace and this provider's contribution to
    /// the global LogUp identity — the sum of every component's
    /// `claimed_sum` is the residue the verifier checks.
    pub fn gen_interaction_trace(
        multiplicity: &ColumnEval,
        value: &ColumnEval,
        relation: &RangeCheckRelation,
    ) -> (ColumnVec<ColumnEval>, Self) {
        let log_size = multiplicity.domain.log_size();
        assert_eq!(
            log_size,
            value.domain.log_size(),
            "multiplicity and value columns must share log_size",
        );

        let mut logup = LogupTraceGenerator::new(log_size);
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let denom: PackedQM31 = relation.combine(&[value.data[vec_row]]);
            let numerator = -PackedQM31::from(multiplicity.data[vec_row]);
            col.write_frac(vec_row, numerator, denom);
        }
        col.finalize_col();

        let (interaction_trace, claimed_sum) = logup.finalize_last();
        (interaction_trace, Self { claimed_sum })
    }
}

/// Consecutive batch assignment for `finalize_logup_batched`: entry `i` goes
/// to batch `i / batch`. The interaction generator must write columns with
/// [`write_batched_logup_columns`] using the same `batch` so the layouts
/// match.
pub fn consecutive_batching(entries: usize, batch: usize) -> Vec<usize> {
    (0..entries).map(|index| index / batch).collect()
}

/// Write logup interaction columns with `batch` fractions per column, summed
/// per packed row: `(n1, d1) + (n2, d2) = (n1·d2 + n2·d1, d1·d2)`. Mirrors the
/// AIR-side `finalize_logup_batched(&consecutive_batching(n, batch))` layout.
/// Each entry is `(numerators, denominators)` per packed row, in the exact
/// AIR emission order. A batched column's constraint degree is
/// `batch + max(numerator degree)`, so the component bound must allow it
/// (batch 8 with degree-1 numerators needs `log_size + 3`).
/// Batching vector: pair entries `batch` at a time, but give every entry in
/// `solo` (sorted indices) its own batch — a batch never mixes a solo entry
/// with others, and batches stay consecutive runs of entries.
pub fn batching_with_solo(total: usize, batch: usize, solo: &[usize]) -> Vec<usize> {
    let mut batching = Vec::with_capacity(total);
    let mut batch_id = 0usize;
    let mut filled = 0usize;
    for entry in 0..total {
        let is_solo = solo.contains(&entry);
        if filled > 0 && (is_solo || filled == batch) {
            batch_id += 1;
            filled = 0;
        }
        batching.push(batch_id);
        filled += 1;
        if is_solo {
            batch_id += 1;
            filled = 0;
        }
    }
    batching
}

/// [`write_batched_logup_columns`] generalized to an arbitrary batching
/// vector (consecutive runs of equal batch ids, as the evals'
/// `finalize_logup_batched` expects).
pub fn write_logup_columns_with_batching(
    logup: &mut stwo_constraint_framework::LogupTraceGenerator,
    entries: &[(
        Vec<stwo::prover::backend::simd::qm31::PackedQM31>,
        Vec<stwo::prover::backend::simd::qm31::PackedQM31>,
    )],
    batching: &[usize],
) {
    assert_eq!(entries.len(), batching.len());
    let mut start = 0usize;
    while start < entries.len() {
        let mut end = start + 1;
        while end < entries.len() && batching[end] == batching[start] {
            end += 1;
        }
        let chunk = &entries[start..end];
        let vec_rows = chunk[0].0.len();
        let mut col = logup.new_col();
        for vec_row in 0..vec_rows {
            let mut numerator = chunk[0].0[vec_row];
            let mut denominator = chunk[0].1[vec_row];
            for (next_numerators, next_denominators) in chunk[1..].iter() {
                let n = next_numerators[vec_row];
                let d = next_denominators[vec_row];
                numerator = numerator * d + n * denominator;
                denominator *= d;
            }
            col.write_frac(vec_row, numerator, denominator);
        }
        col.finalize_col();
        start = end;
    }
}

pub fn write_batched_logup_columns(
    logup: &mut stwo_constraint_framework::LogupTraceGenerator,
    entries: &[(
        Vec<stwo::prover::backend::simd::qm31::PackedQM31>,
        Vec<stwo::prover::backend::simd::qm31::PackedQM31>,
    )],
    batch: usize,
) {
    for chunk in entries.chunks(batch) {
        let vec_rows = chunk[0].0.len();
        let mut col = logup.new_col();
        for vec_row in 0..vec_rows {
            let mut numerator = chunk[0].0[vec_row];
            let mut denominator = chunk[0].1[vec_row];
            for (next_numerators, next_denominators) in chunk[1..].iter() {
                let n = next_numerators[vec_row];
                let d = next_denominators[vec_row];
                numerator = numerator * d + n * denominator;
                denominator *= d;
            }
            col.write_frac(vec_row, numerator, denominator);
        }
        col.finalize_col();
    }
}
