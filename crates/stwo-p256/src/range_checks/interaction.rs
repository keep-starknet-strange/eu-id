//! LogUp interaction trace for the range-check providers.

use serde::{Deserialize, Serialize};
use stwo::{
    core::{channel::Channel, fields::qm31::SecureField, ColumnVec},
    prover::backend::simd::qm31::PackedQM31,
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
#[derive(Clone, Debug, Serialize, Deserialize)]
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
    /// Returns the interaction trace and this provider claimed sum.
    ///
    /// The verifier checks the sum of all component claims.
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
        logup.col_from_fn(|vec_row| {
            let denom: PackedQM31 = relation.combine(&[value.data[vec_row]]);
            let numerator = -PackedQM31::from(multiplicity.data[vec_row]);
            (numerator, denom)
        });

        let (interaction_trace, claimed_sum) = logup.finalize_last();
        (interaction_trace, Self { claimed_sum })
    }

    /// Generates a Class-D blinded interaction trace.
    ///
    /// This trace mirrors the single gated entry from
    /// [`super::component::BlindRangeCheckEval`] against the
    /// relation and `value`: numerator `-(1 − is_dummy) · multiplicity` over one
    /// column (`finalize_logup`).
    ///
    /// The numerator is `-m` on real rows (is_dummy = 0) and `0` on dummy rows
    /// regardless of the random `m` committed there. The claimed sum is
    /// identical to the unblinded table over the same real uses.
    pub fn gen_blind_interaction_trace(
        multiplicity: &ColumnEval,
        value: &ColumnEval,
        is_dummy: &ColumnEval,
        relation: &RangeCheckRelation,
    ) -> (ColumnVec<ColumnEval>, Self) {
        let log_size = multiplicity.domain.log_size();
        assert_eq!(
            log_size,
            value.domain.log_size(),
            "multiplicity and value columns must share log_size",
        );
        assert_eq!(
            log_size,
            is_dummy.domain.log_size(),
            "is_dummy column must share log_size",
        );

        // One gated fraction `-(1 − is_dummy)·m / (z − combine(value))`, matching
        // the eval's single `add_to_relation` + `finalize_logup`.
        let one = PackedQM31::broadcast(SecureField::from(1));
        let mut logup = LogupTraceGenerator::new(log_size);
        logup.col_from_fn(|vec_row| {
            let denom: PackedQM31 = relation.combine(&[value.data[vec_row]]);
            let mult = PackedQM31::from(multiplicity.data[vec_row]);
            let dummy = PackedQM31::from(is_dummy.data[vec_row]);
            let numerator = -((one - dummy) * mult);
            (numerator, denom)
        });

        let (interaction_trace, claimed_sum) = logup.finalize_last();
        (interaction_trace, Self { claimed_sum })
    }
}

/// Write logup interaction columns with `batch` fractions per column, summed
/// per packed row: `(n1, d1) + (n2, d2) = (n1·d2 + n2·d1, d1·d2)`. Mirrors the
/// AIR-side `finalize_logup_batched(batch)` layout.
pub fn write_batched_logup_columns(
    logup: &mut stwo_constraint_framework::LogupTraceGenerator,
    entries: &[(
        Vec<stwo::prover::backend::simd::qm31::PackedQM31>,
        Vec<stwo::prover::backend::simd::qm31::PackedQM31>,
    )],
    batch: usize,
) {
    for chunk in entries.chunks(batch) {
        logup.col_from_fn(|vec_row| {
            let mut numerator = chunk[0].0[vec_row];
            let mut denominator = chunk[0].1[vec_row];
            for (next_numerators, next_denominators) in chunk[1..].iter() {
                let n = next_numerators[vec_row];
                let d = next_denominators[vec_row];
                numerator = numerator * d + n * denominator;
                denominator *= d;
            }
            (numerator, denominator)
        });
    }
}
