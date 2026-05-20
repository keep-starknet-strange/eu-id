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
