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
        logup.col_from_fn(|vec_row| {
            let denom: PackedQM31 = relation.combine(&[value.data[vec_row]]);
            let numerator = -PackedQM31::from(multiplicity.data[vec_row]);
            (numerator, denom)
        });

        let (interaction_trace, claimed_sum) = logup.finalize_last();
        (interaction_trace, Self { claimed_sum })
    }

    /// Class-D blinded interaction trace (Q-015 §4b / p4c Class D). Mirrors
    /// [`super::component::BlindRangeCheckEval`]: two fractions per row against
    /// the same relation and `value`, paired into one column
    /// (`finalize_logup_in_pairs`):
    /// - `-multiplicity` (normal yield), and
    /// - `+is_dummy · multiplicity` (cancelling twin).
    ///
    /// Both share the denominator `z − combine(value)`, so the paired fraction
    /// is `(-m + is_dummy · m)/(z − combine(value))`: `-m` on real rows,
    /// `0` on dummy rows regardless of the random `m` there. The claimed sum is
    /// therefore identical to the unblinded table's over the same real uses.
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

        // Mirror the AIR's two `add_to_relation` entries paired by
        // `finalize_logup_in_pairs` EXACTLY: build the two fraction vectors and
        // pair them with `(n0·d1 + n1·d0)/(d0·d1)`. Here d0 = d1 = denom, so the
        // committed running sum matches the framework's OODS reconstruction
        // bit-for-bit (a pre-simplified single fraction would commit a
        // different denominator and desync the verifier).
        let n_vec_rows = multiplicity.data.len();
        let mut neg_num = Vec::with_capacity(n_vec_rows);
        let mut neg_den = Vec::with_capacity(n_vec_rows);
        let mut twin_num = Vec::with_capacity(n_vec_rows);
        let mut twin_den = Vec::with_capacity(n_vec_rows);
        for vec_row in 0..n_vec_rows {
            let denom: PackedQM31 = relation.combine(&[value.data[vec_row]]);
            let mult = PackedQM31::from(multiplicity.data[vec_row]);
            let dummy = PackedQM31::from(is_dummy.data[vec_row]);
            neg_num.push(-mult);
            neg_den.push(denom);
            twin_num.push(dummy * mult);
            twin_den.push(denom);
        }
        let mut logup = LogupTraceGenerator::new(log_size);
        write_batched_logup_columns(&mut logup, &[(neg_num, neg_den), (twin_num, twin_den)], 2);

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
