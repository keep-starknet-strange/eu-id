use serde::{Deserialize, Serialize};
use stwo::core::{
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

use crate::range_checks::{
    range_check_value_column_id, signed_carry_active_column_id, signed_carry_value_column_id,
    RangeCheckComponent, RangeCheckEval, RangeCheckInteractionClaim, SignedCarryRangeComponent,
    SignedCarryRangeEval, RANGE13_BITS,
};

use super::columns::padded_log_size;
use super::columns::M31ColumnEval;
use super::component::{
    AbProductChunkComponent, AbProductChunkEval, CanonicalScalarComponent, CanonicalScalarEval,
    ProductDigitAccumulatorComponent, ProductDigitAccumulatorEval, QnProductChunkComponent,
    QnProductChunkEval, ScalarReductionDigitComponent, ScalarReductionDigitEval,
};
use super::interaction_claim::{zero_interaction_claim, ScalarModMulProofSliceInteractionClaim};
use super::layout::{ScalarModMulFamilyTraces, ScalarModMulLookupUses};
use super::providers::{LookupProviderClaims, LookupProviderTraces, SIGNED_CARRY_EQUATION};
use super::relation::ScalarModMulLookupRelations;
use super::{ScalarModMulFixedSchedule, ScalarModMulInteractionTraces, ScalarModMulMergedRows};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ScalarModMulClaim {
    /// Per-instance mul IDs in the merged block-major order (all scalar_setup
    /// instances first, then all fake_glv instances). `mul_id` is now a base
    /// trace column pinned by LogUp balance, so this field only binds the
    /// instance IDs into the transcript.
    pub mul_ids: Vec<u32>,
    pub canonical_log_size: u32,
    pub ab_chunks_log_size: u32,
    pub qn_chunks_log_size: u32,
    pub accumulator_log_size: u32,
    pub reduction_log_size: u32,
    pub external_limb_links: bool,
}

impl ScalarModMulClaim {
    pub fn from_rows(rows: &ScalarModMulMergedRows) -> Self {
        Self {
            mul_ids: rows.instances.iter().map(|inst| inst.mul_id).collect(),
            canonical_log_size: padded_log_size(rows.canonical_len()),
            ab_chunks_log_size: padded_log_size(rows.ab_chunks_len()),
            qn_chunks_log_size: padded_log_size(rows.qn_chunks_len()),
            accumulator_log_size: padded_log_size(rows.accumulators_len()),
            reduction_log_size: padded_log_size(rows.reduction_len()),
            external_limb_links: false,
        }
    }

    pub fn from_rows_with_external_limb_links(rows: &ScalarModMulMergedRows) -> Self {
        Self {
            external_limb_links: true,
            ..Self::from_rows(rows)
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.mul_ids.len() as u64);
        for &mul_id in &self.mul_ids {
            channel.mix_u64(mul_id as u64);
        }
        channel.mix_u64(self.canonical_log_size as u64);
        channel.mix_u64(self.ab_chunks_log_size as u64);
        channel.mix_u64(self.qn_chunks_log_size as u64);
        channel.mix_u64(self.accumulator_log_size as u64);
        channel.mix_u64(self.reduction_log_size as u64);
        channel.mix_u64(self.external_limb_links as u64);
    }
}

pub(crate) struct ScalarModMulComponents {
    pub(crate) canonical: CanonicalScalarComponent,
    pub(crate) ab_chunks: AbProductChunkComponent,
    pub(crate) qn_chunks: QnProductChunkComponent,
    pub(crate) accumulators: ProductDigitAccumulatorComponent,
    pub(crate) reduction_digits: ScalarReductionDigitComponent,
    pub(crate) range13: Option<RangeCheckComponent>,
    pub(crate) signed_carry: SignedCarryRangeComponent,
}

impl ScalarModMulComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &ScalarModMulClaim,
        interaction_claim: &ScalarModMulProofSliceInteractionClaim,
        lookup_claims: &LookupProviderClaims,
        relations: &ScalarModMulLookupRelations,
    ) -> Self {
        Self::new_inner(
            allocator,
            claim,
            interaction_claim,
            lookup_claims,
            relations,
            true,
        )
    }

    pub(crate) fn new_without_range13_provider(
        allocator: &mut TraceLocationAllocator,
        claim: &ScalarModMulClaim,
        interaction_claim: &ScalarModMulProofSliceInteractionClaim,
        lookup_claims: &LookupProviderClaims,
        relations: &ScalarModMulLookupRelations,
    ) -> Self {
        Self::new_inner(
            allocator,
            claim,
            interaction_claim,
            lookup_claims,
            relations,
            false,
        )
    }

    fn new_inner(
        allocator: &mut TraceLocationAllocator,
        claim: &ScalarModMulClaim,
        interaction_claim: &ScalarModMulProofSliceInteractionClaim,
        lookup_claims: &LookupProviderClaims,
        relations: &ScalarModMulLookupRelations,
        include_range13_provider: bool,
    ) -> Self {
        let scalar_relations = relations.scalar_mod_mul();
        Self {
            canonical: CanonicalScalarComponent::new(
                allocator,
                CanonicalScalarEval {
                    log_size: claim.canonical_log_size,
                    external_limb_links: claim.external_limb_links,
                    relations: scalar_relations.clone(),
                },
                interaction_claim.scalar_mod_mul.canonical_scalars,
            ),
            ab_chunks: AbProductChunkComponent::new(
                allocator,
                AbProductChunkEval {
                    log_size: claim.ab_chunks_log_size,
                    relations: scalar_relations.clone(),
                },
                interaction_claim.scalar_mod_mul.ab_chunks,
            ),
            qn_chunks: QnProductChunkComponent::new(
                allocator,
                QnProductChunkEval {
                    log_size: claim.qn_chunks_log_size,
                    relations: scalar_relations.clone(),
                },
                interaction_claim.scalar_mod_mul.qn_chunks,
            ),
            accumulators: ProductDigitAccumulatorComponent::new(
                allocator,
                ProductDigitAccumulatorEval {
                    log_size: claim.accumulator_log_size,
                    relations: scalar_relations.clone(),
                },
                interaction_claim.scalar_mod_mul.accumulators,
            ),
            reduction_digits: ScalarReductionDigitComponent::new(
                allocator,
                ScalarReductionDigitEval {
                    log_size: claim.reduction_log_size,
                    relations: scalar_relations,
                },
                interaction_claim.scalar_mod_mul.reduction_digits,
            ),
            range13: include_range13_provider.then(|| {
                RangeCheckComponent::new(
                    allocator,
                    RangeCheckEval::new(relations.range13.clone(), lookup_claims.range13.log_size),
                    interaction_claim.range13.claimed_sum,
                )
            }),
            signed_carry: SignedCarryRangeComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.signed_carry.clone(),
                    lookup_claims.signed_carry.log_size,
                    lookup_claims.signed_carry.equation_name.clone(),
                ),
                interaction_claim.signed_carry.claimed_sum,
            ),
        }
    }
}

pub(crate) fn preprocessed_column_ids(
    claim: &ScalarModMulClaim,
    lookup_claims: &LookupProviderClaims,
) -> Vec<PreProcessedColumnId> {
    let interaction_claim = zero_interaction_claim();
    let relations = ScalarModMulLookupRelations::dummy();
    let mut allocator = TraceLocationAllocator::default();
    let _ = ScalarModMulComponents::new(
        &mut allocator,
        claim,
        &interaction_claim,
        lookup_claims,
        &relations,
    );
    allocator.preprocessed_columns().clone()
}

pub(crate) fn gen_preprocessed_trace(
    rows: &ScalarModMulMergedRows,
    lookup_claims: &LookupProviderClaims,
    ids: &[PreProcessedColumnId],
) -> Vec<M31ColumnEval> {
    let schedule = ScalarModMulFixedSchedule::from_rows(rows);
    let schedule_evals = schedule.to_circle_evaluations();
    let lookup_traces =
        LookupProviderTraces::from_uses(lookup_claims, ScalarModMulLookupUses::from_rows(rows));

    let mut columns = Vec::new();
    columns.extend(schedule.canonical.into_iter().zip(schedule_evals.canonical));
    columns.extend(schedule.ab_chunks.into_iter().zip(schedule_evals.ab_chunks));
    columns.extend(schedule.qn_chunks.into_iter().zip(schedule_evals.qn_chunks));
    columns.extend(
        schedule
            .accumulators
            .into_iter()
            .zip(schedule_evals.accumulators),
    );
    columns.extend(
        schedule
            .reduction_digits
            .into_iter()
            .zip(schedule_evals.reduction_digits),
    );
    columns.push((
        super::schedule::ScalarModMulScheduleColumn {
            id: range_check_value_column_id(RANGE13_BITS),
            values: Vec::new(),
        },
        lookup_traces.range13_value,
    ));
    columns.push((
        super::schedule::ScalarModMulScheduleColumn {
            id: signed_carry_value_column_id(SIGNED_CARRY_EQUATION),
            values: Vec::new(),
        },
        lookup_traces.signed_carry_value,
    ));
    columns.push((
        super::schedule::ScalarModMulScheduleColumn {
            id: signed_carry_active_column_id(SIGNED_CARRY_EQUATION),
            values: Vec::new(),
        },
        lookup_traces.signed_carry_active,
    ));

    ids.iter()
        .map(|id| {
            columns
                .iter()
                .find_map(|(column, eval)| (column.id == *id).then(|| eval.clone()))
                .unwrap_or_else(|| panic!("missing preprocessed column {}", id.id))
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn gen_base_trace(
    rows: &ScalarModMulMergedRows,
    lookup_claims: &LookupProviderClaims,
) -> Vec<M31ColumnEval> {
    gen_base_trace_inner(rows, lookup_claims, true)
}

pub(crate) fn gen_base_trace_without_range13_provider(
    rows: &ScalarModMulMergedRows,
    lookup_claims: &LookupProviderClaims,
) -> Vec<M31ColumnEval> {
    gen_base_trace_inner(rows, lookup_claims, false)
}

pub(crate) fn range13_uses(rows: &ScalarModMulMergedRows) -> Vec<M31> {
    ScalarModMulLookupUses::from_rows(rows).range13
}

fn gen_base_trace_inner(
    rows: &ScalarModMulMergedRows,
    lookup_claims: &LookupProviderClaims,
    include_range13_provider: bool,
) -> Vec<M31ColumnEval> {
    let family_traces = ScalarModMulFamilyTraces::from_rows(rows).to_circle_evaluations();
    let lookup_traces =
        LookupProviderTraces::from_uses(lookup_claims, ScalarModMulLookupUses::from_rows(rows));

    let mut trace = Vec::new();
    trace.extend(family_traces.canonical_scalars);
    trace.extend(family_traces.ab_chunks);
    trace.extend(family_traces.qn_chunks);
    trace.extend(family_traces.accumulators);
    trace.extend(family_traces.reduction_digits);
    if include_range13_provider {
        trace.push(lookup_traces.range13_multiplicity);
    }
    trace.push(lookup_traces.signed_carry_multiplicity);
    trace
}

#[cfg(test)]
pub(crate) fn gen_interaction_trace(
    rows: &ScalarModMulMergedRows,
    claim: &ScalarModMulClaim,
    lookup_claims: &LookupProviderClaims,
    relations: &ScalarModMulLookupRelations,
) -> (Vec<M31ColumnEval>, ScalarModMulProofSliceInteractionClaim) {
    gen_interaction_trace_inner(rows, claim, lookup_claims, relations, true)
}

pub(crate) fn gen_interaction_trace_without_range13_provider(
    rows: &ScalarModMulMergedRows,
    claim: &ScalarModMulClaim,
    lookup_claims: &LookupProviderClaims,
    relations: &ScalarModMulLookupRelations,
) -> (Vec<M31ColumnEval>, ScalarModMulProofSliceInteractionClaim) {
    gen_interaction_trace_inner(rows, claim, lookup_claims, relations, false)
}

fn gen_interaction_trace_inner(
    rows: &ScalarModMulMergedRows,
    claim: &ScalarModMulClaim,
    lookup_claims: &LookupProviderClaims,
    relations: &ScalarModMulLookupRelations,
    include_range13_provider: bool,
) -> (Vec<M31ColumnEval>, ScalarModMulProofSliceInteractionClaim) {
    let scalar_relations = relations.scalar_mod_mul();
    let (scalar_trace, scalar_claim) = ScalarModMulInteractionTraces::from_rows(
        rows,
        claim.external_limb_links,
        &scalar_relations,
    );
    let lookup_traces =
        LookupProviderTraces::from_uses(lookup_claims, ScalarModMulLookupUses::from_rows(rows));
    let (range13_trace, range13_claim) = if include_range13_provider {
        RangeCheckInteractionClaim::gen_interaction_trace(
            &lookup_traces.range13_multiplicity,
            &lookup_traces.range13_value,
            &relations.range13,
        )
    } else {
        (
            Vec::new(),
            RangeCheckInteractionClaim {
                claimed_sum: SecureField::from(M31::from_u32_unchecked(0)),
            },
        )
    };
    let (signed_carry_trace, signed_carry_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(
            &lookup_traces.signed_carry_multiplicity,
            &lookup_traces.signed_carry_value,
            &relations.signed_carry,
        );

    let mut trace = Vec::new();
    trace.extend(scalar_trace.canonical_scalars);
    trace.extend(scalar_trace.ab_chunks);
    trace.extend(scalar_trace.qn_chunks);
    trace.extend(scalar_trace.accumulators);
    trace.extend(scalar_trace.reduction_digits);
    trace.extend(range13_trace);
    trace.extend(signed_carry_trace);

    (
        trace,
        ScalarModMulProofSliceInteractionClaim {
            scalar_mod_mul: scalar_claim,
            range13: range13_claim,
            signed_carry: signed_carry_claim,
        },
    )
}

#[cfg(test)]
mod tests {
    use stwo_p256_utils::scalar_arithmetic::{ScalarFieldMulTrace, P256_ORDER};

    use super::*;

    fn scalar(value: u64) -> [u64; 4] {
        [value, 0, 0, 0]
    }

    fn test_rows() -> ScalarModMulMergedRows {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("valid scalar mod-mul trace");
        ScalarModMulMergedRows::new(vec![
            super::super::ScalarModMulTraceRows::new(3, &trace).expect("trace rows generate")
        ])
    }

    #[test]
    fn scalar_mod_mul_claim_records_family_log_sizes() {
        let claim = ScalarModMulClaim::from_rows(&test_rows());

        assert_eq!(claim.mul_ids, vec![3]);
        assert_eq!(claim.canonical_log_size, padded_log_size(4));
        assert_eq!(claim.ab_chunks_log_size, 8);
        assert_eq!(claim.qn_chunks_log_size, 8);
        assert_eq!(claim.accumulator_log_size, 7);
        assert_eq!(claim.reduction_log_size, 6);
    }
}
