//! Native witness, claim, and base/preprocessed-trace generation for the projective RCB
//! multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::{
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    ColumnVec,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::solinas::REDUCTION_MATRIX;

use super::*;
use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{
    FpSolinasError, FpSolinasMulTrace, FP_SOLINAS_LIMB_BASE, FP_SOLINAS_RAW_LIMBS,
};
use crate::fp_solinas_air::{
    fp_solinas_correction_digit_columns, FpSolinasReductionTraceClaim,
    FpSolinasReductionTraceError, FP_SOLINAS_REDUCTION_DIGITS,
};
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim, ProjectivePoint,
};
use crate::range_checks::{
    RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    RANGE13_BITS, RANGE16_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::U256;

/// Schedule-column id namespace for the canonical EC projective-RCB mul trace.
/// Empty so existing preprocessed-column ids are unchanged.
pub const PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC: &str = "";

/// Schedule-column id namespace for the public-key-on-curve mul trace. Keeps the
/// public-key sub-graph's schedule preprocessed columns distinct from the EC
/// projective ones so the two mul traces can coexist in one proof.
pub const PROJECTIVE_RCB_SCHEDULE_NAMESPACE_PUBLIC_KEY: &str = "public_key_";

/// Schedule-column id namespace for the final EC-addition mul trace
/// (`final_add_air.rs`). Distinct prefix so its schedule preprocessed columns
/// coexist with the EC and public-key mul traces in one proof.
pub const PROJECTIVE_RCB_SCHEDULE_NAMESPACE_FINAL_ADD: &str = "final_add_";

pub struct ProjectiveRcbRawProductChunkScheduleColumnIds;

impl ProjectiveRcbRawProductChunkScheduleColumnIds {
    pub fn active(namespace: &str) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, "active")
    }

    pub fn coeff(namespace: &str) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, "coeff")
    }

    pub fn chunk(namespace: &str) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, "chunk")
    }

    pub fn term_active(namespace: &str, term: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, format!("term_active_{term}"))
    }

    pub fn lhs_index(namespace: &str, term: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, format!("lhs_index_{term}"))
    }

    pub fn rhs_index(namespace: &str, term: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, format!("rhs_index_{term}"))
    }

    pub fn digit_use_count(namespace: &str, offset: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(namespace, format!("digit_use_count_{offset}"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductChunkScheduleColumn {
    pub id: PreProcessedColumnId,
    pub values: Vec<M31>,
}

pub struct ProjectiveRcbFoldedContributionScheduleColumnIds;

impl ProjectiveRcbFoldedContributionScheduleColumnIds {
    pub fn active(namespace: &str) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, "active")
    }

    pub fn digit_index(namespace: &str) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, "digit_index")
    }

    pub fn group_index(namespace: &str) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, "group_index")
    }

    pub fn term_active(namespace: &str, term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, format!("term_active_{term}"))
    }

    pub fn raw_coeff(namespace: &str, term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, format!("raw_coeff_{term}"))
    }

    pub fn raw_chunk(namespace: &str, term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, format!("raw_chunk_{term}"))
    }

    pub fn raw_offset(namespace: &str, term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, format!("raw_offset_{term}"))
    }

    pub fn matrix_coeff(namespace: &str, term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(namespace, format!("matrix_coeff_{term}"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedContributionScheduleColumn {
    pub id: PreProcessedColumnId,
    pub values: Vec<M31>,
}

pub struct ProjectiveRcbFoldedDigitScheduleColumnIds;

impl ProjectiveRcbFoldedDigitScheduleColumnIds {
    pub fn active(namespace: &str) -> PreProcessedColumnId {
        folded_digit_schedule_id(namespace, "active")
    }

    pub fn digit_index(namespace: &str) -> PreProcessedColumnId {
        folded_digit_schedule_id(namespace, "digit_index")
    }

    pub fn group_active(namespace: &str, group: usize) -> PreProcessedColumnId {
        folded_digit_schedule_id(namespace, format!("group_active_{group}"))
    }

    pub fn group_index(namespace: &str, group: usize) -> PreProcessedColumnId {
        folded_digit_schedule_id(namespace, format!("group_index_{group}"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedDigitScheduleColumn {
    pub id: PreProcessedColumnId,
    pub values: Vec<M31>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirComponentLogSizes {
    pub mul: u32,
    pub raw_product_chunk: u32,
    pub folded_contribution: u32,
    pub folded_digit: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirProofClaim {
    pub log_sizes: ProjectiveRcbAirComponentLogSizes,
}

impl ProjectiveRcbAirProofClaim {
    pub fn from_trace(trace: &ProjectiveRcbAirTraceClaim) -> Self {
        Self {
            log_sizes: trace.component_log_sizes(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_sizes.mul as u64);
        channel.mix_u64(self.log_sizes.raw_product_chunk as u64);
        channel.mix_u64(self.log_sizes.folded_contribution as u64);
        channel.mix_u64(self.log_sizes.folded_digit as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = ProjectiveRcbAirComponents::new_with_log_sizes(
            &mut allocator,
            self.log_sizes,
            &ProjectiveRcbAirProofInteractionClaim::zero(),
            &ProjectiveRcbMulComponentRelations::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = ProjectiveRcbAirComponents::new_with_log_sizes(
            &mut allocator,
            self.log_sizes,
            &ProjectiveRcbAirProofInteractionClaim::zero(),
            &ProjectiveRcbMulComponentRelations::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = ProjectiveRcbAirComponents::new_with_log_sizes(
            &mut allocator,
            self.log_sizes,
            &ProjectiveRcbAirProofInteractionClaim::zero(),
            &ProjectiveRcbMulComponentRelations::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

pub(crate) fn projective_rcb_signed_carry_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        projective_rcb_signed_carry_log_size(),
        PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
        PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirTraceClaim {
    pub rows: Vec<ProjectiveRcbAirRow>,
}

impl ProjectiveRcbAirTraceClaim {
    pub fn from_projective_trace(
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let rows = trace
            .rows
            .iter()
            .enumerate()
            .map(|(source_index, row)| ProjectiveRcbAirRow::from_projective_row(source_index, row))
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { rows };
        claim.verify_against_projective_trace(trace)?;
        Ok(claim)
    }

    pub fn verify_against_projective_trace(
        &self,
        trace: &ProjectiveEcTraceClaim,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != trace.rows.len() {
            return Err(ProjectiveRcbAirError::RowCountMismatch {
                expected: trace.rows.len(),
                actual: self.rows.len(),
            });
        }
        for (source_index, (air_row, projective_row)) in
            self.rows.iter().zip(&trace.rows).enumerate()
        {
            air_row.verify_against_projective_row(source_index, projective_row)?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn mul_row_count(&self) -> usize {
        self.rows.iter().map(|row| row.muls.len()).sum()
    }

    pub fn reduction_row_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.reduction.rows.len())
            .sum()
    }

    pub fn raw_product_chunk_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.raw_product_chunks.len())
            .sum()
    }

    pub fn folded_digit_row_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.folded_digits.rows.len())
            .sum()
    }

    pub fn folded_contribution_row_count(&self) -> usize {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .map(|mul| mul.folded_contributions.rows.len())
            .sum()
    }

    pub fn internal_interaction_claim(
        &self,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> ProjectiveRcbAirInteractionClaim {
        ProjectiveRcbAirInteractionClaim::from_trace(self, relations)
    }

    pub fn component_log_sizes(&self) -> ProjectiveRcbAirComponentLogSizes {
        ProjectiveRcbAirComponentLogSizes {
            mul: padded_log_size(self.mul_row_count()),
            raw_product_chunk: padded_log_size(self.raw_product_chunk_count()),
            folded_contribution: padded_log_size(self.folded_contribution_row_count()),
            folded_digit: padded_log_size(self.folded_digit_row_count()),
        }
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        self.preprocessed_column_ids_with_namespace(PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC)
    }

    /// Preprocessed schedule-column ids for this mul trace under a given
    /// schedule namespace. The public-key sub-graph uses
    /// [`PROJECTIVE_RCB_SCHEDULE_NAMESPACE_PUBLIC_KEY`] so its schedule columns
    /// stay distinct from the EC projective trace's.
    pub(crate) fn preprocessed_column_ids_with_namespace(
        &self,
        namespace: &'static str,
    ) -> Vec<PreProcessedColumnId> {
        let log_sizes = self.component_log_sizes();
        let mut allocator = TraceLocationAllocator::default();
        let relations = ProjectiveRcbMulComponentRelations::dummy();
        let zero = secure_zero();
        let _ = ProjectiveRcbMulComponent::new(
            &mut allocator,
            ProjectiveRcbMulEval {
                log_size: log_sizes.mul,
                relations: relations.clone(),
            },
            zero,
        );
        let _ = ProjectiveRcbRawProductChunkComponent::new(
            &mut allocator,
            ProjectiveRcbRawProductChunkEval {
                log_size: log_sizes.raw_product_chunk,
                relations: relations.clone(),
                schedule_namespace: namespace,
            },
            zero,
        );
        let _ = ProjectiveRcbFoldedContributionComponent::new(
            &mut allocator,
            ProjectiveRcbFoldedContributionEval {
                log_size: log_sizes.folded_contribution,
                relations: relations.clone(),
                schedule_namespace: namespace,
            },
            zero,
        );
        let _ = ProjectiveRcbFoldedDigitComponent::new(
            &mut allocator,
            ProjectiveRcbFoldedDigitEval {
                log_size: log_sizes.folded_digit,
                relations,
                schedule_namespace: namespace,
            },
            zero,
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn gen_preprocessed_trace(
        &self,
        ids: &[PreProcessedColumnId],
    ) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        self.gen_preprocessed_trace_with_namespace(ids, PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC)
    }

    /// Schedule preprocessed trace for this mul trace under a given namespace.
    pub(crate) fn gen_preprocessed_trace_with_namespace(
        &self,
        ids: &[PreProcessedColumnId],
        namespace: &str,
    ) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        let columns = projective_rcb_air_schedule_preprocessed_columns(self, namespace);
        ids.iter()
            .map(|id| {
                columns
                    .iter()
                    .find_map(|(column_id, eval)| (column_id == id).then(|| eval.clone()))
                    .ok_or_else(|| ProjectiveRcbAirError::PreprocessedColumnMissing {
                        id: id.id.clone(),
                    })
            })
            .collect()
    }

    pub fn verify_preprocessed_trace(&self) -> Result<(), ProjectiveRcbAirError> {
        let ids = self.preprocessed_column_ids();
        let preprocessed = self.gen_preprocessed_trace(&ids)?;
        if ids.len() == preprocessed.len() {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::PreprocessedColumnCountMismatch {
                expected: ids.len(),
                actual: preprocessed.len(),
            })
        }
    }

    pub fn gen_base_trace(&self) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        let log_sizes = self.component_log_sizes();
        let mut columns = Vec::new();
        columns.extend(gen_projective_rcb_mul_base_trace(self, log_sizes.mul)?);
        columns.extend(gen_projective_rcb_raw_product_chunk_base_trace(
            self,
            log_sizes.raw_product_chunk,
        )?);
        columns.extend(gen_projective_rcb_folded_contribution_base_trace(
            self,
            log_sizes.folded_contribution,
        )?);
        columns.extend(gen_projective_rcb_folded_digit_base_trace(
            self,
            log_sizes.folded_digit,
        )?);
        Ok(columns)
    }

    pub fn verify_base_trace(&self) -> Result<(), ProjectiveRcbAirError> {
        let base = self.gen_base_trace()?;
        let expected = PROJECTIVE_RCB_MUL_TRACE_COLUMNS
            + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS;
        if base.len() == expected {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::BaseTraceColumnCountMismatch {
                expected,
                actual: base.len(),
            })
        }
    }

    pub fn gen_interaction_trace(
        &self,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> (
        ProjectiveRcbAirInteractionTraces,
        ProjectiveRcbAirComponentInteractionClaim,
    ) {
        let log_sizes = self.component_log_sizes();
        let (mul, mul_claim) = gen_projective_rcb_family_interaction_trace(
            log_sizes.mul,
            self.mul_rows().map(|(source_index, mul_index, mul)| {
                projective_rcb_mul_row_fractions(source_index, mul_index, mul)
            }),
            projective_rcb_mul_padding_fractions(),
            relations,
            false,
        );
        let (raw_product_chunk, raw_product_chunk_claim) =
            gen_projective_rcb_family_interaction_trace(
                log_sizes.raw_product_chunk,
                self.raw_product_chunk_rows()
                    .map(projective_rcb_raw_product_chunk_fractions),
                projective_rcb_raw_product_chunk_padding_fractions(),
                relations,
                true,
            );
        let (folded_contribution, folded_contribution_claim) =
            gen_projective_rcb_family_interaction_trace(
                log_sizes.folded_contribution,
                self.folded_contribution_rows()
                    .map(projective_rcb_folded_contribution_fractions),
                projective_rcb_folded_contribution_padding_fractions(),
                relations,
                false,
            );
        let (folded_digit, folded_digit_claim) = gen_projective_rcb_family_interaction_trace(
            log_sizes.folded_digit,
            self.folded_digit_rows()
                .map(projective_rcb_folded_digit_fractions),
            projective_rcb_folded_digit_padding_fractions(),
            relations,
            false,
        );

        (
            ProjectiveRcbAirInteractionTraces {
                mul,
                raw_product_chunk,
                folded_contribution,
                folded_digit,
            },
            ProjectiveRcbAirComponentInteractionClaim {
                mul: mul_claim,
                raw_product_chunk: raw_product_chunk_claim,
                folded_contribution: folded_contribution_claim,
                folded_digit: folded_digit_claim,
            },
        )
    }

    pub fn proof_slice_preprocessed_column_ids(
        &self,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let interaction_claim = ProjectiveRcbAirProofInteractionClaim {
            components: ProjectiveRcbAirComponentInteractionClaim {
                mul: secure_zero(),
                raw_product_chunk: secure_zero(),
                folded_contribution: secure_zero(),
                folded_digit: secure_zero(),
            },
            range13: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            signed_carry: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            raw_product_carry16: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
        };
        let _ =
            ProjectiveRcbAirComponents::new(&mut allocator, self, &interaction_claim, relations);
        allocator.preprocessed_columns().clone()
    }

    pub fn gen_proof_slice_preprocessed_trace(
        &self,
        ids: &[PreProcessedColumnId],
    ) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        let mut columns = projective_rcb_air_schedule_preprocessed_columns(
            self,
            PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        );
        let range13 = RangeCheckClaim::new(RANGE13_BITS);
        columns.push((
            crate::range_checks::range_check_value_column_id(RANGE13_BITS),
            range13.gen_preprocessed_column(),
        ));
        let raw_product_carry16 = RangeCheckClaim::new(RANGE16_BITS);
        columns.push((
            crate::range_checks::range_check_value_column_id(RANGE16_BITS),
            raw_product_carry16.gen_preprocessed_column(),
        ));
        let signed_carry = projective_rcb_signed_carry_claim();
        columns.push((
            crate::range_checks::signed_carry_value_column_id(PROJECTIVE_RCB_SIGNED_CARRY_EQUATION),
            signed_carry.gen_value_column(),
        ));
        columns.push((
            crate::range_checks::signed_carry_active_column_id(
                PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
            ),
            signed_carry.gen_active_column(),
        ));

        ids.iter()
            .map(|id| {
                columns
                    .iter()
                    .find_map(|(column_id, eval)| (column_id == id).then(|| eval.clone()))
                    .ok_or_else(|| ProjectiveRcbAirError::PreprocessedColumnMissing {
                        id: id.id.clone(),
                    })
            })
            .collect()
    }

    pub fn gen_proof_slice_base_trace(&self) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        let mut trace = self.gen_base_trace()?;
        let range13 = RangeCheckClaim::new(RANGE13_BITS);
        trace.push(range13.gen_multiplicity_trace(self.range13_lookup_values()));
        let raw_product_carry16 = RangeCheckClaim::new(RANGE16_BITS);
        trace.push(
            raw_product_carry16.gen_multiplicity_trace(self.raw_product_carry16_lookup_values()),
        );
        trace.push(
            projective_rcb_signed_carry_claim()
                .gen_multiplicity_trace(self.signed_carry_lookup_values()?),
        );
        Ok(trace)
    }

    pub fn gen_proof_slice_interaction_trace(
        &self,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Result<(Vec<M31ColumnEval>, ProjectiveRcbAirProofInteractionClaim), ProjectiveRcbAirError>
    {
        let (component_traces, component_claim) = self.gen_interaction_trace(relations);
        let mut trace = component_traces.into_columns();

        let range13 = RangeCheckClaim::new(RANGE13_BITS);
        let range13_values = range13.gen_preprocessed_column();
        let range13_multiplicity = range13.gen_multiplicity_trace(self.range13_lookup_values());
        let (range13_trace, range13_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
            &range13_multiplicity,
            &range13_values,
            &relations.range13,
        );
        trace.extend(range13_trace);

        let raw_product_carry16 = RangeCheckClaim::new(RANGE16_BITS);
        let raw_product_carry16_values = raw_product_carry16.gen_preprocessed_column();
        let raw_product_carry16_multiplicity =
            raw_product_carry16.gen_multiplicity_trace(self.raw_product_carry16_lookup_values());
        let (raw_product_carry16_trace, raw_product_carry16_claim) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &raw_product_carry16_multiplicity,
                &raw_product_carry16_values,
                &relations.raw_product_carry16,
            );
        trace.extend(raw_product_carry16_trace);

        let signed_carry = projective_rcb_signed_carry_claim();
        let signed_carry_values = signed_carry.gen_value_column();
        let signed_carry_multiplicity =
            signed_carry.gen_multiplicity_trace(self.signed_carry_lookup_values()?);
        let (signed_carry_trace, signed_carry_claim) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &signed_carry_multiplicity,
                &signed_carry_values,
                &relations.signed_carry,
            );
        trace.extend(signed_carry_trace);

        Ok((
            trace,
            ProjectiveRcbAirProofInteractionClaim {
                components: component_claim,
                range13: range13_claim,
                raw_product_carry16: raw_product_carry16_claim,
                signed_carry: signed_carry_claim,
            },
        ))
    }

    pub fn verify_proof_slice_traces(
        &self,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Result<(), ProjectiveRcbAirError> {
        let ids = self.proof_slice_preprocessed_column_ids(relations);
        let preprocessed = self.gen_proof_slice_preprocessed_trace(&ids)?;
        let base = self.gen_proof_slice_base_trace()?;
        let (_, interaction_claim) = self.gen_proof_slice_interaction_trace(relations)?;
        if preprocessed.len() != ids.len() {
            return Err(ProjectiveRcbAirError::PreprocessedColumnCountMismatch {
                expected: ids.len(),
                actual: preprocessed.len(),
            });
        }
        let expected_base = PROJECTIVE_RCB_MUL_TRACE_COLUMNS
            + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
            + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
            + 3;
        if base.len() != expected_base {
            return Err(ProjectiveRcbAirError::BaseTraceColumnCountMismatch {
                expected: expected_base,
                actual: base.len(),
            });
        }
        verify_relation_zero("ProjectiveRcbAirProofSlice", interaction_claim.total())
    }

    pub fn verify_interaction_trace(
        &self,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Result<(), ProjectiveRcbAirError> {
        let (traces, claim) = self.gen_interaction_trace(relations);
        let expected = projective_rcb_mul_interaction_columns()
            + projective_rcb_raw_product_chunk_interaction_columns()
            + projective_rcb_folded_contribution_interaction_columns()
            + projective_rcb_folded_digit_interaction_columns();
        let actual = traces.into_columns().len();
        if actual != expected {
            return Err(ProjectiveRcbAirError::InteractionTraceColumnCountMismatch {
                expected,
                actual,
            });
        }
        let _ = claim;
        Ok(())
    }

    pub fn range13_lookup_values(&self) -> Vec<M31> {
        let mut values = Vec::new();
        for (_, _, mul) in self.mul_rows() {
            values.extend(mul.trace.lhs.limbs().iter().copied());
            values.extend(mul.trace.rhs.limbs().iter().copied());
            values.extend(mul.trace.result.limbs().iter().copied());
            for row in &mul.reduction.rows {
                values.push(m31(row.folded_digit));
                values.push(m31(row.result_limb));
            }
            let (_, correction_digits) = fp_solinas_correction_digit_columns(mul.trace.correction)
                .expect("mul trace correction fits the signed window");
            values.extend(correction_digits.iter().copied().map(m31));
            for chunk in &mul.raw_product_chunks {
                values.extend(chunk.digits.iter().copied().map(m31));
            }
            for row in &mul.folded_digits.rows {
                values.push(m31(row.folded_digit));
            }
        }
        values
    }

    pub fn signed_carry_lookup_values(&self) -> Result<Vec<i64>, ProjectiveRcbAirError> {
        let mut values = Vec::new();
        for (_, _, mul) in self.mul_rows() {
            for row in &mul.reduction.rows {
                push_signed_carry_lookup(&mut values, row.prev_carry)?;
                push_signed_carry_lookup(&mut values, row.carry)?;
            }
            for row in &mul.folded_digits.rows {
                push_signed_carry_lookup(&mut values, row.prev_carry)?;
                push_signed_carry_lookup(&mut values, row.carry)?;
            }
        }
        Ok(values)
    }

    pub fn raw_product_carry16_lookup_values(&self) -> Vec<M31> {
        self.raw_product_chunk_rows()
            .map(|chunk| m31(chunk.carry1))
            .collect()
    }

    pub fn range13_consumer_claimed_sum(&self, relation: &RangeCheckRelation) -> SecureField {
        self.range13_lookup_values()
            .into_iter()
            .map(|value| relation_fraction(relation, 1, &[value]))
            .sum()
    }

    pub fn raw_product_carry16_consumer_claimed_sum(
        &self,
        relation: &RangeCheckRelation,
    ) -> SecureField {
        self.raw_product_carry16_lookup_values()
            .into_iter()
            .map(|value| relation_fraction(relation, 1, &[value]))
            .sum()
    }

    pub fn signed_carry_consumer_claimed_sum(
        &self,
        relation: &RangeCheckRelation,
    ) -> Result<SecureField, ProjectiveRcbAirError> {
        Ok(self
            .signed_carry_lookup_values()?
            .into_iter()
            .map(|value| relation_fraction(relation, 1, &[m31_i128(i128::from(value))]))
            .sum())
    }

    fn mul_rows(&self) -> impl Iterator<Item = (usize, usize, &ProjectiveRcbMulRow)> {
        self.rows.iter().flat_map(|row| {
            row.muls
                .iter()
                .enumerate()
                .map(move |(mul_index, mul)| (row.source_index, mul_index, mul))
        })
    }

    fn raw_product_chunk_rows(&self) -> impl Iterator<Item = &ProjectiveRcbRawProductChunkRow> {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .flat_map(|mul| &mul.raw_product_chunks)
    }

    fn folded_contribution_rows(
        &self,
    ) -> impl Iterator<Item = &ProjectiveRcbFoldedContributionRow> {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .flat_map(|mul| &mul.folded_contributions.rows)
    }

    fn folded_digit_rows(&self) -> impl Iterator<Item = &ProjectiveRcbFoldedDigitRow> {
        self.rows
            .iter()
            .flat_map(|row| &row.muls)
            .flat_map(|mul| &mul.folded_digits.rows)
    }
}

pub fn projective_rcb_raw_product_chunk_schedule_columns(
) -> Vec<ProjectiveRcbRawProductChunkScheduleColumn> {
    projective_rcb_raw_product_chunk_schedule_columns_for_mul_count(
        PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        1,
    )
}

fn projective_rcb_raw_product_chunk_schedule_columns_for_mul_count(
    namespace: &str,
    mul_count: usize,
) -> Vec<ProjectiveRcbRawProductChunkScheduleColumn> {
    let active_rows = mul_count * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS;
    let padded_rows = 1usize << padded_log_size(active_rows);
    let mut active = vec![m31(0); padded_rows];
    let mut coeff = vec![m31(0); padded_rows];
    let mut chunk = vec![m31(0); padded_rows];
    let mut term_active = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
    let mut lhs_index = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
    let mut rhs_index = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
    let mut digit_use_count =
        vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS];

    let mut row = 0usize;
    for _ in 0..mul_count {
        for row_coeff in 0..FP_SOLINAS_RAW_LIMBS {
            for row_chunk in 0..coefficient_chunk_count(row_coeff) {
                let pairs =
                    product_chunk_pairs(row_coeff, row_chunk).expect("valid fixed chunk schedule");
                active[row] = m31(1);
                coeff[row] = m31_usize(row_coeff);
                chunk[row] = m31_usize(row_chunk);
                for (term, pair) in pairs.into_iter().enumerate() {
                    if let Some((lhs, rhs)) = pair {
                        term_active[term][row] = m31(1);
                        lhs_index[term][row] = m31_usize(lhs);
                        rhs_index[term][row] = m31_usize(rhs);
                    }
                }
                for (offset, column) in digit_use_count.iter_mut().enumerate() {
                    column[row] =
                        m31_usize(raw_product_chunk_digit_use_count_const(row_coeff, offset));
                }
                row += 1;
            }
        }
    }
    debug_assert_eq!(row, active_rows);

    let mut columns = vec![
        raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::active(namespace),
            active,
        ),
        raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::coeff(namespace),
            coeff,
        ),
        raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::chunk(namespace),
            chunk,
        ),
    ];
    for term in 0..PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS {
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::term_active(namespace, term),
            term_active[term].clone(),
        ));
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::lhs_index(namespace, term),
            lhs_index[term].clone(),
        ));
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::rhs_index(namespace, term),
            rhs_index[term].clone(),
        ));
    }
    for (offset, values) in digit_use_count.into_iter().enumerate() {
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::digit_use_count(namespace, offset),
            values,
        ));
    }
    columns
}

pub fn projective_rcb_raw_product_chunk_schedule_evals() -> Vec<M31ColumnEval> {
    schedule_columns_to_evals(projective_rcb_raw_product_chunk_schedule_columns())
}

pub fn projective_rcb_folded_contribution_schedule_columns(
) -> Vec<ProjectiveRcbFoldedContributionScheduleColumn> {
    projective_rcb_folded_contribution_schedule_columns_for_mul_count(
        PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        1,
    )
}

fn projective_rcb_folded_contribution_schedule_columns_for_mul_count(
    namespace: &str,
    mul_count: usize,
) -> Vec<ProjectiveRcbFoldedContributionScheduleColumn> {
    let active_rows = mul_count * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS;
    let padded_rows = 1usize << padded_log_size(active_rows);
    let mut active = vec![m31(0); padded_rows];
    let mut digit_index = vec![m31(0); padded_rows];
    let mut group_index = vec![m31(0); padded_rows];
    let mut term_active = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS];
    let mut raw_coeff = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS];
    let mut raw_chunk = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS];
    let mut raw_offset = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS];
    let mut matrix_coeff =
        vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS];

    let terms = folded_contribution_schedule_terms();
    let mut row = 0usize;
    for _ in 0..mul_count {
        for row_digit_index in 0..FP_SOLINAS_REDUCTION_DIGITS {
            let digit_terms = terms
                .iter()
                .copied()
                .filter(|term| term.digit_index == row_digit_index)
                .collect::<Vec<_>>();
            for (row_group_index, chunk) in digit_terms
                .chunks(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)
                .enumerate()
            {
                active[row] = m31(1);
                digit_index[row] = m31_usize(row_digit_index);
                group_index[row] = m31_usize(row_group_index);
                for (term_index, term) in chunk.iter().copied().enumerate() {
                    term_active[term_index][row] = m31(1);
                    raw_coeff[term_index][row] = m31_usize(term.raw_coeff);
                    raw_chunk[term_index][row] = m31_usize(term.raw_chunk);
                    raw_offset[term_index][row] = m31_usize(term.raw_offset);
                    matrix_coeff[term_index][row] = m31_i128(i128::from(term.matrix_coeff));
                }
                row += 1;
            }
            if digit_terms.is_empty() {
                active[row] = m31(1);
                digit_index[row] = m31_usize(row_digit_index);
                row += 1;
            }
        }
    }
    debug_assert_eq!(row, active_rows);

    let mut columns = vec![
        folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::active(namespace),
            active,
        ),
        folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::digit_index(namespace),
            digit_index,
        ),
        folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::group_index(namespace),
            group_index,
        ),
    ];
    for term in 0..PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS {
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::term_active(namespace, term),
            term_active[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::raw_coeff(namespace, term),
            raw_coeff[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::raw_chunk(namespace, term),
            raw_chunk[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::raw_offset(namespace, term),
            raw_offset[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(namespace, term),
            matrix_coeff[term].clone(),
        ));
    }
    columns
}

pub fn projective_rcb_folded_contribution_schedule_evals() -> Vec<M31ColumnEval> {
    schedule_columns_to_evals(projective_rcb_folded_contribution_schedule_columns())
}

pub fn projective_rcb_folded_digit_schedule_columns() -> Vec<ProjectiveRcbFoldedDigitScheduleColumn>
{
    projective_rcb_folded_digit_schedule_columns_for_mul_count(
        PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
        1,
    )
}

fn projective_rcb_folded_digit_schedule_columns_for_mul_count(
    namespace: &str,
    mul_count: usize,
) -> Vec<ProjectiveRcbFoldedDigitScheduleColumn> {
    let active_rows = mul_count * FP_SOLINAS_REDUCTION_DIGITS;
    let padded_rows = 1usize << padded_log_size(active_rows);
    let mut active = vec![m31(0); padded_rows];
    let mut digit_index = vec![m31(0); padded_rows];
    let mut group_active = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS];
    let mut group_index = vec![vec![m31(0); padded_rows]; PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS];

    let mut row = 0usize;
    for _ in 0..mul_count {
        for row_digit_index in 0..FP_SOLINAS_REDUCTION_DIGITS {
            active[row] = m31(1);
            digit_index[row] = m31_usize(row_digit_index);
            let group_count = folded_contribution_group_count_for_digit_const(row_digit_index);
            for group in 0..group_count {
                group_active[group][row] = m31(1);
                group_index[group][row] = m31_usize(group);
            }
            row += 1;
        }
    }
    debug_assert_eq!(row, active_rows);

    let mut columns = vec![
        folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::active(namespace),
            active,
        ),
        folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::digit_index(namespace),
            digit_index,
        ),
    ];
    for group in 0..PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS {
        columns.push(folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::group_active(namespace, group),
            group_active[group].clone(),
        ));
        columns.push(folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(namespace, group),
            group_index[group].clone(),
        ));
    }
    columns
}

pub fn projective_rcb_folded_digit_schedule_evals() -> Vec<M31ColumnEval> {
    schedule_columns_to_evals(projective_rcb_folded_digit_schedule_columns())
}

fn projective_rcb_air_schedule_preprocessed_columns(
    trace: &ProjectiveRcbAirTraceClaim,
    namespace: &str,
) -> Vec<(PreProcessedColumnId, M31ColumnEval)> {
    let mul_count = trace.mul_row_count();
    let mut columns = Vec::new();
    columns.extend(
        projective_rcb_raw_product_chunk_schedule_columns_for_mul_count(namespace, mul_count)
            .into_iter()
            .map(|column| column_to_eval(column.id, column.values)),
    );
    columns.extend(
        projective_rcb_folded_contribution_schedule_columns_for_mul_count(namespace, mul_count)
            .into_iter()
            .map(|column| column_to_eval(column.id, column.values)),
    );
    columns.extend(
        projective_rcb_folded_digit_schedule_columns_for_mul_count(namespace, mul_count)
            .into_iter()
            .map(|column| column_to_eval(column.id, column.values)),
    );
    columns
}

pub(crate) fn gen_projective_rcb_mul_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row
            .muls
            .iter()
            .enumerate()
            .map(move |(mul_index, mul)| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_MUL_TRACE_COLUMNS);
                row.push(m31(1));
                row.push(m31_usize(air_row.source_index));
                row.push(m31_usize(mul_index));
                row.extend(mul.trace.lhs.limbs().iter().copied());
                row.extend(mul.trace.rhs.limbs().iter().copied());
                row.extend(mul.trace.result.limbs().iter().copied());
                row.push(m31_i128(mul.folded_digits.final_carry));
                for reduction in &mul.reduction.rows {
                    row.push(m31(reduction.folded_digit));
                    row.push(m31_i128(reduction.correction_product_digit));
                    row.push(m31(reduction.result_limb));
                    row.push(m31_i128(reduction.prev_carry));
                    row.push(m31_i128(reduction.carry));
                }
                let (sign_bit, correction_digits) =
                    fp_solinas_correction_digit_columns(mul.trace.correction)
                        .expect("mul trace correction fits the signed window");
                for digit in correction_digits {
                    row.push(m31(digit));
                }
                row.push(m31(sign_bit));
                row
            })
    });
    rows_to_base_trace(rows, PROJECTIVE_RCB_MUL_TRACE_COLUMNS, log_size)
}

pub(crate) fn gen_projective_rcb_raw_product_chunk_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row.muls.iter().flat_map(|mul| {
            mul.raw_product_chunks.iter().map(|chunk| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS);
                row.push(m31(1));
                row.push(m31_usize(chunk.source_index));
                row.push(m31_usize(chunk.mul_index));
                for term in &chunk.terms {
                    row.push(m31(u32::from(term.active)));
                    row.push(m31(term.lhs_limb));
                    row.push(m31(term.rhs_limb));
                    row.push(m31(term.lhs_limb * term.rhs_limb));
                }
                row.push(m31(chunk.carry1));
                row.extend(chunk.digits.iter().copied().map(m31));
                row.extend(chunk.digit_use_counts.iter().copied().map(m31));
                row
            })
        })
    });
    rows_to_base_trace(
        rows,
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS,
        log_size,
    )
}

pub(crate) fn gen_projective_rcb_folded_contribution_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row.muls.iter().flat_map(|mul| {
            mul.folded_contributions.rows.iter().map(|contribution| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS);
                row.push(m31(1));
                row.push(m31_usize(contribution.source_index));
                row.push(m31_usize(contribution.mul_index));
                for term in &contribution.terms {
                    row.push(m31(u32::from(term.active)));
                    row.push(m31_i128(i128::from(term.matrix_coeff)));
                    row.push(m31(term.raw_digit));
                    row.push(m31_i128(
                        i128::from(term.raw_digit) * i128::from(term.matrix_coeff),
                    ));
                }
                row.push(m31_i128(contribution.contribution_sum));
                row
            })
        })
    });
    rows_to_base_trace(
        rows,
        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS,
        log_size,
    )
}

pub(crate) fn gen_projective_rcb_folded_digit_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row.muls.iter().flat_map(|mul| {
            mul.folded_digits.rows.iter().map(|digit| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS);
                row.push(m31(1));
                row.push(m31_usize(digit.source_index));
                row.push(m31_usize(digit.mul_index));
                for group in &digit.contribution_groups {
                    row.push(m31(u32::from(group.active)));
                    row.push(m31_i128(group.contribution_sum));
                    row.push(if group.active {
                        m31_i128(group.contribution_sum)
                    } else {
                        m31(0)
                    });
                }
                row.push(m31_i128(digit.prev_carry));
                row.push(m31(digit.folded_digit));
                row.push(m31_i128(digit.carry));
                row
            })
        })
    });
    rows_to_base_trace(rows, PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS, log_size)
}

fn rows_to_base_trace(
    rows: impl IntoIterator<Item = Vec<M31>>,
    width: usize,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let row_count = 1usize << log_size;
    let mut columns = vec![vec![m31(0); row_count]; width];
    let mut actual_rows = 0usize;
    for (row_index, row) in rows.into_iter().enumerate() {
        if row.len() != width {
            return Err(ProjectiveRcbAirError::BaseTraceRowWidthMismatch {
                expected: width,
                actual: row.len(),
            });
        }
        if row_index >= row_count {
            return Err(ProjectiveRcbAirError::BaseTraceRowCountMismatch {
                max: row_count,
                actual: row_index + 1,
            });
        }
        for (column, value) in columns.iter_mut().zip(row) {
            column[row_index] = value;
        }
        actual_rows = row_index + 1;
    }
    debug_assert!(actual_rows <= row_count);
    Ok(columns
        .into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect())
}

fn schedule_columns_to_evals<C, I>(columns: I) -> Vec<M31ColumnEval>
where
    C: IntoScheduleColumn,
    I: IntoIterator<Item = C>,
{
    columns
        .into_iter()
        .map(|column| {
            let column = column.into_schedule_column();
            column_to_eval(column.id, column.values).1
        })
        .collect()
}

fn column_to_eval(
    id: PreProcessedColumnId,
    values: Vec<M31>,
) -> (PreProcessedColumnId, M31ColumnEval) {
    let log_size = values.len().trailing_zeros();
    (id, m31_column_eval(log_size, values))
}

struct ScheduleColumnParts {
    id: PreProcessedColumnId,
    values: Vec<M31>,
}

trait IntoScheduleColumn {
    fn into_schedule_column(self) -> ScheduleColumnParts;
}

impl IntoScheduleColumn for ProjectiveRcbRawProductChunkScheduleColumn {
    fn into_schedule_column(self) -> ScheduleColumnParts {
        ScheduleColumnParts {
            id: self.id,
            values: self.values,
        }
    }
}

impl IntoScheduleColumn for ProjectiveRcbFoldedContributionScheduleColumn {
    fn into_schedule_column(self) -> ScheduleColumnParts {
        ScheduleColumnParts {
            id: self.id,
            values: self.values,
        }
    }
}

impl IntoScheduleColumn for ProjectiveRcbFoldedDigitScheduleColumn {
    fn into_schedule_column(self) -> ScheduleColumnParts {
        ScheduleColumnParts {
            id: self.id,
            values: self.values,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirRow {
    pub source_index: usize,
    pub sig_id: M31,
    pub cert_id: M31,
    pub op: ProjectiveEcOp,
    pub output_projective: ProjectivePoint,
    pub muls: Vec<ProjectiveRcbMulRow>,
}

impl ProjectiveRcbAirRow {
    fn from_projective_row(
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<Self, ProjectiveRcbAirError> {
        row.verify()?;
        let lhs = ProjectivePoint::from_prepared(&row.lhs_affine);
        let mut muls = Vec::with_capacity(PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        let output_projective = match row.op {
            ProjectiveEcOp::Double => rcb_double_with_mul_rows(source_index, &lhs, &mut muls)?,
            ProjectiveEcOp::MixedAdd => {
                rcb_mixed_add_with_mul_rows(source_index, &lhs, &row.rhs_affine, &mut muls)?
            }
        };
        if output_projective != row.output_projective {
            return Err(ProjectiveRcbAirError::ProjectiveOutputMismatch { source_index });
        }
        Ok(Self {
            source_index,
            sig_id: row.sig_id,
            cert_id: row.cert_id,
            op: row.op,
            output_projective,
            muls,
        })
    }

    fn verify_against_projective_row(
        &self,
        source_index: usize,
        row: &ProjectiveEcRow,
    ) -> Result<(), ProjectiveRcbAirError> {
        self.verify()?;
        let expected = Self::from_projective_row(source_index, row)?;
        if self == &expected {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::TraceRowsMismatch { source_index })
        }
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        self.output_projective.verify()?;
        for mul in &self.muls {
            mul.verify()?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbMulRow {
    pub step: ProjectiveRcbMulStep,
    pub trace: FpSolinasMulTrace,
    pub raw_product_chunks: Vec<ProjectiveRcbRawProductChunkRow>,
    pub folded_contributions: ProjectiveRcbFoldedContributionTraceClaim,
    pub folded_digits: ProjectiveRcbFoldedDigitTraceClaim,
    pub reduction: FpSolinasReductionTraceClaim,
}

impl ProjectiveRcbMulRow {
    pub(crate) fn new(
        source_index: usize,
        mul_index: usize,
        step: ProjectiveRcbMulStep,
        lhs: &U256,
        rhs: &U256,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let trace = FpSolinasMulTrace::new(lhs, rhs)?;
        let raw_product_chunks =
            ProjectiveRcbRawProductTraceClaim::from_mul_trace(source_index, mul_index, &trace)?
                .rows;
        let folded_contributions = ProjectiveRcbFoldedContributionTraceClaim::from_raw_chunks(
            source_index,
            mul_index,
            &raw_product_chunks,
        )?;
        let folded_digits = ProjectiveRcbFoldedDigitTraceClaim::from_mul_trace(
            source_index,
            mul_index,
            &trace,
            &raw_product_chunks,
            &folded_contributions,
        )?;
        let reduction = FpSolinasReductionTraceClaim::from_mul_trace(&trace)?;
        Ok(Self {
            step,
            trace,
            raw_product_chunks,
            folded_contributions,
            folded_digits,
            reduction,
        })
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        self.trace.verify()?;
        ProjectiveRcbRawProductTraceClaim {
            rows: self.raw_product_chunks.clone(),
        }
        .verify_against_mul_trace(&self.trace)?;
        self.folded_contributions
            .verify_against_raw_chunks(&self.raw_product_chunks)?;
        self.folded_digits.verify_against_mul_trace(
            &self.trace,
            &self.raw_product_chunks,
            &self.folded_contributions,
        )?;
        self.folded_digits
            .verify_against_reduction(&self.reduction)?;
        self.reduction.verify_against_mul_trace(&self.trace)?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedContributionTraceClaim {
    pub rows: Vec<ProjectiveRcbFoldedContributionRow>,
}

impl ProjectiveRcbFoldedContributionTraceClaim {
    pub fn from_raw_chunks(
        source_index: usize,
        mul_index: usize,
        raw_product_chunks: &[ProjectiveRcbRawProductChunkRow],
    ) -> Result<Self, ProjectiveRcbAirError> {
        let terms = folded_contribution_terms(raw_product_chunks)?;
        let mut rows = Vec::new();
        for digit_index in 0..FP_SOLINAS_REDUCTION_DIGITS {
            let digit_terms = terms
                .iter()
                .copied()
                .filter(|term| term.digit_index == digit_index)
                .collect::<Vec<_>>();
            for (group_index, chunk) in digit_terms
                .chunks(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)
                .enumerate()
            {
                let mut row_terms = [ProjectiveRcbFoldedContributionTermRow::inactive();
                    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS];
                for (index, term) in chunk.iter().copied().enumerate() {
                    row_terms[index] = term;
                }
                rows.push(ProjectiveRcbFoldedContributionRow {
                    source_index,
                    mul_index,
                    digit_index,
                    group_index,
                    terms: row_terms,
                    contribution_sum: chunk.iter().map(|term| term.contribution()).sum(),
                });
            }
            if digit_terms.is_empty() {
                rows.push(ProjectiveRcbFoldedContributionRow {
                    source_index,
                    mul_index,
                    digit_index,
                    group_index: 0,
                    terms: [ProjectiveRcbFoldedContributionTermRow::inactive();
                        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS],
                    contribution_sum: 0,
                });
            }
        }
        let claim = Self { rows };
        claim.verify_rows()?;
        Ok(claim)
    }

    pub fn verify_against_raw_chunks(
        &self,
        raw_product_chunks: &[ProjectiveRcbRawProductChunkRow],
    ) -> Result<(), ProjectiveRcbAirError> {
        let expected = Self::from_raw_chunks(
            self.rows.first().map_or(0, |row| row.source_index),
            self.rows.first().map_or(0, |row| row.mul_index),
            raw_product_chunks,
        )?;
        if self == &expected {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::FoldedContributionMismatch)
        }
    }

    fn verify_rows(&self) -> Result<(), ProjectiveRcbAirError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    fn digit_groups(
        &self,
        digit_index: usize,
    ) -> Result<
        [ProjectiveRcbFoldedDigitContributionGroup; PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS],
        ProjectiveRcbAirError,
    > {
        let mut groups = [ProjectiveRcbFoldedDigitContributionGroup::inactive();
            PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS];
        for (count, row) in self
            .rows
            .iter()
            .filter(|row| row.digit_index == digit_index)
            .enumerate()
        {
            row.verify()?;
            if count >= PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS {
                return Err(
                    ProjectiveRcbAirError::FoldedDigitContributionGroupOverflow { digit_index },
                );
            }
            groups[count] = ProjectiveRcbFoldedDigitContributionGroup {
                active: true,
                group_index: row.group_index,
                contribution_sum: row.contribution_sum,
            };
        }
        Ok(groups)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedContributionRow {
    pub source_index: usize,
    pub mul_index: usize,
    pub digit_index: usize,
    pub group_index: usize,
    pub terms: [ProjectiveRcbFoldedContributionTermRow; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS],
    pub contribution_sum: i128,
}

impl ProjectiveRcbFoldedContributionRow {
    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        if self.digit_index >= FP_SOLINAS_REDUCTION_DIGITS {
            return Err(ProjectiveRcbAirError::FoldedContributionDigitOutOfRange {
                digit_index: self.digit_index,
            });
        }
        let sum = self
            .terms
            .iter()
            .filter(|term| term.active)
            .map(ProjectiveRcbFoldedContributionTermRow::contribution)
            .sum::<i128>();
        if sum == self.contribution_sum {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::FoldedContributionSumMismatch {
                digit_index: self.digit_index,
                group_index: self.group_index,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedContributionTermRow {
    pub active: bool,
    pub digit_index: usize,
    pub raw_coeff: usize,
    pub raw_chunk: usize,
    pub raw_offset: usize,
    pub matrix_coeff: i64,
    pub raw_digit: u32,
}

impl ProjectiveRcbFoldedContributionTermRow {
    const fn inactive() -> Self {
        Self {
            active: false,
            digit_index: 0,
            raw_coeff: 0,
            raw_chunk: 0,
            raw_offset: 0,
            matrix_coeff: 0,
            raw_digit: 0,
        }
    }

    fn contribution(&self) -> i128 {
        i128::from(self.matrix_coeff) * i128::from(self.raw_digit)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedDigitTraceClaim {
    pub rows: Vec<ProjectiveRcbFoldedDigitRow>,
    pub final_carry: i128,
}

impl ProjectiveRcbFoldedDigitTraceClaim {
    pub fn from_mul_trace(
        source_index: usize,
        mul_index: usize,
        trace: &FpSolinasMulTrace,
        raw_product_chunks: &[ProjectiveRcbRawProductChunkRow],
        folded_contributions: &ProjectiveRcbFoldedContributionTraceClaim,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let raw_coefficients = raw_coefficients_from_chunks(raw_product_chunks)?;
        let folded_coefficients = fold_raw_coefficients(&raw_coefficients);
        if folded_coefficients != trace.folded_coefficients {
            return Err(ProjectiveRcbAirError::FoldedCoefficientMismatch);
        }
        let mut rows = Vec::with_capacity(FP_SOLINAS_REDUCTION_DIGITS);
        let mut carry = 0i128;
        for digit_index in 0..FP_SOLINAS_REDUCTION_DIGITS {
            let contribution_groups = folded_contributions.digit_groups(digit_index)?;
            let folded_coefficient = contribution_groups
                .iter()
                .filter(|group| group.active)
                .map(|group| group.contribution_sum)
                .sum::<i128>();
            let total = folded_coefficient + carry;
            let folded_digit = total.rem_euclid(FP_SOLINAS_LIMB_BASE);
            let next_carry = total.div_euclid(FP_SOLINAS_LIMB_BASE);
            rows.push(ProjectiveRcbFoldedDigitRow {
                source_index,
                mul_index,
                digit_index,
                contribution_groups,
                folded_coefficient,
                folded_digit: folded_digit as u32,
                prev_carry: carry,
                carry: next_carry,
            });
            carry = next_carry;
        }
        if !(-1..=0).contains(&carry) {
            return Err(ProjectiveRcbAirError::FoldedFinalCarryOutOfRange { carry });
        }
        let claim = Self {
            rows,
            final_carry: carry,
        };
        claim.verify_rows()?;
        Ok(claim)
    }

    pub fn verify_against_mul_trace(
        &self,
        trace: &FpSolinasMulTrace,
        raw_product_chunks: &[ProjectiveRcbRawProductChunkRow],
        folded_contributions: &ProjectiveRcbFoldedContributionTraceClaim,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != FP_SOLINAS_REDUCTION_DIGITS {
            return Err(ProjectiveRcbAirError::FoldedDigitRowCountMismatch {
                expected: FP_SOLINAS_REDUCTION_DIGITS,
                actual: self.rows.len(),
            });
        }
        let expected = Self::from_mul_trace(
            self.rows.first().map_or(0, |row| row.source_index),
            self.rows.first().map_or(0, |row| row.mul_index),
            trace,
            raw_product_chunks,
            folded_contributions,
        )?;
        if self == &expected {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::FoldedDigitMismatch)
        }
    }

    fn verify_rows(&self) -> Result<(), ProjectiveRcbAirError> {
        if !(-1..=0).contains(&self.final_carry) {
            return Err(ProjectiveRcbAirError::FoldedFinalCarryOutOfRange {
                carry: self.final_carry,
            });
        }
        let mut expected_prev = 0i128;
        for (expected_index, row) in self.rows.iter().enumerate() {
            if row.digit_index != expected_index {
                return Err(ProjectiveRcbAirError::FoldedDigitIndexMismatch {
                    expected: expected_index,
                    actual: row.digit_index,
                });
            }
            if row.prev_carry != expected_prev {
                return Err(ProjectiveRcbAirError::FoldedCarryLinkMismatch {
                    digit_index: row.digit_index,
                });
            }
            let contribution_sum = row
                .contribution_groups
                .iter()
                .filter(|group| group.active)
                .map(|group| group.contribution_sum)
                .sum::<i128>();
            if contribution_sum != row.folded_coefficient {
                return Err(ProjectiveRcbAirError::FoldedDigitContributionSumMismatch {
                    digit_index: row.digit_index,
                });
            }
            let total = row.folded_coefficient + row.prev_carry
                - i128::from(row.folded_digit)
                - FP_SOLINAS_LIMB_BASE * row.carry;
            if total != 0 {
                return Err(ProjectiveRcbAirError::FoldedDigitEquationMismatch {
                    digit_index: row.digit_index,
                    value: total,
                });
            }
            expected_prev = row.carry;
        }
        if expected_prev == self.final_carry {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::FoldedFinalCarryMismatch {
                folded: expected_prev,
                reduction: self.final_carry,
            })
        }
    }

    pub fn verify_against_reduction(
        &self,
        reduction: &FpSolinasReductionTraceClaim,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != reduction.rows.len() {
            return Err(ProjectiveRcbAirError::FoldedDigitRowCountMismatch {
                expected: reduction.rows.len(),
                actual: self.rows.len(),
            });
        }
        if self.final_carry != reduction.folded_final_carry {
            return Err(ProjectiveRcbAirError::FoldedFinalCarryMismatch {
                folded: self.final_carry,
                reduction: reduction.folded_final_carry,
            });
        }
        for (folded, reduction) in self.rows.iter().zip(&reduction.rows) {
            if folded.digit_index != reduction.digit_index
                || folded.folded_digit != reduction.folded_digit
            {
                return Err(ProjectiveRcbAirError::FoldedReductionDigitMismatch {
                    digit_index: folded.digit_index,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedDigitRow {
    pub source_index: usize,
    pub mul_index: usize,
    pub digit_index: usize,
    pub contribution_groups:
        [ProjectiveRcbFoldedDigitContributionGroup; PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS],
    pub folded_coefficient: i128,
    pub folded_digit: u32,
    pub prev_carry: i128,
    pub carry: i128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedDigitContributionGroup {
    pub active: bool,
    pub group_index: usize,
    pub contribution_sum: i128,
}

impl ProjectiveRcbFoldedDigitContributionGroup {
    const fn inactive() -> Self {
        Self {
            active: false,
            group_index: 0,
            contribution_sum: 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductTraceClaim {
    pub rows: Vec<ProjectiveRcbRawProductChunkRow>,
}

impl ProjectiveRcbRawProductTraceClaim {
    pub fn from_mul_trace(
        source_index: usize,
        mul_index: usize,
        trace: &FpSolinasMulTrace,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let mut rows = Vec::with_capacity(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS);
        for coeff in 0..FP_SOLINAS_RAW_LIMBS {
            for chunk in 0..coefficient_chunk_count(coeff) {
                rows.push(ProjectiveRcbRawProductChunkRow::from_mul_trace(
                    source_index,
                    mul_index,
                    coeff,
                    chunk,
                    trace,
                )?);
            }
        }
        let claim = Self { rows };
        claim.verify_against_mul_trace(trace)?;
        Ok(claim)
    }

    pub fn verify_against_mul_trace(
        &self,
        trace: &FpSolinasMulTrace,
    ) -> Result<(), ProjectiveRcbAirError> {
        if self.rows.len() != PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS {
            return Err(ProjectiveRcbAirError::RawProductChunkCountMismatch {
                expected: PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS,
                actual: self.rows.len(),
            });
        }
        let mut coeff_sums = [0i128; FP_SOLINAS_RAW_LIMBS];
        for row in &self.rows {
            row.verify()?;
            coeff_sums[row.coeff] += row.product_sum();
            let expected = ProjectiveRcbRawProductChunkRow::from_mul_trace(
                row.source_index,
                row.mul_index,
                row.coeff,
                row.chunk,
                trace,
            )?;
            if row != &expected {
                return Err(ProjectiveRcbAirError::RawProductChunkMismatch {
                    coeff: row.coeff,
                    chunk: row.chunk,
                });
            }
        }
        if coeff_sums == trace.raw_product {
            Ok(())
        } else {
            Err(ProjectiveRcbAirError::RawProductCoefficientMismatch)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductChunkRow {
    pub source_index: usize,
    pub mul_index: usize,
    pub coeff: usize,
    pub chunk: usize,
    pub terms: [ProjectiveRcbRawProductTermRow; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS],
    pub carry1: u32,
    pub digits: [u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
    pub digit_use_counts: [u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
}

impl ProjectiveRcbRawProductChunkRow {
    fn from_mul_trace(
        source_index: usize,
        mul_index: usize,
        coeff: usize,
        chunk: usize,
        trace: &FpSolinasMulTrace,
    ) -> Result<Self, ProjectiveRcbAirError> {
        let pairs = product_chunk_pairs(coeff, chunk)?;
        let mut terms =
            [ProjectiveRcbRawProductTermRow::inactive(); PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
        let mut product_sum = 0i128;
        for (term_index, maybe_pair) in pairs.into_iter().enumerate() {
            if let Some((lhs_index, rhs_index)) = maybe_pair {
                let lhs_limb = trace.lhs.limbs()[lhs_index].0;
                let rhs_limb = trace.rhs.limbs()[rhs_index].0;
                product_sum += i128::from(lhs_limb) * i128::from(rhs_limb);
                terms[term_index] = ProjectiveRcbRawProductTermRow {
                    active: true,
                    lhs_index,
                    rhs_index,
                    lhs_limb,
                    rhs_limb,
                };
            }
        }
        let digits = split_raw_product_chunk(product_sum)?;
        Ok(Self {
            source_index,
            mul_index,
            coeff,
            chunk,
            terms,
            carry1: raw_product_chunk_carry1(digits),
            digits,
            digit_use_counts: core::array::from_fn(|offset| {
                raw_product_chunk_digit_use_count_const(coeff, offset) as u32
            }),
        })
    }

    pub fn verify(&self) -> Result<(), ProjectiveRcbAirError> {
        if self.coeff >= FP_SOLINAS_RAW_LIMBS {
            return Err(ProjectiveRcbAirError::RawProductCoeffOutOfRange { coeff: self.coeff });
        }
        if self.chunk >= coefficient_chunk_count(self.coeff) {
            return Err(ProjectiveRcbAirError::RawProductChunkOutOfRange {
                coeff: self.coeff,
                chunk: self.chunk,
            });
        }
        let expected_pairs = product_chunk_pairs(self.coeff, self.chunk)?;
        for (term, expected_pair) in self.terms.iter().zip(expected_pairs) {
            match expected_pair {
                Some((lhs_index, rhs_index)) => {
                    if !term.active || term.lhs_index != lhs_index || term.rhs_index != rhs_index {
                        return Err(ProjectiveRcbAirError::RawProductTermMismatch {
                            coeff: self.coeff,
                            chunk: self.chunk,
                        });
                    }
                }
                None => {
                    if *term != ProjectiveRcbRawProductTermRow::inactive() {
                        return Err(ProjectiveRcbAirError::RawProductTermMismatch {
                            coeff: self.coeff,
                            chunk: self.chunk,
                        });
                    }
                }
            }
        }
        let digits = split_raw_product_chunk(self.product_sum())?;
        if self.digits != digits {
            Err(ProjectiveRcbAirError::RawProductChunkDigitMismatch {
                coeff: self.coeff,
                chunk: self.chunk,
            })
        } else if self.carry1 != raw_product_chunk_carry1(digits) {
            Err(ProjectiveRcbAirError::RawProductChunkDigitMismatch {
                coeff: self.coeff,
                chunk: self.chunk,
            })
        } else if self.digit_use_counts
            != core::array::from_fn(|offset| {
                raw_product_chunk_digit_use_count_const(self.coeff, offset) as u32
            })
        {
            Err(ProjectiveRcbAirError::RawProductChunkUseCountMismatch {
                coeff: self.coeff,
                chunk: self.chunk,
            })
        } else {
            Ok(())
        }
    }

    fn product_sum(&self) -> i128 {
        self.terms
            .iter()
            .filter(|term| term.active)
            .map(|term| i128::from(term.lhs_limb) * i128::from(term.rhs_limb))
            .sum()
    }
}

fn raw_product_chunk_carry1(digits: [u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS]) -> u32 {
    digits[1] + (FP_SOLINAS_LIMB_BASE as u32) * digits[2]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductTermRow {
    pub active: bool,
    pub lhs_index: usize,
    pub rhs_index: usize,
    pub lhs_limb: u32,
    pub rhs_limb: u32,
}

impl ProjectiveRcbRawProductTermRow {
    const fn inactive() -> Self {
        Self {
            active: false,
            lhs_index: 0,
            rhs_index: 0,
            lhs_limb: 0,
            rhs_limb: 0,
        }
    }
}

pub const PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP: usize = 13;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbMulStep {
    DoubleX1Squared,
    DoubleY1Squared,
    DoubleZ1Squared,
    DoubleX1Y1,
    DoubleX1Z1,
    DoubleBT2,
    DoubleX3Y3,
    DoubleX3T3,
    DoubleBZ3,
    DoubleT0Z3,
    DoubleY1Z1,
    DoubleT0Z3Final,
    DoubleT0T1,
    MixedX1X2,
    MixedY1Y2,
    MixedX2Y2X1Y1,
    MixedY2Z1,
    MixedX2Z1,
    MixedBZ1,
    MixedBY3,
    MixedT4Y3,
    MixedT0Y3,
    MixedX3Z3,
    MixedT3X3,
    MixedT4Z3,
    MixedT3T0,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectiveRcbAirError {
    Projective(ProjectiveEcError),
    FpSolinas(FpSolinasError),
    FpSolinasReduction(FpSolinasReductionTraceError),
    RowCountMismatch {
        expected: usize,
        actual: usize,
    },
    RawProductChunkCountMismatch {
        expected: usize,
        actual: usize,
    },
    RawProductCoeffOutOfRange {
        coeff: usize,
    },
    RawProductChunkOutOfRange {
        coeff: usize,
        chunk: usize,
    },
    RawProductTermMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductChunkDigitMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductChunkUseCountMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductChunkMismatch {
        coeff: usize,
        chunk: usize,
    },
    RawProductCoefficientMismatch,
    RawProductChunkOverflow {
        value: i128,
    },
    FoldedContributionDigitOutOfRange {
        digit_index: usize,
    },
    FoldedContributionMismatch,
    FoldedContributionSumMismatch {
        digit_index: usize,
        group_index: usize,
    },
    FoldedDigitRowCountMismatch {
        expected: usize,
        actual: usize,
    },
    FoldedDigitIndexMismatch {
        expected: usize,
        actual: usize,
    },
    FoldedCarryLinkMismatch {
        digit_index: usize,
    },
    FoldedDigitEquationMismatch {
        digit_index: usize,
        value: i128,
    },
    FoldedDigitContributionGroupOverflow {
        digit_index: usize,
    },
    FoldedDigitContributionSumMismatch {
        digit_index: usize,
    },
    FoldedCoefficientMismatch,
    FoldedDigitMismatch,
    FoldedFinalCarryOutOfRange {
        carry: i128,
    },
    FoldedFinalCarryMismatch {
        folded: i128,
        reduction: i128,
    },
    FoldedReductionDigitMismatch {
        digit_index: usize,
    },
    RelationImbalance {
        relation: &'static str,
    },
    PreprocessedColumnMissing {
        id: String,
    },
    PreprocessedColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    BaseTraceColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    BaseTraceRowWidthMismatch {
        expected: usize,
        actual: usize,
    },
    BaseTraceRowCountMismatch {
        max: usize,
        actual: usize,
    },
    InteractionTraceColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    ProofLayer(String),
    SignedCarryLookupOutOfRange {
        value: i128,
        bound: i64,
    },
    ProjectiveOutputMismatch {
        source_index: usize,
    },
    TraceRowsMismatch {
        source_index: usize,
    },
}

impl From<ProjectiveEcError> for ProjectiveRcbAirError {
    fn from(value: ProjectiveEcError) -> Self {
        Self::Projective(value)
    }
}

impl From<FpSolinasError> for ProjectiveRcbAirError {
    fn from(value: FpSolinasError) -> Self {
        Self::FpSolinas(value)
    }
}

impl From<FpSolinasReductionTraceError> for ProjectiveRcbAirError {
    fn from(value: FpSolinasReductionTraceError) -> Self {
        Self::FpSolinasReduction(value)
    }
}

fn raw_product_chunk_schedule_id(namespace: &str, name: impl Into<String>) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "p256_projective_rcb_{namespace}raw_product_chunk_{}",
            name.into()
        ),
    }
}

fn folded_contribution_schedule_id(
    namespace: &str,
    name: impl Into<String>,
) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "p256_projective_rcb_{namespace}folded_contribution_{}",
            name.into()
        ),
    }
}

fn folded_digit_schedule_id(namespace: &str, name: impl Into<String>) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "p256_projective_rcb_{namespace}folded_digit_{}",
            name.into()
        ),
    }
}

fn raw_product_chunk_schedule_column(
    id: PreProcessedColumnId,
    values: Vec<M31>,
) -> ProjectiveRcbRawProductChunkScheduleColumn {
    ProjectiveRcbRawProductChunkScheduleColumn { id, values }
}

fn folded_contribution_schedule_column(
    id: PreProcessedColumnId,
    values: Vec<M31>,
) -> ProjectiveRcbFoldedContributionScheduleColumn {
    ProjectiveRcbFoldedContributionScheduleColumn { id, values }
}

fn folded_digit_schedule_column(
    id: PreProcessedColumnId,
    values: Vec<M31>,
) -> ProjectiveRcbFoldedDigitScheduleColumn {
    ProjectiveRcbFoldedDigitScheduleColumn { id, values }
}

fn push_signed_carry_lookup(
    values: &mut Vec<i64>,
    value: i128,
) -> Result<(), ProjectiveRcbAirError> {
    if value.abs() <= i128::from(PROJECTIVE_RCB_SIGNED_CARRY_BOUND) {
        values.push(value as i64);
        Ok(())
    } else {
        Err(ProjectiveRcbAirError::SignedCarryLookupOutOfRange {
            value,
            bound: PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
        })
    }
}

fn coefficient_pairs(coeff: usize) -> impl Iterator<Item = (usize, usize)> {
    let start = coeff.saturating_sub(N_LIMBS - 1);
    let end = coeff.min(N_LIMBS - 1);
    (start..=end).map(move |lhs_index| (lhs_index, coeff - lhs_index))
}

fn product_chunk_pairs(
    coeff: usize,
    chunk: usize,
) -> Result<[Option<(usize, usize)>; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS], ProjectiveRcbAirError>
{
    if coeff >= FP_SOLINAS_RAW_LIMBS {
        return Err(ProjectiveRcbAirError::RawProductCoeffOutOfRange { coeff });
    }
    if chunk >= coefficient_chunk_count(coeff) {
        return Err(ProjectiveRcbAirError::RawProductChunkOutOfRange { coeff, chunk });
    }
    let mut pairs = [None; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS];
    let skipped = chunk * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS;
    for (index, pair) in coefficient_pairs(coeff)
        .skip(skipped)
        .take(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS)
        .enumerate()
    {
        pairs[index] = Some(pair);
    }
    Ok(pairs)
}

fn split_raw_product_chunk(
    mut value: i128,
) -> Result<[u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS], ProjectiveRcbAirError> {
    if !(0..=(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS as i128 * (FP_SOLINAS_LIMB_BASE - 1).pow(2)))
        .contains(&value)
    {
        return Err(ProjectiveRcbAirError::RawProductChunkOverflow { value });
    }
    let mut digits = [0u32; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS];
    for digit in &mut digits {
        *digit = value.rem_euclid(FP_SOLINAS_LIMB_BASE) as u32;
        value = value.div_euclid(FP_SOLINAS_LIMB_BASE);
    }
    if value == 0 {
        Ok(digits)
    } else {
        Err(ProjectiveRcbAirError::RawProductChunkOverflow { value })
    }
}

fn raw_coefficients_from_chunks(
    chunks: &[ProjectiveRcbRawProductChunkRow],
) -> Result<[i128; FP_SOLINAS_RAW_LIMBS], ProjectiveRcbAirError> {
    let mut coeffs = [0i128; FP_SOLINAS_RAW_LIMBS];
    let mut seen = [[false; 10]; FP_SOLINAS_RAW_LIMBS];
    for chunk in chunks {
        chunk.verify()?;
        if chunk.chunk >= seen[chunk.coeff].len() {
            return Err(ProjectiveRcbAirError::RawProductChunkOutOfRange {
                coeff: chunk.coeff,
                chunk: chunk.chunk,
            });
        }
        if seen[chunk.coeff][chunk.chunk] {
            return Err(ProjectiveRcbAirError::RawProductChunkMismatch {
                coeff: chunk.coeff,
                chunk: chunk.chunk,
            });
        }
        seen[chunk.coeff][chunk.chunk] = true;
        coeffs[chunk.coeff] += chunk.product_sum();
    }
    for (coeff, seen_chunks) in seen.iter().enumerate() {
        for is_seen in seen_chunks.iter().take(coefficient_chunk_count(coeff)) {
            if !*is_seen {
                return Err(ProjectiveRcbAirError::RawProductChunkCountMismatch {
                    expected: PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS,
                    actual: chunks.len(),
                });
            }
        }
    }
    Ok(coeffs)
}

fn folded_contribution_terms(
    chunks: &[ProjectiveRcbRawProductChunkRow],
) -> Result<Vec<ProjectiveRcbFoldedContributionTermRow>, ProjectiveRcbAirError> {
    let mut terms = Vec::new();
    for chunk in chunks {
        chunk.verify()?;
        for (raw_offset, raw_digit) in chunk.digits.iter().copied().enumerate() {
            if chunk.coeff < N_LIMBS {
                let digit_index = chunk.coeff + raw_offset;
                if digit_index < FP_SOLINAS_REDUCTION_DIGITS {
                    terms.push(ProjectiveRcbFoldedContributionTermRow {
                        active: true,
                        digit_index,
                        raw_coeff: chunk.coeff,
                        raw_chunk: chunk.chunk,
                        raw_offset,
                        matrix_coeff: 1,
                        raw_digit,
                    });
                }
            } else {
                let high = chunk.coeff - N_LIMBS;
                for low in 0..N_LIMBS {
                    let matrix_coeff = REDUCTION_MATRIX[high][low];
                    if matrix_coeff == 0 {
                        continue;
                    }
                    let digit_index = low + raw_offset;
                    if digit_index < FP_SOLINAS_REDUCTION_DIGITS {
                        terms.push(ProjectiveRcbFoldedContributionTermRow {
                            active: true,
                            digit_index,
                            raw_coeff: chunk.coeff,
                            raw_chunk: chunk.chunk,
                            raw_offset,
                            matrix_coeff,
                            raw_digit,
                        });
                    }
                }
            }
        }
    }
    Ok(terms)
}

fn folded_contribution_schedule_terms() -> Vec<ProjectiveRcbFoldedContributionTermRow> {
    let mut terms = Vec::new();
    for coeff in 0..FP_SOLINAS_RAW_LIMBS {
        for chunk in 0..coefficient_chunk_count(coeff) {
            for raw_offset in 0..PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS {
                if coeff < N_LIMBS {
                    let digit_index = coeff + raw_offset;
                    if digit_index < FP_SOLINAS_REDUCTION_DIGITS {
                        terms.push(ProjectiveRcbFoldedContributionTermRow {
                            active: true,
                            digit_index,
                            raw_coeff: coeff,
                            raw_chunk: chunk,
                            raw_offset,
                            matrix_coeff: 1,
                            raw_digit: 0,
                        });
                    }
                } else {
                    let high = coeff - N_LIMBS;
                    for low in 0..N_LIMBS {
                        let matrix_coeff = REDUCTION_MATRIX[high][low];
                        if matrix_coeff == 0 {
                            continue;
                        }
                        let digit_index = low + raw_offset;
                        if digit_index < FP_SOLINAS_REDUCTION_DIGITS {
                            terms.push(ProjectiveRcbFoldedContributionTermRow {
                                active: true,
                                digit_index,
                                raw_coeff: coeff,
                                raw_chunk: chunk,
                                raw_offset,
                                matrix_coeff,
                                raw_digit: 0,
                            });
                        }
                    }
                }
            }
        }
    }
    terms
}

fn fold_raw_coefficients(raw: &[i128; FP_SOLINAS_RAW_LIMBS]) -> [i128; N_LIMBS] {
    let mut folded = [0i128; N_LIMBS];
    folded.copy_from_slice(&raw[..N_LIMBS]);
    for high in 0..(N_LIMBS - 1) {
        let high_coeff = raw[N_LIMBS + high];
        for (low, folded_coeff) in folded.iter_mut().enumerate() {
            *folded_coeff += high_coeff * i128::from(REDUCTION_MATRIX[high][low]);
        }
    }
    folded
}

fn rcb_double_with_mul_rows(
    source_index: usize,
    input: &ProjectivePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let x1 = input.x.to_u256();
    let y1 = input.y.to_u256();
    let z1 = input.z.to_u256();

    let t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX1Squared,
        &x1,
        &x1,
        muls,
    )?;
    let t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleY1Squared,
        &y1,
        &y1,
        muls,
    )?;
    let mut t2 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleZ1Squared,
        &z1,
        &z1,
        muls,
    )?;
    let mut t3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX1Y1,
        &x1,
        &y1,
        muls,
    )?;
    t3 = fp_add(&t3, &t3);
    let mut z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX1Z1,
        &x1,
        &z1,
        muls,
    )?;
    z3 = fp_add(&z3, &z3);
    let mut y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleBT2,
        &curve_b(),
        &t2,
        muls,
    )?;
    y3 = fp_sub(&y3, &z3);
    let mut x3 = fp_add(&y3, &y3);
    y3 = fp_add(&x3, &y3);
    x3 = fp_sub(&t1, &y3);
    y3 = fp_add(&t1, &y3);
    y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX3Y3,
        &x3,
        &y3,
        muls,
    )?;
    x3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleX3T3,
        &x3,
        &t3,
        muls,
    )?;
    t3 = fp_add(&t2, &t2);
    t2 = fp_add(&t2, &t3);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleBZ3,
        &curve_b(),
        &z3,
        muls,
    )?;
    z3 = fp_sub(&z3, &t2);
    z3 = fp_sub(&z3, &t0);
    t3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &t3);
    t3 = fp_add(&t0, &t0);
    let mut t0 = fp_add(&t3, &t0);
    t0 = fp_sub(&t0, &t2);
    t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleT0Z3,
        &t0,
        &z3,
        muls,
    )?;
    y3 = fp_add(&y3, &t0);
    t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleY1Z1,
        &y1,
        &z1,
        muls,
    )?;
    t0 = fp_add(&t0, &t0);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleT0Z3Final,
        &t0,
        &z3,
        muls,
    )?;
    x3 = fp_sub(&x3, &z3);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::DoubleT0T1,
        &t0,
        &t1,
        muls,
    )?;
    z3 = fp_add(&z3, &z3);
    z3 = fp_add(&z3, &z3);

    Ok(projective_from_u256(x3, y3, z3))
}

fn rcb_mixed_add_with_mul_rows(
    source_index: usize,
    state: &ProjectivePoint,
    operand: &PreparedAffinePoint,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<ProjectivePoint, ProjectiveRcbAirError> {
    let Some(operand) = operand.to_option() else {
        return Ok(state.clone());
    };

    let x1 = state.x.to_u256();
    let y1 = state.y.to_u256();
    let z1 = state.z.to_u256();
    let x2 = operand.x;
    let y2 = operand.y;

    let mut t0 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX1X2,
        &x1,
        &x2,
        muls,
    )?;
    let mut t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedY1Y2,
        &y1,
        &y2,
        muls,
    )?;
    let mut t3 = fp_add(&x2, &y2);
    let mut t4 = fp_add(&x1, &y1);
    t3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX2Y2X1Y1,
        &t3,
        &t4,
        muls,
    )?;
    t4 = fp_add(&t0, &t1);
    t3 = fp_sub(&t3, &t4);
    t4 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedY2Z1,
        &y2,
        &z1,
        muls,
    )?;
    t4 = fp_add(&t4, &y1);
    let mut y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX2Z1,
        &x2,
        &z1,
        muls,
    )?;
    y3 = fp_add(&y3, &x1);
    let mut z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedBZ1,
        &curve_b(),
        &z1,
        muls,
    )?;
    let mut x3 = fp_sub(&y3, &z3);
    z3 = fp_add(&x3, &x3);
    x3 = fp_add(&x3, &z3);
    z3 = fp_sub(&t1, &x3);
    x3 = fp_add(&t1, &x3);
    y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedBY3,
        &curve_b(),
        &y3,
        muls,
    )?;
    t1 = fp_add(&z1, &z1);
    let t2 = fp_add(&t1, &z1);
    y3 = fp_sub(&y3, &t2);
    y3 = fp_sub(&y3, &t0);
    t1 = fp_add(&y3, &y3);
    y3 = fp_add(&t1, &y3);
    t1 = fp_add(&t0, &t0);
    t0 = fp_add(&t1, &t0);
    t0 = fp_sub(&t0, &t2);
    t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT4Y3,
        &t4,
        &y3,
        muls,
    )?;
    let t2 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT0Y3,
        &t0,
        &y3,
        muls,
    )?;
    y3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedX3Z3,
        &x3,
        &z3,
        muls,
    )?;
    y3 = fp_add(&y3, &t2);
    x3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT3X3,
        &t3,
        &x3,
        muls,
    )?;
    x3 = fp_sub(&x3, &t1);
    z3 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT4Z3,
        &t4,
        &z3,
        muls,
    )?;
    t1 = fp_mul(
        source_index,
        ProjectiveRcbMulStep::MixedT3T0,
        &t3,
        &t0,
        muls,
    )?;
    z3 = fp_add(&z3, &t1);

    Ok(projective_from_u256(x3, y3, z3))
}

fn fp_mul(
    source_index: usize,
    step: ProjectiveRcbMulStep,
    lhs: &U256,
    rhs: &U256,
    muls: &mut Vec<ProjectiveRcbMulRow>,
) -> Result<U256, ProjectiveRcbAirError> {
    let row = ProjectiveRcbMulRow::new(source_index, muls.len(), step, lhs, rhs)?;
    let result = row.trace.result.to_u256();
    muls.push(row);
    Ok(result)
}

fn projective_from_u256(x: U256, y: U256, z: U256) -> ProjectivePoint {
    ProjectivePoint {
        x: crate::limbs::P256M31BigInt::from_u256(&x),
        y: crate::limbs::P256M31BigInt::from_u256(&y),
        z: crate::limbs::P256M31BigInt::from_u256(&z),
    }
}

fn fp_add(lhs: &U256, rhs: &U256) -> U256 {
    add_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn fp_sub(lhs: &U256, rhs: &U256) -> U256 {
    sub_mod_witness(lhs, rhs, &modulus()).result.to_u256()
}

fn modulus() -> U256 {
    U256::from_le_u64s(&P256_MODULUS)
}

fn curve_b() -> U256 {
    U256::from_le_u64s(&P256_B)
}
