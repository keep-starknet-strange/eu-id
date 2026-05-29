use stwo::core::{
    fields::{m31::M31, qm31::SecureField},
    utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    ColumnVec,
};
use stwo::prover::backend::simd::{
    m31::{LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::solinas::REDUCTION_MATRIX;

use crate::constants::{P256_B, P256_MODULUS};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::fp_solinas::{
    FpSolinasError, FpSolinasMulTrace, FP_SOLINAS_LIMB_BASE, FP_SOLINAS_RAW_LIMBS,
    M31_CENTERED_BOUND,
};
use crate::fp_solinas_air::{
    add_fp_solinas_reduction_digit, FpSolinasReductionDigitColumns, FpSolinasReductionRelations,
    FpSolinasReductionTraceClaim, FpSolinasReductionTraceError,
    FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT, FP_SOLINAS_REDUCTION_DIGITS,
    FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS,
};
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt};
use crate::prepared_table::PreparedAffinePoint;
use crate::projective::{
    ProjectiveEcError, ProjectiveEcOp, ProjectiveEcRow, ProjectiveEcTraceClaim, ProjectivePoint,
};
use crate::range_checks::{
    add_range_check, RangeCheckClaim, RangeCheckComponent, RangeCheckEval,
    RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::U256;

pub type ProjectiveRcbMulComponent = FrameworkComponent<ProjectiveRcbMulEval>;
pub type ProjectiveRcbRawProductChunkComponent =
    FrameworkComponent<ProjectiveRcbRawProductChunkEval>;
pub type ProjectiveRcbFoldedContributionComponent =
    FrameworkComponent<ProjectiveRcbFoldedContributionEval>;
pub type ProjectiveRcbFoldedDigitComponent = FrameworkComponent<ProjectiveRcbFoldedDigitEval>;

pub const PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY: usize = 5;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY: usize = 6;
pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY: usize = 5;
pub const PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY: usize = 4;
pub const PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY: usize = 4;
const QM31_TRACE_COLUMNS: usize = 4;
pub const PROJECTIVE_RCB_SIGNED_CARRY_EQUATION: &str = "projective_rcb_reduction";
pub const PROJECTIVE_RCB_SIGNED_CARRY_BOUND: i64 = projective_rcb_signed_carry_bound();
pub const PROJECTIVE_RCB_MUL_ROLE_LHS: u32 = 0;
pub const PROJECTIVE_RCB_MUL_ROLE_RHS: u32 = 1;
pub const PROJECTIVE_RCB_MUL_ROLE_RESULT: u32 = 2;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS: usize = 2;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS: usize = 3;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS: usize = raw_product_chunk_count();
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERM_TRACE_COLUMNS: usize = 2;
pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS: usize = 4;
pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS: usize = folded_contribution_row_count_const();
pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERM_TRACE_COLUMNS: usize = 1;
pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS: usize = 2
    + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS
        * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERM_TRACE_COLUMNS
    + 1;
pub const PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS: usize =
    folded_contribution_max_groups_per_digit_const();
pub const PROJECTIVE_RCB_FOLDED_DIGIT_GROUP_TRACE_COLUMNS: usize = 1;
pub const PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS: usize =
    2 + PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS * PROJECTIVE_RCB_FOLDED_DIGIT_GROUP_TRACE_COLUMNS + 3;
pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS: usize = 2
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERM_TRACE_COLUMNS
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS;
pub const PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS: usize = 2;
pub const PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS: usize = 1;
pub const PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS: usize = 3 * N_LIMBS;
pub const PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS: usize =
    FP_SOLINAS_REDUCTION_DIGITS * FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS + 1;
pub const PROJECTIVE_RCB_MUL_TRACE_COLUMNS: usize = PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS;

relation!(
    ProjectiveRcbMulLimbRelation,
    PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY
);
relation!(
    ProjectiveRcbRawProductChunkDigitRelation,
    PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY
);
relation!(
    ProjectiveRcbFoldedContributionRelation,
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY
);
relation!(
    ProjectiveRcbFoldedDigitRelation,
    PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY
);
relation!(
    ProjectiveRcbFoldedCarryRelation,
    PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY
);

pub struct ProjectiveRcbRawProductChunkScheduleColumnIds;

impl ProjectiveRcbRawProductChunkScheduleColumnIds {
    pub fn active() -> PreProcessedColumnId {
        raw_product_chunk_schedule_id("active")
    }

    pub fn coeff() -> PreProcessedColumnId {
        raw_product_chunk_schedule_id("coeff")
    }

    pub fn chunk() -> PreProcessedColumnId {
        raw_product_chunk_schedule_id("chunk")
    }

    pub fn term_active(term: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(format!("term_active_{term}"))
    }

    pub fn lhs_index(term: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(format!("lhs_index_{term}"))
    }

    pub fn rhs_index(term: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(format!("rhs_index_{term}"))
    }

    pub fn digit_use_count(offset: usize) -> PreProcessedColumnId {
        raw_product_chunk_schedule_id(format!("digit_use_count_{offset}"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbRawProductChunkScheduleColumn {
    pub id: PreProcessedColumnId,
    pub values: Vec<M31>,
}

pub struct ProjectiveRcbFoldedContributionScheduleColumnIds;

impl ProjectiveRcbFoldedContributionScheduleColumnIds {
    pub fn active() -> PreProcessedColumnId {
        folded_contribution_schedule_id("active")
    }

    pub fn digit_index() -> PreProcessedColumnId {
        folded_contribution_schedule_id("digit_index")
    }

    pub fn group_index() -> PreProcessedColumnId {
        folded_contribution_schedule_id("group_index")
    }

    pub fn term_active(term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(format!("term_active_{term}"))
    }

    pub fn raw_coeff(term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(format!("raw_coeff_{term}"))
    }

    pub fn raw_chunk(term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(format!("raw_chunk_{term}"))
    }

    pub fn raw_offset(term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(format!("raw_offset_{term}"))
    }

    pub fn matrix_coeff(term: usize) -> PreProcessedColumnId {
        folded_contribution_schedule_id(format!("matrix_coeff_{term}"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbFoldedContributionScheduleColumn {
    pub id: PreProcessedColumnId,
    pub values: Vec<M31>,
}

pub struct ProjectiveRcbFoldedDigitScheduleColumnIds;

impl ProjectiveRcbFoldedDigitScheduleColumnIds {
    pub fn active() -> PreProcessedColumnId {
        folded_digit_schedule_id("active")
    }

    pub fn digit_index() -> PreProcessedColumnId {
        folded_digit_schedule_id("digit_index")
    }

    pub fn group_active(group: usize) -> PreProcessedColumnId {
        folded_digit_schedule_id(format!("group_active_{group}"))
    }

    pub fn group_index(group: usize) -> PreProcessedColumnId {
        folded_digit_schedule_id(format!("group_index_{group}"))
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectiveRcbAirComponentInteractionClaim {
    pub mul: SecureField,
    pub raw_product_chunk: SecureField,
    pub folded_contribution: SecureField,
    pub folded_digit: SecureField,
}

impl ProjectiveRcbAirComponentInteractionClaim {
    pub fn total(&self) -> SecureField {
        self.mul + self.raw_product_chunk + self.folded_contribution + self.folded_digit
    }
}

#[derive(Clone, Debug)]
pub struct ProjectiveRcbAirInteractionTraces {
    pub mul: ColumnVec<M31ColumnEval>,
    pub raw_product_chunk: ColumnVec<M31ColumnEval>,
    pub folded_contribution: ColumnVec<M31ColumnEval>,
    pub folded_digit: ColumnVec<M31ColumnEval>,
}

impl ProjectiveRcbAirInteractionTraces {
    pub fn into_columns(self) -> Vec<M31ColumnEval> {
        let mut columns = Vec::new();
        columns.extend(self.mul);
        columns.extend(self.raw_product_chunk);
        columns.extend(self.folded_contribution);
        columns.extend(self.folded_digit);
        columns
    }
}

#[derive(Clone, Debug)]
pub struct ProjectiveRcbAirProofInteractionClaim {
    pub components: ProjectiveRcbAirComponentInteractionClaim,
    pub range13: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
}

impl ProjectiveRcbAirProofInteractionClaim {
    pub fn total(&self) -> SecureField {
        self.components.total() + self.range13.claimed_sum + self.signed_carry.claimed_sum
    }
}

pub struct ProjectiveRcbAirComponents {
    pub mul: ProjectiveRcbMulComponent,
    pub raw_product_chunk: ProjectiveRcbRawProductChunkComponent,
    pub folded_contribution: ProjectiveRcbFoldedContributionComponent,
    pub folded_digit: ProjectiveRcbFoldedDigitComponent,
    pub range13: RangeCheckComponent,
    pub signed_carry: SignedCarryRangeComponent,
}

impl ProjectiveRcbAirComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &ProjectiveRcbAirTraceClaim,
        interaction_claim: &ProjectiveRcbAirProofInteractionClaim,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Self {
        let log_sizes = claim.component_log_sizes();
        Self {
            mul: ProjectiveRcbMulComponent::new(
                allocator,
                ProjectiveRcbMulEval {
                    log_size: log_sizes.mul,
                    relations: relations.clone(),
                },
                interaction_claim.components.mul,
            ),
            raw_product_chunk: ProjectiveRcbRawProductChunkComponent::new(
                allocator,
                ProjectiveRcbRawProductChunkEval {
                    log_size: log_sizes.raw_product_chunk,
                    relations: relations.clone(),
                },
                interaction_claim.components.raw_product_chunk,
            ),
            folded_contribution: ProjectiveRcbFoldedContributionComponent::new(
                allocator,
                ProjectiveRcbFoldedContributionEval {
                    log_size: log_sizes.folded_contribution,
                    relations: relations.clone(),
                },
                interaction_claim.components.folded_contribution,
            ),
            folded_digit: ProjectiveRcbFoldedDigitComponent::new(
                allocator,
                ProjectiveRcbFoldedDigitEval {
                    log_size: log_sizes.folded_digit,
                    relations: relations.clone(),
                },
                interaction_claim.components.folded_digit,
            ),
            range13: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(relations.range13.clone(), RANGE13_BITS),
                interaction_claim.range13.claimed_sum,
            ),
            signed_carry: SignedCarryRangeComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.signed_carry.clone(),
                    projective_rcb_signed_carry_log_size(),
                    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
                ),
                interaction_claim.signed_carry.claimed_sum,
            ),
        }
    }
}

#[derive(Clone)]
pub struct ProjectiveRcbMulEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

impl FrameworkEval for ProjectiveRcbMulEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let mul_index = eval.next_trace_mask();
        let columns = ProjectiveRcbMulColumns::read(&mut eval);

        eval.add_constraint(active.clone() * (one::<E>() - active.clone()));
        add_projective_rcb_mul_row(
            &mut eval,
            self.relations.as_refs(),
            active,
            source_index,
            mul_index,
            &columns,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct ProjectiveRcbRawProductChunkEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

#[derive(Clone)]
pub struct ProjectiveRcbFoldedContributionEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

#[derive(Clone)]
pub struct ProjectiveRcbFoldedDigitEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
}

impl FrameworkEval for ProjectiveRcbFoldedContributionEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 3
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns = ProjectiveRcbFoldedContributionColumns::read(&mut eval);

        add_projective_rcb_folded_contribution(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl FrameworkEval for ProjectiveRcbFoldedDigitEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns = ProjectiveRcbFoldedDigitColumns::read(&mut eval);

        add_projective_rcb_folded_digit(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl FrameworkEval for ProjectiveRcbRawProductChunkEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns = ProjectiveRcbRawProductChunkColumns::read(&mut eval);

        eval.add_constraint(columns.active.clone() * (one::<E>() - columns.active.clone()));
        add_projective_rcb_raw_product_chunk(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone, Debug)]
pub struct ProjectiveRcbMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub mul_limb: ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: ProjectiveRcbFoldedCarryRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            mul_limb: ProjectiveRcbMulLimbRelation::dummy(),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::dummy(),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::dummy(),
            folded_digit: ProjectiveRcbFoldedDigitRelation::dummy(),
            folded_carry: ProjectiveRcbFoldedCarryRelation::dummy(),
        }
    }

    pub fn as_refs(&self) -> ProjectiveRcbMulRelations<'_> {
        ProjectiveRcbMulRelations {
            range13: &self.range13,
            signed_carry: &self.signed_carry,
            mul_limb: &self.mul_limb,
            raw_product_chunk_digit: &self.raw_product_chunk_digit,
            folded_contribution: &self.folded_contribution,
            folded_digit: &self.folded_digit,
            folded_carry: &self.folded_carry,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ProjectiveRcbMulRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    pub mul_limb: &'a ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: &'a ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: &'a ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: &'a ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: &'a ProjectiveRcbFoldedCarryRelation,
}

pub struct ProjectiveRcbMulColumns<E: EvalAtRow> {
    pub lhs: P256EvalBigInt<E>,
    pub rhs: P256EvalBigInt<E>,
    pub result: P256EvalBigInt<E>,
    pub folded_final_carry: E::F,
    pub reduction: [FpSolinasReductionDigitColumns<E>; FP_SOLINAS_REDUCTION_DIGITS],
}

impl<E: EvalAtRow> ProjectiveRcbMulColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            lhs: eval.next_p256_bigint(),
            rhs: eval.next_p256_bigint(),
            result: eval.next_p256_bigint(),
            folded_final_carry: eval.next_trace_mask(),
            reduction: core::array::from_fn(|_| FpSolinasReductionDigitColumns {
                folded_digit: eval.next_trace_mask(),
                correction_product_digit: eval.next_trace_mask(),
                result_limb: eval.next_trace_mask(),
                prev_carry: eval.next_trace_mask(),
                carry: eval.next_trace_mask(),
            }),
        }
    }
}

pub fn add_projective_rcb_mul_row<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    gate: E::F,
    source_index: E::F,
    mul_index: E::F,
    columns: &ProjectiveRcbMulColumns<E>,
) {
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_LHS,
        N_LIMBS as u32,
        &columns.lhs,
    );
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_RHS,
        N_LIMBS as u32,
        &columns.rhs,
    );
    add_mul_limb_group(
        eval,
        relations,
        gate.clone(),
        source_index.clone(),
        mul_index.clone(),
        PROJECTIVE_RCB_MUL_ROLE_RESULT,
        0,
        &columns.result,
    );

    let reduction_relations = FpSolinasReductionRelations {
        range13: relations.range13,
        signed_carry: relations.signed_carry,
    };
    for row in &columns.reduction {
        add_fp_solinas_reduction_digit(eval, reduction_relations, gate.clone(), row);
    }
    for (digit_index, row) in columns.reduction.iter().enumerate() {
        eval.add_to_relation(RelationEntry::new(
            relations.folded_digit,
            E::EF::from(gate.clone()),
            &[
                source_index.clone(),
                mul_index.clone(),
                constant(digit_index as u32),
                row.folded_digit.clone(),
            ],
        ));
    }
    eval.add_to_relation(RelationEntry::new(
        relations.folded_carry,
        -E::EF::from(gate.clone()),
        &[
            source_index.clone(),
            mul_index.clone(),
            constant(0),
            zero::<E>(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        relations.folded_carry,
        E::EF::from(gate.clone()),
        &[
            source_index.clone(),
            mul_index.clone(),
            constant(FP_SOLINAS_REDUCTION_DIGITS as u32),
            columns.folded_final_carry.clone(),
        ],
    ));

    eval.add_constraint(gate.clone() * columns.reduction[0].prev_carry.clone());
    for digit_index in 1..FP_SOLINAS_REDUCTION_DIGITS {
        eval.add_constraint(
            gate.clone()
                * (columns.reduction[digit_index].prev_carry.clone()
                    - columns.reduction[digit_index - 1].carry.clone()),
        );
    }
    eval.add_constraint(
        gate.clone()
            * columns.folded_final_carry.clone()
            * (columns.folded_final_carry.clone() + one::<E>()),
    );
    eval.add_constraint(
        gate * (columns.reduction[FP_SOLINAS_REDUCTION_DIGITS - 1]
            .carry
            .clone()
            + columns.folded_final_carry.clone()),
    );
}

pub struct ProjectiveRcbRawProductChunkColumns<E: EvalAtRow> {
    pub active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub coeff: E::F,
    pub chunk: E::F,
    pub terms: [ProjectiveRcbRawProductTermColumns<E>; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS],
    pub digits: [E::F; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
    pub digit_use_counts: [E::F; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
}

impl<E: EvalAtRow> ProjectiveRcbRawProductChunkColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            active: eval
                .get_preprocessed_column(ProjectiveRcbRawProductChunkScheduleColumnIds::active()),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            coeff: eval
                .get_preprocessed_column(ProjectiveRcbRawProductChunkScheduleColumnIds::coeff()),
            chunk: eval
                .get_preprocessed_column(ProjectiveRcbRawProductChunkScheduleColumnIds::chunk()),
            terms: core::array::from_fn(|term| ProjectiveRcbRawProductTermColumns {
                term_active: eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::term_active(term),
                ),
                lhs_index: eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::lhs_index(term),
                ),
                rhs_index: eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::rhs_index(term),
                ),
                lhs_limb: eval.next_trace_mask(),
                rhs_limb: eval.next_trace_mask(),
            }),
            digits: core::array::from_fn(|_| eval.next_trace_mask()),
            digit_use_counts: core::array::from_fn(|offset| {
                eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::digit_use_count(offset),
                )
            }),
        }
    }
}

pub struct ProjectiveRcbRawProductTermColumns<E: EvalAtRow> {
    pub term_active: E::F,
    pub lhs_index: E::F,
    pub rhs_index: E::F,
    pub lhs_limb: E::F,
    pub rhs_limb: E::F,
}

pub fn add_projective_rcb_raw_product_chunk<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbRawProductChunkColumns<E>,
) {
    let mut product_sum = zero::<E>();
    for term in &columns.terms {
        eval.add_constraint(
            columns.active.clone()
                * term.term_active.clone()
                * (one::<E>() - term.term_active.clone()),
        );
        product_sum += term.term_active.clone() * term.lhs_limb.clone() * term.rhs_limb.clone();
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.lhs_limb.clone(),
        );
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.rhs_limb.clone(),
        );
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            E::EF::from(columns.active.clone() * term.term_active.clone()),
            columns.source_index.clone(),
            columns.mul_index.clone(),
            constant(PROJECTIVE_RCB_MUL_ROLE_LHS),
            term.lhs_index.clone(),
            term.lhs_limb.clone(),
        );
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            E::EF::from(columns.active.clone() * term.term_active.clone()),
            columns.source_index.clone(),
            columns.mul_index.clone(),
            constant(PROJECTIVE_RCB_MUL_ROLE_RHS),
            term.rhs_index.clone(),
            term.rhs_limb.clone(),
        );
    }

    add_range_check(
        eval,
        relations.range13,
        columns.active.clone(),
        columns.digits[0].clone(),
    );
    add_range_check(
        eval,
        relations.range13,
        columns.active.clone(),
        columns.digits[1].clone(),
    );
    eval.add_constraint(
        columns.active.clone()
            * columns.digits[2].clone()
            * (columns.digits[2].clone() - one::<E>()),
    );
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    eval.add_constraint(
        columns.active.clone()
            * (product_sum
                - columns.digits[0].clone()
                - limb_base.clone() * columns.digits[1].clone()
                - limb_base.clone() * limb_base * columns.digits[2].clone()),
    );

    for (offset, digit) in columns.digits.iter().enumerate() {
        eval.add_to_relation(RelationEntry::new(
            relations.raw_product_chunk_digit,
            -E::EF::from(columns.active.clone() * columns.digit_use_counts[offset].clone()),
            &[
                columns.source_index.clone(),
                columns.mul_index.clone(),
                columns.coeff.clone(),
                columns.chunk.clone(),
                constant(offset as u32),
                digit.clone(),
            ],
        ));
    }
}

pub struct ProjectiveRcbFoldedContributionColumns<E: EvalAtRow> {
    pub active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub digit_index: E::F,
    pub group_index: E::F,
    pub terms:
        [ProjectiveRcbFoldedContributionTermColumns<E>; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS],
    pub contribution_sum: E::F,
}

impl<E: EvalAtRow> ProjectiveRcbFoldedContributionColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            active:
                eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::active(),
                ),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            digit_index: eval.get_preprocessed_column(
                ProjectiveRcbFoldedContributionScheduleColumnIds::digit_index(),
            ),
            group_index: eval.get_preprocessed_column(
                ProjectiveRcbFoldedContributionScheduleColumnIds::group_index(),
            ),
            terms: core::array::from_fn(|term| ProjectiveRcbFoldedContributionTermColumns {
                term_active: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::term_active(term),
                ),
                raw_coeff: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::raw_coeff(term),
                ),
                raw_chunk: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::raw_chunk(term),
                ),
                raw_offset: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::raw_offset(term),
                ),
                matrix_coeff: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(term),
                ),
                raw_digit: eval.next_trace_mask(),
            }),
            contribution_sum: eval.next_trace_mask(),
        }
    }
}

pub struct ProjectiveRcbFoldedContributionTermColumns<E: EvalAtRow> {
    pub term_active: E::F,
    pub raw_coeff: E::F,
    pub raw_chunk: E::F,
    pub raw_offset: E::F,
    pub matrix_coeff: E::F,
    pub raw_digit: E::F,
}

pub struct ProjectiveRcbFoldedDigitColumns<E: EvalAtRow> {
    pub active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub digit_index: E::F,
    pub groups: [ProjectiveRcbFoldedDigitGroupColumns<E>; PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS],
    pub prev_carry: E::F,
    pub folded_digit: E::F,
    pub carry: E::F,
}

impl<E: EvalAtRow> ProjectiveRcbFoldedDigitColumns<E> {
    fn read(eval: &mut E) -> Self {
        Self {
            active: eval
                .get_preprocessed_column(ProjectiveRcbFoldedDigitScheduleColumnIds::active()),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            digit_index: eval
                .get_preprocessed_column(ProjectiveRcbFoldedDigitScheduleColumnIds::digit_index()),
            groups: core::array::from_fn(|group| ProjectiveRcbFoldedDigitGroupColumns {
                group_active: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedDigitScheduleColumnIds::group_active(group),
                ),
                group_index: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(group),
                ),
                contribution_sum: eval.next_trace_mask(),
            }),
            prev_carry: eval.next_trace_mask(),
            folded_digit: eval.next_trace_mask(),
            carry: eval.next_trace_mask(),
        }
    }
}

pub struct ProjectiveRcbFoldedDigitGroupColumns<E: EvalAtRow> {
    pub group_active: E::F,
    pub group_index: E::F,
    pub contribution_sum: E::F,
}

pub fn add_projective_rcb_folded_contribution<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbFoldedContributionColumns<E>,
) {
    let mut sum = zero::<E>();
    for term in &columns.terms {
        sum += term.term_active.clone() * term.matrix_coeff.clone() * term.raw_digit.clone();
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.matrix_coeff.clone(),
        );
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.raw_digit.clone(),
        );
        eval.add_to_relation(RelationEntry::new(
            relations.raw_product_chunk_digit,
            E::EF::from(columns.active.clone() * term.term_active.clone()),
            &[
                columns.source_index.clone(),
                columns.mul_index.clone(),
                term.raw_coeff.clone(),
                term.raw_chunk.clone(),
                term.raw_offset.clone(),
                term.raw_digit.clone(),
            ],
        ));
    }
    eval.add_constraint(columns.active.clone() * (sum - columns.contribution_sum.clone()));
    eval.add_to_relation(RelationEntry::new(
        relations.folded_contribution,
        -E::EF::from(columns.active.clone()),
        &[
            columns.source_index.clone(),
            columns.mul_index.clone(),
            columns.digit_index.clone(),
            columns.group_index.clone(),
            columns.contribution_sum.clone(),
        ],
    ));
}

pub fn add_projective_rcb_folded_digit<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbFoldedDigitColumns<E>,
) {
    let mut contribution_sum = zero::<E>();
    for group in &columns.groups {
        contribution_sum += group.group_active.clone() * group.contribution_sum.clone();
        constrain_unused(
            eval,
            columns.active.clone(),
            group.group_active.clone(),
            group.contribution_sum.clone(),
        );
        eval.add_to_relation(RelationEntry::new(
            relations.folded_contribution,
            E::EF::from(columns.active.clone() * group.group_active.clone()),
            &[
                columns.source_index.clone(),
                columns.mul_index.clone(),
                columns.digit_index.clone(),
                group.group_index.clone(),
                group.contribution_sum.clone(),
            ],
        ));
    }

    add_range_check(
        eval,
        relations.range13,
        columns.active.clone(),
        columns.folded_digit.clone(),
    );
    add_range_check(
        eval,
        relations.signed_carry,
        columns.active.clone(),
        columns.prev_carry.clone(),
    );
    add_range_check(
        eval,
        relations.signed_carry,
        columns.active.clone(),
        columns.carry.clone(),
    );

    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    eval.add_constraint(
        columns.active.clone()
            * (contribution_sum + columns.prev_carry.clone()
                - columns.folded_digit.clone()
                - limb_base * columns.carry.clone()),
    );

    eval.add_to_relation(RelationEntry::new(
        relations.folded_carry,
        E::EF::from(columns.active.clone()),
        &[
            columns.source_index.clone(),
            columns.mul_index.clone(),
            columns.digit_index.clone(),
            columns.prev_carry.clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        relations.folded_carry,
        -E::EF::from(columns.active.clone()),
        &[
            columns.source_index.clone(),
            columns.mul_index.clone(),
            columns.digit_index.clone() + one::<E>(),
            columns.carry.clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        relations.folded_digit,
        -E::EF::from(columns.active.clone()),
        &[
            columns.source_index.clone(),
            columns.mul_index.clone(),
            columns.digit_index.clone(),
            columns.folded_digit.clone(),
        ],
    ));
}

pub const fn projective_rcb_raw_product_chunk_max_abs_expr() -> i128 {
    let product_sum =
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS as i128 * (FP_SOLINAS_LIMB_BASE - 1).pow(2);
    product_sum
        + (FP_SOLINAS_LIMB_BASE - 1)
        + FP_SOLINAS_LIMB_BASE * (FP_SOLINAS_LIMB_BASE - 1)
        + FP_SOLINAS_LIMB_BASE * FP_SOLINAS_LIMB_BASE
}

pub fn projective_rcb_raw_product_chunk_fits_m31() -> bool {
    projective_rcb_raw_product_chunk_max_abs_expr() < M31_CENTERED_BOUND
}

pub const fn projective_rcb_folded_contribution_max_abs_expr() -> i128 {
    let contribution = PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS as i128
        * (1i128 << 12)
        * (FP_SOLINAS_LIMB_BASE - 1);
    2 * contribution
}

pub fn projective_rcb_folded_contribution_fits_m31() -> bool {
    projective_rcb_folded_contribution_max_abs_expr() < M31_CENTERED_BOUND
}

pub const fn projective_rcb_folded_digit_max_abs_contribution_sum() -> i128 {
    folded_contribution_max_abs_digit_sum_const()
}

pub fn projective_rcb_folded_digit_contribution_sum_fits_m31() -> bool {
    projective_rcb_folded_digit_max_abs_contribution_sum() < M31_CENTERED_BOUND
}

pub const fn projective_rcb_signed_carry_bound() -> i64 {
    max_i64(
        folded_digit_carry_bound(),
        fp_solinas_reduction_digit_carry_bound(),
    )
}

pub const fn projective_rcb_signed_carry_log_size() -> u32 {
    (2 * PROJECTIVE_RCB_SIGNED_CARRY_BOUND as u64 + 1)
        .next_power_of_two()
        .ilog2()
}

fn projective_rcb_signed_carry_claim() -> SignedCarryRangeClaim {
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
            },
            zero,
        );
        let _ = ProjectiveRcbFoldedContributionComponent::new(
            &mut allocator,
            ProjectiveRcbFoldedContributionEval {
                log_size: log_sizes.folded_contribution,
                relations: relations.clone(),
            },
            zero,
        );
        let _ = ProjectiveRcbFoldedDigitComponent::new(
            &mut allocator,
            ProjectiveRcbFoldedDigitEval {
                log_size: log_sizes.folded_digit,
                relations,
            },
            zero,
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn gen_preprocessed_trace(
        &self,
        ids: &[PreProcessedColumnId],
    ) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        let columns = projective_rcb_air_schedule_preprocessed_columns(self);
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
        );
        let (raw_product_chunk, raw_product_chunk_claim) =
            gen_projective_rcb_family_interaction_trace(
                log_sizes.raw_product_chunk,
                self.raw_product_chunk_rows()
                    .map(projective_rcb_raw_product_chunk_fractions),
                projective_rcb_raw_product_chunk_padding_fractions(),
                relations,
            );
        let (folded_contribution, folded_contribution_claim) =
            gen_projective_rcb_family_interaction_trace(
                log_sizes.folded_contribution,
                self.folded_contribution_rows()
                    .map(projective_rcb_folded_contribution_fractions),
                projective_rcb_folded_contribution_padding_fractions(),
                relations,
            );
        let (folded_digit, folded_digit_claim) = gen_projective_rcb_family_interaction_trace(
            log_sizes.folded_digit,
            self.folded_digit_rows()
                .map(projective_rcb_folded_digit_fractions),
            projective_rcb_folded_digit_padding_fractions(),
            relations,
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
        };
        let _ =
            ProjectiveRcbAirComponents::new(&mut allocator, self, &interaction_claim, relations);
        allocator.preprocessed_columns().clone()
    }

    pub fn gen_proof_slice_preprocessed_trace(
        &self,
        ids: &[PreProcessedColumnId],
    ) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
        let mut columns = projective_rcb_air_schedule_preprocessed_columns(self);
        let range13 = RangeCheckClaim::new(RANGE13_BITS);
        columns.push((
            crate::range_checks::range_check_value_column_id(RANGE13_BITS),
            range13.gen_preprocessed_column(),
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
            + 2;
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
            for chunk in &mul.raw_product_chunks {
                values.push(m31(chunk.digits[0]));
                values.push(m31(chunk.digits[1]));
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

    pub fn range13_consumer_claimed_sum(&self, relation: &RangeCheckRelation) -> SecureField {
        self.range13_lookup_values()
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
    projective_rcb_raw_product_chunk_schedule_columns_for_mul_count(1)
}

fn projective_rcb_raw_product_chunk_schedule_columns_for_mul_count(
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
            ProjectiveRcbRawProductChunkScheduleColumnIds::active(),
            active,
        ),
        raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::coeff(),
            coeff,
        ),
        raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::chunk(),
            chunk,
        ),
    ];
    for term in 0..PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS {
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::term_active(term),
            term_active[term].clone(),
        ));
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::lhs_index(term),
            lhs_index[term].clone(),
        ));
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::rhs_index(term),
            rhs_index[term].clone(),
        ));
    }
    for (offset, values) in digit_use_count.into_iter().enumerate() {
        columns.push(raw_product_chunk_schedule_column(
            ProjectiveRcbRawProductChunkScheduleColumnIds::digit_use_count(offset),
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
    projective_rcb_folded_contribution_schedule_columns_for_mul_count(1)
}

fn projective_rcb_folded_contribution_schedule_columns_for_mul_count(
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
            ProjectiveRcbFoldedContributionScheduleColumnIds::active(),
            active,
        ),
        folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::digit_index(),
            digit_index,
        ),
        folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::group_index(),
            group_index,
        ),
    ];
    for term in 0..PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS {
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::term_active(term),
            term_active[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::raw_coeff(term),
            raw_coeff[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::raw_chunk(term),
            raw_chunk[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::raw_offset(term),
            raw_offset[term].clone(),
        ));
        columns.push(folded_contribution_schedule_column(
            ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(term),
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
    projective_rcb_folded_digit_schedule_columns_for_mul_count(1)
}

fn projective_rcb_folded_digit_schedule_columns_for_mul_count(
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
        folded_digit_schedule_column(ProjectiveRcbFoldedDigitScheduleColumnIds::active(), active),
        folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::digit_index(),
            digit_index,
        ),
    ];
    for group in 0..PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS {
        columns.push(folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::group_active(group),
            group_active[group].clone(),
        ));
        columns.push(folded_digit_schedule_column(
            ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(group),
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
) -> Vec<(PreProcessedColumnId, M31ColumnEval)> {
    let mul_count = trace.mul_row_count();
    let mut columns = Vec::new();
    columns.extend(
        projective_rcb_raw_product_chunk_schedule_columns_for_mul_count(mul_count)
            .into_iter()
            .map(|column| column_to_eval(column.id, column.values)),
    );
    columns.extend(
        projective_rcb_folded_contribution_schedule_columns_for_mul_count(mul_count)
            .into_iter()
            .map(|column| column_to_eval(column.id, column.values)),
    );
    columns.extend(
        projective_rcb_folded_digit_schedule_columns_for_mul_count(mul_count)
            .into_iter()
            .map(|column| column_to_eval(column.id, column.values)),
    );
    columns
}

fn gen_projective_rcb_mul_base_trace(
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
                row
            })
    });
    rows_to_base_trace(rows, PROJECTIVE_RCB_MUL_TRACE_COLUMNS, log_size)
}

fn gen_projective_rcb_raw_product_chunk_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row.muls.iter().flat_map(|mul| {
            mul.raw_product_chunks.iter().map(|chunk| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS);
                row.push(m31_usize(chunk.source_index));
                row.push(m31_usize(chunk.mul_index));
                for term in &chunk.terms {
                    row.push(m31(term.lhs_limb));
                    row.push(m31(term.rhs_limb));
                }
                row.extend(chunk.digits.iter().copied().map(m31));
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

fn gen_projective_rcb_folded_contribution_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row.muls.iter().flat_map(|mul| {
            mul.folded_contributions.rows.iter().map(|contribution| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS);
                row.push(m31_usize(contribution.source_index));
                row.push(m31_usize(contribution.mul_index));
                row.extend(contribution.terms.iter().map(|term| m31(term.raw_digit)));
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

fn gen_projective_rcb_folded_digit_base_trace(
    trace: &ProjectiveRcbAirTraceClaim,
    log_size: u32,
) -> Result<Vec<M31ColumnEval>, ProjectiveRcbAirError> {
    let rows = trace.rows.iter().flat_map(|air_row| {
        air_row.muls.iter().flat_map(|mul| {
            mul.folded_digits.rows.iter().map(|digit| {
                let mut row = Vec::with_capacity(PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS);
                row.push(m31_usize(digit.source_index));
                row.push(m31_usize(digit.mul_index));
                row.extend(
                    digit
                        .contribution_groups
                        .iter()
                        .map(|group| m31_i128(group.contribution_sum)),
                );
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProjectiveRcbFractionSpec {
    relation: ProjectiveRcbRelationKind,
    numerator: i64,
    values: Vec<M31>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProjectiveRcbRelationKind {
    Range13,
    SignedCarry,
    MulLimb,
    RawProductChunkDigit,
    FoldedContribution,
    FoldedDigit,
    FoldedCarry,
}

fn gen_projective_rcb_family_interaction_trace(
    log_size: u32,
    rows: impl IntoIterator<Item = Vec<ProjectiveRcbFractionSpec>>,
    padding_fractions: Vec<ProjectiveRcbFractionSpec>,
    relations: &ProjectiveRcbMulComponentRelations,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    let row_fractions = rows.into_iter().collect::<Vec<_>>();
    let padded_rows = 1usize << log_size;
    assert!(
        row_fractions.len() <= padded_rows,
        "active rows exceed interaction domain"
    );
    let mut storage_fractions = vec![padding_fractions; padded_rows];
    for (coset_index, fractions) in row_fractions.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        storage_fractions[row] = fractions;
    }
    let max_fractions = storage_fractions.iter().map(Vec::len).max().unwrap_or(0);
    if max_fractions == 0 {
        return (Vec::new(), secure_zero());
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    for batch in 0..max_fractions.div_ceil(2) {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (numerator, denominator) =
                    projective_rcb_batch_fraction(&storage_fractions[row], batch, relations);
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    logup.finalize_last()
}

fn projective_rcb_batch_fraction(
    fractions: &[ProjectiveRcbFractionSpec],
    batch: usize,
    relations: &ProjectiveRcbMulComponentRelations,
) -> (SecureField, SecureField) {
    let first = fractions
        .get(2 * batch)
        .map(|fraction| projective_rcb_fraction(fraction, relations));
    let second = fractions
        .get(2 * batch + 1)
        .map(|fraction| projective_rcb_fraction(fraction, relations));
    match (first, second) {
        (Some((n0, d0)), Some((n1, d1))) => (n0 * d1 + n1 * d0, d0 * d1),
        (Some(fraction), None) | (None, Some(fraction)) => fraction,
        (None, None) => zero_fraction(),
    }
}

fn projective_rcb_fraction(
    fraction: &ProjectiveRcbFractionSpec,
    relations: &ProjectiveRcbMulComponentRelations,
) -> (SecureField, SecureField) {
    let denominator = match fraction.relation {
        ProjectiveRcbRelationKind::Range13 => relations.range13.combine(&fraction.values),
        ProjectiveRcbRelationKind::SignedCarry => relations.signed_carry.combine(&fraction.values),
        ProjectiveRcbRelationKind::MulLimb => relations.mul_limb.combine(&fraction.values),
        ProjectiveRcbRelationKind::RawProductChunkDigit => {
            relations.raw_product_chunk_digit.combine(&fraction.values)
        }
        ProjectiveRcbRelationKind::FoldedContribution => {
            relations.folded_contribution.combine(&fraction.values)
        }
        ProjectiveRcbRelationKind::FoldedDigit => relations.folded_digit.combine(&fraction.values),
        ProjectiveRcbRelationKind::FoldedCarry => relations.folded_carry.combine(&fraction.values),
    };
    (secure_from_i64(fraction.numerator), denominator)
}

fn zero_fraction() -> (SecureField, SecureField) {
    (secure_zero(), secure_one())
}

fn projective_rcb_mul_row_fractions(
    source_index: usize,
    mul_index: usize,
    mul: &ProjectiveRcbMulRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_mul_fraction_count());
    for (role, limbs, multiplicity) in [
        (
            PROJECTIVE_RCB_MUL_ROLE_LHS,
            mul.trace.lhs.limbs(),
            -(N_LIMBS as i64),
        ),
        (
            PROJECTIVE_RCB_MUL_ROLE_RHS,
            mul.trace.rhs.limbs(),
            -(N_LIMBS as i64),
        ),
    ] {
        for (limb_index, limb) in limbs.iter().enumerate() {
            fractions.push(range13_fraction(1, *limb));
            fractions.push(mul_limb_fraction(
                multiplicity,
                source_index,
                mul_index,
                role,
                limb_index,
                *limb,
            ));
        }
    }
    for limb in mul.trace.result.limbs() {
        fractions.push(range13_fraction(1, *limb));
    }
    for row in &mul.reduction.rows {
        fractions.push(range13_fraction(1, m31(row.folded_digit)));
        fractions.push(range13_fraction(1, m31(row.result_limb)));
        fractions.push(signed_carry_fraction(1, m31_i128(row.prev_carry)));
        fractions.push(signed_carry_fraction(1, m31_i128(row.carry)));
    }
    for row in &mul.reduction.rows {
        fractions.push(folded_digit_fraction(
            1,
            source_index,
            mul_index,
            row.digit_index,
            m31(row.folded_digit),
        ));
    }
    fractions.push(folded_carry_fraction(
        -1,
        source_index,
        mul_index,
        0,
        m31(0),
    ));
    fractions.push(folded_carry_fraction(
        1,
        source_index,
        mul_index,
        FP_SOLINAS_REDUCTION_DIGITS,
        m31_i128(mul.folded_digits.final_carry),
    ));
    debug_assert_eq!(fractions.len(), projective_rcb_mul_fraction_count());
    fractions
}

fn projective_rcb_raw_product_chunk_fractions(
    row: &ProjectiveRcbRawProductChunkRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_raw_product_chunk_fraction_count());
    for term in &row.terms {
        let active = i64::from(term.active);
        fractions.push(mul_limb_fraction(
            active,
            row.source_index,
            row.mul_index,
            PROJECTIVE_RCB_MUL_ROLE_LHS,
            term.lhs_index,
            m31(term.lhs_limb),
        ));
        fractions.push(mul_limb_fraction(
            active,
            row.source_index,
            row.mul_index,
            PROJECTIVE_RCB_MUL_ROLE_RHS,
            term.rhs_index,
            m31(term.rhs_limb),
        ));
    }
    fractions.push(range13_fraction(1, m31(row.digits[0])));
    fractions.push(range13_fraction(1, m31(row.digits[1])));
    for (offset, digit) in row.digits.iter().enumerate() {
        fractions.push(raw_product_chunk_digit_fraction(
            -(row.digit_use_counts[offset] as i64),
            row.source_index,
            row.mul_index,
            row.coeff,
            row.chunk,
            offset,
            m31(*digit),
        ));
    }
    debug_assert_eq!(
        fractions.len(),
        projective_rcb_raw_product_chunk_fraction_count()
    );
    fractions
}

fn projective_rcb_folded_contribution_fractions(
    row: &ProjectiveRcbFoldedContributionRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_folded_contribution_fraction_count());
    for term in &row.terms {
        fractions.push(raw_product_chunk_digit_fraction(
            i64::from(term.active),
            row.source_index,
            row.mul_index,
            term.raw_coeff,
            term.raw_chunk,
            term.raw_offset,
            m31(term.raw_digit),
        ));
    }
    fractions.push(folded_contribution_fraction(
        -1,
        row.source_index,
        row.mul_index,
        row.digit_index,
        row.group_index,
        m31_i128(row.contribution_sum),
    ));
    debug_assert_eq!(
        fractions.len(),
        projective_rcb_folded_contribution_fraction_count()
    );
    fractions
}

fn projective_rcb_folded_digit_fractions(
    row: &ProjectiveRcbFoldedDigitRow,
) -> Vec<ProjectiveRcbFractionSpec> {
    let mut fractions = Vec::with_capacity(projective_rcb_folded_digit_fraction_count());
    for group in &row.contribution_groups {
        fractions.push(folded_contribution_fraction(
            i64::from(group.active),
            row.source_index,
            row.mul_index,
            row.digit_index,
            group.group_index,
            m31_i128(group.contribution_sum),
        ));
    }
    fractions.push(range13_fraction(1, m31(row.folded_digit)));
    fractions.push(signed_carry_fraction(1, m31_i128(row.prev_carry)));
    fractions.push(signed_carry_fraction(1, m31_i128(row.carry)));
    fractions.push(folded_carry_fraction(
        1,
        row.source_index,
        row.mul_index,
        row.digit_index,
        m31_i128(row.prev_carry),
    ));
    fractions.push(folded_carry_fraction(
        -1,
        row.source_index,
        row.mul_index,
        row.digit_index + 1,
        m31_i128(row.carry),
    ));
    fractions.push(folded_digit_fraction(
        -1,
        row.source_index,
        row.mul_index,
        row.digit_index,
        m31(row.folded_digit),
    ));
    debug_assert_eq!(
        fractions.len(),
        projective_rcb_folded_digit_fraction_count()
    );
    fractions
}

fn projective_rcb_mul_padding_fractions() -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_mul_fraction_count())
}

fn projective_rcb_raw_product_chunk_padding_fractions() -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_raw_product_chunk_fraction_count())
}

fn projective_rcb_folded_contribution_padding_fractions() -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_folded_contribution_fraction_count())
}

fn projective_rcb_folded_digit_padding_fractions() -> Vec<ProjectiveRcbFractionSpec> {
    zeroed_projective_rcb_fractions(projective_rcb_folded_digit_fraction_count())
}

fn zeroed_projective_rcb_fractions(count: usize) -> Vec<ProjectiveRcbFractionSpec> {
    (0..count).map(|_| range13_fraction(0, m31(0))).collect()
}

fn projective_rcb_mul_fraction_count() -> usize {
    2 * N_LIMBS * 2 + N_LIMBS + 4 * FP_SOLINAS_REDUCTION_DIGITS + FP_SOLINAS_REDUCTION_DIGITS + 2
}

fn projective_rcb_raw_product_chunk_fraction_count() -> usize {
    2 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 2 + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS
}

fn projective_rcb_folded_contribution_fraction_count() -> usize {
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS + 1
}

fn projective_rcb_folded_digit_fraction_count() -> usize {
    PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS + 6
}

fn projective_rcb_mul_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_mul_fraction_count().div_ceil(2)
}

fn projective_rcb_raw_product_chunk_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_raw_product_chunk_fraction_count().div_ceil(2)
}

fn projective_rcb_folded_contribution_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_folded_contribution_fraction_count().div_ceil(2)
}

fn projective_rcb_folded_digit_interaction_columns() -> usize {
    QM31_TRACE_COLUMNS * projective_rcb_folded_digit_fraction_count().div_ceil(2)
}

fn range13_fraction(numerator: i64, value: M31) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::Range13,
        numerator,
        values: vec![value],
    }
}

fn signed_carry_fraction(numerator: i64, value: M31) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::SignedCarry,
        numerator,
        values: vec![value],
    }
}

fn mul_limb_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    role: u32,
    limb_index: usize,
    limb: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::MulLimb,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31(role),
            m31_usize(limb_index),
            limb,
        ],
    }
}

fn raw_product_chunk_digit_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    coeff: usize,
    chunk: usize,
    offset: usize,
    digit: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::RawProductChunkDigit,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(coeff),
            m31_usize(chunk),
            m31_usize(offset),
            digit,
        ],
    }
}

fn folded_contribution_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    digit_index: usize,
    group_index: usize,
    contribution_sum: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::FoldedContribution,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(digit_index),
            m31_usize(group_index),
            contribution_sum,
        ],
    }
}

fn folded_digit_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    digit_index: usize,
    folded_digit: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::FoldedDigit,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(digit_index),
            folded_digit,
        ],
    }
}

fn folded_carry_fraction(
    numerator: i64,
    source_index: usize,
    mul_index: usize,
    digit_index: usize,
    carry: M31,
) -> ProjectiveRcbFractionSpec {
    ProjectiveRcbFractionSpec {
        relation: ProjectiveRcbRelationKind::FoldedCarry,
        numerator,
        values: vec![
            m31_usize(source_index),
            m31_usize(mul_index),
            m31_usize(digit_index),
            carry,
        ],
    }
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
pub struct ProjectiveRcbAirInteractionClaim {
    pub mul_limb: SecureField,
    pub raw_product_chunk_digit: SecureField,
    pub folded_contribution: SecureField,
    pub folded_digit: SecureField,
    pub folded_carry: SecureField,
}

impl ProjectiveRcbAirInteractionClaim {
    pub fn from_trace(
        trace: &ProjectiveRcbAirTraceClaim,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Self {
        let mut claim = Self::zero();
        for row in &trace.rows {
            for (mul_index, mul) in row.muls.iter().enumerate() {
                claim.add_mul_limb_fractions(row.source_index, mul_index, mul, relations);
                claim.add_raw_product_fractions(mul, relations);
                claim.add_folded_contribution_fractions(mul, relations);
                claim.add_folded_digit_fractions(row.source_index, mul_index, mul, relations);
                claim.add_folded_carry_fractions(row.source_index, mul_index, mul, relations);
            }
        }
        claim
    }

    pub fn zero() -> Self {
        let zero = secure_zero();
        Self {
            mul_limb: zero,
            raw_product_chunk_digit: zero,
            folded_contribution: zero,
            folded_digit: zero,
            folded_carry: zero,
        }
    }

    pub fn verify_balanced(&self) -> Result<(), ProjectiveRcbAirError> {
        verify_relation_zero("ProjectiveRcbMulLimb", self.mul_limb)?;
        verify_relation_zero(
            "ProjectiveRcbRawProductChunkDigit",
            self.raw_product_chunk_digit,
        )?;
        verify_relation_zero("ProjectiveRcbFoldedContribution", self.folded_contribution)?;
        verify_relation_zero("ProjectiveRcbFoldedDigit", self.folded_digit)?;
        verify_relation_zero("ProjectiveRcbFoldedCarry", self.folded_carry)
    }

    fn add_mul_limb_fractions(
        &mut self,
        source_index: usize,
        mul_index: usize,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for (role, limbs) in [
            (PROJECTIVE_RCB_MUL_ROLE_LHS, mul.trace.lhs.limbs()),
            (PROJECTIVE_RCB_MUL_ROLE_RHS, mul.trace.rhs.limbs()),
        ] {
            for (limb_index, limb) in limbs.iter().enumerate() {
                self.mul_limb += relation_fraction(
                    &relations.mul_limb,
                    -(N_LIMBS as i64),
                    &[
                        m31_usize(source_index),
                        m31_usize(mul_index),
                        m31(role),
                        m31_usize(limb_index),
                        *limb,
                    ],
                );
            }
        }
        for chunk in &mul.raw_product_chunks {
            for term in &chunk.terms {
                if term.active {
                    self.mul_limb += relation_fraction(
                        &relations.mul_limb,
                        1,
                        &[
                            m31_usize(chunk.source_index),
                            m31_usize(chunk.mul_index),
                            m31(PROJECTIVE_RCB_MUL_ROLE_LHS),
                            m31_usize(term.lhs_index),
                            m31(term.lhs_limb),
                        ],
                    );
                    self.mul_limb += relation_fraction(
                        &relations.mul_limb,
                        1,
                        &[
                            m31_usize(chunk.source_index),
                            m31_usize(chunk.mul_index),
                            m31(PROJECTIVE_RCB_MUL_ROLE_RHS),
                            m31_usize(term.rhs_index),
                            m31(term.rhs_limb),
                        ],
                    );
                }
            }
        }
    }

    fn add_raw_product_fractions(
        &mut self,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for chunk in &mul.raw_product_chunks {
            for (offset, digit) in chunk.digits.iter().enumerate() {
                let use_count = chunk.digit_use_counts[offset] as i64;
                if use_count != 0 {
                    self.raw_product_chunk_digit += relation_fraction(
                        &relations.raw_product_chunk_digit,
                        -use_count,
                        &[
                            m31_usize(chunk.source_index),
                            m31_usize(chunk.mul_index),
                            m31_usize(chunk.coeff),
                            m31_usize(chunk.chunk),
                            m31_usize(offset),
                            m31(*digit),
                        ],
                    );
                }
            }
        }
        for row in &mul.folded_contributions.rows {
            for term in &row.terms {
                if term.active {
                    self.raw_product_chunk_digit += relation_fraction(
                        &relations.raw_product_chunk_digit,
                        1,
                        &[
                            m31_usize(row.source_index),
                            m31_usize(row.mul_index),
                            m31_usize(term.raw_coeff),
                            m31_usize(term.raw_chunk),
                            m31_usize(term.raw_offset),
                            m31(term.raw_digit),
                        ],
                    );
                }
            }
        }
    }

    fn add_folded_contribution_fractions(
        &mut self,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for row in &mul.folded_contributions.rows {
            self.folded_contribution += relation_fraction(
                &relations.folded_contribution,
                -1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index),
                    m31_usize(row.group_index),
                    m31_i128(row.contribution_sum),
                ],
            );
        }
        for row in &mul.folded_digits.rows {
            for group in &row.contribution_groups {
                if group.active {
                    self.folded_contribution += relation_fraction(
                        &relations.folded_contribution,
                        1,
                        &[
                            m31_usize(row.source_index),
                            m31_usize(row.mul_index),
                            m31_usize(row.digit_index),
                            m31_usize(group.group_index),
                            m31_i128(group.contribution_sum),
                        ],
                    );
                }
            }
        }
    }

    fn add_folded_digit_fractions(
        &mut self,
        source_index: usize,
        mul_index: usize,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        for row in &mul.folded_digits.rows {
            self.folded_digit += relation_fraction(
                &relations.folded_digit,
                -1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index),
                    m31(row.folded_digit),
                ],
            );
        }
        for row in &mul.reduction.rows {
            self.folded_digit += relation_fraction(
                &relations.folded_digit,
                1,
                &[
                    m31_usize(source_index),
                    m31_usize(mul_index),
                    m31_usize(row.digit_index),
                    m31(row.folded_digit),
                ],
            );
        }
    }

    fn add_folded_carry_fractions(
        &mut self,
        source_index: usize,
        mul_index: usize,
        mul: &ProjectiveRcbMulRow,
        relations: &ProjectiveRcbMulComponentRelations,
    ) {
        self.folded_carry += relation_fraction(
            &relations.folded_carry,
            -1,
            &[
                m31_usize(source_index),
                m31_usize(mul_index),
                m31(0),
                m31(0),
            ],
        );
        self.folded_carry += relation_fraction(
            &relations.folded_carry,
            1,
            &[
                m31_usize(source_index),
                m31_usize(mul_index),
                m31_usize(FP_SOLINAS_REDUCTION_DIGITS),
                m31_i128(mul.folded_digits.final_carry),
            ],
        );
        for row in &mul.folded_digits.rows {
            self.folded_carry += relation_fraction(
                &relations.folded_carry,
                1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index),
                    m31_i128(row.prev_carry),
                ],
            );
            self.folded_carry += relation_fraction(
                &relations.folded_carry,
                -1,
                &[
                    m31_usize(row.source_index),
                    m31_usize(row.mul_index),
                    m31_usize(row.digit_index + 1),
                    m31_i128(row.carry),
                ],
            );
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
    fn new(
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
        Ok(Self {
            source_index,
            mul_index,
            coeff,
            chunk,
            terms,
            digits: split_raw_product_chunk(product_sum)?,
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

#[allow(clippy::too_many_arguments)]
fn add_mul_limb_group<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    gate: E::F,
    source_index: E::F,
    mul_index: E::F,
    role: u32,
    relation_multiplicity: u32,
    value: &P256EvalBigInt<E>,
) {
    for (limb_index, limb) in value.limbs().iter().enumerate() {
        add_range_check(eval, relations.range13, gate.clone(), limb.clone());
        if relation_multiplicity != 0 {
            add_projective_rcb_mul_limb_relation(
                eval,
                relations.mul_limb,
                -E::EF::from(gate.clone() * constant::<E::F>(relation_multiplicity)),
                source_index.clone(),
                mul_index.clone(),
                constant(role),
                constant(limb_index as u32),
                limb.clone(),
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn add_projective_rcb_mul_limb_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &ProjectiveRcbMulLimbRelation,
    numerator: E::EF,
    source_index: E::F,
    mul_index: E::F,
    role: E::F,
    limb_index: E::F,
    limb: E::F,
) {
    eval.add_to_relation(RelationEntry::new(
        relation,
        numerator,
        &[source_index, mul_index, role, limb_index, limb],
    ));
}

fn constrain_unused<E: EvalAtRow>(eval: &mut E, active: E::F, term_active: E::F, value: E::F) {
    eval.add_constraint(active * (one::<E>() - term_active) * value);
}

fn constant<F: From<M31>>(value: u32) -> F {
    F::from(M31::from_u32_unchecked(value))
}

fn zero<E: EvalAtRow>() -> E::F {
    constant(0)
}

fn one<E: EvalAtRow>() -> E::F {
    constant(1)
}

fn relation_fraction<R: Relation<M31, SecureField>>(
    relation: &R,
    numerator: i64,
    values: &[M31],
) -> SecureField {
    secure_from_i64(numerator) / relation.combine(values)
}

fn verify_relation_zero(
    relation: &'static str,
    value: SecureField,
) -> Result<(), ProjectiveRcbAirError> {
    if value == secure_zero() {
        Ok(())
    } else {
        Err(ProjectiveRcbAirError::RelationImbalance { relation })
    }
}

fn secure_zero() -> SecureField {
    SecureField::from(m31(0))
}

fn secure_one() -> SecureField {
    SecureField::from(m31(1))
}

fn secure_from_i64(value: i64) -> SecureField {
    SecureField::from(m31_i128(i128::from(value)))
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn m31_usize(value: usize) -> M31 {
    m31(value as u32)
}

fn m31_i128(value: i128) -> M31 {
    const M31_MODULUS: i128 = (1i128 << 31) - 1;
    M31::from_u32_unchecked(value.rem_euclid(M31_MODULUS) as u32)
}

fn raw_product_chunk_schedule_id(name: impl Into<String>) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_projective_rcb_raw_product_chunk_{}", name.into()),
    }
}

fn folded_contribution_schedule_id(name: impl Into<String>) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_projective_rcb_folded_contribution_{}", name.into()),
    }
}

fn folded_digit_schedule_id(name: impl Into<String>) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_projective_rcb_folded_digit_{}", name.into()),
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

const fn raw_product_chunk_count() -> usize {
    let mut coeff = 0usize;
    let mut count = 0usize;
    while coeff < FP_SOLINAS_RAW_LIMBS {
        count += coefficient_chunk_count_const(coeff);
        coeff += 1;
    }
    count
}

const fn folded_contribution_row_count_const() -> usize {
    let mut digit_index = 0usize;
    let mut rows = 0usize;
    while digit_index < FP_SOLINAS_REDUCTION_DIGITS {
        let terms = folded_contribution_term_count_for_digit_const(digit_index);
        if terms == 0 {
            rows += 1;
        } else {
            rows += terms.div_ceil(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS);
        }
        digit_index += 1;
    }
    rows
}

const fn folded_contribution_max_groups_per_digit_const() -> usize {
    let mut digit_index = 0usize;
    let mut max_groups = 0usize;
    while digit_index < FP_SOLINAS_REDUCTION_DIGITS {
        let groups = folded_contribution_group_count_for_digit_const(digit_index);
        if groups > max_groups {
            max_groups = groups;
        }
        digit_index += 1;
    }
    max_groups
}

const fn folded_contribution_group_count_for_digit_const(digit_index: usize) -> usize {
    let terms = folded_contribution_term_count_for_digit_const(digit_index);
    if terms == 0 {
        1
    } else {
        terms.div_ceil(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)
    }
}

const fn folded_contribution_term_count_for_digit_const(digit_index: usize) -> usize {
    let mut coeff = 0usize;
    let mut count = 0usize;
    while coeff < FP_SOLINAS_RAW_LIMBS {
        let chunks = coefficient_chunk_count_const(coeff);
        let mut chunk = 0usize;
        while chunk < chunks {
            let mut raw_offset = 0usize;
            while raw_offset < PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS {
                if coeff < N_LIMBS {
                    if coeff + raw_offset == digit_index {
                        count += 1;
                    }
                } else {
                    let high = coeff - N_LIMBS;
                    let mut low = 0usize;
                    while low < N_LIMBS {
                        if low + raw_offset == digit_index && REDUCTION_MATRIX[high][low] != 0 {
                            count += 1;
                        }
                        low += 1;
                    }
                }
                raw_offset += 1;
            }
            chunk += 1;
        }
        coeff += 1;
    }
    count
}

const fn folded_contribution_max_abs_digit_sum_const() -> i128 {
    let mut digit_index = 0usize;
    let mut max_abs_sum = 0i128;
    while digit_index < FP_SOLINAS_REDUCTION_DIGITS {
        let digit_sum = folded_contribution_abs_digit_sum_const(digit_index);
        if digit_sum > max_abs_sum {
            max_abs_sum = digit_sum;
        }
        digit_index += 1;
    }
    max_abs_sum
}

const fn folded_contribution_abs_digit_sum_const(digit_index: usize) -> i128 {
    let mut coeff = 0usize;
    let mut sum = 0i128;
    while coeff < FP_SOLINAS_RAW_LIMBS {
        let chunks = coefficient_chunk_count_const(coeff);
        let mut chunk = 0usize;
        while chunk < chunks {
            let mut raw_offset = 0usize;
            while raw_offset < PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS {
                if coeff < N_LIMBS {
                    if coeff + raw_offset == digit_index {
                        sum += FP_SOLINAS_LIMB_BASE - 1;
                    }
                } else {
                    let high = coeff - N_LIMBS;
                    let mut low = 0usize;
                    while low < N_LIMBS {
                        let matrix_coeff = REDUCTION_MATRIX[high][low];
                        if low + raw_offset == digit_index && matrix_coeff != 0 {
                            sum += abs_i64(matrix_coeff) as i128 * (FP_SOLINAS_LIMB_BASE - 1);
                        }
                        low += 1;
                    }
                }
                raw_offset += 1;
            }
            chunk += 1;
        }
        coeff += 1;
    }
    sum
}

const fn folded_digit_carry_bound() -> i64 {
    carry_bound_from_abs_terms(folded_contribution_max_abs_digit_sum_const())
}

const fn fp_solinas_reduction_digit_carry_bound() -> i64 {
    let abs_terms = FP_SOLINAS_LIMB_BASE - 1
        + FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT
        + FP_SOLINAS_LIMB_BASE
        - 1;
    carry_bound_from_abs_terms(abs_terms)
}

const fn carry_bound_from_abs_terms(abs_terms: i128) -> i64 {
    ceil_div_i128(abs_terms, FP_SOLINAS_LIMB_BASE - 1) as i64
}

const fn ceil_div_i128(value: i128, divisor: i128) -> i128 {
    (value + divisor - 1) / divisor
}

const fn max_i64(lhs: i64, rhs: i64) -> i64 {
    if lhs > rhs {
        lhs
    } else {
        rhs
    }
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

const fn raw_product_chunk_digit_use_count_const(coeff: usize, offset: usize) -> usize {
    if coeff < N_LIMBS {
        if coeff + offset < FP_SOLINAS_REDUCTION_DIGITS {
            1
        } else {
            0
        }
    } else {
        let high = coeff - N_LIMBS;
        let mut low = 0usize;
        let mut count = 0usize;
        while low < N_LIMBS {
            if low + offset < FP_SOLINAS_REDUCTION_DIGITS && REDUCTION_MATRIX[high][low] != 0 {
                count += 1;
            }
            low += 1;
        }
        count
    }
}

const fn abs_i64(value: i64) -> i64 {
    if value < 0 {
        -value
    } else {
        value
    }
}

const fn coefficient_chunk_count_const(coeff: usize) -> usize {
    coefficient_term_count_const(coeff).div_ceil(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS)
}

fn coefficient_chunk_count(coeff: usize) -> usize {
    coefficient_term_count(coeff).div_ceil(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS)
}

const fn coefficient_term_count_const(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        FP_SOLINAS_RAW_LIMBS - coeff
    }
}

fn coefficient_term_count(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        FP_SOLINAS_RAW_LIMBS - coeff
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
    if !(0..=(2 * (FP_SOLINAS_LIMB_BASE - 1).pow(2))).contains(&value) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::curve::point_double;
    use crate::range_checks::{RangeCheckClaim, SignedCarryRangeClaim, RANGE13_BITS};
    use crate::types::AffinePoint;
    use num_traits::Zero;
    use stwo::core::air::Component;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::TraceLocationAllocator;

    fn generator() -> PreparedAffinePoint {
        PreparedAffinePoint::from_affine(AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        })
    }

    fn one_row_trace(op: ProjectiveEcOp, rhs: PreparedAffinePoint) -> ProjectiveEcTraceClaim {
        let lhs = generator();
        let output = match op {
            ProjectiveEcOp::Double => {
                PreparedAffinePoint::from_affine(point_double(&lhs.to_option().unwrap()).output)
            }
            ProjectiveEcOp::MixedAdd => {
                let output =
                    crate::curve::point_add(&lhs.to_option().unwrap(), &rhs.to_option().unwrap())
                        .output;
                PreparedAffinePoint::from_affine(output)
            }
        };
        ProjectiveEcTraceClaim {
            rows: vec![ProjectiveEcRow::new(
                M31::from_u32_unchecked(0),
                M31::from_u32_unchecked(0),
                op,
                &lhs,
                &rhs,
                &output,
            )],
        }
    }

    #[test]
    fn projective_rcb_air_rows_verify_double() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.active_row_count(), 1);
        assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
        assert_eq!(
            claim.raw_product_chunk_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
        );
        assert_eq!(
            claim.folded_digit_row_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            claim.folded_contribution_row_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS
        );
        assert_eq!(
            claim.reduction_row_count(),
            PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP * FP_SOLINAS_REDUCTION_DIGITS
        );
        claim
            .internal_interaction_claim(&ProjectiveRcbMulComponentRelations::dummy())
            .verify_balanced()
            .expect("internal relations balance");
    }

    #[test]
    fn projective_rcb_air_rows_verify_mixed_add() {
        let g = generator();
        let rhs = PreparedAffinePoint::from_affine(point_double(&g.to_option().unwrap()).output);
        let trace = one_row_trace(ProjectiveEcOp::MixedAdd, rhs);
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.active_row_count(), 1);
        assert_eq!(claim.mul_row_count(), PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP);
    }

    #[test]
    fn projective_rcb_air_rows_skip_operand_infinity_mixed_add() {
        let lhs = generator();
        let output = lhs.clone();
        let trace = ProjectiveEcTraceClaim {
            rows: vec![ProjectiveEcRow::new(
                M31::from_u32_unchecked(0),
                M31::from_u32_unchecked(0),
                ProjectiveEcOp::MixedAdd,
                &lhs,
                &PreparedAffinePoint::infinity(),
                &output,
            )],
        };
        let claim = ProjectiveRcbAirTraceClaim::from_projective_trace(&trace)
            .expect("valid infinity-add RCB AIR trace");

        claim
            .verify_against_projective_trace(&trace)
            .expect("claim verifies");
        assert_eq!(claim.mul_row_count(), 0);
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_reduction_digit() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].reduction.rows[0].folded_digit ^= 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated reduction row must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FpSolinasReduction(
                FpSolinasReductionTraceError::TraceRowsMismatch
                    | FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
            ) | ProjectiveRcbAirError::FoldedReductionDigitMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_raw_product_digit() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].raw_product_chunks[0].digits[0] ^= 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated raw product chunk must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::RawProductChunkDigitMismatch { .. }
                | ProjectiveRcbAirError::RawProductChunkMismatch { .. }
        ));
        assert!(matches!(
            claim
                .internal_interaction_claim(&ProjectiveRcbMulComponentRelations::dummy())
                .verify_balanced()
                .expect_err("mutated relation tuple must imbalance"),
            ProjectiveRcbAirError::RelationImbalance {
                relation: "ProjectiveRcbRawProductChunkDigit"
            }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_raw_product_schedule_metadata() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].raw_product_chunks[0].digit_use_counts[0] += 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated raw product schedule metadata must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::RawProductChunkUseCountMismatch { .. }
                | ProjectiveRcbAirError::RawProductChunkMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_folded_digit() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].folded_digits.rows[0].folded_digit ^= 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated folded digit must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FoldedDigitMismatch
                | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
                | ProjectiveRcbAirError::FoldedReductionDigitMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_folded_digit_contribution_group() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].folded_digits.rows[0].contribution_groups[0].contribution_sum += 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated folded digit contribution group must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FoldedDigitContributionSumMismatch { .. }
                | ProjectiveRcbAirError::FoldedDigitMismatch
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_folded_digit_schedule_metadata() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].folded_digits.rows[0].contribution_groups[0].group_index += 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated folded digit schedule metadata must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FoldedDigitMismatch
                | ProjectiveRcbAirError::FoldedDigitContributionSumMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_folded_contribution() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].folded_contributions.rows[0].contribution_sum += 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated folded contribution row must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FoldedContributionMismatch
                | ProjectiveRcbAirError::FoldedContributionSumMismatch { .. }
                | ProjectiveRcbAirError::FoldedDigitMismatch
                | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_folded_contribution_schedule_metadata() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].muls[0].folded_contributions.rows[0].terms[0].matrix_coeff += 1;

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated folded contribution schedule metadata must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::FoldedContributionMismatch
                | ProjectiveRcbAirError::FoldedContributionSumMismatch { .. }
                | ProjectiveRcbAirError::FoldedDigitMismatch
                | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_rows_detect_mutated_projective_output() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let mut claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        claim.rows[0].output_projective.x = crate::limbs::P256M31BigInt::zero();

        let err = claim
            .verify_against_projective_trace(&trace)
            .expect_err("mutated output must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::TraceRowsMismatch { .. }
                | ProjectiveRcbAirError::Projective(ProjectiveEcError::InvalidProjectiveInfinity)
        ));
    }

    #[test]
    fn projective_rcb_mul_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbMulComponent::new(
            &mut allocator,
            ProjectiveRcbMulEval {
                log_size: 6,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS,
            1 + 2 + 3 * N_LIMBS + 1 + 5 * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS
        );
        assert_eq!(PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY, 5);
        assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY, 4);
        assert_eq!(PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY, 4);
        assert_eq!(
            ProjectiveRcbMulEval {
                log_size: 6,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            }
            .max_constraint_log_degree_bound(),
            8
        );
    }

    #[test]
    fn projective_rcb_raw_product_chunk_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbRawProductChunkComponent::new(
            &mut allocator,
            ProjectiveRcbRawProductChunkEval {
                log_size: 8,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS, 210);
        assert_eq!(
            PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS,
            2 + 2 * 2 + 3
        );
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
        );
        assert!(allocator
            .preprocessed_columns()
            .contains(&ProjectiveRcbRawProductChunkScheduleColumnIds::coeff()));
        assert!(allocator
            .preprocessed_columns()
            .contains(&ProjectiveRcbRawProductChunkScheduleColumnIds::digit_use_count(2)));
        assert_eq!(PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY, 6);
        assert!(projective_rcb_raw_product_chunk_fits_m31());
    }

    #[test]
    fn projective_rcb_raw_product_chunk_schedule_columns_match_fixed_rows() {
        let columns = projective_rcb_raw_product_chunk_schedule_columns();
        let log_size = padded_log_size(PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS);
        let row_count = 1usize << log_size;

        assert_eq!(
            columns.len(),
            3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3
        );
        assert!(columns
            .iter()
            .all(|column| column.values.len() == row_count));
        assert_eq!(
            columns[0].values[..PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS]
                .iter()
                .filter(|&&value| value == m31(1))
                .count(),
            PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
        );
        assert_eq!(columns[1].values[0], m31(0));
        assert_eq!(columns[2].values[0], m31(0));
        assert_eq!(
            columns[1].values[PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS - 1],
            m31_usize(FP_SOLINAS_RAW_LIMBS - 1)
        );
        assert_eq!(
            projective_rcb_raw_product_chunk_schedule_evals().len(),
            columns.len()
        );
    }

    #[test]
    fn projective_rcb_folded_contribution_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbFoldedContributionComponent::new(
            &mut allocator,
            ProjectiveRcbFoldedContributionEval {
                log_size: 9,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS, 2 + 4 + 1);
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
        );
        assert!(allocator
            .preprocessed_columns()
            .contains(&ProjectiveRcbFoldedContributionScheduleColumnIds::active()));
        assert!(allocator
            .preprocessed_columns()
            .contains(&ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(3)));
        assert_eq!(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY, 5);
        assert!(projective_rcb_folded_contribution_fits_m31());
        assert_eq!(
            ProjectiveRcbFoldedContributionEval {
                log_size: 9,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            }
            .max_constraint_log_degree_bound(),
            12
        );
    }

    #[test]
    fn projective_rcb_folded_contribution_schedule_columns_match_fixed_rows() {
        let columns = projective_rcb_folded_contribution_schedule_columns();
        let log_size = padded_log_size(PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS);
        let row_count = 1usize << log_size;
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let fixed_rows = &claim.rows[0].muls[0].folded_contributions.rows;

        assert_eq!(
            columns.len(),
            3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS
        );
        assert!(columns
            .iter()
            .all(|column| column.values.len() == row_count));
        assert_eq!(
            columns[0].values[..PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS]
                .iter()
                .filter(|&&value| value == m31(1))
                .count(),
            PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS
        );
        assert_eq!(columns[1].values[0], m31(0));
        assert_eq!(columns[2].values[0], m31(0));
        assert_eq!(
            columns[1].values[PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS - 1],
            m31_usize(FP_SOLINAS_REDUCTION_DIGITS - 1)
        );
        assert_eq!(fixed_rows.len(), PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS);
        for (row_index, row) in fixed_rows.iter().enumerate() {
            assert_eq!(columns[0].values[row_index], m31(1));
            assert_eq!(columns[1].values[row_index], m31_usize(row.digit_index));
            assert_eq!(columns[2].values[row_index], m31_usize(row.group_index));
            for (term_index, term) in row.terms.iter().enumerate() {
                let base = 3 + 5 * term_index;
                assert_eq!(columns[base].values[row_index], m31(u32::from(term.active)));
                assert_eq!(
                    columns[base + 1].values[row_index],
                    m31_usize(term.raw_coeff)
                );
                assert_eq!(
                    columns[base + 2].values[row_index],
                    m31_usize(term.raw_chunk)
                );
                assert_eq!(
                    columns[base + 3].values[row_index],
                    m31_usize(term.raw_offset)
                );
                assert_eq!(
                    columns[base + 4].values[row_index],
                    m31_i128(i128::from(term.matrix_coeff))
                );
            }
        }
        assert_eq!(
            projective_rcb_folded_contribution_schedule_evals().len(),
            columns.len()
        );
    }

    #[test]
    fn projective_rcb_folded_digit_eval_allocates_expected_width() {
        let mut allocator = TraceLocationAllocator::default();
        let component = ProjectiveRcbFoldedDigitComponent::new(
            &mut allocator,
            ProjectiveRcbFoldedDigitEval {
                log_size: 9,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            },
            SecureField::zero(),
        );

        assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS, 30);
        assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS, 2 + 30 + 3);
        assert_eq!(
            component.trace_log_degree_bounds()[1].len(),
            PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
        );
        assert!(allocator
            .preprocessed_columns()
            .contains(&ProjectiveRcbFoldedDigitScheduleColumnIds::active()));
        assert!(allocator
            .preprocessed_columns()
            .contains(&ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(29)));
        assert_eq!(PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY, 4);
        assert_eq!(PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY, 4);
        assert!(projective_rcb_folded_digit_contribution_sum_fits_m31());
        assert_eq!(
            ProjectiveRcbFoldedDigitEval {
                log_size: 9,
                relations: ProjectiveRcbMulComponentRelations::dummy(),
            }
            .max_constraint_log_degree_bound(),
            11
        );
    }

    #[test]
    fn projective_rcb_folded_digit_schedule_columns_match_fixed_rows() {
        let columns = projective_rcb_folded_digit_schedule_columns();
        let log_size = padded_log_size(FP_SOLINAS_REDUCTION_DIGITS);
        let row_count = 1usize << log_size;
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let fixed_rows = &claim.rows[0].muls[0].folded_digits.rows;

        assert_eq!(columns.len(), 2 + 2 * PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS);
        assert!(columns
            .iter()
            .all(|column| column.values.len() == row_count));
        assert_eq!(
            columns[0].values[..FP_SOLINAS_REDUCTION_DIGITS]
                .iter()
                .filter(|&&value| value == m31(1))
                .count(),
            FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(columns[1].values[0], m31(0));
        assert_eq!(
            columns[1].values[FP_SOLINAS_REDUCTION_DIGITS - 1],
            m31_usize(FP_SOLINAS_REDUCTION_DIGITS - 1)
        );
        assert_eq!(fixed_rows.len(), FP_SOLINAS_REDUCTION_DIGITS);
        for (row_index, row) in fixed_rows.iter().enumerate() {
            assert_eq!(columns[0].values[row_index], m31(1));
            assert_eq!(columns[1].values[row_index], m31_usize(row.digit_index));
            for (group_index, group) in row.contribution_groups.iter().enumerate() {
                let base = 2 + 2 * group_index;
                assert_eq!(
                    columns[base].values[row_index],
                    m31(u32::from(group.active))
                );
                assert_eq!(
                    columns[base + 1].values[row_index],
                    m31_usize(group.group_index)
                );
            }
        }
        assert_eq!(
            projective_rcb_folded_digit_schedule_evals().len(),
            columns.len()
        );
    }

    #[test]
    fn projective_rcb_air_preprocessed_trace_uses_global_claim_sizes() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let ids = claim.preprocessed_column_ids();
        let preprocessed = claim
            .gen_preprocessed_trace(&ids)
            .expect("registered schedule columns generate");
        let log_sizes = claim.component_log_sizes();

        assert_eq!(
            ids.len(),
            (3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3)
                + (3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)
                + (2 + 2 * PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS)
        );
        assert_eq!(preprocessed.len(), ids.len());
        assert_eq!(
            preprocessed[0].domain.log_size(),
            log_sizes.raw_product_chunk
        );
        assert_eq!(
            preprocessed[3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3]
                .domain
                .log_size(),
            log_sizes.folded_contribution
        );
        assert_eq!(
            preprocessed[(3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3)
                + (3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)]
                .domain
                .log_size(),
            log_sizes.folded_digit
        );
        assert!(ids.contains(&ProjectiveRcbRawProductChunkScheduleColumnIds::coeff()));
        assert!(ids.contains(&ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(3)));
        assert!(ids.contains(&ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(29)));
        claim
            .verify_preprocessed_trace()
            .expect("full schedule preprocessed trace verifies");
    }

    #[test]
    fn projective_rcb_air_preprocessed_trace_rejects_unknown_column_id() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let err = claim
            .gen_preprocessed_trace(&[PreProcessedColumnId {
                id: "p256_projective_rcb_missing".to_string(),
            }])
            .expect_err("unknown preprocessed column must fail");

        assert!(matches!(
            err,
            ProjectiveRcbAirError::PreprocessedColumnMissing { .. }
        ));
    }

    #[test]
    fn projective_rcb_air_base_trace_materializes_component_columns() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let base = claim.gen_base_trace().expect("base trace materializes");
        let log_sizes = claim.component_log_sizes();
        let raw_start = PROJECTIVE_RCB_MUL_TRACE_COLUMNS;
        let folded_contribution_start = raw_start + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS;
        let folded_digit_start =
            folded_contribution_start + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS;

        assert_eq!(
            base.len(),
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS
                + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
                + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
                + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
        );
        assert_eq!(base[0].domain.log_size(), log_sizes.mul);
        assert_eq!(
            base[raw_start].domain.log_size(),
            log_sizes.raw_product_chunk
        );
        assert_eq!(
            base[folded_contribution_start].domain.log_size(),
            log_sizes.folded_contribution
        );
        assert_eq!(
            base[folded_digit_start].domain.log_size(),
            log_sizes.folded_digit
        );
        assert_eq!(
            base[0]
                .to_cpu()
                .iter()
                .filter(|&&value| value == m31(1))
                .count(),
            claim.mul_row_count()
        );
        claim
            .verify_base_trace()
            .expect("base trace shape verifies");
    }

    #[test]
    fn projective_rcb_air_interaction_trace_materializes_paired_logup_columns() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let relations = ProjectiveRcbMulComponentRelations::dummy();
        let (traces, interaction_claim) = claim.gen_interaction_trace(&relations);
        let log_sizes = claim.component_log_sizes();

        assert_eq!(traces.mul.len(), projective_rcb_mul_interaction_columns());
        assert_eq!(
            traces.raw_product_chunk.len(),
            projective_rcb_raw_product_chunk_interaction_columns()
        );
        assert_eq!(
            traces.folded_contribution.len(),
            projective_rcb_folded_contribution_interaction_columns()
        );
        assert_eq!(
            traces.folded_digit.len(),
            projective_rcb_folded_digit_interaction_columns()
        );
        assert!(traces
            .mul
            .iter()
            .all(|column| column.domain.log_size() == log_sizes.mul));
        assert!(traces
            .raw_product_chunk
            .iter()
            .all(|column| column.domain.log_size() == log_sizes.raw_product_chunk));
        assert!(traces
            .folded_contribution
            .iter()
            .all(|column| column.domain.log_size() == log_sizes.folded_contribution));
        assert!(traces
            .folded_digit
            .iter()
            .all(|column| column.domain.log_size() == log_sizes.folded_digit));
        assert_ne!(interaction_claim.total(), secure_zero());
        claim
            .verify_interaction_trace(&relations)
            .expect("interaction trace shape verifies");
    }

    #[test]
    fn projective_rcb_air_range_lookup_consumers_balance_with_providers() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let relations = ProjectiveRcbMulComponentRelations::dummy();

        let range13_values = claim.range13_lookup_values();
        assert_eq!(
            range13_values.len(),
            claim.mul_row_count()
                * (3 * N_LIMBS
                    + 2 * FP_SOLINAS_REDUCTION_DIGITS
                    + 2 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
                    + FP_SOLINAS_REDUCTION_DIGITS)
        );
        let range13 = RangeCheckClaim::new(RANGE13_BITS);
        let range13_preprocessed = range13.gen_preprocessed_column();
        let range13_multiplicity = range13.gen_multiplicity_trace(range13_values);
        let (_, range13_provider) =
            crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
                &range13_multiplicity,
                &range13_preprocessed,
                &relations.range13,
            );
        assert_eq!(
            range13_provider.claimed_sum + claim.range13_consumer_claimed_sum(&relations.range13),
            secure_zero()
        );

        let signed_carry_values = claim
            .signed_carry_lookup_values()
            .expect("signed carries fit fixed bound");
        assert_eq!(
            signed_carry_values.len(),
            claim.mul_row_count() * 4 * FP_SOLINAS_REDUCTION_DIGITS
        );
        let max_abs = signed_carry_values
            .iter()
            .map(|value| value.abs())
            .max()
            .unwrap_or_default();
        assert!(max_abs <= PROJECTIVE_RCB_SIGNED_CARRY_BOUND);
        let signed_carry = SignedCarryRangeClaim::new(
            projective_rcb_signed_carry_log_size(),
            PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
            PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
        );
        let signed_carry_preprocessed = signed_carry.gen_value_column();
        let signed_carry_multiplicity = signed_carry.gen_multiplicity_trace(signed_carry_values);
        let (_, signed_carry_provider) =
            crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
                &signed_carry_multiplicity,
                &signed_carry_preprocessed,
                &relations.signed_carry,
            );
        assert_eq!(
            signed_carry_provider.claimed_sum
                + claim
                    .signed_carry_consumer_claimed_sum(&relations.signed_carry)
                    .expect("signed carry consumer sum generates"),
            secure_zero()
        );
    }

    #[test]
    fn projective_rcb_air_proof_slice_materializes_registered_traces() {
        let trace = one_row_trace(ProjectiveEcOp::Double, PreparedAffinePoint::infinity());
        let claim =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&trace).expect("valid RCB AIR trace");
        let relations = ProjectiveRcbMulComponentRelations::dummy();
        let ids = claim.proof_slice_preprocessed_column_ids(&relations);
        let preprocessed = claim
            .gen_proof_slice_preprocessed_trace(&ids)
            .expect("proof preprocessed trace generates");
        let base = claim
            .gen_proof_slice_base_trace()
            .expect("proof base trace generates");
        let (interaction, interaction_claim) = claim
            .gen_proof_slice_interaction_trace(&relations)
            .expect("proof interaction trace generates");
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components =
            ProjectiveRcbAirComponents::new(&mut allocator, &claim, &interaction_claim, &relations);

        assert!(
            ids.contains(&crate::range_checks::range_check_value_column_id(
                RANGE13_BITS
            ))
        );
        assert!(
            ids.contains(&crate::range_checks::signed_carry_value_column_id(
                PROJECTIVE_RCB_SIGNED_CARRY_EQUATION
            ))
        );
        assert!(
            ids.contains(&crate::range_checks::signed_carry_active_column_id(
                PROJECTIVE_RCB_SIGNED_CARRY_EQUATION
            ))
        );
        assert_eq!(preprocessed.len(), ids.len());
        assert_eq!(
            base.len(),
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS
                + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
                + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
                + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
                + 2
        );
        assert_eq!(interaction_claim.total(), secure_zero());
        assert!(!interaction.is_empty());
        assert_eq!(components.mul.log_size(), claim.component_log_sizes().mul);
        assert_eq!(
            components.raw_product_chunk.log_size(),
            claim.component_log_sizes().raw_product_chunk
        );
        assert_eq!(components.range13.log_size(), RANGE13_BITS);
        assert_eq!(
            components.signed_carry.log_size(),
            projective_rcb_signed_carry_log_size()
        );
        claim
            .verify_proof_slice_traces(&relations)
            .expect("proof slice trace shape verifies");
    }
}
