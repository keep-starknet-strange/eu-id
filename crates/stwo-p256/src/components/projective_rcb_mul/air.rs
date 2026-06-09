//! AIR constraint evaluation (FrameworkEval impls, column readers, constraint builders) for the
//! projective RCB multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use super::*;
use crate::fp_solinas::{
    FP_SOLINAS_LIMB_BASE, FP_SOLINAS_SIGNED_CORRECTION_LIMBS, M31_CENTERED_BOUND,
};
use crate::fp_solinas_air::{
    add_fp_solinas_correction_digit_binding, add_fp_solinas_reduction_digit,
    FpSolinasCorrectionDigitColumns, FpSolinasReductionDigitColumns, FpSolinasReductionRelations,
    FP_SOLINAS_REDUCTION_DIGITS, FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS,
};
use crate::limbs::{EvalP256BigIntExt, P256EvalBigInt};
use crate::range_checks::add_range_check;

pub type ProjectiveRcbMulComponent = FrameworkComponent<ProjectiveRcbMulEval>;

pub type ProjectiveRcbRawProductChunkComponent =
    FrameworkComponent<ProjectiveRcbRawProductChunkEval>;

pub type ProjectiveRcbFoldedContributionComponent =
    FrameworkComponent<ProjectiveRcbFoldedContributionEval>;

pub type ProjectiveRcbFoldedDigitComponent = FrameworkComponent<ProjectiveRcbFoldedDigitEval>;

pub const PROJECTIVE_RCB_SIGNED_CARRY_EQUATION: &str = "projective_rcb_reduction";

pub const PROJECTIVE_RCB_SIGNED_CARRY_BOUND: i64 = projective_rcb_signed_carry_bound();

pub const PROJECTIVE_RCB_MUL_ROLE_LHS: u32 = 0;

pub const PROJECTIVE_RCB_MUL_ROLE_RHS: u32 = 1;

pub const PROJECTIVE_RCB_MUL_ROLE_RESULT: u32 = 2;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS: usize = 8;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS: usize = 3;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CARRY_BITS: u32 = 16;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS: usize = raw_product_chunk_count();

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERM_TRACE_COLUMNS: usize = 4;

pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS: usize = 4;

pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS: usize = folded_contribution_row_count_const();

pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERM_TRACE_COLUMNS: usize = 4;

pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS: usize = 1
    + 2
    + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS
        * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERM_TRACE_COLUMNS
    + 1;

pub const PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS: usize =
    folded_contribution_max_groups_per_digit_const();

pub const PROJECTIVE_RCB_FOLDED_DIGIT_GROUP_TRACE_COLUMNS: usize = 3;

pub const PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS: usize = 1
    + 2
    + PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS * PROJECTIVE_RCB_FOLDED_DIGIT_GROUP_TRACE_COLUMNS
    + 3;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS: usize = 1
    + 2
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERM_TRACE_COLUMNS
    + 1
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS
    + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS;

pub const PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS: usize = 2;

pub const PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS: usize = 1;

pub const PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS: usize = 3 * N_LIMBS;

/// Per-mul correction-digit columns that pin `correction_product_digit` to the
/// convolution of range-checked 13-bit digits with the constant modulus limbs
/// (closes C1): nine 13-bit digits plus one boolean sign bit.
pub const PROJECTIVE_RCB_MUL_CORRECTION_DIGIT_TRACE_COLUMNS: usize =
    FP_SOLINAS_SIGNED_CORRECTION_LIMBS + 1;

pub const PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS: usize =
    FP_SOLINAS_REDUCTION_DIGITS * FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS
        + 1
        + PROJECTIVE_RCB_MUL_CORRECTION_DIGIT_TRACE_COLUMNS;

pub const PROJECTIVE_RCB_MUL_TRACE_COLUMNS: usize = PROJECTIVE_RCB_MUL_ACTIVE_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_ID_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_LIMB_TRACE_COLUMNS
    + PROJECTIVE_RCB_MUL_REDUCTION_TRACE_COLUMNS;

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
        self.log_size + 1
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
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct ProjectiveRcbRawProductChunkEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
    /// Schedule-column id namespace. Use
    /// [`PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC`] for the EC projective trace and
    /// [`PROJECTIVE_RCB_SCHEDULE_NAMESPACE_PUBLIC_KEY`] for the public-key trace
    /// so two mul traces' schedule preprocessed columns stay distinct.
    pub schedule_namespace: &'static str,
}

#[derive(Clone)]
pub struct ProjectiveRcbFoldedContributionEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
    pub schedule_namespace: &'static str,
}

#[derive(Clone)]
pub struct ProjectiveRcbFoldedDigitEval {
    pub log_size: u32,
    pub relations: ProjectiveRcbMulComponentRelations,
    pub schedule_namespace: &'static str,
}

impl FrameworkEval for ProjectiveRcbFoldedContributionEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns =
            ProjectiveRcbFoldedContributionColumns::read(&mut eval, self.schedule_namespace);

        add_projective_rcb_folded_contribution(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup();
        eval
    }
}

impl FrameworkEval for ProjectiveRcbFoldedDigitEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns = ProjectiveRcbFoldedDigitColumns::read(&mut eval, self.schedule_namespace);

        add_projective_rcb_folded_digit(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup();
        eval
    }
}

impl FrameworkEval for ProjectiveRcbRawProductChunkEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let columns = ProjectiveRcbRawProductChunkColumns::read(&mut eval, self.schedule_namespace);

        add_projective_rcb_raw_product_chunk(&mut eval, self.relations.as_refs(), &columns);
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub struct ProjectiveRcbMulColumns<E: EvalAtRow> {
    pub lhs: P256EvalBigInt<E>,
    pub rhs: P256EvalBigInt<E>,
    pub result: P256EvalBigInt<E>,
    pub folded_final_carry: E::F,
    pub reduction: [FpSolinasReductionDigitColumns<E>; FP_SOLINAS_REDUCTION_DIGITS],
    /// Per-mul correction digits + sign bit that pin every
    /// `correction_product_digit` to its honest convolution value (closes C1).
    pub correction: FpSolinasCorrectionDigitColumns<E>,
}

impl<E: EvalAtRow> ProjectiveRcbMulColumns<E> {
    pub(crate) fn read(eval: &mut E) -> Self {
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
            correction: FpSolinasCorrectionDigitColumns {
                digits: core::array::from_fn(|_| eval.next_trace_mask()),
                sign_bit: eval.next_trace_mask(),
            },
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
    // C1: pin every (otherwise free) correction_product_digit to the convolution
    // of the range-checked 13-bit correction digits with the constant modulus
    // limbs, bounding each product digit by construction and forcing the honest
    // value.
    let product_digits: [E::F; FP_SOLINAS_REDUCTION_DIGITS] =
        core::array::from_fn(|d| columns.reduction[d].correction_product_digit.clone());
    add_fp_solinas_correction_digit_binding(
        eval,
        relations.range13,
        gate.clone(),
        &columns.correction,
        &product_digits,
    );
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
    pub schedule_active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub coeff: E::F,
    pub chunk: E::F,
    pub terms: [ProjectiveRcbRawProductTermColumns<E>; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS],
    pub carry1: E::F,
    pub digits: [E::F; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
    pub digit_use_counts: [E::F; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
    pub schedule_digit_use_counts: [E::F; PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS],
}

impl<E: EvalAtRow> ProjectiveRcbRawProductChunkColumns<E> {
    fn read(eval: &mut E, namespace: &str) -> Self {
        Self {
            active: eval.next_trace_mask(),
            schedule_active: eval.get_preprocessed_column(
                ProjectiveRcbRawProductChunkScheduleColumnIds::active(namespace),
            ),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            coeff: eval.get_preprocessed_column(
                ProjectiveRcbRawProductChunkScheduleColumnIds::coeff(namespace),
            ),
            chunk: eval.get_preprocessed_column(
                ProjectiveRcbRawProductChunkScheduleColumnIds::chunk(namespace),
            ),
            terms: core::array::from_fn(|term| ProjectiveRcbRawProductTermColumns {
                term_active: eval.next_trace_mask(),
                schedule_term_active: eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::term_active(namespace, term),
                ),
                lhs_index: eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::lhs_index(namespace, term),
                ),
                rhs_index: eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::rhs_index(namespace, term),
                ),
                lhs_limb: eval.next_trace_mask(),
                rhs_limb: eval.next_trace_mask(),
                product: eval.next_trace_mask(),
            }),
            carry1: eval.next_trace_mask(),
            digits: core::array::from_fn(|_| eval.next_trace_mask()),
            digit_use_counts: core::array::from_fn(|_| eval.next_trace_mask()),
            schedule_digit_use_counts: core::array::from_fn(|offset| {
                eval.get_preprocessed_column(
                    ProjectiveRcbRawProductChunkScheduleColumnIds::digit_use_count(
                        namespace, offset,
                    ),
                )
            }),
        }
    }
}

pub struct ProjectiveRcbRawProductTermColumns<E: EvalAtRow> {
    pub term_active: E::F,
    pub schedule_term_active: E::F,
    pub lhs_index: E::F,
    pub rhs_index: E::F,
    pub lhs_limb: E::F,
    pub rhs_limb: E::F,
    pub product: E::F,
}

fn add_raw_product_chunk_polynomial_constraints<E: EvalAtRow>(
    eval: &mut E,
    columns: &ProjectiveRcbRawProductChunkColumns<E>,
) {
    let mut product_sum = zero::<E>();
    eval.add_constraint(columns.active.clone() * (one::<E>() - columns.active.clone()));
    eval.add_constraint(columns.active.clone() - columns.schedule_active.clone());
    for term in &columns.terms {
        eval.add_constraint(term.term_active.clone() - term.schedule_term_active.clone());
        eval.add_constraint(term.term_active.clone() * (one::<E>() - term.term_active.clone()));
        eval.add_constraint(term.lhs_limb.clone() * term.rhs_limb.clone() - term.product.clone());
        product_sum += term.term_active.clone() * term.product.clone();
        constrain_unused(
            eval,
            columns.mul_index.clone(),
            term.term_active.clone(),
            term.lhs_limb.clone(),
        );
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.rhs_limb.clone(),
        );
    }
    for offset in 0..PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS {
        eval.add_constraint(
            columns.digit_use_counts[offset].clone()
                - columns.schedule_digit_use_counts[offset].clone(),
        );
    }
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    eval.add_constraint(
        product_sum - columns.digits[0].clone() - limb_base.clone() * columns.carry1.clone(),
    );
    eval.add_constraint(
        columns.carry1.clone() - columns.digits[1].clone() - limb_base * columns.digits[2].clone(),
    );
}

fn add_raw_product_chunk_relations<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbRawProductChunkColumns<E>,
) {
    for term in &columns.terms {
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            E::EF::from(term.term_active.clone()),
            columns.source_index.clone(),
            columns.mul_index.clone(),
            constant(PROJECTIVE_RCB_MUL_ROLE_LHS),
            term.lhs_index.clone(),
            term.lhs_limb.clone(),
        );
        add_projective_rcb_mul_limb_relation(
            eval,
            relations.mul_limb,
            E::EF::from(term.term_active.clone()),
            columns.source_index.clone(),
            columns.mul_index.clone(),
            constant(PROJECTIVE_RCB_MUL_ROLE_RHS),
            term.rhs_index.clone(),
            term.rhs_limb.clone(),
        );
    }
    for digit in &columns.digits {
        add_range_check(
            eval,
            relations.range13,
            columns.active.clone(),
            digit.clone(),
        );
    }
    add_range_check(
        eval,
        relations.raw_product_carry16,
        columns.active.clone(),
        columns.carry1.clone(),
    );
    for (offset, digit) in columns.digits.iter().enumerate() {
        eval.add_to_relation(RelationEntry::new(
            relations.raw_product_chunk_digit,
            -E::EF::from(columns.digit_use_counts[offset].clone()),
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

pub fn add_projective_rcb_raw_product_chunk<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbRawProductChunkColumns<E>,
) {
    add_raw_product_chunk_polynomial_constraints(eval, columns);
    add_raw_product_chunk_relations(eval, relations, columns);
}

pub struct ProjectiveRcbFoldedContributionColumns<E: EvalAtRow> {
    pub active: E::F,
    pub schedule_active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub digit_index: E::F,
    pub group_index: E::F,
    pub terms:
        [ProjectiveRcbFoldedContributionTermColumns<E>; PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS],
    pub contribution_sum: E::F,
}

impl<E: EvalAtRow> ProjectiveRcbFoldedContributionColumns<E> {
    fn read(eval: &mut E, namespace: &str) -> Self {
        Self {
            active: eval.next_trace_mask(),
            schedule_active: eval.get_preprocessed_column(
                ProjectiveRcbFoldedContributionScheduleColumnIds::active(namespace),
            ),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            digit_index: eval.get_preprocessed_column(
                ProjectiveRcbFoldedContributionScheduleColumnIds::digit_index(namespace),
            ),
            group_index: eval.get_preprocessed_column(
                ProjectiveRcbFoldedContributionScheduleColumnIds::group_index(namespace),
            ),
            terms: core::array::from_fn(|term| ProjectiveRcbFoldedContributionTermColumns {
                term_active: eval.next_trace_mask(),
                schedule_term_active: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::term_active(namespace, term),
                ),
                raw_coeff: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::raw_coeff(namespace, term),
                ),
                raw_chunk: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::raw_chunk(namespace, term),
                ),
                raw_offset: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::raw_offset(namespace, term),
                ),
                schedule_matrix_coeff: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedContributionScheduleColumnIds::matrix_coeff(namespace, term),
                ),
                matrix_coeff: eval.next_trace_mask(),
                raw_digit: eval.next_trace_mask(),
                contribution: eval.next_trace_mask(),
            }),
            contribution_sum: eval.next_trace_mask(),
        }
    }
}

pub struct ProjectiveRcbFoldedContributionTermColumns<E: EvalAtRow> {
    pub term_active: E::F,
    pub schedule_term_active: E::F,
    pub raw_coeff: E::F,
    pub raw_chunk: E::F,
    pub raw_offset: E::F,
    pub schedule_matrix_coeff: E::F,
    pub matrix_coeff: E::F,
    pub raw_digit: E::F,
    pub contribution: E::F,
}

pub struct ProjectiveRcbFoldedDigitColumns<E: EvalAtRow> {
    pub active: E::F,
    pub schedule_active: E::F,
    pub source_index: E::F,
    pub mul_index: E::F,
    pub digit_index: E::F,
    pub groups: [ProjectiveRcbFoldedDigitGroupColumns<E>; PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS],
    pub prev_carry: E::F,
    pub folded_digit: E::F,
    pub carry: E::F,
}

impl<E: EvalAtRow> ProjectiveRcbFoldedDigitColumns<E> {
    fn read(eval: &mut E, namespace: &str) -> Self {
        Self {
            active: eval.next_trace_mask(),
            schedule_active: eval.get_preprocessed_column(
                ProjectiveRcbFoldedDigitScheduleColumnIds::active(namespace),
            ),
            source_index: eval.next_trace_mask(),
            mul_index: eval.next_trace_mask(),
            digit_index: eval.get_preprocessed_column(
                ProjectiveRcbFoldedDigitScheduleColumnIds::digit_index(namespace),
            ),
            groups: core::array::from_fn(|group| ProjectiveRcbFoldedDigitGroupColumns {
                group_active: eval.next_trace_mask(),
                schedule_group_active: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedDigitScheduleColumnIds::group_active(namespace, group),
                ),
                group_index: eval.get_preprocessed_column(
                    ProjectiveRcbFoldedDigitScheduleColumnIds::group_index(namespace, group),
                ),
                contribution_sum: eval.next_trace_mask(),
                selected_contribution: eval.next_trace_mask(),
            }),
            prev_carry: eval.next_trace_mask(),
            folded_digit: eval.next_trace_mask(),
            carry: eval.next_trace_mask(),
        }
    }
}

pub struct ProjectiveRcbFoldedDigitGroupColumns<E: EvalAtRow> {
    pub group_active: E::F,
    pub schedule_group_active: E::F,
    pub group_index: E::F,
    pub contribution_sum: E::F,
    pub selected_contribution: E::F,
}

fn add_folded_contribution_polynomial_constraints<E: EvalAtRow>(
    eval: &mut E,
    columns: &ProjectiveRcbFoldedContributionColumns<E>,
) {
    let mut sum = zero::<E>();
    eval.add_constraint(columns.active.clone() * (one::<E>() - columns.active.clone()));
    eval.add_constraint(columns.active.clone() - columns.schedule_active.clone());
    for term in &columns.terms {
        eval.add_constraint(term.term_active.clone() - term.schedule_term_active.clone());
        eval.add_constraint(term.term_active.clone() * (one::<E>() - term.term_active.clone()));
        eval.add_constraint(term.matrix_coeff.clone() - term.schedule_matrix_coeff.clone());
        eval.add_constraint(
            term.matrix_coeff.clone() * term.raw_digit.clone() - term.contribution.clone(),
        );
        sum += term.term_active.clone() * term.contribution.clone();
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.raw_digit.clone(),
        );
        constrain_unused(
            eval,
            columns.active.clone(),
            term.term_active.clone(),
            term.contribution.clone(),
        );
    }
    eval.add_constraint(columns.active.clone() * (sum - columns.contribution_sum.clone()));
}

fn add_folded_contribution_relations<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbFoldedContributionColumns<E>,
) {
    for term in &columns.terms {
        eval.add_to_relation(RelationEntry::new(
            relations.raw_product_chunk_digit,
            E::EF::from(term.term_active.clone()),
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

pub fn add_projective_rcb_folded_contribution<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbFoldedContributionColumns<E>,
) {
    add_folded_contribution_polynomial_constraints(eval, columns);
    add_folded_contribution_relations(eval, relations, columns);
}

fn add_folded_digit_polynomial_constraints<E: EvalAtRow>(
    eval: &mut E,
    columns: &ProjectiveRcbFoldedDigitColumns<E>,
) {
    let mut contribution_sum = zero::<E>();
    eval.add_constraint(columns.active.clone() * (one::<E>() - columns.active.clone()));
    eval.add_constraint(columns.active.clone() - columns.schedule_active.clone());
    for group in &columns.groups {
        eval.add_constraint(group.group_active.clone() - group.schedule_group_active.clone());
        eval.add_constraint(group.group_active.clone() * (one::<E>() - group.group_active.clone()));
        eval.add_constraint(
            group.group_active.clone() * group.contribution_sum.clone()
                - group.selected_contribution.clone(),
        );
        contribution_sum += group.selected_contribution.clone();
        constrain_unused(
            eval,
            columns.active.clone(),
            group.group_active.clone(),
            group.contribution_sum.clone(),
        );
        constrain_unused(
            eval,
            columns.active.clone(),
            group.group_active.clone(),
            group.selected_contribution.clone(),
        );
    }

    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    eval.add_constraint(
        columns.active.clone()
            * (contribution_sum + columns.prev_carry.clone()
                - columns.folded_digit.clone()
                - limb_base * columns.carry.clone()),
    );
}

fn add_folded_digit_relations<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbFoldedDigitColumns<E>,
) {
    for group in &columns.groups {
        eval.add_to_relation(RelationEntry::new(
            relations.folded_contribution,
            E::EF::from(group.group_active.clone()),
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

pub fn add_projective_rcb_folded_digit<E: EvalAtRow>(
    eval: &mut E,
    relations: ProjectiveRcbMulRelations<'_>,
    columns: &ProjectiveRcbFoldedDigitColumns<E>,
) {
    add_folded_digit_polynomial_constraints(eval, columns);
    add_folded_digit_relations(eval, relations, columns);
}

pub const fn projective_rcb_raw_product_chunk_max_abs_expr() -> i128 {
    max_i128(
        projective_rcb_raw_product_chunk_first_carry_equation_max_abs_expr(),
        projective_rcb_raw_product_chunk_second_carry_equation_max_abs_expr(),
    )
}

pub const fn projective_rcb_raw_product_chunk_first_carry_equation_max_abs_expr() -> i128 {
    let product_sum =
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS as i128 * (FP_SOLINAS_LIMB_BASE - 1).pow(2);
    product_sum
        + (FP_SOLINAS_LIMB_BASE - 1)
        + FP_SOLINAS_LIMB_BASE * ((1i128 << PROJECTIVE_RCB_RAW_PRODUCT_CARRY_BITS) - 1)
}

pub const fn projective_rcb_raw_product_chunk_second_carry_equation_max_abs_expr() -> i128 {
    ((1i128 << PROJECTIVE_RCB_RAW_PRODUCT_CARRY_BITS) - 1)
        + (FP_SOLINAS_LIMB_BASE - 1)
        + FP_SOLINAS_LIMB_BASE * (FP_SOLINAS_LIMB_BASE - 1)
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
