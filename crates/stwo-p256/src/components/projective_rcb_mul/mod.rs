use stwo::core::{
    air::Component,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::ComponentProver;
use stwo_constraint_framework::{EvalAtRow, TraceLocationAllocator};
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::solinas::REDUCTION_MATRIX;

use crate::fp_solinas::{FP_SOLINAS_LIMB_BASE, FP_SOLINAS_RAW_LIMBS};
use crate::fp_solinas_air::{
    FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT, FP_SOLINAS_REDUCTION_DIGITS,
};
use crate::range_checks::{
    RangeCheckComponent, RangeCheckEval, SignedCarryRangeComponent, SignedCarryRangeEval,
    RANGE13_BITS,
};

pub mod air;
pub mod interaction;
pub mod relation;
pub mod trace;

pub use air::*;
pub use interaction::*;
pub use relation::*;
pub use trace::*;

#[cfg(test)]
mod tests;

const QM31_TRACE_COLUMNS: usize = 4;

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
        Self::new_with_log_sizes(
            allocator,
            claim.component_log_sizes(),
            interaction_claim,
            relations,
        )
    }

    pub fn new_with_log_sizes(
        allocator: &mut TraceLocationAllocator,
        log_sizes: ProjectiveRcbAirComponentLogSizes,
        interaction_claim: &ProjectiveRcbAirProofInteractionClaim,
        relations: &ProjectiveRcbMulComponentRelations,
    ) -> Self {
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
                    schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
                },
                interaction_claim.components.raw_product_chunk,
            ),
            folded_contribution: ProjectiveRcbFoldedContributionComponent::new(
                allocator,
                ProjectiveRcbFoldedContributionEval {
                    log_size: log_sizes.folded_contribution,
                    relations: relations.clone(),
                    schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
                },
                interaction_claim.components.folded_contribution,
            ),
            folded_digit: ProjectiveRcbFoldedDigitComponent::new(
                allocator,
                ProjectiveRcbFoldedDigitEval {
                    log_size: log_sizes.folded_digit,
                    relations: relations.clone(),
                    schedule_namespace: PROJECTIVE_RCB_SCHEDULE_NAMESPACE_EC,
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

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.mul as &dyn Component,
            &self.raw_product_chunk as &dyn Component,
            &self.folded_contribution as &dyn Component,
            &self.folded_digit as &dyn Component,
            &self.range13 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.mul as &dyn ComponentProver<SimdBackend>,
            &self.raw_product_chunk as &dyn ComponentProver<SimdBackend>,
            &self.folded_contribution as &dyn ComponentProver<SimdBackend>,
            &self.folded_digit as &dyn ComponentProver<SimdBackend>,
            &self.range13 as &dyn ComponentProver<SimdBackend>,
            &self.signed_carry as &dyn ComponentProver<SimdBackend>,
        ]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            self.components()
                .into_iter()
                .map(|component| component.trace_log_degree_bounds()),
        )
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
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
