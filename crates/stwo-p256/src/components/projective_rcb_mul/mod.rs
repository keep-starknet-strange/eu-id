use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::solinas::REDUCTION_MATRIX;

use crate::fp_solinas::{FP_SOLINAS_LIMB_BASE, FP_SOLINAS_RAW_LIMBS};
use crate::fp_solinas_air::{
    FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT, FP_SOLINAS_REDUCTION_DIGITS,
};

pub mod relation;
pub mod trace;

pub use relation::*;
pub use trace::*;

pub const PROJECTIVE_RCB_SIGNED_CARRY_EQUATION: &str = "projective_rcb_reduction";

pub const PROJECTIVE_RCB_SIGNED_CARRY_BOUND: i64 = projective_rcb_signed_carry_bound();

pub const PROJECTIVE_RCB_MUL_ROLE_LHS: u32 = 0;

pub const PROJECTIVE_RCB_MUL_ROLE_RHS: u32 = 1;

pub const PROJECTIVE_RCB_MUL_ROLE_RESULT: u32 = 2;

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

#[cfg(test)]
mod tests;

// Schoolbook silo geometry used to derive the shared signed-carry bound.
// This value preserves the `2^18` table and signed-carry encoding.
const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS: usize = 8;
const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGITS: usize = 3;

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

const fn coefficient_term_count_const(coeff: usize) -> usize {
    if coeff < N_LIMBS {
        coeff + 1
    } else {
        FP_SOLINAS_RAW_LIMBS - coeff
    }
}
