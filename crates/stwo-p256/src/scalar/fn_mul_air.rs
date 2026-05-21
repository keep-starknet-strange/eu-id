use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{FNMUL_CHUNK_TERMS, PRODUCT_CHUNKS};

pub const FNMUL_SPLIT_CHUNK_TERMS: usize = FNMUL_CHUNK_TERMS;
pub const FNMUL_SPLIT_PRODUCT_CHUNKS: usize = PRODUCT_CHUNKS;
pub const FNMUL_SPLIT_CHUNK_DIGITS: usize = 3;
pub const FNMUL_SPLIT_CHUNK_TOP_DIGIT_BOUND: i64 = 1;
pub const M31_CENTERED_BOUND: i64 = (1i64 << 30) - 1;

const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

/// Worst-case absolute value of a split product chunk decomposition:
///
/// ```text
/// sum(a_i*b_i for up to 2 terms) - d0 - B*d1 - B^2*d2 = 0
/// ```
///
/// with `d0,d1 < B` and `d2 in {0,1}`.
pub const fn split_chunk_max_abs_expr() -> i64 {
    let product = (LIMB_BOUND - 1) * (LIMB_BOUND - 1);
    FNMUL_SPLIT_CHUNK_TERMS as i64 * product
        + (LIMB_BOUND - 1)
        + LIMB_BOUND * (LIMB_BOUND - 1)
        + LIMB_BOUND * LIMB_BOUND * FNMUL_SPLIT_CHUNK_TOP_DIGIT_BOUND
}

/// Conservative worst-case absolute value of the normalized split digit
/// equation:
///
/// ```text
/// ab_digit - qn_digit - result_digit + carry_in - B*carry_out = 0
/// ```
///
/// A digit can receive at most `ceil(N_LIMBS / 2)` chunk digits from a
/// coefficient, and at most three adjacent coefficient digit layers
/// (`d0`, previous `d1`, previous-previous `d2`).
pub const fn split_digit_max_abs_expr() -> i64 {
    let chunks_per_coeff =
        (N_LIMBS as i64 + FNMUL_SPLIT_CHUNK_TERMS as i64 - 1) / FNMUL_SPLIT_CHUNK_TERMS as i64;
    let product_digit_bound = 3 * chunks_per_coeff * (LIMB_BOUND - 1) + chunks_per_coeff;
    let diff_bound = 2 * product_digit_bound + (LIMB_BOUND - 1);
    let carry_bound = (diff_bound + LIMB_BOUND - 1) / LIMB_BOUND;
    diff_bound + carry_bound + LIMB_BOUND * carry_bound
}

pub fn split_fnmul_fits_m31_centered() -> bool {
    split_chunk_max_abs_expr() < M31_CENTERED_BOUND
        && split_digit_max_abs_expr() < M31_CENTERED_BOUND
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_fnmul_chunk_constraints_fit_m31_centered() {
        assert!(split_chunk_max_abs_expr() < M31_CENTERED_BOUND);
    }

    #[test]
    fn split_fnmul_digit_constraints_fit_m31_centered() {
        assert!(split_digit_max_abs_expr() < M31_CENTERED_BOUND);
    }

    #[test]
    fn split_fnmul_uses_expected_chunk_count() {
        assert_eq!(FNMUL_SPLIT_PRODUCT_CHUNKS, 210);
        assert_eq!(FNMUL_SPLIT_CHUNK_TERMS, 2);
        assert!(split_fnmul_fits_m31_centered());
    }
}
