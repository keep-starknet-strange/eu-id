use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::solinas::{ReductionMatrix, REDUCTION_MATRIX};

use crate::constants::P256_MODULUS;
use crate::field_ops::mul_mod_witness;
use crate::limbs::P256M31BigInt;
use crate::types::U256;

pub const FP_SOLINAS_RAW_LIMBS: usize = 2 * N_LIMBS - 1;
pub const FP_SOLINAS_SIGNED_CORRECTION_LIMBS: usize = 9;
pub const FP_SOLINAS_LIMB_BASE: i128 = 1i128 << LIMB_BITS;
pub const M31_CENTERED_BOUND: i128 = (1i128 << 30) - 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FpSolinasMulTrace {
    pub lhs: P256M31BigInt,
    pub rhs: P256M31BigInt,
    pub result: P256M31BigInt,
    pub raw_product: [i128; FP_SOLINAS_RAW_LIMBS],
    pub folded_coefficients: [i128; N_LIMBS],
    pub correction: i128,
    pub carries: [i128; N_LIMBS],
}

impl FpSolinasMulTrace {
    pub fn new(lhs: &U256, rhs: &U256) -> Result<Self, FpSolinasError> {
        let modulus = U256::from_le_u64s(&P256_MODULUS);
        let result = mul_mod_witness(lhs, rhs, &modulus).result.to_u256();
        Self::new_with_result(lhs, rhs, &result)
    }

    pub fn new_with_result(lhs: &U256, rhs: &U256, result: &U256) -> Result<Self, FpSolinasError> {
        let lhs = P256M31BigInt::from_u256(lhs);
        let rhs = P256M31BigInt::from_u256(rhs);
        let result = P256M31BigInt::from_u256(result);
        let raw_product = raw_product(&lhs, &rhs);
        let folded_coefficients = fold_raw_product(&raw_product, &REDUCTION_MATRIX);
        let correction = solve_signed_correction(&folded_coefficients, &result)?;
        let carries = compute_carries(&folded_coefficients, &result, correction)?;
        let trace = Self {
            lhs,
            rhs,
            result,
            raw_product,
            folded_coefficients,
            correction,
            carries,
        };
        trace.verify()?;
        Ok(trace)
    }

    pub fn verify(&self) -> Result<(), FpSolinasError> {
        require_limbs_in_range("lhs", &self.lhs)?;
        require_limbs_in_range("rhs", &self.rhs)?;
        require_limbs_in_range("result", &self.result)?;
        if !is_less_than_modulus(&self.result) {
            return Err(FpSolinasError::NonCanonicalResult);
        }

        let expected_raw = raw_product(&self.lhs, &self.rhs);
        if self.raw_product != expected_raw {
            return Err(FpSolinasError::RawProductMismatch);
        }

        let expected_folded = fold_raw_product(&self.raw_product, &REDUCTION_MATRIX);
        if self.folded_coefficients != expected_folded {
            return Err(FpSolinasError::FoldedCoefficientMismatch);
        }

        let expected_carries =
            compute_carries(&self.folded_coefficients, &self.result, self.correction)?;
        if self.carries != expected_carries {
            return Err(FpSolinasError::CarryMismatch);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FpSolinasError {
    LimbOutOfRange {
        field: &'static str,
        limb: usize,
        value: u32,
    },
    NonCanonicalResult,
    RawProductMismatch,
    FoldedCoefficientMismatch,
    NoSignedCorrection,
    CarryResidueMismatch {
        limb: usize,
        residue: i128,
    },
    FinalCarryMismatch {
        carry: i128,
    },
    CarryMismatch,
}

fn raw_product(lhs: &P256M31BigInt, rhs: &P256M31BigInt) -> [i128; FP_SOLINAS_RAW_LIMBS] {
    let mut raw = [0i128; FP_SOLINAS_RAW_LIMBS];
    for i in 0..N_LIMBS {
        for j in 0..N_LIMBS {
            raw[i + j] += i128::from(lhs.limbs()[i].0) * i128::from(rhs.limbs()[j].0);
        }
    }
    raw
}

fn fold_raw_product(
    raw_product: &[i128; FP_SOLINAS_RAW_LIMBS],
    matrix: &ReductionMatrix,
) -> [i128; N_LIMBS] {
    let mut folded = [0i128; N_LIMBS];
    folded.copy_from_slice(&raw_product[..N_LIMBS]);
    for high in 0..(N_LIMBS - 1) {
        let high_coeff = raw_product[N_LIMBS + high];
        for (low, folded_coeff) in folded.iter_mut().enumerate() {
            *folded_coeff += high_coeff * i128::from(matrix[high][low]);
        }
    }
    folded
}

fn compute_carries(
    folded: &[i128; N_LIMBS],
    result: &P256M31BigInt,
    correction: i128,
) -> Result<[i128; N_LIMBS], FpSolinasError> {
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let mut carries = [0i128; N_LIMBS];
    let mut carry = 0i128;
    for i in 0..N_LIMBS {
        let total = folded[i]
            - i128::from(result.limbs()[i].0)
            - correction * i128::from(modulus.limbs()[i].0)
            + carry;
        let residue = total.rem_euclid(FP_SOLINAS_LIMB_BASE);
        if residue != 0 {
            return Err(FpSolinasError::CarryResidueMismatch { limb: i, residue });
        }
        carry = total.div_euclid(FP_SOLINAS_LIMB_BASE);
        carries[i] = carry;
    }
    if carry != 0 {
        return Err(FpSolinasError::FinalCarryMismatch { carry });
    }
    Ok(carries)
}

fn solve_signed_correction(
    folded: &[i128; N_LIMBS],
    result: &P256M31BigInt,
) -> Result<i128, FpSolinasError> {
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let mut coeffs = folded
        .iter()
        .zip(result.limbs())
        .map(|(&folded, result)| folded - i128::from(result.0))
        .collect::<Vec<_>>();
    coeffs.resize(N_LIMBS * 2, 0);

    let mut correction_digits = [0u32; N_LIMBS];
    for digit_index in 0..N_LIMBS {
        let digit = (-coeffs[digit_index]).rem_euclid(FP_SOLINAS_LIMB_BASE);
        correction_digits[digit_index] = digit as u32;
        for j in 0..N_LIMBS {
            coeffs[digit_index + j] -= digit * i128::from(modulus.limbs()[j].0);
        }
        debug_assert_eq!(coeffs[digit_index].rem_euclid(FP_SOLINAS_LIMB_BASE), 0);
        let carry = coeffs[digit_index].div_euclid(FP_SOLINAS_LIMB_BASE);
        coeffs[digit_index + 1] += carry;
        coeffs[digit_index] = 0;
    }

    signed_correction_from_digits(&correction_digits)
}

fn signed_correction_from_digits(digits: &[u32; N_LIMBS]) -> Result<i128, FpSolinasError> {
    let high_positive = digits[FP_SOLINAS_SIGNED_CORRECTION_LIMBS..]
        .iter()
        .all(|&digit| digit == 0);
    let high_negative = digits[FP_SOLINAS_SIGNED_CORRECTION_LIMBS..]
        .iter()
        .all(|&digit| i128::from(digit) == FP_SOLINAS_LIMB_BASE - 1);
    if !high_positive && !high_negative {
        return Err(FpSolinasError::NoSignedCorrection);
    }

    let mut value = 0i128;
    let mut place = 1i128;
    for digit in &digits[..FP_SOLINAS_SIGNED_CORRECTION_LIMBS] {
        value += i128::from(*digit) * place;
        place *= FP_SOLINAS_LIMB_BASE;
    }
    if high_negative {
        value -= place;
    }
    Ok(value)
}

fn require_limbs_in_range(
    field: &'static str,
    value: &P256M31BigInt,
) -> Result<(), FpSolinasError> {
    let bound = 1u32 << LIMB_BITS;
    for (limb, value) in value.limbs().iter().enumerate() {
        if value.0 >= bound {
            return Err(FpSolinasError::LimbOutOfRange {
                field,
                limb,
                value: value.0,
            });
        }
    }
    Ok(())
}

fn is_less_than_modulus(value: &P256M31BigInt) -> bool {
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    for (lhs, rhs) in value.limbs().iter().zip(modulus.limbs()).rev() {
        match lhs.0.cmp(&rhs.0) {
            core::cmp::Ordering::Less => return true,
            core::cmp::Ordering::Greater => return false,
            core::cmp::Ordering::Equal => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn max_abs_folded_coefficient_bound() -> i128 {
        let max_raw_limb = N_LIMBS as i128 * (FP_SOLINAS_LIMB_BASE - 1).pow(2);
        let max_matrix_column_sum = (0..N_LIMBS)
            .map(|column| {
                REDUCTION_MATRIX
                    .iter()
                    .map(|row| i128::from(row[column].abs()))
                    .sum::<i128>()
            })
            .max()
            .unwrap();
        max_raw_limb * (1 + max_matrix_column_sum)
    }

    #[test]
    fn fp_solinas_mul_trace_verifies_small_product() {
        let trace = FpSolinasMulTrace::new(&scalar(7), &scalar(11)).expect("valid trace");

        trace.verify().expect("trace verifies");
        assert_eq!(trace.result.to_u256(), scalar(77));
    }

    #[test]
    fn fp_solinas_mul_trace_matches_generic_modular_product() {
        let lhs = U256::from_le_u64s(&P256_GX);
        let rhs = U256::from_le_u64s(&P256_GY);
        let modulus = U256::from_le_u64s(&P256_MODULUS);
        let generic = mul_mod_witness(&lhs, &rhs, &modulus).result.to_u256();
        let trace = FpSolinasMulTrace::new(&lhs, &rhs).expect("valid trace");

        trace.verify().expect("trace verifies");
        assert_eq!(trace.result.to_u256(), generic);
    }

    #[test]
    fn fp_solinas_folded_coefficients_need_split_before_m31_air() {
        let folded_bound = max_abs_folded_coefficient_bound();

        assert!(folded_bound > M31_CENTERED_BOUND);
        assert!(folded_bound < (1i128 << 67));
        assert_eq!(FP_SOLINAS_SIGNED_CORRECTION_LIMBS * LIMB_BITS, 117);
    }

    #[test]
    fn fp_solinas_observed_corrections_fit_signed_window() {
        let cases = [
            (scalar(7), scalar(11)),
            (U256::from_le_u64s(&P256_GX), U256::from_le_u64s(&P256_GY)),
            (
                U256::from_le_u64s(&P256_MODULUS),
                U256::from_le_u64s(&P256_MODULUS),
            ),
        ];

        for (lhs, rhs) in cases {
            let trace = FpSolinasMulTrace::new(&lhs, &rhs).expect("valid trace");
            assert!(trace.correction.abs() < (1i128 << 116));
        }
    }

    #[test]
    fn fp_solinas_mul_trace_detects_mutated_raw_product() {
        let mut trace = FpSolinasMulTrace::new(&scalar(7), &scalar(11)).expect("valid trace");
        trace.raw_product[0] += 1;

        let err = trace.verify().expect_err("mutated raw product must fail");

        assert_eq!(err, FpSolinasError::RawProductMismatch);
    }

    #[test]
    fn fp_solinas_mul_trace_detects_mutated_folded_coefficient() {
        let mut trace = FpSolinasMulTrace::new(&scalar(7), &scalar(11)).expect("valid trace");
        trace.folded_coefficients[0] += 1;

        let err = trace
            .verify()
            .expect_err("mutated folded coefficient must fail");

        assert_eq!(err, FpSolinasError::FoldedCoefficientMismatch);
    }

    #[test]
    fn fp_solinas_mul_trace_detects_mutated_result() {
        let generic_wrong = scalar(78);

        let err = FpSolinasMulTrace::new_with_result(&scalar(7), &scalar(11), &generic_wrong)
            .expect_err("wrong result must fail");

        assert!(matches!(
            err,
            FpSolinasError::FinalCarryMismatch { .. }
                | FpSolinasError::CarryResidueMismatch { .. }
                | FpSolinasError::NoSignedCorrection
        ));
    }
}
