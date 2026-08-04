use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::P256_MODULUS;
use crate::fp_solinas::{
    FpSolinasError, FpSolinasMulTrace, FP_SOLINAS_LIMB_BASE, FP_SOLINAS_SIGNED_CORRECTION_LIMBS,
    M31_CENTERED_BOUND,
};
use crate::limbs::P256M31BigInt;
use crate::range_checks::{add_range_check, RangeCheckRelation};
use crate::types::U256;

// Each active row proves one split Solinas reduction digit.
// The row uses this recurrence:
// folded_digit - correction_product_digit - result_limb
//     + prev_carry - 2^13 * carry = 0.
// The caller supplies columns in the recurrence order.
// Range13 checks the folded and result digits.
// A signed table checks both carries.
// The correction accumulator supplies `correction_product_digit`.
// The complete constraint has degree 2.
pub const FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS: usize = 5;
pub const FP_SOLINAS_REDUCTION_DIGITS: usize = N_LIMBS + FP_SOLINAS_SIGNED_CORRECTION_LIMBS - 1;
pub const FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT: i128 =
    FP_SOLINAS_SIGNED_CORRECTION_LIMBS as i128 * (FP_SOLINAS_LIMB_BASE - 1).pow(2);
pub const FP_SOLINAS_REDUCTION_MAX_ABS_EXPR: i128 = 603_996_185;

#[derive(Clone, Copy)]
pub struct FpSolinasReductionRelations<'a> {
    /// 13-bit range table for canonical limbs and split correction digits.
    pub range13: &'a RangeCheckRelation,
    /// Signed carry table configured for the Solinas reduction carry bound.
    pub signed_carry: &'a RangeCheckRelation,
}

pub struct FpSolinasReductionDigitColumns<E: EvalAtRow> {
    pub folded_digit: E::F,
    pub correction_product_digit: E::F,
    pub result_limb: E::F,
    pub prev_carry: E::F,
    pub carry: E::F,
}

/// Enforce one split Solinas reduction digit:
///
/// ```text
/// folded_digit - correction_product_digit - result_limb
///     + prev_carry - 2^13 * carry = 0
/// ```
///
/// This is the row-local recurrence used after high-product terms have been
/// folded through the P-256 Solinas matrix and split into 13-bit digits. It is
/// intentionally narrower than a whole field multiplication row. Raw product
/// generation, matrix folding, and carry-link relations are separate rows.
pub fn add_fp_solinas_reduction_digit<E: EvalAtRow>(
    eval: &mut E,
    relations: FpSolinasReductionRelations<'_>,
    gate: E::F,
    columns: &FpSolinasReductionDigitColumns<E>,
) {
    add_range_check(
        eval,
        relations.range13,
        gate.clone(),
        columns.folded_digit.clone(),
    );
    add_range_check(
        eval,
        relations.range13,
        gate.clone(),
        columns.result_limb.clone(),
    );
    add_range_check(
        eval,
        relations.signed_carry,
        gate.clone(),
        columns.prev_carry.clone(),
    );
    add_range_check(
        eval,
        relations.signed_carry,
        gate.clone(),
        columns.carry.clone(),
    );

    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let recurrence = columns.folded_digit.clone()
        - columns.correction_product_digit.clone()
        - columns.result_limb.clone()
        + columns.prev_carry.clone()
        - limb_base * columns.carry.clone();
    eval.add_constraint(gate * recurrence);
}

pub fn fp_solinas_reduction_digit_fits_m31() -> bool {
    FP_SOLINAS_REDUCTION_MAX_ABS_EXPR < M31_CENTERED_BOUND
}

/// Per-multiplication witness columns that *generate* the otherwise-free
/// `correction_product_digit` values: the nine signed 13-bit digits of
/// `|correction|` plus a boolean sign bit. They are shared across all
/// [`FP_SOLINAS_REDUCTION_DIGITS`] reduction-digit rows of one Fp multiply.
///
/// These columns bind each correction product digit to a constrained convolution.
/// Without this binding, the correction product digit would be a free witness.
/// Range13 checks the correction digits.
/// Constant modulus limbs determine the unique correction product.
pub struct FpSolinasCorrectionDigitColumns<E: EvalAtRow> {
    /// Little-endian 13-bit digits of `|correction|`.
    pub digits: [E::F; FP_SOLINAS_SIGNED_CORRECTION_LIMBS],
    /// Sign bit: `0` for non-negative correction, `1` for negative.
    pub sign_bit: E::F,
}

/// Bind the free `correction_product_digit` columns to the constrained
/// convolution of range-checked 13-bit correction digits with the constant
/// P-256 modulus limbs, closing C1.
///
/// Enforces, gated by `gate`:
///  * each `correction_digit[i] ∈ [0, 2¹³)` (Range13 lookup).
///  * `sign_bit ∈ {0, 1}` (`sign_bit·(sign_bit−1) = 0`). And, with
///    `sign = 1 − 2·sign_bit`,
///  * for every reduction digit `d`,
///    `correction_product_digit[d] = sign · Σ_{i+j=d} correction_digit[i]·MOD[j]`
///    where `MOD[j]` are the constant modulus limbs.
///
/// The convolution term has degree two (`sign × digit`). Gated it is degree
/// three, matching the sign-bit boolean constraint above and fitting
/// the `log_size + 1` constraint-degree bound, so no auxiliary `signed_digit`
/// columns are required.
pub fn add_fp_solinas_correction_digit_binding<E: EvalAtRow>(
    eval: &mut E,
    range13: &RangeCheckRelation,
    gate: E::F,
    correction: &FpSolinasCorrectionDigitColumns<E>,
    product_digits: &[E::F; FP_SOLINAS_REDUCTION_DIGITS],
) {
    for digit in &correction.digits {
        add_range_check(eval, range13, gate.clone(), digit.clone());
    }
    eval.add_constraint(
        gate.clone()
            * correction.sign_bit.clone()
            * (correction.sign_bit.clone() - E::F::from(M31::from_u32_unchecked(1))),
    );

    // sign = 1 - 2 * sign_bit  (∈ {+1, -1}).
    let sign = E::F::from(M31::from_u32_unchecked(1))
        - correction.sign_bit.clone()
        - correction.sign_bit.clone();

    // Constant P-256 modulus limbs (`< 2¹³`, canonical M31), hoisted out of the
    // convolution loop. `mod_limbs[j]` is the `j`-th 13-bit limb.
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let mod_limbs = modulus.limbs();

    for (d, product_digit) in product_digits.iter().enumerate() {
        let mut convolution = E::F::from(M31::from_u32_unchecked(0));
        for (i, digit) in correction.digits.iter().enumerate() {
            // i + j = d, with j a valid modulus-limb index.
            if d < i || d - i >= N_LIMBS {
                continue;
            }
            convolution += digit.clone() * E::F::from(mod_limbs[d - i]);
        }
        eval.add_constraint(gate.clone() * (product_digit.clone() - sign.clone() * convolution));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FpSolinasReductionTraceClaim {
    pub rows: Vec<FpSolinasReductionRow>,
    pub folded_final_carry: i128,
}

impl FpSolinasReductionTraceClaim {
    pub fn from_mul_trace(trace: &FpSolinasMulTrace) -> Result<Self, FpSolinasReductionTraceError> {
        let (folded_digits, folded_final_carry) = folded_digits(trace)?;
        let correction_product_digits = correction_product_digits(trace)?;
        let mut rows = Vec::with_capacity(FP_SOLINAS_REDUCTION_DIGITS);
        let mut carry = 0i128;
        for digit_index in 0..FP_SOLINAS_REDUCTION_DIGITS {
            let result_limb = if digit_index < N_LIMBS {
                trace.result.limbs()[digit_index].0
            } else {
                0
            };
            let total = i128::from(folded_digits[digit_index])
                - correction_product_digits[digit_index]
                - i128::from(result_limb)
                + carry;
            let residue = total.rem_euclid(FP_SOLINAS_LIMB_BASE);
            if residue != 0 {
                return Err(FpSolinasReductionTraceError::ReductionResidueMismatch {
                    digit_index,
                    residue,
                });
            }
            let next_carry = total.div_euclid(FP_SOLINAS_LIMB_BASE);
            rows.push(FpSolinasReductionRow {
                digit_index,
                folded_digit: folded_digits[digit_index],
                correction_product_digit: correction_product_digits[digit_index],
                result_limb,
                prev_carry: carry,
                carry: next_carry,
            });
            carry = next_carry;
        }
        if carry + folded_final_carry != 0 {
            return Err(FpSolinasReductionTraceError::FinalCarryMismatch {
                carry,
                folded_final_carry,
            });
        }
        let claim = Self {
            rows,
            folded_final_carry,
        };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify_against_mul_trace(
        &self,
        trace: &FpSolinasMulTrace,
    ) -> Result<(), FpSolinasReductionTraceError> {
        let expected = Self::from_mul_trace(trace)?;
        if self == &expected {
            Ok(())
        } else {
            Err(FpSolinasReductionTraceError::TraceRowsMismatch)
        }
    }

    pub fn verify(&self) -> Result<(), FpSolinasReductionTraceError> {
        if self.rows.len() != FP_SOLINAS_REDUCTION_DIGITS {
            return Err(FpSolinasReductionTraceError::RowCountMismatch {
                expected: FP_SOLINAS_REDUCTION_DIGITS,
                actual: self.rows.len(),
            });
        }
        if !(-1..=0).contains(&self.folded_final_carry) {
            return Err(FpSolinasReductionTraceError::FoldedFinalCarryOutOfRange {
                carry: self.folded_final_carry,
            });
        }
        let mut expected_prev = 0i128;
        for (expected_index, row) in self.rows.iter().enumerate() {
            row.verify()?;
            if row.digit_index != expected_index {
                return Err(FpSolinasReductionTraceError::DigitIndexMismatch {
                    expected: expected_index,
                    actual: row.digit_index,
                });
            }
            if row.prev_carry != expected_prev {
                return Err(FpSolinasReductionTraceError::CarryLinkMismatch {
                    digit_index: row.digit_index,
                });
            }
            expected_prev = row.carry;
        }
        if expected_prev + self.folded_final_carry != 0 {
            return Err(FpSolinasReductionTraceError::FinalCarryMismatch {
                carry: expected_prev,
                folded_final_carry: self.folded_final_carry,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FpSolinasReductionRow {
    pub digit_index: usize,
    pub folded_digit: u32,
    pub correction_product_digit: i128,
    pub result_limb: u32,
    pub prev_carry: i128,
    pub carry: i128,
}

impl FpSolinasReductionRow {
    pub fn verify(&self) -> Result<(), FpSolinasReductionTraceError> {
        require_range13("folded_digit", self.digit_index, self.folded_digit)?;
        require_range13("result_limb", self.digit_index, self.result_limb)?;
        if self.correction_product_digit.abs() > FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT {
            return Err(
                FpSolinasReductionTraceError::CorrectionProductDigitOutOfRange {
                    digit_index: self.digit_index,
                    value: self.correction_product_digit,
                },
            );
        }
        let total = i128::from(self.folded_digit)
            - self.correction_product_digit
            - i128::from(self.result_limb)
            + self.prev_carry
            - FP_SOLINAS_LIMB_BASE * self.carry;
        if total == 0 {
            Ok(())
        } else {
            Err(FpSolinasReductionTraceError::ReductionEquationMismatch {
                digit_index: self.digit_index,
                value: total,
            })
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FpSolinasReductionTraceError {
    FpSolinas(FpSolinasError),
    RowCountMismatch {
        expected: usize,
        actual: usize,
    },
    DigitIndexMismatch {
        expected: usize,
        actual: usize,
    },
    LimbOutOfRange {
        field: &'static str,
        digit_index: usize,
        value: u32,
    },
    CorrectionProductDigitOutOfRange {
        digit_index: usize,
        value: i128,
    },
    FoldedResidueMismatch {
        digit_index: usize,
        residue: i128,
    },
    FoldedFinalCarryOutOfRange {
        carry: i128,
    },
    ReductionResidueMismatch {
        digit_index: usize,
        residue: i128,
    },
    ReductionEquationMismatch {
        digit_index: usize,
        value: i128,
    },
    CarryLinkMismatch {
        digit_index: usize,
    },
    FinalCarryMismatch {
        carry: i128,
        folded_final_carry: i128,
    },
    TraceRowsMismatch,
}

impl From<FpSolinasError> for FpSolinasReductionTraceError {
    fn from(value: FpSolinasError) -> Self {
        Self::FpSolinas(value)
    }
}

fn folded_digits(
    trace: &FpSolinasMulTrace,
) -> Result<([u32; FP_SOLINAS_REDUCTION_DIGITS], i128), FpSolinasReductionTraceError> {
    let mut digits = [0u32; FP_SOLINAS_REDUCTION_DIGITS];
    let mut carry = 0i128;
    for (digit_index, digit) in digits.iter_mut().enumerate() {
        let folded = trace
            .folded_coefficients
            .get(digit_index)
            .copied()
            .unwrap_or(0);
        let total = folded + carry;
        let residue = total.rem_euclid(FP_SOLINAS_LIMB_BASE);
        if !(0..FP_SOLINAS_LIMB_BASE).contains(&residue) {
            return Err(FpSolinasReductionTraceError::FoldedResidueMismatch {
                digit_index,
                residue,
            });
        }
        *digit = residue as u32;
        carry = total.div_euclid(FP_SOLINAS_LIMB_BASE);
    }
    if !(-1..=0).contains(&carry) {
        return Err(FpSolinasReductionTraceError::FoldedFinalCarryOutOfRange { carry });
    }
    Ok((digits, carry))
}

fn correction_product_digits(
    trace: &FpSolinasMulTrace,
) -> Result<[i128; FP_SOLINAS_REDUCTION_DIGITS], FpSolinasReductionTraceError> {
    let (sign, correction_digits) = signed_correction_digits(trace.correction)?;
    let modulus = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    let mut digits = [0i128; FP_SOLINAS_REDUCTION_DIGITS];
    for (correction_index, correction_digit) in correction_digits.iter().enumerate() {
        for modulus_index in 0..N_LIMBS {
            digits[correction_index + modulus_index] +=
                sign * i128::from(*correction_digit) * i128::from(modulus.limbs()[modulus_index].0);
        }
    }
    Ok(digits)
}

/// Returns trace values for [`add_fp_solinas_correction_digit_binding`].
///
/// The values contain a sign bit and nine little-endian 13-bit digits.
pub fn fp_solinas_correction_digit_columns(
    correction: i128,
) -> Result<(u32, [u32; FP_SOLINAS_SIGNED_CORRECTION_LIMBS]), FpSolinasReductionTraceError> {
    let (sign, digits) = signed_correction_digits(correction)?;
    let sign_bit = if sign < 0 { 1 } else { 0 };
    Ok((sign_bit, digits))
}

fn signed_correction_digits(
    correction: i128,
) -> Result<(i128, [u32; FP_SOLINAS_SIGNED_CORRECTION_LIMBS]), FpSolinasReductionTraceError> {
    let sign = if correction < 0 { -1 } else { 1 };
    let mut value = correction.abs();
    let mut digits = [0u32; FP_SOLINAS_SIGNED_CORRECTION_LIMBS];
    for digit in &mut digits {
        *digit = value.rem_euclid(FP_SOLINAS_LIMB_BASE) as u32;
        value = value.div_euclid(FP_SOLINAS_LIMB_BASE);
    }
    if value != 0 {
        return Err(FpSolinasReductionTraceError::FpSolinas(
            FpSolinasError::NoSignedCorrection,
        ));
    }
    Ok((sign, digits))
}

fn require_range13(
    field: &'static str,
    digit_index: usize,
    value: u32,
) -> Result<(), FpSolinasReductionTraceError> {
    if value < (1 << LIMB_BITS) {
        Ok(())
    } else {
        Err(FpSolinasReductionTraceError::LimbOutOfRange {
            field,
            digit_index,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::fp_solinas::FpSolinasMulTrace;
    use crate::types::U256;

    #[test]
    fn fp_solinas_reduction_digit_row_shape_is_narrow() {
        assert_eq!(FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS, 5);
    }

    #[test]
    fn fp_solinas_reduction_digit_expression_has_m31_headroom() {
        let limb_max = FP_SOLINAS_LIMB_BASE - 1;
        let carry_bound = 18;
        let max_abs = limb_max
            + FP_SOLINAS_CORRECTION_PRODUCT_MAX_ABS_DIGIT
            + limb_max
            + carry_bound
            + FP_SOLINAS_LIMB_BASE * carry_bound;

        assert_eq!(max_abs, FP_SOLINAS_REDUCTION_MAX_ABS_EXPR);
        assert!(fp_solinas_reduction_digit_fits_m31());
    }

    #[test]
    fn fp_solinas_reduction_trace_rows_verify_for_mul_trace() {
        let trace =
            FpSolinasMulTrace::new(&U256::from_le_u64s(&P256_GX), &U256::from_le_u64s(&P256_GY))
                .expect("valid mul trace");
        let rows =
            FpSolinasReductionTraceClaim::from_mul_trace(&trace).expect("valid reduction rows");

        rows.verify().expect("reduction rows verify");
        assert_eq!(rows.rows.len(), FP_SOLINAS_REDUCTION_DIGITS);
        rows.verify_against_mul_trace(&trace)
            .expect("reduction rows match mul trace");
    }

    #[test]
    fn fp_solinas_reduction_trace_detects_mutated_digit() {
        let trace =
            FpSolinasMulTrace::new(&U256::from_le_u64s(&P256_GX), &U256::from_le_u64s(&P256_GY))
                .expect("valid mul trace");
        let mut rows =
            FpSolinasReductionTraceClaim::from_mul_trace(&trace).expect("valid reduction rows");
        rows.rows[0].folded_digit ^= 1;

        let err = rows.verify().expect_err("mutated digit must fail");

        assert!(matches!(
            err,
            FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
        ));
    }

    #[test]
    fn fp_solinas_reduction_trace_detects_broken_carry_link() {
        let trace =
            FpSolinasMulTrace::new(&U256::from_le_u64s(&P256_GX), &U256::from_le_u64s(&P256_GY))
                .expect("valid mul trace");
        let mut rows =
            FpSolinasReductionTraceClaim::from_mul_trace(&trace).expect("valid reduction rows");
        rows.rows[1].prev_carry += 1;

        let err = rows.verify().expect_err("mutated carry link must fail");

        assert!(matches!(
            err,
            FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
                | FpSolinasReductionTraceError::CarryLinkMismatch { .. }
        ));
    }
}
