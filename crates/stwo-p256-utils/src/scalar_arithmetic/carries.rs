use crate::constants::{LIMB_BITS, N_LIMBS};

use super::error::ScalarArithmeticError;
use super::types::{BigIntCarries, ProductCarries, PRODUCT_EQUATION_LIMBS};

const LIMB_RADIX: i64 = 1i64 << LIMB_BITS;

pub(super) fn build_carries(mut limb_total: impl FnMut(usize, i64) -> i64) -> BigIntCarries {
    let mut carries = [0; N_LIMBS];
    let mut carry = 0;
    for (limb, carry_out) in carries.iter_mut().enumerate() {
        let total = limb_total(limb, carry);
        debug_assert_eq!(total % LIMB_RADIX, 0);
        carry = total / LIMB_RADIX;
        *carry_out = carry;
    }
    debug_assert_eq!(carry, 0);
    carries
}

pub(super) fn build_product_carries(
    mut limb_total: impl FnMut(usize, i64) -> i64,
) -> ProductCarries {
    let mut carries = [0; PRODUCT_EQUATION_LIMBS];
    let mut carry = 0;
    for (limb, carry_out) in carries.iter_mut().enumerate() {
        let total = limb_total(limb, carry);
        debug_assert_eq!(total % LIMB_RADIX, 0);
        carry = total / LIMB_RADIX;
        *carry_out = carry;
    }
    debug_assert_eq!(carry, 0);
    carries
}

pub(super) fn verify_limb_equation(
    equation: &'static str,
    carries: &BigIntCarries,
    mut limb_total: impl FnMut(usize, i64) -> i64,
) -> Result<(), ScalarArithmeticError> {
    verify_carries(equation, carries, &mut limb_total)
}

pub(super) fn verify_product_equation(
    equation: &'static str,
    carries: &ProductCarries,
    mut limb_total: impl FnMut(usize, i64) -> i64,
) -> Result<(), ScalarArithmeticError> {
    verify_carries(equation, carries, &mut limb_total)
}

fn verify_carries<const N: usize>(
    equation: &'static str,
    carries: &[i64; N],
    limb_total: &mut impl FnMut(usize, i64) -> i64,
) -> Result<(), ScalarArithmeticError> {
    let mut carry = 0;
    for (limb, &actual_carry) in carries.iter().enumerate() {
        let total = limb_total(limb, carry);
        if total % LIMB_RADIX != 0 {
            return Err(ScalarArithmeticError::LimbEquationRemainder {
                equation,
                limb,
                total,
            });
        }
        let expected_carry = total / LIMB_RADIX;
        if actual_carry != expected_carry {
            return Err(ScalarArithmeticError::CarryMismatch {
                equation,
                limb,
                expected: expected_carry,
                actual: actual_carry,
            });
        }
        carry = actual_carry;
    }

    if carry != 0 {
        return Err(ScalarArithmeticError::FinalCarryNonZero { equation, carry });
    }
    Ok(())
}
