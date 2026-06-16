use super::carries::{build_product_carries, verify_product_equation};
use super::error::ScalarArithmeticError;
use super::limbs::{check_limbs_range, result_limb_i64, words_to_limbs};
use super::types::{BigIntLimbs, ProductCarries, U256Words};
use super::validation::{require_matching_limbs, CanonicalLtTrace};
use super::words::{divmod_512, mul_512, words_from_512_low, words_to_512};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnMulTrace {
    pub a: BigIntLimbs,
    pub b: BigIntLimbs,
    pub modulus: BigIntLimbs,
    pub result: BigIntLimbs,
    pub quotient: BigIntLimbs,
    pub carries: ProductCarries,
}

impl FnMulTrace {
    pub fn new(
        a: &U256Words,
        b: &U256Words,
        modulus: &U256Words,
    ) -> Result<Self, ScalarArithmeticError> {
        if modulus.iter().all(|&word| word == 0) {
            return Err(ScalarArithmeticError::InvalidBound {
                bound_name: "modulus",
            });
        }

        let product = mul_512(&words_to_512(a), &words_to_512(b));
        let (quotient, remainder) = divmod_512(&product, &words_to_512(modulus));
        let result_words = words_from_512_low(&remainder);
        let quotient_words = words_from_512_low(&quotient);

        let a = words_to_limbs(a);
        let b = words_to_limbs(b);
        let modulus = words_to_limbs(modulus);
        let result = words_to_limbs(&result_words);
        let quotient = words_to_limbs(&quotient_words);
        let ab_raw = schoolbook_mul_raw(&a, &b);
        let qm_raw = schoolbook_mul_raw(&quotient, &modulus);
        let carries = build_product_carries(|limb, carry_in| {
            raw_limb_i64(&ab_raw, limb)
                - raw_limb_i64(&qm_raw, limb)
                - result_limb_i64(&result, limb)
                + carry_in
        });

        Ok(Self {
            a,
            b,
            modulus,
            result,
            quotient,
            carries,
        })
    }

    pub fn result_words(&self) -> U256Words {
        super::limbs::limbs_to_words(&self.result)
    }

    pub fn quotient_words(&self) -> U256Words {
        super::limbs::limbs_to_words(&self.quotient)
    }

    pub fn verify(&self, equation: &'static str) -> Result<(), ScalarArithmeticError> {
        check_limbs_range("mul_a", &self.a)?;
        check_limbs_range("mul_b", &self.b)?;
        check_limbs_range("mul_modulus", &self.modulus)?;
        check_limbs_range("mul_result", &self.result)?;
        check_limbs_range("mul_quotient", &self.quotient)?;

        let ab_raw = schoolbook_mul_raw(&self.a, &self.b);
        let qm_raw = schoolbook_mul_raw(&self.quotient, &self.modulus);
        verify_product_equation(equation, &self.carries, |limb, carry_in| {
            raw_limb_i64(&ab_raw, limb)
                - raw_limb_i64(&qm_raw, limb)
                - result_limb_i64(&self.result, limb)
                + carry_in
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarFieldMulTrace {
    pub equation: &'static str,
    pub mul: FnMulTrace,
    pub a_lt_modulus: CanonicalLtTrace,
    pub b_lt_modulus: CanonicalLtTrace,
    pub result_lt_modulus: CanonicalLtTrace,
    pub quotient_lt_modulus: CanonicalLtTrace,
}

impl ScalarFieldMulTrace {
    pub fn new(
        equation: &'static str,
        a: &U256Words,
        b: &U256Words,
        modulus: &U256Words,
    ) -> Result<Self, ScalarArithmeticError> {
        let mul = FnMulTrace::new(a, b, modulus)?;
        let result = mul.result_words();
        let quotient = mul.quotient_words();

        Ok(Self {
            equation,
            mul,
            a_lt_modulus: CanonicalLtTrace::new("mul_a", a, "modulus", modulus)?,
            b_lt_modulus: CanonicalLtTrace::new("mul_b", b, "modulus", modulus)?,
            result_lt_modulus: CanonicalLtTrace::new("mul_result", &result, "modulus", modulus)?,
            quotient_lt_modulus: CanonicalLtTrace::new(
                "mul_quotient",
                &quotient,
                "modulus",
                modulus,
            )?,
        })
    }

    pub fn new_with_expected_result(
        equation: &'static str,
        a: &U256Words,
        b: &U256Words,
        expected_result: &U256Words,
        modulus: &U256Words,
    ) -> Result<Self, ScalarArithmeticError> {
        let trace = Self::new(equation, a, b, modulus)?;
        if trace.mul.result_words() != *expected_result {
            return Err(ScalarArithmeticError::UnexpectedProductRemainder { equation });
        }
        Ok(trace)
    }

    pub fn verify(&self) -> Result<(), ScalarArithmeticError> {
        self.a_lt_modulus.verify()?;
        self.b_lt_modulus.verify()?;
        self.result_lt_modulus.verify()?;
        self.quotient_lt_modulus.verify()?;

        require_matching_limbs("a_lt_modulus.value", &self.a_lt_modulus.value, &self.mul.a)?;
        require_matching_limbs(
            "a_lt_modulus.bound",
            &self.a_lt_modulus.bound,
            &self.mul.modulus,
        )?;
        require_matching_limbs("b_lt_modulus.value", &self.b_lt_modulus.value, &self.mul.b)?;
        require_matching_limbs(
            "b_lt_modulus.bound",
            &self.b_lt_modulus.bound,
            &self.mul.modulus,
        )?;
        require_matching_limbs(
            "result_lt_modulus.value",
            &self.result_lt_modulus.value,
            &self.mul.result,
        )?;
        require_matching_limbs(
            "result_lt_modulus.bound",
            &self.result_lt_modulus.bound,
            &self.mul.modulus,
        )?;
        require_matching_limbs(
            "quotient_lt_modulus.value",
            &self.quotient_lt_modulus.value,
            &self.mul.quotient,
        )?;
        require_matching_limbs(
            "quotient_lt_modulus.bound",
            &self.quotient_lt_modulus.bound,
            &self.mul.modulus,
        )?;

        self.mul.verify(self.equation)
    }
}

fn schoolbook_mul_raw(
    a: &BigIntLimbs,
    b: &BigIntLimbs,
) -> [u64; 2 * crate::constants::N_LIMBS - 1] {
    let mut result = [0u64; 2 * crate::constants::N_LIMBS - 1];
    for (i, &a_limb) in a.iter().enumerate() {
        for (j, &b_limb) in b.iter().enumerate() {
            result[i + j] += u64::from(a_limb) * u64::from(b_limb);
        }
    }
    result
}

fn raw_limb_i64<const N: usize>(raw: &[u64; N], limb: usize) -> i64 {
    raw.get(limb).copied().unwrap_or(0) as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar_arithmetic::P256_ORDER;

    fn scalar(value: u64) -> U256Words {
        [value, 0, 0, 0]
    }

    #[test]
    fn fn_mul_trace_verifies_modular_product() {
        let trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("operands are canonical");

        trace.verify().expect("multiplication trace verifies");
        assert_eq!(trace.mul.result_words(), scalar(77));
    }

    #[test]
    fn fn_mul_trace_rejects_expected_result_mismatch() {
        let err = ScalarFieldMulTrace::new_with_expected_result(
            "test_mul",
            &scalar(7),
            &scalar(11),
            &scalar(76),
            &P256_ORDER,
        )
        .expect_err("wrong expected remainder must fail");

        assert!(matches!(
            err,
            ScalarArithmeticError::UnexpectedProductRemainder { .. }
        ));
    }

    #[test]
    fn fn_mul_trace_detects_mutated_quotient() {
        let mut trace = ScalarFieldMulTrace::new("test_mul", &scalar(7), &scalar(11), &P256_ORDER)
            .expect("operands are canonical");
        trace.mul.quotient[0] = 1;

        let err = trace
            .verify()
            .expect_err("mutated quotient must fail range binding or product equation");
        assert!(matches!(
            err,
            ScalarArithmeticError::TraceMismatch { .. }
                | ScalarArithmeticError::LimbEquationRemainder { .. }
                | ScalarArithmeticError::CarryMismatch { .. }
                | ScalarArithmeticError::FinalCarryNonZero { .. }
        ));
    }
}
