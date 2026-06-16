use super::error::ScalarArithmeticError;
use super::limbs::{is_zero_limbs, words_to_limbs};
use super::mul::ScalarFieldMulTrace;
use super::types::{BigIntLimbs, U256Words, P256_ORDER};
use super::validation::{
    require_matching_limbs, require_nonzero, CanonicalLtTrace, DigestReductionTrace,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSetupTrace {
    pub n: BigIntLimbs,
    pub z: BigIntLimbs,
    pub r: BigIntLimbs,
    pub s: BigIntLimbs,
    pub u1: BigIntLimbs,
    pub u2: BigIntLimbs,
    pub r_lt_n: CanonicalLtTrace,
    pub s_lt_n: CanonicalLtTrace,
    pub z_reduction: DigestReductionTrace,
    pub s_u1_eq: ScalarFieldMulTrace,
    pub s_u2_eq: ScalarFieldMulTrace,
}

impl ScalarSetupTrace {
    pub fn new_with_u1_u2(
        z: &U256Words,
        r: &U256Words,
        s: &U256Words,
        u1: &U256Words,
        u2: &U256Words,
    ) -> Result<Self, ScalarArithmeticError> {
        require_nonzero("r", r)?;
        require_nonzero("s", s)?;

        let r_lt_n = CanonicalLtTrace::new("r", r, "n", &P256_ORDER)?;
        let s_lt_n = CanonicalLtTrace::new("s", s, "n", &P256_ORDER)?;
        let z_reduction = DigestReductionTrace::new(z, &P256_ORDER)?;
        let z_red = super::limbs::limbs_to_words(&z_reduction.z_red);

        let s_u1_eq = ScalarFieldMulTrace::new_with_expected_result(
            "scalar_setup_u1",
            s,
            u1,
            &z_red,
            &P256_ORDER,
        )?;
        let s_u2_eq = ScalarFieldMulTrace::new_with_expected_result(
            "scalar_setup_u2",
            s,
            u2,
            r,
            &P256_ORDER,
        )?;

        Ok(Self {
            n: words_to_limbs(&P256_ORDER),
            z: words_to_limbs(z),
            r: words_to_limbs(r),
            s: words_to_limbs(s),
            u1: words_to_limbs(u1),
            u2: words_to_limbs(u2),
            r_lt_n,
            s_lt_n,
            z_reduction,
            s_u1_eq,
            s_u2_eq,
        })
    }

    pub fn verify(&self) -> Result<(), ScalarArithmeticError> {
        if is_zero_limbs(&self.r) {
            return Err(ScalarArithmeticError::ZeroValue { value_name: "r" });
        }
        if is_zero_limbs(&self.s) {
            return Err(ScalarArithmeticError::ZeroValue { value_name: "s" });
        }

        self.r_lt_n.verify()?;
        self.s_lt_n.verify()?;
        self.z_reduction.verify()?;
        self.s_u1_eq.verify()?;
        self.s_u2_eq.verify()?;

        require_matching_limbs("r_lt_n.value", &self.r_lt_n.value, &self.r)?;
        require_matching_limbs("r_lt_n.bound", &self.r_lt_n.bound, &self.n)?;
        require_matching_limbs("s_lt_n.value", &self.s_lt_n.value, &self.s)?;
        require_matching_limbs("s_lt_n.bound", &self.s_lt_n.bound, &self.n)?;
        require_matching_limbs("z_reduction.z", &self.z_reduction.z, &self.z)?;
        require_matching_limbs("z_reduction.n", &self.z_reduction.n, &self.n)?;

        require_matching_limbs("s_u1.a", &self.s_u1_eq.mul.a, &self.s)?;
        require_matching_limbs("s_u1.b", &self.s_u1_eq.mul.b, &self.u1)?;
        require_matching_limbs(
            "s_u1.result",
            &self.s_u1_eq.mul.result,
            &self.z_reduction.z_red,
        )?;
        require_matching_limbs("s_u1.modulus", &self.s_u1_eq.mul.modulus, &self.n)?;

        require_matching_limbs("s_u2.a", &self.s_u2_eq.mul.a, &self.s)?;
        require_matching_limbs("s_u2.b", &self.s_u2_eq.mul.b, &self.u2)?;
        require_matching_limbs("s_u2.result", &self.s_u2_eq.mul.result, &self.r)?;
        require_matching_limbs("s_u2.modulus", &self.s_u2_eq.mul.modulus, &self.n)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar(value: u64) -> U256Words {
        [value, 0, 0, 0]
    }

    #[test]
    fn scalar_setup_with_supplied_u1_u2_verifies() {
        let z = scalar(42);
        let r = scalar(77);
        let s = scalar(1);
        let u1 = z;
        let u2 = r;

        let trace = ScalarSetupTrace::new_with_u1_u2(&z, &r, &s, &u1, &u2)
            .expect("valid supplied scalar setup");

        trace.verify().expect("scalar setup verifies");
    }
}
