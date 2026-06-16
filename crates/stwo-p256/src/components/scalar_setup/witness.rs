use crate::curve::mod_inverse;
use crate::field_ops::mul_mod_witness;
use crate::types::{curve_order, U256};
use stwo_p256_utils::scalar_arithmetic;

pub use stwo_p256_utils::scalar_arithmetic::{BigIntLimbs, ScalarArithmeticError, U256Words};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSetupWitness {
    pub trace: scalar_arithmetic::ScalarSetupTrace,
}

impl ScalarSetupWitness {
    pub fn new(z: &U256, r: &U256, s: &U256) -> Result<Self, ScalarArithmeticError> {
        let z_words = z.to_le_u64s();
        let r_words = r.to_le_u64s();
        let s_words = s.to_le_u64s();
        scalar_arithmetic::require_nonzero("r", &r_words)?;
        scalar_arithmetic::require_nonzero("s", &s_words)?;
        scalar_arithmetic::CanonicalLtTrace::new(
            "r",
            &r_words,
            "n",
            &scalar_arithmetic::P256_ORDER,
        )?;
        scalar_arithmetic::CanonicalLtTrace::new(
            "s",
            &s_words,
            "n",
            &scalar_arithmetic::P256_ORDER,
        )?;

        let n = curve_order();
        let s_inv = mod_inverse(s, &n);
        let z_reduction = scalar_arithmetic::DigestReductionTrace::new(&z_words, &n.to_le_u64s())?;
        let z_red = U256::from_le_u64s(&scalar_arithmetic::limbs_to_words(&z_reduction.z_red));
        let u1 = mul_mod_witness(&z_red, &s_inv, &n).result.to_u256();
        let u2 = mul_mod_witness(r, &s_inv, &n).result.to_u256();

        Ok(Self {
            trace: scalar_arithmetic::ScalarSetupTrace::new_with_u1_u2(
                &z_words,
                &r_words,
                &s_words,
                &u1.to_le_u64s(),
                &u2.to_le_u64s(),
            )?,
        })
    }

    pub fn verify(&self) -> Result<(), ScalarArithmeticError> {
        self.trace.verify()
    }

    pub fn u1(&self) -> U256Words {
        scalar_arithmetic::limbs_to_words(&self.trace.u1)
    }

    pub fn u2(&self) -> U256Words {
        scalar_arithmetic::limbs_to_words(&self.trace.u2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::P256_ORDER;

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    #[test]
    fn scalar_setup_witness_verifies_valid_equations() {
        let witness = ScalarSetupWitness::new(&scalar(42), &scalar(77), &scalar(11))
            .expect("valid scalar setup witness");

        witness.verify().expect("scalar setup verifies");
        assert_eq!(
            witness.trace.s_u1_eq.mul.result,
            witness.trace.z_reduction.z_red
        );
        assert_eq!(witness.trace.s_u2_eq.mul.result, witness.trace.r);
    }

    #[test]
    fn scalar_setup_allows_zero_digest_reduction() {
        let witness = ScalarSetupWitness::new(&U256::ZERO, &scalar(77), &scalar(11))
            .expect("zero digest is valid");

        witness.verify().expect("scalar setup verifies");
        assert_eq!(witness.trace.z_reduction.z_red, [0; 20]);
        assert_eq!(witness.u1(), [0; 4]);
    }

    #[test]
    fn scalar_setup_rejects_zero_r() {
        let err = ScalarSetupWitness::new(&scalar(42), &U256::ZERO, &scalar(11))
            .expect_err("r = 0 is invalid");

        assert!(matches!(
            err,
            ScalarArithmeticError::ZeroValue { value_name: "r" }
        ));
    }

    #[test]
    fn scalar_setup_rejects_s_equal_to_order() {
        let n = U256::from_le_u64s(&P256_ORDER);
        let err = ScalarSetupWitness::new(&scalar(42), &scalar(77), &n)
            .expect_err("s = n is non-canonical");

        assert!(matches!(
            err,
            ScalarArithmeticError::NonCanonical {
                value_name: "s",
                ..
            }
        ));
    }

    #[test]
    fn scalar_setup_detects_mutated_u1_result() {
        let mut witness = ScalarSetupWitness::new(&scalar(42), &scalar(77), &scalar(11))
            .expect("valid scalar setup witness");
        witness.trace.s_u1_eq.mul.result[0] = 41;

        let err = witness.verify().expect_err("mutated u1 result must fail");
        assert!(matches!(
            err,
            ScalarArithmeticError::TraceMismatch { .. }
                | ScalarArithmeticError::LimbEquationRemainder { .. }
                | ScalarArithmeticError::CarryMismatch { .. }
        ));
    }

    #[test]
    fn scalar_setup_detects_mutated_u2_carry() {
        let mut witness = ScalarSetupWitness::new(&scalar(42), &scalar(77), &scalar(11))
            .expect("valid scalar setup witness");
        witness.trace.s_u2_eq.mul.carries[0] += 1;

        let err = witness.verify().expect_err("mutated u2 carry must fail");
        assert!(matches!(err, ScalarArithmeticError::CarryMismatch { .. }));
    }

    #[test]
    fn scalar_setup_detects_mutated_digest_reduction() {
        let mut witness = ScalarSetupWitness::new(&scalar(42), &scalar(77), &scalar(11))
            .expect("valid scalar setup witness");
        witness.trace.z_reduction.z_red[0] = 41;

        let err = witness
            .verify()
            .expect_err("mutated digest reduction must fail");
        assert!(matches!(
            err,
            ScalarArithmeticError::TraceMismatch { .. }
                | ScalarArithmeticError::LimbEquationRemainder { .. }
                | ScalarArithmeticError::CarryMismatch { .. }
        ));
    }
}
