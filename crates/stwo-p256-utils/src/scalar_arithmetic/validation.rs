use core::cmp::Ordering;

use super::carries::{build_carries, verify_limb_equation};
use super::error::ScalarArithmeticError;
use super::limbs::{check_limbs_range, limb_i64, words_to_limbs};
use super::types::{BigIntCarries, BigIntLimbs, U256Words};
use super::words::{checked_sub_words, cmp_words, is_zero_words, sub_one_words};

const DIGEST_TOP_LIMB_BOUND: u32 = 1u32 << 9;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalLtTrace {
    pub value_name: &'static str,
    pub bound_name: &'static str,
    pub value: BigIntLimbs,
    pub bound: BigIntLimbs,
    /// Slack for `value < bound`: `value + slack + 1 = bound`.
    pub slack: BigIntLimbs,
    pub carries: BigIntCarries,
}

impl CanonicalLtTrace {
    pub fn new(
        value_name: &'static str,
        value: &U256Words,
        bound_name: &'static str,
        bound: &U256Words,
    ) -> Result<Self, ScalarArithmeticError> {
        ensure_nonzero_bound(bound_name, bound)?;
        if cmp_words(value, bound) != Ordering::Less {
            return Err(ScalarArithmeticError::NonCanonical {
                value_name,
                bound_name,
            });
        }

        let bound_minus_one =
            sub_one_words(bound).ok_or(ScalarArithmeticError::InvalidBound { bound_name })?;
        let slack_words = checked_sub_words(&bound_minus_one, value).ok_or(
            ScalarArithmeticError::NonCanonical {
                value_name,
                bound_name,
            },
        )?;

        let value = words_to_limbs(value);
        let bound = words_to_limbs(bound);
        let slack = words_to_limbs(&slack_words);
        let carries = build_carries(|limb, carry_in| {
            limb_i64(&value, limb) + limb_i64(&slack, limb) + i64::from(limb == 0)
                - limb_i64(&bound, limb)
                + carry_in
        });

        Ok(Self {
            value_name,
            bound_name,
            value,
            bound,
            slack,
            carries,
        })
    }

    pub fn verify(&self) -> Result<(), ScalarArithmeticError> {
        check_limbs_range(self.value_name, &self.value)?;
        check_limbs_range(self.bound_name, &self.bound)?;
        check_limbs_range("lt_slack", &self.slack)?;
        verify_limb_equation("canonical_lt", &self.carries, |limb, carry_in| {
            limb_i64(&self.value, limb) + limb_i64(&self.slack, limb) + i64::from(limb == 0)
                - limb_i64(&self.bound, limb)
                + carry_in
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigestReductionTrace {
    pub z: BigIntLimbs,
    pub z_red: BigIntLimbs,
    pub z_ge_n: u32,
    pub n: BigIntLimbs,
    pub carries: BigIntCarries,
    pub z_red_lt_n: CanonicalLtTrace,
}

impl DigestReductionTrace {
    pub fn new(z: &U256Words, n: &U256Words) -> Result<Self, ScalarArithmeticError> {
        ensure_nonzero_bound("n", n)?;
        let z_ge_n = u32::from(cmp_words(z, n) != Ordering::Less);
        let z_red_words = if z_ge_n == 1 {
            checked_sub_words(z, n).expect("z >= n")
        } else {
            *z
        };

        let z = words_to_limbs(z);
        let z_red = words_to_limbs(&z_red_words);
        let n_limbs = words_to_limbs(n);
        let carries = build_carries(|limb, carry_in| {
            limb_i64(&z, limb)
                - limb_i64(&z_red, limb)
                - i64::from(z_ge_n) * limb_i64(&n_limbs, limb)
                + carry_in
        });
        let z_red_lt_n = CanonicalLtTrace::new("z_red", &z_red_words, "n", n)?;

        Ok(Self {
            z,
            z_red,
            z_ge_n,
            n: n_limbs,
            carries,
            z_red_lt_n,
        })
    }

    pub fn verify(&self) -> Result<(), ScalarArithmeticError> {
        check_limbs_range("z", &self.z)?;
        check_digest_top_limb(&self.z)?;
        check_limbs_range("z_red", &self.z_red)?;
        check_limbs_range("n", &self.n)?;
        if self.z_ge_n > 1 {
            return Err(ScalarArithmeticError::InvalidBoolean {
                name: "z_ge_n",
                value: self.z_ge_n,
            });
        }

        self.z_red_lt_n.verify()?;
        require_matching_limbs("z_red_lt_n.value", &self.z_red_lt_n.value, &self.z_red)?;
        require_matching_limbs("z_red_lt_n.bound", &self.z_red_lt_n.bound, &self.n)?;

        verify_limb_equation("digest_reduction", &self.carries, |limb, carry_in| {
            limb_i64(&self.z, limb)
                - limb_i64(&self.z_red, limb)
                - i64::from(self.z_ge_n) * limb_i64(&self.n, limb)
                + carry_in
        })
    }
}

pub fn require_nonzero(
    value_name: &'static str,
    value: &U256Words,
) -> Result<(), ScalarArithmeticError> {
    if is_zero_words(value) {
        Err(ScalarArithmeticError::ZeroValue { value_name })
    } else {
        Ok(())
    }
}

pub(super) fn require_matching_limbs(
    value_name: &'static str,
    actual: &BigIntLimbs,
    expected: &BigIntLimbs,
) -> Result<(), ScalarArithmeticError> {
    if actual == expected {
        Ok(())
    } else {
        Err(ScalarArithmeticError::TraceMismatch { value_name })
    }
}

fn ensure_nonzero_bound(
    bound_name: &'static str,
    bound: &U256Words,
) -> Result<(), ScalarArithmeticError> {
    if is_zero_words(bound) {
        Err(ScalarArithmeticError::InvalidBound { bound_name })
    } else {
        Ok(())
    }
}

fn check_digest_top_limb(value: &BigIntLimbs) -> Result<(), ScalarArithmeticError> {
    let top_limb = value[value.len() - 1];
    if top_limb < DIGEST_TOP_LIMB_BOUND {
        Ok(())
    } else {
        Err(ScalarArithmeticError::LimbOutOfRange {
            value_name: "z_top_limb",
            limb: value.len() - 1,
            value: top_limb,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar_arithmetic::{limbs_to_words, P256_ORDER};

    fn scalar(value: u64) -> U256Words {
        [value, 0, 0, 0]
    }

    #[test]
    fn canonical_lt_accepts_value_below_bound() {
        let trace = CanonicalLtTrace::new("value", &scalar(41), "bound", &scalar(101))
            .expect("value is below bound");

        trace.verify().expect("canonical trace verifies");
        assert_eq!(limbs_to_words(&trace.slack), scalar(59));
    }

    #[test]
    fn canonical_lt_rejects_value_equal_to_bound() {
        let err = CanonicalLtTrace::new("value", &scalar(101), "bound", &scalar(101))
            .expect_err("value equal to bound is non-canonical");

        assert!(matches!(err, ScalarArithmeticError::NonCanonical { .. }));
    }

    #[test]
    fn canonical_lt_detects_mutated_slack() {
        let mut trace = CanonicalLtTrace::new("value", &scalar(41), "bound", &scalar(101))
            .expect("value is below bound");
        trace.slack[0] = 58;

        let err = trace
            .verify()
            .expect_err("mutated slack must fail the limb equation");
        assert!(matches!(
            err,
            ScalarArithmeticError::LimbEquationRemainder { .. }
                | ScalarArithmeticError::CarryMismatch { .. }
        ));
    }

    #[test]
    fn canonical_lt_rejects_wrapped_negative_slack_by_final_carry() {
        let mut trace = CanonicalLtTrace::new("value", &scalar(100), "bound", &scalar(101))
            .expect("value is below bound");
        trace.value = words_to_limbs(&scalar(101));
        trace.slack = [8191; crate::constants::N_LIMBS];
        trace.carries = [1; crate::constants::N_LIMBS];

        let err = trace
            .verify()
            .expect_err("wrapped -1 slack must leave nonzero final carry");
        assert!(matches!(
            err,
            ScalarArithmeticError::FinalCarryNonZero { carry: 1, .. }
        ));
    }

    #[test]
    fn digest_reduction_keeps_small_digest() {
        let trace = DigestReductionTrace::new(&scalar(42), &P256_ORDER).expect("digest reduces");

        trace.verify().expect("digest reduction verifies");
        assert_eq!(trace.z_ge_n, 0);
        assert_eq!(limbs_to_words(&trace.z_red), scalar(42));
    }

    #[test]
    fn digest_reduction_subtracts_order_once() {
        let z = [
            P256_ORDER[0] + 17,
            P256_ORDER[1],
            P256_ORDER[2],
            P256_ORDER[3],
        ];
        let trace = DigestReductionTrace::new(&z, &P256_ORDER).expect("digest reduces");

        trace.verify().expect("digest reduction verifies");
        assert_eq!(trace.z_ge_n, 1);
        assert_eq!(limbs_to_words(&trace.z_red), scalar(17));
    }

    #[test]
    fn digest_reduction_detects_mutated_flag() {
        let mut trace =
            DigestReductionTrace::new(&scalar(42), &P256_ORDER).expect("digest reduces");
        trace.z_ge_n = 1;

        let err = trace
            .verify()
            .expect_err("wrong reduction branch must fail");
        assert!(matches!(
            err,
            ScalarArithmeticError::LimbEquationRemainder { .. }
                | ScalarArithmeticError::CarryMismatch { .. }
                | ScalarArithmeticError::FinalCarryNonZero { .. }
        ));
    }
}
