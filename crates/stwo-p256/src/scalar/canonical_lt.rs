use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::BigIntLimbs;

use crate::limbs::P256EvalBigInt;
use crate::range_checks::{add_range_check, RangeCheckRelation};

/// Lookup relations consumed by [`add_canonical_lt_fixed_bound`].
#[derive(Clone, Copy)]
pub struct CanonicalLtRelations<'a> {
    /// 13-bit range table for value and slack limbs.
    pub limb_range: &'a RangeCheckRelation,
}

/// Enforce `value < bound` using `value + slack + 1 = bound`.
///
/// This function assumes `value` is the actual value being checked. The caller
/// should pass the same limb columns used by the consuming row, or separately
/// constrain equality before consuming this comparison. All constraints and
/// lookups are gated by `gate`; callers must use the same 0/1 selector that
/// guards downstream consumption.
pub fn add_canonical_lt_fixed_bound<E: EvalAtRow>(
    eval: &mut E,
    relations: CanonicalLtRelations<'_>,
    gate: E::F,
    value: &P256EvalBigInt<E>,
    bound: &BigIntLimbs,
    slack: &P256EvalBigInt<E>,
    carries: &[E::F; N_LIMBS],
) {
    assert!(bound.iter().all(|&limb| limb < (1u32 << LIMB_BITS)));
    let one = E::F::from(M31::from_u32_unchecked(1));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));

    for i in 0..N_LIMBS {
        add_range_check(
            eval,
            relations.limb_range,
            gate.clone(),
            value.limbs()[i].clone(),
        );
        add_range_check(
            eval,
            relations.limb_range,
            gate.clone(),
            slack.limbs()[i].clone(),
        );

        eval.add_constraint(gate.clone() * carries[i].clone() * (carries[i].clone() - one.clone()));

        let prev_carry = if i == 0 {
            E::F::from(M31::from_u32_unchecked(0))
        } else {
            carries[i - 1].clone()
        };
        let delta = if i == 0 {
            one.clone()
        } else {
            E::F::from(M31::from_u32_unchecked(0))
        };
        let recurrence = value.limbs()[i].clone() + slack.limbs()[i].clone() + prev_carry + delta
            - fixed_limb::<E>(bound, i)
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }

    eval.add_constraint(gate * carries[N_LIMBS - 1].clone());
}

fn fixed_limb<E: EvalAtRow>(limbs: &BigIntLimbs, index: usize) -> E::F {
    E::F::from(M31::from_u32_unchecked(limbs[index]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_p256_utils::scalar_arithmetic::{CanonicalLtTrace, P256_ORDER};

    const M31_MODULUS: i64 = (1i64 << 31) - 1;
    const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

    #[test]
    fn canonical_lt_limb_expression_has_m31_headroom() {
        let max = (LIMB_BOUND - 1) + (LIMB_BOUND - 1) + 1 + 1;
        let min = -(LIMB_BOUND - 1) - LIMB_BOUND;

        assert!(max < M31_MODULUS);
        assert!(min > -M31_MODULUS);
    }

    #[test]
    fn canonical_lt_trace_uses_boolean_carries() {
        let trace = CanonicalLtTrace::new("value", &[41, 0, 0, 0], "n", &P256_ORDER)
            .expect("value below n");

        assert!(trace.carries.iter().all(|&carry| carry == 0 || carry == 1));
    }
}
