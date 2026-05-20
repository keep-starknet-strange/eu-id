use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::BigIntLimbs;

use crate::limbs::P256EvalBigInt;
use crate::range_checks::{add_range_check, RangeCheckRelation};

/// Lookup relations consumed by [`add_canonical_lt_fixed_bound`] and
/// [`add_canonical_lt_witness_bound`].
///
/// `limb_range` is the 13-bit limb table. `carry_range` may be a small
/// unsigned range table such as Range7; the gadget also constrains each carry
/// to be boolean, so the effective carry set is exactly `{0, 1}`.
#[derive(Clone, Copy)]
pub struct CanonicalLtRelations<'a> {
    pub limb_range: &'a RangeCheckRelation,
    pub carry_range: &'a RangeCheckRelation,
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
    add_canonical_lt_constraints(
        eval,
        relations,
        gate,
        value,
        FixedBound { limbs: bound },
        slack,
        carries,
    );
}

/// Enforce `value < bound` where the bound is also witness-provided.
///
/// Use this only when the bound limbs are separately bound to public or
/// preprocessed data. Otherwise the prover can choose an easier bound. The
/// `gate` must be the same 0/1 selector that guards downstream consumption.
pub fn add_canonical_lt_witness_bound<E: EvalAtRow>(
    eval: &mut E,
    relations: CanonicalLtRelations<'_>,
    gate: E::F,
    value: &P256EvalBigInt<E>,
    bound: &P256EvalBigInt<E>,
    slack: &P256EvalBigInt<E>,
    carries: &[E::F; N_LIMBS],
) {
    add_canonical_lt_constraints(
        eval,
        relations,
        gate,
        value,
        WitnessBound { limbs: bound },
        slack,
        carries,
    );
}

fn add_canonical_lt_constraints<E: EvalAtRow, B: BoundLimbs<E>>(
    eval: &mut E,
    relations: CanonicalLtRelations<'_>,
    gate: E::F,
    value: &P256EvalBigInt<E>,
    bound: B,
    slack: &P256EvalBigInt<E>,
    carries: &[E::F; N_LIMBS],
) {
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
        if bound.is_witness() {
            add_range_check(eval, relations.limb_range, gate.clone(), bound.limb(i));
        }

        add_range_check(
            eval,
            relations.carry_range,
            gate.clone(),
            carries[i].clone(),
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
            - bound.limb(i)
            - limb_base.clone() * carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }

    eval.add_constraint(gate * carries[N_LIMBS - 1].clone());
}

trait BoundLimbs<E: EvalAtRow> {
    fn limb(&self, index: usize) -> E::F;
    fn is_witness(&self) -> bool;
}

struct FixedBound<'a> {
    limbs: &'a BigIntLimbs,
}

impl<E: EvalAtRow> BoundLimbs<E> for FixedBound<'_> {
    fn limb(&self, index: usize) -> E::F {
        E::F::from(M31::from_u32_unchecked(self.limbs[index]))
    }

    fn is_witness(&self) -> bool {
        false
    }
}

struct WitnessBound<'a, E: EvalAtRow> {
    limbs: &'a P256EvalBigInt<E>,
}

impl<E: EvalAtRow> BoundLimbs<E> for WitnessBound<'_, E> {
    fn limb(&self, index: usize) -> E::F {
        self.limbs.limbs()[index].clone()
    }

    fn is_witness(&self) -> bool {
        true
    }
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
