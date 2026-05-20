use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, BigIntLimbs, P256_ORDER};

use crate::limbs::P256EvalBigInt;
use crate::range_checks::{add_range_check, RangeCheckRelation};

use super::canonical_lt::{add_canonical_lt_fixed_bound, CanonicalLtRelations};

pub const DIGEST_TOP_LIMB_BITS: u32 = 9;
pub const DIGEST_REDUCTION_CARRY_BOUND: i64 = 1;
pub const FULL_FNMUL_MAX_ABS_COMBINED_EXPR: i64 = 5_368_045_569;
pub const M31_CENTERED_BOUND: i64 = (1i64 << 30) - 1;

/// Range-check relations consumed by [`add_digest_reduction`].
#[derive(Clone, Copy)]
pub struct DigestReductionRelations<'a> {
    /// 13-bit range table for ordinary 20x13 limbs.
    pub range13: &'a RangeCheckRelation,
    /// 9-bit range table for the top digest limb, enforcing `z < 2^256`.
    pub range9: &'a RangeCheckRelation,
    /// Signed carry table for the digest-reduction recurrence.
    ///
    /// Must be configured with [`DIGEST_REDUCTION_CARRY_BOUND`].
    pub signed_carry: &'a RangeCheckRelation,
    /// Carry table used by the nested `z_red < n` comparison.
    ///
    /// The comparison helper additionally constrains these carries to boolean.
    pub comparison_carry: &'a RangeCheckRelation,
}

pub struct DigestReductionColumns<E: EvalAtRow> {
    pub z: P256EvalBigInt<E>,
    pub z_red: P256EvalBigInt<E>,
    pub z_ge_n: E::F,
    pub carries: [E::F; N_LIMBS],
    pub z_red_lt_n_slack: P256EvalBigInt<E>,
    pub z_red_lt_n_carries: [E::F; N_LIMBS],
}

/// Enforce `z_red = z mod n` for a 256-bit digest.
///
/// The helper proves:
///
/// ```text
/// z - z_red - z_ge_n * n = 0
/// z_ge_n in {0, 1}
/// z < 2^256          (top limb Range9)
/// z_red < n          (canonical less-than helper)
/// ```
///
/// Soundness relies on `2^256 < 2n`, so one subtraction is sufficient.
/// `gate` must be the same 0/1 selector used by consumers of the reduced
/// digest.
pub fn add_digest_reduction<E: EvalAtRow>(
    eval: &mut E,
    relations: DigestReductionRelations<'_>,
    gate: E::F,
    columns: &DigestReductionColumns<E>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let n_limbs = words_to_limbs(&P256_ORDER);

    eval.add_constraint(gate.clone() * columns.z_ge_n.clone() * (columns.z_ge_n.clone() - one));

    for i in 0..N_LIMBS {
        let z_range = if i == N_LIMBS - 1 {
            relations.range9
        } else {
            relations.range13
        };
        add_range_check(eval, z_range, gate.clone(), columns.z.limbs()[i].clone());
        add_range_check(
            eval,
            relations.signed_carry,
            gate.clone(),
            columns.carries[i].clone(),
        );

        let prev_carry = if i == 0 {
            zero.clone()
        } else {
            columns.carries[i - 1].clone()
        };
        let recurrence = columns.z.limbs()[i].clone()
            - columns.z_red.limbs()[i].clone()
            - columns.z_ge_n.clone() * fixed_limb::<E>(&n_limbs, i)
            + prev_carry
            - limb_base.clone() * columns.carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }
    eval.add_constraint(gate.clone() * columns.carries[N_LIMBS - 1].clone());

    add_canonical_lt_fixed_bound(
        eval,
        CanonicalLtRelations {
            limb_range: relations.range13,
            carry_range: relations.comparison_carry,
        },
        gate,
        &columns.z_red,
        &n_limbs,
        &columns.z_red_lt_n_slack,
        &columns.z_red_lt_n_carries,
    );
}

pub fn full_fnmul_requires_split() -> bool {
    FULL_FNMUL_MAX_ABS_COMBINED_EXPR > M31_CENTERED_BOUND
}

fn fixed_limb<E: EvalAtRow>(limbs: &BigIntLimbs, index: usize) -> E::F {
    E::F::from(M31::from_u32_unchecked(limbs[index]))
}

#[cfg(test)]
mod tests {
    use super::*;

    const M31_MODULUS: i64 = (1i64 << 31) - 1;
    const LIMB_BOUND: i64 = 1i64 << LIMB_BITS;

    #[test]
    fn digest_reduction_limb_expression_has_m31_headroom() {
        let max = (LIMB_BOUND - 1)
            + DIGEST_REDUCTION_CARRY_BOUND
            + LIMB_BOUND * DIGEST_REDUCTION_CARRY_BOUND;
        let min = -(LIMB_BOUND - 1)
            - (LIMB_BOUND - 1)
            - DIGEST_REDUCTION_CARRY_BOUND
            - LIMB_BOUND * DIGEST_REDUCTION_CARRY_BOUND;

        assert!(max < M31_MODULUS);
        assert!(min > -M31_MODULUS);
    }

    #[test]
    fn digest_top_limb_uses_nine_bits() {
        assert_eq!(DIGEST_TOP_LIMB_BITS, 9);
        assert_eq!(N_LIMBS * LIMB_BITS, 260);
        assert_eq!(
            (N_LIMBS - 1) * LIMB_BITS + DIGEST_TOP_LIMB_BITS as usize,
            256
        );
    }

    #[test]
    fn full_fnmul_is_not_direct_m31_safe() {
        assert!(full_fnmul_requires_split());
    }
}
