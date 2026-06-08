use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use crate::limbs::P256EvalBigInt;
use crate::range_checks::RangeCheckRelation;

use crate::scalar::canonical_lt::{add_canonical_lt_fixed_bound, CanonicalLtRelations};
use super::{
    provide_scalar_limb, ScalarLimbRelation, PRODUCT_SCALAR_LIMB_USE_COUNT, ROLE_A, ROLE_B,
    ROLE_QUOTIENT, ROLE_RESULT,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarModMulLimbRole {
    A,
    B,
    Quotient,
    Result,
}

impl ScalarModMulLimbRole {
    pub const fn relation_role(self) -> u32 {
        match self {
            Self::A => ROLE_A,
            Self::B => ROLE_B,
            Self::Quotient => ROLE_QUOTIENT,
            Self::Result => ROLE_RESULT,
        }
    }

    const fn provider_multiplicity(self) -> u32 {
        match self {
            Self::A | Self::B | Self::Quotient => PRODUCT_SCALAR_LIMB_USE_COUNT,
            Self::Result => 1,
        }
    }
}

pub struct CanonicalLtNColumns<E: EvalAtRow> {
    /// Scalar limbs being proven canonical.
    pub value: P256EvalBigInt<E>,
    /// Nonnegative slack for `value + slack + 1 = n`.
    pub slack: P256EvalBigInt<E>,
    /// Boolean carry chain for the canonical less-than recurrence.
    pub carries: [E::F; N_LIMBS],
}

#[derive(Clone, Copy)]
pub struct CanonicalLtNRelations<'a> {
    /// 13-bit range table for scalar and slack limbs.
    pub range13: &'a RangeCheckRelation,
}

#[derive(Clone, Copy)]
pub struct CanonicalScalarLimbRelations<'a> {
    /// 13-bit range table for scalar and slack limbs.
    pub range13: &'a RangeCheckRelation,
    /// Provider side of the keyed scalar limb relation.
    pub scalar_limb: &'a ScalarLimbRelation,
}

/// Prove `value < n`.
pub fn add_canonical_lt_n<E: EvalAtRow>(
    eval: &mut E,
    relations: CanonicalLtNRelations<'_>,
    gate: E::F,
    columns: &CanonicalLtNColumns<E>,
) {
    let n_limbs = words_to_limbs(&P256_ORDER);
    add_canonical_lt_fixed_bound(
        eval,
        CanonicalLtRelations {
            limb_range: relations.range13,
        },
        gate.clone(),
        &columns.value,
        &n_limbs,
        &columns.slack,
        &columns.carries,
    );
}

/// Prove a scalar is canonical and provide its limbs for scalar mod-mul rows.
///
/// The role determines the exact LogUp multiplicity: each `A`, `B`, and
/// `QUOTIENT` limb is consumed once for every limb on the opposite side of the
/// product, while `RESULT` limbs are consumed once by reduction digit rows.
pub fn add_canonical_scalar_limb_provider<E: EvalAtRow>(
    eval: &mut E,
    relations: CanonicalScalarLimbRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    role: ScalarModMulLimbRole,
    columns: &CanonicalLtNColumns<E>,
) {
    add_canonical_lt_n(
        eval,
        CanonicalLtNRelations {
            range13: relations.range13,
        },
        gate.clone(),
        columns,
    );

    let relation_role = role.relation_role();
    let multiplicity = role.provider_multiplicity();
    for (i, limb) in columns.value.limbs().iter().enumerate() {
        provide_scalar_limb(
            eval,
            relations.scalar_limb,
            gate.clone(),
            mul_id.clone(),
            (relation_role, i),
            limb.clone(),
            multiplicity,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_limb_roles_map_to_relation_roles_and_multiplicity() {
        assert_eq!(ScalarModMulLimbRole::A.relation_role(), ROLE_A);
        assert_eq!(ScalarModMulLimbRole::B.relation_role(), ROLE_B);
        assert_eq!(
            ScalarModMulLimbRole::Quotient.relation_role(),
            ROLE_QUOTIENT
        );
        assert_eq!(ScalarModMulLimbRole::Result.relation_role(), ROLE_RESULT);

        assert_eq!(
            ScalarModMulLimbRole::A.provider_multiplicity(),
            PRODUCT_SCALAR_LIMB_USE_COUNT
        );
        assert_eq!(
            ScalarModMulLimbRole::B.provider_multiplicity(),
            PRODUCT_SCALAR_LIMB_USE_COUNT
        );
        assert_eq!(
            ScalarModMulLimbRole::Quotient.provider_multiplicity(),
            PRODUCT_SCALAR_LIMB_USE_COUNT
        );
        assert_eq!(ScalarModMulLimbRole::Result.provider_multiplicity(), 1);
    }
}
