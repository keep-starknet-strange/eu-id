use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use crate::limbs::P256EvalBigInt;
use crate::range_checks::RangeCheckRelation;

use super::super::canonical_lt::{add_canonical_lt_fixed_bound, CanonicalLtRelations};
use super::{provide_scalar_value, ScalarValueRelation};

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
    /// Provider side of the keyed canonical scalar relation.
    pub scalar_value: &'a ScalarValueRelation,
}

/// Prove `value < n` and provide the keyed canonical scalar value.
///
/// The provided key is `(mul_id, role, value limbs...)`. Soundness of a full
/// multiplication instance requires the product/reduction helpers to consume
/// the same `mul_id` and role exactly once.
pub fn add_canonical_lt_n_provider<E: EvalAtRow>(
    eval: &mut E,
    relations: CanonicalLtNRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    role: u32,
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
    provide_scalar_value(
        eval,
        relations.scalar_value,
        gate,
        mul_id,
        role,
        &columns.value,
    );
}
