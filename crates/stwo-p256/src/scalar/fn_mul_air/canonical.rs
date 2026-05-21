use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::scalar_arithmetic::{words_to_limbs, P256_ORDER};

use crate::limbs::P256EvalBigInt;
use crate::range_checks::RangeCheckRelation;

use super::super::canonical_lt::{add_canonical_lt_fixed_bound, CanonicalLtRelations};
use super::{provide_scalar_value, ScalarValueRelation};

pub struct CanonicalLtNColumns<E: EvalAtRow> {
    pub value: P256EvalBigInt<E>,
    pub slack: P256EvalBigInt<E>,
    pub carries: [E::F; stwo_p256_utils::constants::N_LIMBS],
}

#[derive(Clone, Copy)]
pub struct CanonicalLtNRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub scalar_value: &'a ScalarValueRelation,
}

/// Prove `value < n` and provide the keyed canonical scalar value.
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
