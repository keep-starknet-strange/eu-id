use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::scalar_arithmetic::PRODUCT_EQUATION_LIMBS;

use crate::limbs::P256EvalBigInt;
use crate::range_checks::{add_range_check, RangeCheckRelation};

use super::{
    consume_product_digit, consume_scalar_value, FnMulLinkRelations, ROLE_RESULT, SIDE_AB, SIDE_QN,
};

/// Reduction row for `A * B - Q * n - result = 0`.
///
/// Product digits are consumed through LogUp rather than recomputed locally.
/// This keeps the row narrow relative to the product helper and makes the
/// copy boundary explicit.
pub struct ScalarReductionColumns<E: EvalAtRow> {
    /// Canonical result scalar consumed under role `RESULT`.
    pub result: P256EvalBigInt<E>,
    /// Product digits consumed from the `A * B` side.
    pub ab_digits: [E::F; PRODUCT_EQUATION_LIMBS],
    /// Product digits consumed from the `Q * n` side.
    pub qn_digits: [E::F; PRODUCT_EQUATION_LIMBS],
    /// Signed carry chain for the normalized product equation.
    pub carries: [E::F; PRODUCT_EQUATION_LIMBS],
}

#[derive(Clone, Copy)]
pub struct ScalarReductionRelations<'a> {
    /// Signed carry table configured with `FNMUL_SPLIT_CARRY_BOUND`.
    pub signed_carry: &'a RangeCheckRelation,
    /// LogUp links to canonical scalar providers and product digit providers.
    pub links: FnMulLinkRelations<'a>,
}

/// Consume product digits and prove `AB - QN - result = 0` with signed carries.
///
/// The final carry is constrained to zero, so the recurrence proves integer
/// equality over the full 40-limb product width, not only equality modulo
/// `B^40`.
pub fn add_scalar_reduction_consumer<E: EvalAtRow>(
    eval: &mut E,
    relations: ScalarReductionRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    columns: &ScalarReductionColumns<E>,
) {
    consume_scalar_value(
        eval,
        relations.links.scalar_value,
        gate.clone(),
        mul_id.clone(),
        ROLE_RESULT,
        &columns.result,
    );

    let zero = E::F::from(M31::from_u32_unchecked(0));
    let limb_base = E::F::from(M31::from_u32_unchecked(
        1u32 << stwo_p256_utils::constants::LIMB_BITS,
    ));

    for i in 0..PRODUCT_EQUATION_LIMBS {
        consume_product_digit(
            eval,
            relations.links.product_digit,
            gate.clone(),
            mul_id.clone(),
            SIDE_AB,
            i,
            columns.ab_digits[i].clone(),
        );
        consume_product_digit(
            eval,
            relations.links.product_digit,
            gate.clone(),
            mul_id.clone(),
            SIDE_QN,
            i,
            columns.qn_digits[i].clone(),
        );
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
        let recurrence = columns.ab_digits[i].clone()
            - columns.qn_digits[i].clone()
            - result_limb::<E>(&columns.result, i)
            + prev_carry
            - limb_base.clone() * columns.carries[i].clone();
        eval.add_constraint(gate.clone() * recurrence);
    }

    eval.add_constraint(gate * columns.carries[PRODUCT_EQUATION_LIMBS - 1].clone());
}

fn result_limb<E: EvalAtRow>(result: &P256EvalBigInt<E>, index: usize) -> E::F {
    result
        .limbs()
        .get(index)
        .cloned()
        .unwrap_or_else(|| E::F::from(M31::from_u32_unchecked(0)))
}
