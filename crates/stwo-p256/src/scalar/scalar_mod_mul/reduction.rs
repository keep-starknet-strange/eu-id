use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::PRODUCT_EQUATION_LIMBS;

use crate::range_checks::{add_range_check, RangeCheckRelation};

use super::{
    consume_product_digit, consume_reduction_carry, consume_scalar_limb, provide_reduction_carry,
    ScalarLimbRelation, ScalarProductDigitRelation, ScalarReductionCarryRelation, ROLE_RESULT,
    SIDE_AB, SIDE_QN,
};

pub const SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS: usize = 5;

pub struct ScalarReductionDigitColumns<E: EvalAtRow> {
    pub ab_digit: E::F,
    pub qn_digit: E::F,
    pub result_limb: E::F,
    pub prev_carry: E::F,
    pub carry: E::F,
}

#[derive(Clone, Copy)]
pub struct ScalarReductionDigitRelations<'a> {
    /// Signed carry table configured with `SCALAR_MOD_MUL_SPLIT_CARRY_BOUND`.
    pub signed_carry: &'a RangeCheckRelation,
    /// Links canonical result limbs to reduction rows.
    pub scalar_limb: &'a ScalarLimbRelation,
    /// Links product digit accumulators to reduction rows.
    pub product_digit: &'a ScalarProductDigitRelation,
    /// Links each carry to the next reduction digit row.
    pub reduction_carry: &'a ScalarReductionCarryRelation,
}

/// Prove one digit of `A * B - Q * n - result = 0`.
///
/// Carry continuity is enforced through `reduction_carry`: row `i` provides
/// `carry_i`, and row `i + 1` consumes it as `prev_carry`. The first row fixes
/// `prev_carry = 0`; the last row fixes `carry_39 = 0`.
pub fn add_scalar_reduction_digit<E: EvalAtRow>(
    eval: &mut E,
    relations: ScalarReductionDigitRelations<'_>,
    gate: E::F,
    mul_id: E::F,
    digit_index: usize,
    columns: &ScalarReductionDigitColumns<E>,
) {
    assert!(
        digit_index < PRODUCT_EQUATION_LIMBS,
        "reduction digit index {digit_index} outside 0..{PRODUCT_EQUATION_LIMBS}",
    );

    consume_product_digit(
        eval,
        relations.product_digit,
        gate.clone(),
        mul_id.clone(),
        SIDE_AB,
        digit_index,
        columns.ab_digit.clone(),
    );
    consume_product_digit(
        eval,
        relations.product_digit,
        gate.clone(),
        mul_id.clone(),
        SIDE_QN,
        digit_index,
        columns.qn_digit.clone(),
    );

    if digit_index < N_LIMBS {
        consume_scalar_limb(
            eval,
            relations.scalar_limb,
            gate.clone(),
            mul_id.clone(),
            ROLE_RESULT,
            digit_index,
            columns.result_limb.clone(),
        );
    } else {
        eval.add_constraint(gate.clone() * columns.result_limb.clone());
    }

    if digit_index == 0 {
        eval.add_constraint(gate.clone() * columns.prev_carry.clone());
    } else {
        consume_reduction_carry(
            eval,
            relations.reduction_carry,
            gate.clone(),
            mul_id.clone(),
            digit_index - 1,
            columns.prev_carry.clone(),
        );
    }

    add_range_check(
        eval,
        relations.signed_carry,
        gate.clone(),
        columns.carry.clone(),
    );

    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let recurrence =
        columns.ab_digit.clone() - columns.qn_digit.clone() - columns.result_limb.clone()
            + columns.prev_carry.clone()
            - limb_base * columns.carry.clone();
    eval.add_constraint(gate.clone() * recurrence);

    if digit_index + 1 == PRODUCT_EQUATION_LIMBS {
        eval.add_constraint(gate * columns.carry.clone());
    } else {
        provide_reduction_carry(
            eval,
            relations.reduction_carry,
            gate,
            mul_id,
            digit_index,
            columns.carry.clone(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduction_digit_row_is_narrow() {
        assert_eq!(SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS, 5);
    }

    #[test]
    fn reduction_digit_count_matches_product_width() {
        assert_eq!(PRODUCT_EQUATION_LIMBS, 2 * N_LIMBS);
    }
}
