use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::range_checks::RangeCheckRelation;

relation!(ScalarLimbRelation, 4);
relation!(ScalarProductChunkDigitRelation, 6);
relation!(ScalarProductDigitRelation, 4);
relation!(ScalarReductionCarryRelation, 3);

/// Relation key shape: `(mul_id, role, limb_index, limb_value)`.
pub const SCALAR_LIMB_RELATION_ARITY: usize = 4;
/// Relation key shape: `(mul_id, side, coeff, chunk, digit_offset, digit_value)`.
pub const PRODUCT_CHUNK_DIGIT_RELATION_ARITY: usize = 6;
/// Relation key shape: `(mul_id, side, digit_index, digit_value)`.
pub const PRODUCT_DIGIT_RELATION_ARITY: usize = 4;
/// Relation key shape: `(mul_id, digit_index, carry_value)`.
pub const REDUCTION_CARRY_RELATION_ARITY: usize = 3;

#[derive(Clone)]
pub struct ScalarModMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub scalar_limb: ScalarLimbRelation,
    pub product_chunk_digit: ScalarProductChunkDigitRelation,
    pub product_digit: ScalarProductDigitRelation,
    pub reduction_carry: ScalarReductionCarryRelation,
}

#[derive(Clone)]
pub(crate) struct ScalarModMulLookupRelations {
    pub(crate) range13: RangeCheckRelation,
    pub(crate) signed_carry: RangeCheckRelation,
    pub(crate) scalar_limb: ScalarLimbRelation,
    pub(crate) product_chunk_digit: ScalarProductChunkDigitRelation,
    pub(crate) product_digit: ScalarProductDigitRelation,
    pub(crate) reduction_carry: ScalarReductionCarryRelation,
}

impl ScalarModMulLookupRelations {
    pub(crate) fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range13: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            scalar_limb: ScalarLimbRelation::draw(channel),
            product_chunk_digit: ScalarProductChunkDigitRelation::draw(channel),
            product_digit: ScalarProductDigitRelation::draw(channel),
            reduction_carry: ScalarReductionCarryRelation::draw(channel),
        }
    }

    pub(crate) fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            scalar_limb: ScalarLimbRelation::dummy(),
            product_chunk_digit: ScalarProductChunkDigitRelation::dummy(),
            product_digit: ScalarProductDigitRelation::dummy(),
            reduction_carry: ScalarReductionCarryRelation::dummy(),
        }
    }

    pub(crate) fn scalar_mod_mul(&self) -> ScalarModMulComponentRelations {
        ScalarModMulComponentRelations {
            range13: self.range13.clone(),
            signed_carry: self.signed_carry.clone(),
            scalar_limb: self.scalar_limb.clone(),
            product_chunk_digit: self.product_chunk_digit.clone(),
            product_digit: self.product_digit.clone(),
            reduction_carry: self.reduction_carry.clone(),
        }
    }
}
