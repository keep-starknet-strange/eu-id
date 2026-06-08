//! Lookup relations for the projective RCB multiplication AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::range_checks::RangeCheckRelation;

pub const PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY: usize = 5;

pub const PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY: usize = 6;

pub const PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY: usize = 5;

pub const PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY: usize = 4;

pub const PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY: usize = 4;

relation!(
    ProjectiveRcbMulLimbRelation,
    PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY
);

relation!(
    ProjectiveRcbRawProductChunkDigitRelation,
    PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_DIGIT_RELATION_ARITY
);

relation!(
    ProjectiveRcbFoldedContributionRelation,
    PROJECTIVE_RCB_FOLDED_CONTRIBUTION_RELATION_ARITY
);

relation!(
    ProjectiveRcbFoldedDigitRelation,
    PROJECTIVE_RCB_FOLDED_DIGIT_RELATION_ARITY
);

relation!(
    ProjectiveRcbFoldedCarryRelation,
    PROJECTIVE_RCB_FOLDED_CARRY_RELATION_ARITY
);

#[derive(Clone, Debug)]
pub struct ProjectiveRcbMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub mul_limb: ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: ProjectiveRcbFoldedCarryRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range13: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            mul_limb: ProjectiveRcbMulLimbRelation::draw(channel),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::draw(channel),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::draw(channel),
            folded_digit: ProjectiveRcbFoldedDigitRelation::draw(channel),
            folded_carry: ProjectiveRcbFoldedCarryRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            mul_limb: ProjectiveRcbMulLimbRelation::dummy(),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::dummy(),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::dummy(),
            folded_digit: ProjectiveRcbFoldedDigitRelation::dummy(),
            folded_carry: ProjectiveRcbFoldedCarryRelation::dummy(),
        }
    }

    pub fn as_refs(&self) -> ProjectiveRcbMulRelations<'_> {
        ProjectiveRcbMulRelations {
            range13: &self.range13,
            signed_carry: &self.signed_carry,
            mul_limb: &self.mul_limb,
            raw_product_chunk_digit: &self.raw_product_chunk_digit,
            folded_contribution: &self.folded_contribution,
            folded_digit: &self.folded_digit,
            folded_carry: &self.folded_carry,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ProjectiveRcbMulRelations<'a> {
    pub range13: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    pub mul_limb: &'a ProjectiveRcbMulLimbRelation,
    pub raw_product_chunk_digit: &'a ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: &'a ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: &'a ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: &'a ProjectiveRcbFoldedCarryRelation,
}
