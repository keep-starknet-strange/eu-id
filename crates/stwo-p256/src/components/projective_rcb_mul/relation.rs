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

/// Result relation linking the hinted-mul provider to the projective-source
/// consumers (C5 plumbing): keyed `(source_index, mul_index, role,
/// limb_0..limb_19)` where `role ∈ {LHS, RHS, RESULT}` — one WIDE tuple per
/// proven value instead of one per limb (both sides hold all 20 limbs in a
/// single row, and the wide random-α combine carries identical binding power
/// at 1/20th the interaction columns). The provider YIELDS every proven
/// `fp_mul`'s `lhs`/`rhs`/`result`; the fake-GLV and prepared-table projective
/// sources CONSUME the muls of the EC op on their row.
pub const PROJECTIVE_RCB_MUL_RESULT_RELATION_ARITY: usize =
    3 + stwo_p256_utils::constants::N_LIMBS;

relation!(
    ProjectiveRcbMulLimbRelation,
    PROJECTIVE_RCB_MUL_LIMB_RELATION_ARITY
);

relation!(
    ProjectiveRcbMulResultRelation,
    PROJECTIVE_RCB_MUL_RESULT_RELATION_ARITY
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
    pub raw_product_carry16: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub mul_limb: ProjectiveRcbMulLimbRelation,
    pub mul_result: ProjectiveRcbMulResultRelation,
    pub raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: ProjectiveRcbFoldedCarryRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range13: RangeCheckRelation::draw(channel),
            raw_product_carry16: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            mul_limb: ProjectiveRcbMulLimbRelation::draw(channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(channel),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::draw(channel),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::draw(channel),
            folded_digit: ProjectiveRcbFoldedDigitRelation::draw(channel),
            folded_carry: ProjectiveRcbFoldedCarryRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            raw_product_carry16: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            mul_limb: ProjectiveRcbMulLimbRelation::dummy(),
            mul_result: ProjectiveRcbMulResultRelation::dummy(),
            raw_product_chunk_digit: ProjectiveRcbRawProductChunkDigitRelation::dummy(),
            folded_contribution: ProjectiveRcbFoldedContributionRelation::dummy(),
            folded_digit: ProjectiveRcbFoldedDigitRelation::dummy(),
            folded_carry: ProjectiveRcbFoldedCarryRelation::dummy(),
        }
    }

    pub fn as_refs(&self) -> ProjectiveRcbMulRelations<'_> {
        ProjectiveRcbMulRelations {
            range13: &self.range13,
            raw_product_carry16: &self.raw_product_carry16,
            signed_carry: &self.signed_carry,
            mul_limb: &self.mul_limb,
            mul_result: &self.mul_result,
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
    pub raw_product_carry16: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    pub mul_limb: &'a ProjectiveRcbMulLimbRelation,
    pub mul_result: &'a ProjectiveRcbMulResultRelation,
    pub raw_product_chunk_digit: &'a ProjectiveRcbRawProductChunkDigitRelation,
    pub folded_contribution: &'a ProjectiveRcbFoldedContributionRelation,
    pub folded_digit: &'a ProjectiveRcbFoldedDigitRelation,
    pub folded_carry: &'a ProjectiveRcbFoldedCarryRelation,
}
