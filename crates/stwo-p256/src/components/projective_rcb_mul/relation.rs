//! Lookup relations shared by the hinted-mul provider and the
//! projective-source consumers.

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::range_checks::RangeCheckRelation;

/// Links hinted multiplication results to projective-source consumers.
///
/// The key is `(source_index, mul_index, role, limb_0..limb_19)`.
/// Role identifies the left operand, right operand, or result.
/// One wide tuple binds all 20 limbs.
/// The provider yields each proven value.
/// Fake-GLV and prepared-table sources consume the required values.
pub const PROJECTIVE_RCB_MUL_RESULT_RELATION_ARITY: usize = 3 + stwo_p256_utils::constants::N_LIMBS;

relation!(
    ProjectiveRcbMulResultRelation,
    PROJECTIVE_RCB_MUL_RESULT_RELATION_ARITY
);

/// The relation instances shared between the hinted-mul provider and its
/// consumers in the monolith: the wide mul-result link plus the hinted
/// component's range13 table.
#[derive(Clone, Debug)]
pub struct ProjectiveRcbMulComponentRelations {
    pub range13: RangeCheckRelation,
    pub mul_result: ProjectiveRcbMulResultRelation,
}

impl ProjectiveRcbMulComponentRelations {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range13: RangeCheckRelation::draw(channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            range13: RangeCheckRelation::dummy(),
            mul_result: ProjectiveRcbMulResultRelation::dummy(),
        }
    }
}
