//! Lookup relations shared by the hinted-mul provider and the
//! projective-source consumers.

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::range_checks::RangeCheckRelation;

/// Result relation linking the hinted-mul provider to the projective-source
/// consumers (C5 plumbing): keyed `(source_index, mul_index, role,
/// limb_0..limb_19)` where `role ∈ {LHS, RHS, RESULT}` — one WIDE tuple per
/// proven value instead of one per limb (both sides hold all 20 limbs in a
/// single row, and the wide random-α combine carries identical binding power
/// at 1/20th the interaction columns). The provider YIELDS every proven
/// `fp_mul`'s `lhs`/`rhs`/`result`; the fake-GLV and prepared-table projective
/// sources CONSUME the muls of the EC op on their row.
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
