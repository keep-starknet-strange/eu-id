//! LogUp relation declarations and the relations bundle for the FinalAdd AIR.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo_constraint_framework::relation;
use stwo_p256_utils::constants::N_LIMBS;

use crate::prepared_table::FinalCheckHintRelation;
use crate::projective_air::ProjectiveRcbMulResultRelation;
use crate::range_checks::RangeCheckRelation;

/// `(sig_id, cert_id, point[PREPARED_TABLE_EC_POINT_COLUMNS])` — re-exported
/// arity for the hint consumer.
pub use crate::prepared_table::FINAL_CHECK_HINT_RELATION_ARITY;

/// Output relation: the proven `(sig_id, x3[N_LIMBS])` forwarded to the final
/// check, which consumes it as `r_x`.
pub const FINAL_ADD_OUTPUT_RELATION_ARITY: usize = 1 + N_LIMBS;

relation!(FinalAddOutputRelation, FINAL_ADD_OUTPUT_RELATION_ARITY);

#[derive(Clone)]
pub struct FinalAddRelations {
    /// SHARED with the hinted-mul provider: final-add's four muls are proven
    /// as hinted rows (source_index = hinted_source_offset + sig_id), and the
    /// check consumes them through the same wide
    /// `(source_index, mul_index, role, limb_0..limb_19)` relation instance.
    pub mul_result: ProjectiveRcbMulResultRelation,
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub hint: FinalCheckHintRelation,
    pub output: FinalAddOutputRelation,
    /// γ-digest relation + challenge (SHARED with every adopter).
    pub gamma_digest: crate::components::gamma_digest::GammaDigestRelation,
    pub gamma_challenge: crate::components::gamma_digest::GammaChallenge,
}
