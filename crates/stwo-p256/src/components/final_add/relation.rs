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

/// Carries each proven fake-GLV sign bit to the final-add component.
///
/// The tuple is `(sig_id, cert_id, sign_bit)`.
/// `fake_glv_scalar` provides the relation for each active certificate.
/// `FinalAddCheckEval` consumes the relation for each finite point.
/// These bits select the correct orientation of `R_2`.
pub const FINAL_ADD_SIGN_RELATION_ARITY: usize = 3;

relation!(FinalAddSignRelation, FINAL_ADD_SIGN_RELATION_ARITY);

#[derive(Clone)]
pub struct FinalAddRelations {
    /// Shared multiplication relation for the final-add hinted rows.
    ///
    /// The source index is `hinted_source_offset + sig_id`.
    pub mul_result: ProjectiveRcbMulResultRelation,
    pub range13: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub hint: FinalCheckHintRelation,
    pub output: FinalAddOutputRelation,
    /// Per-cert proven `s2_sign_bit` (provider: `fake_glv_scalar`). Used to
    /// orient `R_2` so the bound x-coordinate is `x(h_1 + h_2)`.
    pub sign: FinalAddSignRelation,
    /// γ-digest relation + challenge (SHARED with every adopter).
    pub gamma_digest: crate::components::gamma_digest::GammaDigestRelation,
    pub gamma_challenge: crate::components::gamma_digest::GammaChallenge,
}
