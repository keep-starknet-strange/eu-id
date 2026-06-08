//! LogUp relation declarations and the relations bundle for the FinalAdd AIR.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo_constraint_framework::relation;
use stwo_p256_utils::constants::N_LIMBS;

use crate::prepared_table::FinalCheckHintRelation;
use crate::projective_air::ProjectiveRcbMulComponentRelations;

/// `(sig_id, cert_id, point[PREPARED_TABLE_EC_POINT_COLUMNS])` — re-exported
/// arity for the hint consumer.
pub use crate::prepared_table::FINAL_CHECK_HINT_RELATION_ARITY;

/// Output relation: the proven `(sig_id, x3[N_LIMBS])` forwarded to the final
/// check, which consumes it as `r_x`.
pub const FINAL_ADD_OUTPUT_RELATION_ARITY: usize = 1 + N_LIMBS;

relation!(FinalAddOutputRelation, FINAL_ADD_OUTPUT_RELATION_ARITY);

/// Result relation linking the mul provider to the check consumer:
/// `(mul_index, role, limb_index, limb)`.
pub const FINAL_ADD_MUL_RESULT_ARITY: usize = 4;

relation!(FinalAddMulResultRelation, FINAL_ADD_MUL_RESULT_ARITY);

#[derive(Clone)]
pub struct FinalAddRelations {
    pub mul: ProjectiveRcbMulComponentRelations,
    pub result: FinalAddMulResultRelation,
    pub hint: FinalCheckHintRelation,
    pub output: FinalAddOutputRelation,
}
