//! LogUp relation declarations and the pinning-relations bundle for the
//! prepared-table AIR family.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change). Relation tuple
//! arities and canonical-role constants remain in `mod.rs` (cross-cutting across
//! air/trace/interaction) and reach the `relation!` macros below via `super::*`.

use stwo_constraint_framework::relation;

use super::*;

relation!(
    PreparedTableEcRowRelation,
    PREPARED_TABLE_EC_ROW_RELATION_ARITY
);

// --- Prepared-table point relations ----------------------------------------
//
// `CertBaseRelation` binds each table base point to the proven certificate base.
// Certificate 0 uses G, and certificate 1 uses public key Q.
relation!(CertBaseRelation, CERT_BASE_RELATION_ARITY);

// `PreparedTableCanonicalRelation` ties every other prepared-table operand
// (`P3 = 3P`, `R`, `R3 = 3R`, `-R`, `-R3`, `2P`, `2R`) to a single canonical
// per-(sig,cert,role) value. Both providers and consumers are prepared-table
// rows (self-balancing within `PreparedTableEcRowEval`), except cert0's `P3`
// which is provided as the fixed constant `3·G`.
relation!(
    PreparedTableCanonicalRelation,
    PREPARED_TABLE_CANONICAL_RELATION_ARITY
);

// `FinalCheckHintRelation` forwards the proven signed hint point `R_i`.
// The fake-GLV sign bit selects `R_i = -h_i` or `R_i = +h_i`.
// Prepared-table rows provide two copies of each active `R_i` tuple.
// Final-add and curve-membership components each consume one copy.
relation!(FinalCheckHintRelation, FINAL_CHECK_HINT_RELATION_ARITY);

/// Relations the `PreparedTableEcRowEval` provider consumes/provides to pin the
/// prepared table to the certificate base point.
///
/// The monolithic STARK uses `Some` because `cert_bind` provides `CertBaseRelation`.
/// The standalone slice uses `None` and emits only `PreparedTableEcRowRelation`.
///
/// The AIR negation requires 13-bit `neg` and `src` limbs.
/// The canonical relation binds these values to range-checked projective operands.
/// Thus, this component does not need another range lookup.
#[derive(Clone)]
pub struct PreparedTablePinningRelations {
    pub cert_base: CertBaseRelation,
    pub canonical: PreparedTableCanonicalRelation,
    /// Forwards the pinned signed hint `R_i` (the `DoubleR` row's `lhs`) to the
    /// FinalEcdsaCheck component. `None` for paths that do not consume it.
    pub final_check_hint: Option<FinalCheckHintRelation>,
}
