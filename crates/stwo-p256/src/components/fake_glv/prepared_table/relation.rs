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

// --- PreparedTablePoints pinning relations (full table-pinning, Phase 2) ---
//
// `CertBaseRelation` binds every prepared-table cell that must equal the cert
// base point `P` (= G for cert0, = public key Q for cert1) to the in-AIR
// `cert.base` proven in `cert_bind.rs`. Provider: `CertScalarInputAirEval`
// (yield `-m(cert_id)`). Consumer: `PreparedTableEcRowEval` (use `+1` per P-cell).
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

// `FinalCheckHintRelation` forwards the in-AIR-pinned signed hint point `R_i`
// (= `±h_i`, where the sign is the per-cert `s2_sign_bit` from the Garaga
// decomposition: `R_i = -h_i` when the bit is 1, `R_i = +h_i` when it is 0 —
// both occur for honest signatures) from the prepared table to the
// FinalEcdsaCheck / FinalAdd components.
// Provider: `PreparedTableEcRowEval` yields `R_i` (= the `DoubleR` row's `lhs`,
// which role-`R` pinning already binds to the canonical per-cert value) once per
// active `DoubleR` row, gated `active * DoubleR_flag`, multiplicity `-1`.
// Consumer: `FinalEcdsaCheck` uses `R_1` at `(sig, 0)` and `R_2` at `(sig, 1)`.
relation!(FinalCheckHintRelation, FINAL_CHECK_HINT_RELATION_ARITY);

/// Relations the `PreparedTableEcRowEval` provider consumes/provides to pin the
/// prepared table to the cert base point. `Some` in the monolithic STARK (where
/// `cert_bind` provides `CertBaseRelation`); `None` for the legacy standalone
/// slice, which emits only `PreparedTableEcRowRelation`.
///
/// The in-AIR negation (`neg.y + src.y = p`) needs `neg`/`src` limbs bounded to
/// 13 bits; that bound is inherited transitively — the canonical relation ties
/// each `neg`/`src` to a base-row operand which feeds the projective EC-add,
/// where every affine limb is already `Range13`-checked. So no extra range
/// lookup is consumed here.
#[derive(Clone)]
pub struct PreparedTablePinningRelations {
    pub cert_base: CertBaseRelation,
    pub canonical: PreparedTableCanonicalRelation,
    /// Forwards the pinned signed hint `R_i` (the `DoubleR` row's `lhs`) to the
    /// FinalEcdsaCheck component. `None` for paths that do not consume it.
    pub final_check_hint: Option<FinalCheckHintRelation>,
}
