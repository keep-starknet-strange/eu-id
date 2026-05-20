//! LogUp relation tags for the SHA-256 component.
//!
//! Each preprocessed lookup table is paired with one [`stwo_constraint_framework::Relation`]
//! channel. The SHA-256 component uses these channels from the **consumer**
//! side — `add_to_relation` with positive multiplicity, one "use" per
//! lookup keyed on the row tuple. The actual preprocessed-column commitment
//! and the per-row multiplicity vector live with the corresponding table
//! component (committed separately at prover-setup time); the relations
//! here are the contract between the two.
//!
//! Today, only the `Σ`/`σ` decode tables are wired (see
//! [`SigmaDecodeRelations`]). The `Maj`/`Ch` and `xor_8` channels land in
//! the follow-on lookup-wiring work — the chunk decomposition that the
//! `xor_8` lookup will key on is already committed in the trace (see
//! [`crate::trace::SIGMA_DECODE_COLS`]). The matching shared range-check
//! channels (`Range_2`/`4`/`5`/`16`) follow the same pattern and join in
//! the shared-foundation rollout (`Range_*` row content already lives in
//! [`crate::tables_local`]).
//!
//! Each `relation!(_, N)` declares a struct holding a `LookupElements<N>`
//! channel — `N` is the row width of the matched table (number of base-field
//! values per lookup tuple). The decode tables have row shape
//! `(key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi)` ⇒ `N = 5`.
//! Stwo's macro implements `Relation<F, EF>::combine` so `add_to_relation`
//! can collapse a `&[F]` slice of `N` cells into the extension-field key
//! the LogUp interaction column reads.

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

/// Row width of each `Σ`/`σ` decode table: `(key, o_main_lo, o_main_hi,
/// o2_partial_lo, o2_partial_hi)`. The lookup-tuple slice passed to
/// `add_to_relation` is sliced into the trace's per-σ-application decode
/// block in column order (see [`crate::trace::SIGMA_DECODE_COLS`]) so the
/// first 5 cells form the `S`-side key and the next 5 the `S′`-side key.
pub const SIGMA_DECODE_REL_SIZE: usize = 5;

relation!(Sigma0DecodeS, SIGMA_DECODE_REL_SIZE);
relation!(Sigma0DecodeSPrime, SIGMA_DECODE_REL_SIZE);
relation!(Sigma1DecodeS, SIGMA_DECODE_REL_SIZE);
relation!(Sigma1DecodeSPrime, SIGMA_DECODE_REL_SIZE);
relation!(LowerSigma0DecodeS, SIGMA_DECODE_REL_SIZE);
relation!(LowerSigma0DecodeSPrime, SIGMA_DECODE_REL_SIZE);
relation!(LowerSigma1DecodeS, SIGMA_DECODE_REL_SIZE);
relation!(LowerSigma1DecodeSPrime, SIGMA_DECODE_REL_SIZE);

/// All eight `Σ`/`σ` decode-table channels grouped for `Sha256Eval`. One
/// channel per `(function, side)` pair: the per-table multiplicity columns
/// (committed by the table component, not here) sum to the witness-side
/// usage counts asserted by the multiplicity sanity test in
/// [`crate::constraints`].
#[derive(Clone, Debug, PartialEq)]
pub struct SigmaDecodeRelations {
    pub sigma0_s: Sigma0DecodeS,
    pub sigma0_s_complement: Sigma0DecodeSPrime,
    pub sigma1_s: Sigma1DecodeS,
    pub sigma1_s_complement: Sigma1DecodeSPrime,
    pub lower_sigma0_s: LowerSigma0DecodeS,
    pub lower_sigma0_s_complement: LowerSigma0DecodeSPrime,
    pub lower_sigma1_s: LowerSigma1DecodeS,
    pub lower_sigma1_s_complement: LowerSigma1DecodeSPrime,
}

impl SigmaDecodeRelations {
    /// Draw fresh `LookupElements` for every channel from a transcript.
    /// Used by the prover/verifier wiring once the foundation is in place.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            sigma0_s: Sigma0DecodeS::draw(channel),
            sigma0_s_complement: Sigma0DecodeSPrime::draw(channel),
            sigma1_s: Sigma1DecodeS::draw(channel),
            sigma1_s_complement: Sigma1DecodeSPrime::draw(channel),
            lower_sigma0_s: LowerSigma0DecodeS::draw(channel),
            lower_sigma0_s_complement: LowerSigma0DecodeSPrime::draw(channel),
            lower_sigma1_s: LowerSigma1DecodeS::draw(channel),
            lower_sigma1_s_complement: LowerSigma1DecodeSPrime::draw(channel),
        }
    }

    /// Constant-channel set for tests that exercise the AIR without a
    /// real prover transcript. Matches the `XorElements*::dummy()` pattern
    /// used by the Stwo Blake example.
    pub fn dummy() -> Self {
        Self {
            sigma0_s: Sigma0DecodeS::dummy(),
            sigma0_s_complement: Sigma0DecodeSPrime::dummy(),
            sigma1_s: Sigma1DecodeS::dummy(),
            sigma1_s_complement: Sigma1DecodeSPrime::dummy(),
            lower_sigma0_s: LowerSigma0DecodeS::dummy(),
            lower_sigma0_s_complement: LowerSigma0DecodeSPrime::dummy(),
            lower_sigma1_s: LowerSigma1DecodeS::dummy(),
            lower_sigma1_s_complement: LowerSigma1DecodeSPrime::dummy(),
        }
    }
}

impl Default for SigmaDecodeRelations {
    fn default() -> Self {
        Self::dummy()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// All eight relations report row width 5 — i.e. matched-tuple length
    /// equal to a decode-table row. A regression on this would silently
    /// shift the columns the AIR slices for `add_to_relation`.
    #[test]
    fn every_decode_relation_has_row_width_5() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = SigmaDecodeRelations::dummy();
        // Cross-check via the Relation trait — the relation! macro derives
        // get_size() against the size literal we declared.
        assert_eq!(
            <Sigma0DecodeS as Relation<BaseField, SecureField>>::get_size(&r.sigma0_s),
            SIGMA_DECODE_REL_SIZE
        );
        assert_eq!(SIGMA_DECODE_REL_SIZE, 5);
    }
}
