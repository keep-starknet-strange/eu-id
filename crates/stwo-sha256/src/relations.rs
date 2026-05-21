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
//! Four channel families are wired into the constraint layer today:
//!   - [`SigmaDecodeRelations`] — the eight `Σ`/`σ` decode tables.
//!   - [`MajRelation`] / [`ChRelation`] — the packed Maj/Ch lookup,
//!     sharing one underlying table at width `W ≥ MAX_ROUND_GROUP_BITS`.
//!     Maj keys on `(a, b, c, maj)`; Ch keys on `(e, f, g, ch)` — two
//!     row-width-4 relations against the same `(a, b, c, maj, ch)` table
//!     content (each commits its own multiplicity column).
//!   - [`Xor8Relation`] — the single 2¹⁶-row `(x, y, z = x ⊕ y)` table,
//!     fired chunk-wise to combine the two `O2` partials of every
//!     σ-application.
//!   - [`SplitPackRelations`] — the eight split-and-pack tables (one per
//!     partition × `{lo, hi}` half) that map a 16-bit half-word to its
//!     packed-group decomposition. Round-side rows are width 4 (`key + 3
//!     packed groups`); σ-side rows are width 3 (`key + packed_s +
//!     packed_s_complement`). Firing each lookup implicitly range-checks
//!     the input limb to `[0, 2¹⁶)` and supplies the packed values the
//!     Maj/Ch and `Σ`/`σ` decode-key reconstruction read.
//!
//! The matching shared range-check channels (`Range_2`/`4`/`5`/`16`) follow
//! the same pattern and join in the shared-foundation rollout (`Range_*`
//! row content already lives in [`crate::tables_local`]).
//!
//! Each `relation!(_, N)` declares a struct holding a `LookupElements<N>`
//! channel — `N` is the row width of the matched table (number of base-field
//! values per lookup tuple). The decode tables have row shape
//! `(key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi)` ⇒ `N = 5`;
//! the Maj/Ch table projects to row shape `(a, b, c, out)` ⇒ `N = 4`; and
//! `xor_8` is `(x, y, z)` ⇒ `N = 3`. Stwo's macro implements
//! `Relation<F, EF>::combine` so `add_to_relation` can collapse a `&[F]`
//! slice of `N` cells into the extension-field key the LogUp interaction
//! column reads.

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

/// Row width of the packed Maj/Ch lookup tuples: `(a, b, c, out)`. Both
/// `MajRelation` and `ChRelation` use this width — they project the
/// underlying 5-column `(a, b, c, maj, ch)` table content into a 4-cell
/// row by exposing only one of the two outputs, with the table component
/// committing two separate multiplicity columns (one per relation).
pub const MAJ_CH_REL_SIZE: usize = 4;

relation!(MajRelation, MAJ_CH_REL_SIZE);
relation!(ChRelation, MAJ_CH_REL_SIZE);

/// Row width of the generic 8-bit XOR table: `(x, y, z)` with `z = x ⊕ y`,
/// `x, y, z ∈ [0, 256)`. Fired chunk-wise (4 lookups per σ-application) to
/// combine the two `O2` partials of every `Σ`/`σ` evaluation.
pub const XOR_8_REL_SIZE: usize = 3;

relation!(Xor8Relation, XOR_8_REL_SIZE);

/// Row width of a **round-partition** split-and-pack table: `(key,
/// packed_group_0, packed_group_1, packed_group_2)`. Three packed groups
/// because the `Σ0`/`Maj` and `Σ1`/`Ch` partitions each place exactly
/// three of their six groups in each 16-bit half (see
/// [`crate::partitions::SIGMA0_GROUPS`] / [`crate::partitions::SIGMA1_GROUPS`]).
/// `key` is the 16-bit half-word the partition's groups live in; matching
/// this row pins the half-word to `[0, 2¹⁶)` implicitly (design §11 L1).
pub const ROUND_SPLIT_PACK_REL_SIZE: usize = 4;

relation!(Sigma0SplitPackLo, ROUND_SPLIT_PACK_REL_SIZE);
relation!(Sigma0SplitPackHi, ROUND_SPLIT_PACK_REL_SIZE);
relation!(Sigma1SplitPackLo, ROUND_SPLIT_PACK_REL_SIZE);
relation!(Sigma1SplitPackHi, ROUND_SPLIT_PACK_REL_SIZE);

/// Row width of a **σ-partition** split-and-pack table: `(key,
/// packed_s, packed_s_complement)`. Each `σ` partition is just
/// `{S∩lo / S∩hi / S'∩lo / S'∩hi}` (no `Maj`/`Ch` co-service), so per
/// half the table emits one packed `S`-side value and one packed
/// `S'`-side value. The two halves' packed `S` values combine linearly
/// to the σ-decode-table key `key_s` (and analogously for `key_s'`).
pub const SIGMA_SPLIT_PACK_REL_SIZE: usize = 3;

relation!(LowerSigma0SplitPackLo, SIGMA_SPLIT_PACK_REL_SIZE);
relation!(LowerSigma0SplitPackHi, SIGMA_SPLIT_PACK_REL_SIZE);
relation!(LowerSigma1SplitPackLo, SIGMA_SPLIT_PACK_REL_SIZE);
relation!(LowerSigma1SplitPackHi, SIGMA_SPLIT_PACK_REL_SIZE);

/// All eight split-and-pack channels grouped for `Sha256Eval`. Round-side
/// channels (Σ0/Maj a-side, Σ1/Ch e-side) feed both the packed Maj/Ch
/// lookups and the `Σ` decode-key reconstruction. σ-side channels feed
/// only the σ decode-key reconstruction (`σ` partitions do not co-serve
/// Maj/Ch).
#[derive(Clone, Debug, PartialEq)]
pub struct SplitPackRelations {
    pub sigma0_lo: Sigma0SplitPackLo,
    pub sigma0_hi: Sigma0SplitPackHi,
    pub sigma1_lo: Sigma1SplitPackLo,
    pub sigma1_hi: Sigma1SplitPackHi,
    pub lower_sigma0_lo: LowerSigma0SplitPackLo,
    pub lower_sigma0_hi: LowerSigma0SplitPackHi,
    pub lower_sigma1_lo: LowerSigma1SplitPackLo,
    pub lower_sigma1_hi: LowerSigma1SplitPackHi,
}

impl SplitPackRelations {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            sigma0_lo: Sigma0SplitPackLo::draw(channel),
            sigma0_hi: Sigma0SplitPackHi::draw(channel),
            sigma1_lo: Sigma1SplitPackLo::draw(channel),
            sigma1_hi: Sigma1SplitPackHi::draw(channel),
            lower_sigma0_lo: LowerSigma0SplitPackLo::draw(channel),
            lower_sigma0_hi: LowerSigma0SplitPackHi::draw(channel),
            lower_sigma1_lo: LowerSigma1SplitPackLo::draw(channel),
            lower_sigma1_hi: LowerSigma1SplitPackHi::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            sigma0_lo: Sigma0SplitPackLo::dummy(),
            sigma0_hi: Sigma0SplitPackHi::dummy(),
            sigma1_lo: Sigma1SplitPackLo::dummy(),
            sigma1_hi: Sigma1SplitPackHi::dummy(),
            lower_sigma0_lo: LowerSigma0SplitPackLo::dummy(),
            lower_sigma0_hi: LowerSigma0SplitPackHi::dummy(),
            lower_sigma1_lo: LowerSigma1SplitPackLo::dummy(),
            lower_sigma1_hi: LowerSigma1SplitPackHi::dummy(),
        }
    }
}

impl Default for SplitPackRelations {
    fn default() -> Self {
        Self::dummy()
    }
}

/// All LogUp channels the SHA-256 AIR consumes today: the eight `Σ`/`σ`
/// decode-table channels, the packed Maj/Ch pair, the chunk-wise `xor_8`
/// channel, and the eight split-and-pack channels. Aggregated so
/// `Sha256Eval` holds a single relations bundle and the prover-side
/// `draw` walks the transcript once per component.
#[derive(Clone, Debug, PartialEq)]
pub struct Sha256Relations {
    pub sigma_decode: SigmaDecodeRelations,
    pub maj: MajRelation,
    pub ch: ChRelation,
    pub xor_8: Xor8Relation,
    pub split_pack: SplitPackRelations,
}

impl Sha256Relations {
    /// Draw fresh `LookupElements` for every channel from a transcript.
    /// The draw order is fixed — decode channels first (matching the
    /// existing 3.9.3 pattern), then Maj, then Ch, then `xor_8`, then the
    /// split-and-pack channels. Changing the order rotates the
    /// verifier-side challenges and breaks proof portability.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::draw(channel),
            maj: MajRelation::draw(channel),
            ch: ChRelation::draw(channel),
            xor_8: Xor8Relation::draw(channel),
            split_pack: SplitPackRelations::draw(channel),
        }
    }

    /// Constant-channel set for tests. Mirrors [`SigmaDecodeRelations::dummy`]
    /// so the AIR can be exercised without a real prover transcript.
    pub fn dummy() -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::dummy(),
            maj: MajRelation::dummy(),
            ch: ChRelation::dummy(),
            xor_8: Xor8Relation::dummy(),
            split_pack: SplitPackRelations::dummy(),
        }
    }
}

impl Default for Sha256Relations {
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

    #[test]
    fn maj_and_ch_relations_have_row_width_4() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        assert_eq!(
            <MajRelation as Relation<BaseField, SecureField>>::get_size(&r.maj),
            MAJ_CH_REL_SIZE
        );
        assert_eq!(
            <ChRelation as Relation<BaseField, SecureField>>::get_size(&r.ch),
            MAJ_CH_REL_SIZE
        );
        assert_eq!(MAJ_CH_REL_SIZE, 4);
    }

    #[test]
    fn xor_8_relation_has_row_width_3() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        assert_eq!(
            <Xor8Relation as Relation<BaseField, SecureField>>::get_size(&r.xor_8),
            XOR_8_REL_SIZE
        );
        assert_eq!(XOR_8_REL_SIZE, 3);
    }

    /// The four round-side split-and-pack channels expose row width 4.
    /// Cross-checked through the `Relation` trait so an off-by-one in the
    /// macro declaration would fail closed.
    #[test]
    fn round_split_pack_relations_have_row_width_4() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        for size in [
            <Sigma0SplitPackLo as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.sigma0_lo,
            ),
            <Sigma0SplitPackHi as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.sigma0_hi,
            ),
            <Sigma1SplitPackLo as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.sigma1_lo,
            ),
            <Sigma1SplitPackHi as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.sigma1_hi,
            ),
        ] {
            assert_eq!(size, ROUND_SPLIT_PACK_REL_SIZE);
        }
        assert_eq!(ROUND_SPLIT_PACK_REL_SIZE, 4);
    }

    /// The four σ-side split-and-pack channels expose row width 3.
    #[test]
    fn sigma_split_pack_relations_have_row_width_3() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        for size in [
            <LowerSigma0SplitPackLo as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.lower_sigma0_lo,
            ),
            <LowerSigma0SplitPackHi as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.lower_sigma0_hi,
            ),
            <LowerSigma1SplitPackLo as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.lower_sigma1_lo,
            ),
            <LowerSigma1SplitPackHi as Relation<BaseField, SecureField>>::get_size(
                &r.split_pack.lower_sigma1_hi,
            ),
        ] {
            assert_eq!(size, SIGMA_SPLIT_PACK_REL_SIZE);
        }
        assert_eq!(SIGMA_SPLIT_PACK_REL_SIZE, 3);
    }
}
