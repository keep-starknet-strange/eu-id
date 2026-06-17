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
//! Five channel families are wired into the constraint layer:
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
//!     packed-group decomposition. Round-side rows are width 5 (`key + 4
//!     packed groups`, the four W=6 sub-groups in that half); σ-side rows
//!     are width 3 (`key + packed_s + packed_s_complement`). Firing each
//!     lookup implicitly range-checks
//!     the input limb to `[0, 2¹⁶)` and supplies the packed values the
//!     Maj/Ch and `Σ`/`σ` decode-key reconstruction read.
//!   - [`RangeRelations`] — the four width-1 range-check channels
//!     `Range_2`/`Range_4`/`Range_5`/`Range_16`. `Range_k` pins a single
//!     base-field value into `[0, k)`. The mod-2³² limb-add carries are
//!     range-checked through `Range_{2,4,5}` per the headroom audit
//!     (`crate::headroom`); terminal 16-bit limbs (the final block's
//!     `h_out`, per design §10.2) are range-checked through `Range_16`.
//!     Row content for each `Range_k` is the table `crate::tables_local::range_k()`.
//!
//! Each `relation!(_, N)` declares a struct holding a `LookupElements<N>`
//! channel — `N` is the row width of the matched table (number of base-field
//! values per lookup tuple). The decode tables have row shape
//! `(key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi)` ⇒ `N = 5`;
//! the Maj/Ch table projects to row shape `(a, b, c, out)` ⇒ `N = 4`;
//! `xor_8` is `(x, y, z)` ⇒ `N = 3`; the range channels are `(value)` ⇒
//! `N = 1`. Stwo's macro implements `Relation<F, EF>::combine` so
//! `add_to_relation` can collapse a `&[F]` slice of `N` cells into the
//! extension-field key the LogUp interaction column reads.

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
/// packed_group_0, …, packed_group_3)`. Four packed groups because the
/// `W = 6` `Σ0`/`Maj` and `Σ1`/`Ch` partitions each place exactly four of
/// their eight groups in each 16-bit half (see
/// [`crate::partitions::SIGMA0_GROUPS`] / [`crate::partitions::SIGMA1_GROUPS`]
/// and [`crate::partitions::round_groups_half_indices`]).
/// `key` is the 16-bit half-word the partition's groups live in; matching
/// this row pins the half-word to `[0, 2¹⁶)` implicitly (design §11 L1).
pub const ROUND_SPLIT_PACK_REL_SIZE: usize = 5;

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

/// Row width of every `Range_k` channel: a single base-field value pinned
/// to `[0, k)`. The lookup tuple passed to `add_to_relation` is a 1-cell
/// slice — the carry limb (for mod-2³² adds) or the terminal 16-bit limb
/// (for `Range_16` on `h_out`).
pub const RANGE_REL_SIZE: usize = 1;

relation!(Range2Relation, RANGE_REL_SIZE);
relation!(Range4Relation, RANGE_REL_SIZE);
relation!(Range5Relation, RANGE_REL_SIZE);
relation!(Range16Relation, RANGE_REL_SIZE);

/// The four range-check channels grouped for `Sha256Eval`.
///
/// - `range_2` / `range_4` / `range_5` pin the `(carry_lo, carry_hi)`
///   pair of each mod-2³² limb-add (per the headroom audit's family
///   bound: `k=4` for the schedule recurrence, `k=5` for `T1`, `k=2`
///   everywhere else).
/// - `range_16` pins terminal 16-bit limbs that are not transitively
///   pinned by a downstream split-and-pack / σ-decode lookup — most
///   importantly the final block's `h_out` digest limbs.
///
/// Each channel produces one preprocessed-column row per value and has its
/// own multiplicity column committed by the matching producer component.
#[derive(Clone, Debug, PartialEq)]
pub struct RangeRelations {
    pub range_2: Range2Relation,
    pub range_4: Range4Relation,
    pub range_5: Range5Relation,
    pub range_16: Range16Relation,
}

impl RangeRelations {
    /// Draw one challenge per `Range_k` channel in the canonical
    /// `crate::components::RANGE_TABLES` order.
    ///
    /// **Mn3 — single source of truth.** Both the preprocessed-trace
    /// generator (`crate::preprocessed`), the multiplicity assembly
    /// (`crate::multiplicities` / `crate::interaction`), and this
    /// challenge-draw side iterate the same `RANGE_TABLES` slice, so a
    /// future refactor that reorders the canonical list automatically
    /// keeps the consumer ⇄ producer LogUp balance intact. A drift
    /// between the two used to be a hidden coupling — `draw` now
    /// re-derives its order from `RANGE_TABLES` directly.
    pub fn draw(channel: &mut impl Channel) -> Self {
        use crate::components::{RangeKind, RANGE_TABLES};
        let mut out = Self::dummy();
        for &kind in RANGE_TABLES {
            match kind {
                RangeKind::Range2 => out.range_2 = Range2Relation::draw(channel),
                RangeKind::Range4 => out.range_4 = Range4Relation::draw(channel),
                RangeKind::Range5 => out.range_5 = Range5Relation::draw(channel),
                RangeKind::Range16 => out.range_16 = Range16Relation::draw(channel),
            }
        }
        out
    }

    pub fn dummy() -> Self {
        Self {
            range_2: Range2Relation::dummy(),
            range_4: Range4Relation::dummy(),
            range_5: Range5Relation::dummy(),
            range_16: Range16Relation::dummy(),
        }
    }
}

impl Default for RangeRelations {
    fn default() -> Self {
        Self::dummy()
    }
}

/// Row width of the cross-component digest relation: the 32 bytes of the
/// final-block SHA-256 digest. The digest byte string is `H0..H7` each
/// serialised **big-endian** (FIPS 180-4 §5); the 32 cells are laid out
/// per state word `j` as `[hi.b1, hi.b0, lo.b1, lo.b0]` — i.e.
/// `word_j.to_be_bytes()` — so cell `4j+k` is digest byte `4j+k`.
pub const DIGEST_REL_SIZE: usize = crate::constants::DIGEST_BYTES;

/// The cross-component digest channel is **shared** with the consumer (the P256
/// `z` binding, §6.3): a yield here only cancels against a require there if both
/// sides combine over the *same* drawn `LookupElements`. So the relation type is
/// defined once in the common [`air_core`] crate and aliased here, rather than
/// declared locally. Width, and the `relation!`-generated `draw`/`dummy`/
/// `combine`, are unchanged — 6.2's transcript order and width-32 test still
/// hold — so this is a transparent move, not a behavioural change.
pub use air_core::relations::DigestBytesRelation as Sha256Digest;

// The shared arity must match this crate's digest-byte count, or the provider
// and consumer would size their relation tuples differently and silently fail
// to balance.
const _: () = assert!(DIGEST_REL_SIZE == air_core::relations::DIGEST_BYTES_ARITY);

/// The cross-component digest channel (interface-contract item 2:
/// `SHA_DIGEST ↔ ECDSA_Z`). **This is the one relation the SHA-256 AIR uses
/// from the *provider* side**: on the final block of a multi-block hash it
/// *yields* the 32 digest bytes (`add_to_relation(&digest, −is_last_block,
/// &[b0..b31])`), so a downstream module (the P256 ECDSA `z` binding, §6.3;
/// the field predicates reuse the same byte-bridge machinery, §6.5) can
/// *require* them. Unlike every other channel here, the yield has no
/// in-module consumer, so it leaves the SHA module's claimed-sum non-zero —
/// it only cancels once a consumer requires the same bytes, which is what
/// makes the combined proof bind "the signature is over the hash of this
/// preimage". The yield is gated behind `Sha256Eval::expose_digest` so the
/// standalone SHA proof (no consumer) still self-balances.
///
/// **Representation bridge (interface-contract item 4).** SHA holds the
/// digest as 16-bit `(lo, hi)` limbs; P256 holds `z` as 13-bit limbs. The
/// two cannot be equated limb-for-limb, so the relation carries **bytes**:
/// the SHA AIR decomposes each limb into two bytes (`limb = 256·b1 + b0`)
/// and yields the 32 big-endian bytes. The byte values are tied to the
/// (already `Range_16`-pinned) `h_out` limbs by that decomposition
/// constraint; the **`[0, 256)` range-check of each byte is the consumer's
/// responsibility** (P256 already witnesses and range-checks `z`'s byte
/// decomposition). A consumer that requires out-of-range bytes cannot match
/// the honest in-range bytes a correct prover yields, so the balance fails
/// closed — see the relation's use in `crate::constraints::Sha256Eval`.
#[derive(Clone, Debug, PartialEq)]
pub struct DigestRelation {
    pub digest: Sha256Digest,
}

impl DigestRelation {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            digest: Sha256Digest::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            digest: Sha256Digest::dummy(),
        }
    }
}

impl Default for DigestRelation {
    fn default() -> Self {
        Self::dummy()
    }
}

/// All LogUp channels the SHA-256 AIR consumes today: the eight `Σ`/`σ`
/// decode-table channels, the packed Maj/Ch pair, the chunk-wise `xor_8`
/// channel, the eight split-and-pack channels, and the four range-check
/// channels. Aggregated so `Sha256Eval` holds a single relations bundle
/// and the prover-side `draw` walks the transcript once per component.
#[derive(Clone, Debug, PartialEq)]
pub struct Sha256Relations {
    pub sigma_decode: SigmaDecodeRelations,
    pub maj: MajRelation,
    pub ch: ChRelation,
    pub xor_8: Xor8Relation,
    pub split_pack: SplitPackRelations,
    pub range: RangeRelations,
    /// Cross-component digest channel — provider side. Always drawn so the
    /// relation bundle is uniform; only *used* when `Sha256Eval::expose_digest`
    /// is set (the combined-proof path). See [`DigestRelation`].
    pub digest: DigestRelation,
}

impl Sha256Relations {
    /// Draw fresh `LookupElements` for every channel from a transcript.
    /// The draw order is fixed — decode channels first (matching the
    /// existing 3.9.3 pattern), then Maj, then Ch, then `xor_8`, then the
    /// split-and-pack channels, then the range channels. Changing the
    /// order rotates the verifier-side challenges and breaks proof
    /// portability.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::draw(channel),
            maj: MajRelation::draw(channel),
            ch: ChRelation::draw(channel),
            xor_8: Xor8Relation::draw(channel),
            split_pack: SplitPackRelations::draw(channel),
            range: RangeRelations::draw(channel),
            // Drawn last so adding it leaves every earlier channel's
            // challenge unchanged (the draw order above is frozen — see the
            // doc-comment). Prover and verifier both draw it whether or not
            // the digest is exposed, keeping the transcript symmetric.
            digest: DigestRelation::draw(channel),
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
            range: RangeRelations::dummy(),
            digest: DigestRelation::dummy(),
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

    /// The four round-side split-and-pack channels expose row width 5
    /// (`key + 4` packed sub-groups at `W = 6`). Cross-checked through the
    /// `Relation` trait so an off-by-one in the macro declaration would
    /// fail closed.
    #[test]
    fn round_split_pack_relations_have_row_width_5() {
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
        assert_eq!(ROUND_SPLIT_PACK_REL_SIZE, 5);
    }

    /// Every `Range_k` channel exposes row width 1. The lookup tuple
    /// passed to `add_to_relation` is a single carry / terminal-limb cell.
    #[test]
    fn range_relations_have_row_width_1() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        for size in [
            <Range2Relation as Relation<BaseField, SecureField>>::get_size(&r.range.range_2),
            <Range4Relation as Relation<BaseField, SecureField>>::get_size(&r.range.range_4),
            <Range5Relation as Relation<BaseField, SecureField>>::get_size(&r.range.range_5),
            <Range16Relation as Relation<BaseField, SecureField>>::get_size(&r.range.range_16),
        ] {
            assert_eq!(size, RANGE_REL_SIZE);
        }
        assert_eq!(RANGE_REL_SIZE, 1);
    }

    /// The cross-component digest channel exposes row width 32 — the 32
    /// big-endian bytes of the SHA-256 digest. A regression here would
    /// desync the provider tuple from the consumer (P256 `z`) tuple and
    /// silently break the combined-proof balance.
    #[test]
    fn digest_relation_has_row_width_32() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        assert_eq!(
            <Sha256Digest as Relation<BaseField, SecureField>>::get_size(&r.digest.digest),
            DIGEST_REL_SIZE
        );
        assert_eq!(DIGEST_REL_SIZE, 32);
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
