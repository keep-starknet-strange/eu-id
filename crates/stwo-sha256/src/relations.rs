//! LogUp relation tags for the SHA-256 component.
//!
//! Active range tables are paired with [`stwo_constraint_framework::Relation`]
//! channels. The SHA-256 component consumes those channels with positive
//! multiplicity and the producer components yield the matching rows with
//! negative multiplicity. The digest and field channels are cross-module
//! provider surfaces.
//!
//! Four channel families are live in the constraint layer:
//!   - [`RangeRelations`] — the four width-1 range-check channels
//!     `Range_2`/`Range_4`/`Range_5`/`Range_8`. `Range_k` pins a single
//!     base-field value into `[0, k)`. The mod-2³² limb-add carries are
//!     range-checked through `Range_{2,4,5}` per the headroom audit
//!     (`crate::headroom`); terminal 16-bit limbs (the final block's
//!     `h_out`, per design §10.2) are range-checked through `Range_8` bytes.
//!     Row content for each `Range_k` is the table `crate::tables_local::range_k()`.
//!   - [`Sha256Digest`] — the shared 32-byte digest provider relation.
//!   - [`Sha256Field`] — the shared credential-field byte provider relation.
//!   - [`SlotIoRelations`] — per-slot digest/field bridges for multi-message mode.
//!
//! The decode/Maj/Ch/xor_8 relation types remain in [`Sha256Relations`] only
//! as frozen transcript draws for challenge-order compatibility.
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

use air_core::relations::SharedRelation;
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

/// Row width of every `Range_k` channel: a single base-field value pinned
/// to `[0, k)`. The lookup tuple passed to `add_to_relation` is a 1-cell
/// slice — the carry limb (for mod-2³² adds) or a terminal byte.
pub const RANGE_REL_SIZE: usize = 1;

relation!(Range2Relation, RANGE_REL_SIZE);
relation!(Range4Relation, RANGE_REL_SIZE);
relation!(Range5Relation, RANGE_REL_SIZE);
relation!(Range8Relation, RANGE_REL_SIZE);

/// The four range-check channels grouped for `Sha256Eval`.
///
/// - `range_2` / `range_4` / `range_5` pin the `(carry_lo, carry_hi)`
///   pair of each mod-2³² limb-add (per the headroom audit's family
///   bound: `k=4` for the schedule recurrence, `k=5` for `T1`, `k=2`
///   everywhere else).
/// - `range_8` pins terminal digest bytes and exposed message bytes.
///
/// Each channel produces one preprocessed-column row per value and has its
/// own multiplicity column committed by the matching producer component.
#[derive(Clone, Debug, PartialEq)]
pub struct RangeRelations {
    pub range_2: Range2Relation,
    pub range_4: Range4Relation,
    pub range_5: Range5Relation,
    pub range_8: Range8Relation,
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
                RangeKind::Range8 => out.range_8 = Range8Relation::draw(channel),
            }
        }
        out
    }

    pub fn dummy() -> Self {
        Self {
            range_2: Range2Relation::dummy(),
            range_4: Range4Relation::dummy(),
            range_5: Range5Relation::dummy(),
            range_8: Range8Relation::dummy(),
        }
    }
}

impl Default for RangeRelations {
    fn default() -> Self {
        Self::dummy()
    }
}

#[derive(Clone, Default)]
pub struct SharedRangeRelations {
    pub range_2: SharedRelation<Range2Relation>,
    pub range_4: SharedRelation<Range4Relation>,
    pub range_5: SharedRelation<Range5Relation>,
    pub range_8: SharedRelation<Range8Relation>,
}

impl SharedRangeRelations {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&self, relations: &RangeRelations) {
        self.range_2.set(relations.range_2.clone());
        self.range_4.set(relations.range_4.clone());
        self.range_5.set(relations.range_5.clone());
        self.range_8.set(relations.range_8.clone());
    }

    pub fn get(&self) -> RangeRelations {
        RangeRelations {
            range_2: self.range_2.get(),
            range_4: self.range_4.get(),
            range_5: self.range_5.get(),
            range_8: self.range_8.get(),
        }
    }
}

#[derive(Clone, Default)]
pub struct SharedShaTableRelations {
    pub range: SharedRangeRelations,
}

impl SharedShaTableRelations {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&self, range: &RangeRelations) {
        self.range.set(range);
    }
}

/// Row width of the cross-component digest relation: the 32 bytes of the
/// final-block SHA-256 digest. The digest byte string is `H0..H7` each
/// serialised **big-endian** (FIPS 180-4 §5); the 32 cells are laid out
/// per state word `j` as `[hi.b1, hi.b0, lo.b1, lo.b0]` — i.e.
/// `word_j.to_be_bytes()` — so cell `4j+k` is digest byte `4j+k`.
pub const DIGEST_REL_SIZE: usize = crate::constants::DIGEST_BYTES;

/// The cross-component digest channel is **shared** with the consumer: a yield
/// here only cancels against a require there if both
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

/// The cross-component digest channel. **This is the relation the SHA-256 AIR uses
/// from the *provider* side**: on the final block of a multi-block hash it
/// *yields* the 32 digest bytes (`add_to_relation(&digest, −is_last_block,
/// &[b0..b31])`), so a downstream module (the ML-DSA digest binding; the
/// field predicates reuse the same byte-bridge machinery) can
/// *require* them. Unlike every other channel here, the yield has no
/// in-module consumer, so it leaves the SHA module's claimed-sum non-zero —
/// it only cancels once a consumer requires the same bytes, which is what
/// makes the combined proof bind "the signature is over the hash of this
/// preimage". The yield is gated behind `Sha256Eval::expose_digest` so the
/// standalone SHA proof (no consumer) still self-balances.
///
/// **Representation bridge.** SHA holds the digest as 16-bit `(lo, hi)` limbs,
/// while consumers bind canonical digest bytes. The two surfaces cannot be
/// equated limb-for-limb, so the relation carries **bytes**:
/// the SHA AIR decomposes each limb into two bytes (`limb = 256·b1 + b0`)
/// and yields the 32 big-endian bytes. The byte values are tied to the
/// `h_out` limbs by that decomposition constraint, and the provider pins every
/// byte to `[0, 256)` through `Range_8`. Consumers therefore receive a
/// canonical byte tuple without needing a second range check.
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

/// The cross-component credential-field channel is **shared** with the predicate
/// consumers, so — like [`Sha256Digest`] — the relation type is
/// defined once in [`air_core`] and aliased here. Width 3: `(field_id,
/// byte_index, value)`.
pub use air_core::relations::FieldBytesRelation as Sha256Field;

// The shared arity must match this crate's expectation, or the provider and
// consumer would size their relation tuples differently and silently fail to
// balance.
pub const FIELD_REL_SIZE: usize = air_core::relations::FIELD_BYTES_ARITY;

/// The cross-component credential-field channel (interface-contract item 3:
/// `CRED_FIELD ↔ PREDICATE_INPUT`). The second cross-module channel the SHA-256
/// AIR uses from the **provider** side: when a non-empty
/// [`crate::field_exposure::FieldExposure`] is configured, on the **first block**
/// it *yields* one `(field_id, byte_index, value)` tuple per exposed credential
/// byte (`add_to_relation(&field, −is_first_block, &[field_id, byte_index,
/// value])`), so a downstream predicate can *require* exactly the byte window of
/// the field it binds. Like the digest yield, these terms have no
/// in-module consumer — they leave the SHA module's claimed sum non-zero until a
/// predicate consumer cancels them — so they are gated behind the field-exposure
/// spec (empty by default), keeping a standalone SHA proof self-balancing.
///
/// **Representation bridge (interface-contract item 4).** The message words live
/// in the trace as 16-bit `(lo, hi)` limbs; the field bytes are their big-endian
/// decomposition (`limb = 256·b1 + b0`), the same byte bridge the digest uses.
/// The byte values are tied to the byte-decomposition-pinned message-word limbs by
/// that decomposition. Like the digest, the provider range-checks every byte;
/// this is especially important because a field window can be **sub-word**: an edge byte shares a
/// limb with a non-exposed neighbour, and a 16-bit limb's split `256·b_hi + b_lo`
/// is unique only when *both* bytes are in `[0, 256)`. So the provider itself
/// range-checks **every** exposed byte to `[0, 256)` (one `Range8` lookup per
/// byte). With both bytes of every touched limb pinned, each yielded
/// byte is exactly the signed preimage byte — the binding holds without trusting
/// the consumer to range-check anything.
#[derive(Clone, Debug, PartialEq)]
pub struct FieldRelation {
    pub field: Sha256Field,
}

impl FieldRelation {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            field: Sha256Field::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            field: Sha256Field::dummy(),
        }
    }
}

impl Default for FieldRelation {
    fn default() -> Self {
        Self::dummy()
    }
}

/// Per-slot cross-module channels of a multi-slot consumer: each slot gets
/// its OWN digest and field relation, drawn in slot order. Distinct
/// per-slot relations make cross-slot digest/field substitution
/// inexpressible at the relation level, and they map one-to-one onto the
/// per-instance `SharedDigestRelation` / `SharedFieldRelation` handles the
/// mdoc consumers already hold — merging the SHA instances changes nothing
/// on the consumer side.
#[derive(Clone, Debug, PartialEq)]
pub struct SlotIoRelations {
    pub digest: DigestRelation,
    pub field: FieldRelation,
}

impl SlotIoRelations {
    /// Draw one (digest, field) pair per slot, in slot order. Both sides of
    /// the transcript call this at the same point (after the shared-table
    /// handshake), mirroring the single-instance draw order
    /// (digest first, then field).
    pub fn draw_per_slot(channel: &mut impl Channel, n_slots: usize) -> Vec<Self> {
        (0..n_slots)
            .map(|_| Self {
                digest: DigestRelation::draw(channel),
                field: FieldRelation::draw(channel),
            })
            .collect()
    }

    pub fn dummy_per_slot(n_slots: usize) -> Vec<Self> {
        (0..n_slots)
            .map(|_| Self {
                digest: DigestRelation::dummy(),
                field: FieldRelation::dummy(),
            })
            .collect()
    }
}

/// All LogUp channels in the frozen SHA-256 transcript. The live AIR consumes
/// the four range-check channels plus optional cross-component digest/field
/// channels. The decode/Maj/Ch/xor_8 draws are vestigial draws, frozen for
/// challenge-order compatibility; remove only with a coordinated repin.
#[derive(Clone, Debug, PartialEq)]
pub struct Sha256Relations {
    pub sigma_decode: SigmaDecodeRelations,
    pub maj: MajRelation,
    pub ch: ChRelation,
    pub xor_8: Xor8Relation,
    pub range: RangeRelations,
    /// Cross-component digest channel — provider side. Always drawn so the
    /// relation bundle is uniform; only *used* when `Sha256Eval::expose_digest`
    /// is set (the combined-proof path). See [`DigestRelation`].
    pub digest: DigestRelation,
    /// Cross-component credential-field channel — provider side. Always drawn so
    /// the relation bundle is uniform; only *used* when a non-empty field
    /// exposure is configured (the predicate-binding path). See
    /// [`FieldRelation`].
    pub field: FieldRelation,
}

impl Sha256Relations {
    /// Draw fresh `LookupElements` for every channel from a transcript.
    /// The draw order is fixed — decode channels first (matching the
    /// existing 3.9.3 pattern), then Maj, then Ch, then `xor_8`, then the
    /// range channels. Changing the
    /// order rotates the verifier-side challenges and breaks proof
    /// portability.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::draw(channel),
            maj: MajRelation::draw(channel),
            ch: ChRelation::draw(channel),
            xor_8: Xor8Relation::draw(channel),
            range: RangeRelations::draw(channel),
            // Drawn after every standalone channel so adding it leaves their
            // challenges unchanged (the draw order above is frozen — see the
            // doc-comment). Prover and verifier both draw it whether or not
            // the digest is exposed, keeping the transcript symmetric.
            digest: DigestRelation::draw(channel),
            // Drawn last (after the digest), same reasoning: additive, so the
            // field channel never perturbs an earlier channel's challenge.
            field: FieldRelation::draw(channel),
        }
    }

    pub fn draw_sha_tables_provider(channel: &mut impl Channel) -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::dummy(),
            maj: MajRelation::dummy(),
            ch: ChRelation::dummy(),
            xor_8: Xor8Relation::dummy(),
            range: RangeRelations::draw(channel),
            digest: DigestRelation::dummy(),
            field: FieldRelation::dummy(),
        }
    }

    pub fn draw_with_shared_tables(
        channel: &mut impl Channel,
        shared: &SharedShaTableRelations,
    ) -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::dummy(),
            maj: MajRelation::dummy(),
            ch: ChRelation::dummy(),
            xor_8: Xor8Relation::dummy(),
            range: shared.range.get(),
            digest: DigestRelation::draw(channel),
            field: FieldRelation::draw(channel),
        }
    }

    /// Multi-slot consumer draw: the fixed tables come from the shared
    /// handles (as [`Self::draw_with_shared_tables`]); the single-instance
    /// digest/field channels stay DUMMY (the multi eval never touches them)
    /// and each slot draws its own (digest, field) pair instead, in slot
    /// order.
    pub fn draw_multi_with_shared_tables(
        channel: &mut impl Channel,
        shared: &SharedShaTableRelations,
        n_slots: usize,
    ) -> (Self, Vec<SlotIoRelations>) {
        let base = Self {
            sigma_decode: SigmaDecodeRelations::dummy(),
            maj: MajRelation::dummy(),
            ch: ChRelation::dummy(),
            xor_8: Xor8Relation::dummy(),
            range: shared.range.get(),
            digest: DigestRelation::dummy(),
            field: FieldRelation::dummy(),
        };
        let slots = SlotIoRelations::draw_per_slot(channel, n_slots);
        (base, slots)
    }

    /// Constant-channel set for tests. Mirrors [`SigmaDecodeRelations::dummy`]
    /// so the AIR can be exercised without a real prover transcript.
    pub fn dummy() -> Self {
        Self {
            sigma_decode: SigmaDecodeRelations::dummy(),
            maj: MajRelation::dummy(),
            ch: ChRelation::dummy(),
            xor_8: Xor8Relation::dummy(),
            range: RangeRelations::dummy(),
            digest: DigestRelation::dummy(),
            field: FieldRelation::dummy(),
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
            <Range8Relation as Relation<BaseField, SecureField>>::get_size(&r.range.range_8),
        ] {
            assert_eq!(size, RANGE_REL_SIZE);
        }
        assert_eq!(RANGE_REL_SIZE, 1);
    }

    /// The cross-component digest channel exposes row width 32 — the 32
    /// big-endian bytes of the SHA-256 digest. A regression here would
    /// desync the provider tuple from the consumer tuple and
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

    /// The cross-component credential-field channel exposes row width 3 —
    /// `(field_id, byte_index, value)`. A regression here would desync the
    /// provider tuple from the predicate consumer and silently break
    /// the combined-proof balance.
    #[test]
    fn field_relation_has_row_width_3() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::Relation;
        let r = Sha256Relations::dummy();
        assert_eq!(
            <Sha256Field as Relation<BaseField, SecureField>>::get_size(&r.field.field),
            FIELD_REL_SIZE
        );
        assert_eq!(FIELD_REL_SIZE, 3);
    }
}
