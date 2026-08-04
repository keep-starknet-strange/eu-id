//! LogUp relation tags for the SHA-256 component.
//!
//! Each active lookup table has one
//! [`stwo_constraint_framework::Relation`] channel. The SHA component adds a
//! positive consumer term for each lookup. A table component adds the matching
//! negative producer term.
//!
//! [`RangeRelations`] contains the four active width-one channels. `Range_2`,
//! `Range_4`, and `Range_5` check modulo-2³² carries. `Range_8` checks terminal
//! digest bytes. The AIR then reconstructs the 16-bit `h_out` limbs.
//!
//! The digest and field relations connect SHA to other components.

use air_core::relations::SharedRelation;
use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

/// Row width of each `Range_k` channel.
///
/// The one-cell tuple is an addition carry or terminal digest byte.
pub const RANGE_REL_SIZE: usize = 1;

relation!(Range2Relation, RANGE_REL_SIZE);
relation!(Range4Relation, RANGE_REL_SIZE);
relation!(Range5Relation, RANGE_REL_SIZE);
relation!(Range8Relation, RANGE_REL_SIZE);

/// The four range-check channels grouped for `Sha256Eval`.
///
/// - `range_2`, `range_4`, and `range_5` constrain addition carry pairs.
///   The audited bounds use `k=4` for schedules and `k=5` for `T1`.
///   All other addition families use `k=2`.
/// - `range_8` pins every terminal digest byte. Recomposition from two
///   checked bytes pins each final `h_out` limb to 16 bits.
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
    /// `RANGE_TABLES` defines the canonical channel order.
    ///
    /// Preprocessing, multiplicity assembly, interaction generation, and
    /// challenge generation all use this slice.
    /// A reordered slice changes all four paths together.
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
/// serialized in big-endian order (FIPS 180-4 §5). The 32 cells are laid out
/// per state word `j` as `[hi.b1, hi.b0, lo.b1, lo.b0]` — i.e.
/// `word_j.to_be_bytes()` — so cell `4j+k` is digest byte `4j+k`.
pub const DIGEST_REL_SIZE: usize = crate::constants::DIGEST_BYTES;

/// The digest provider and consumer share this channel. Their terms cancel
/// only when both use identical `LookupElements`. [`air_core`] defines the
/// common type, and this crate uses an alias.
pub use air_core::relations::DigestBytesRelation as Sha256Digest;

// The shared arity must match this crate's digest-byte count, or the provider
// and consumer would size their relation tuples differently and silently fail
// to balance.
const _: () = assert!(DIGEST_REL_SIZE == air_core::relations::DIGEST_BYTES_ARITY);

/// Cross-component channel from a SHA digest to an ECDSA `z` input.
///
/// On the final block, the SHA AIR yields all 32 digest bytes.
/// A downstream P-256 module requires the same tuple.
/// The isolated yield leaves a nonzero SHA claim sum.
/// A matching consumer cancels it and binds the signature preimage.
/// `Sha256Eval::expose_digest` gates the yield.
/// The standalone SHA proof leaves this option disabled.
///
/// SHA uses 16-bit limbs, while P-256 uses 13-bit limbs for `z`. The relation
/// carries bytes instead of limbs.
/// The SHA AIR decomposes each limb with `limb = 256·b1 + b0`.
/// It yields the 32 big-endian bytes.
/// `Range_8` constrains each byte before it crosses the module boundary.
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

/// The shared credential-field channel.
///
/// [`air_core`] defines this three-cell relation as
/// `(field_id, byte_index, value)`. This crate uses an alias.
pub use air_core::relations::FieldBytesRelation as Sha256Field;

// The shared arity must match this crate's expectation, or the provider and
// consumer would size their relation tuples differently and silently fail to
// balance.
pub const FIELD_REL_SIZE: usize = air_core::relations::FIELD_BYTES_ARITY;

/// Cross-component channel from credential bytes to predicate inputs.
///
/// A nonempty [`crate::field_exposure::FieldExposure`] enables this provider.
/// It yields `(field_id, byte_index, value)` for each selected byte.
/// The target block gates each tuple.
/// A downstream predicate requires the same byte window.
/// These yields need an external consumer to balance.
/// The standalone SHA proof uses an empty exposure.
///
/// **Representation bridge (interface-contract item 4).** Every message word
/// already has 32 committed LSB-first bit planes. The AIR constrains each bit
/// boolean and recomposes them to the 16-bit `(lo, hi)` schedule limbs. A field
/// byte is the corresponding linear eight-bit big-endian projection. It is in
/// `[0, 256)` and equals the preimage byte.
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

/// Relations used by the active bit-plane AIR.
#[derive(Clone, Debug, PartialEq)]
pub struct Sha256Relations {
    pub range: RangeRelations,
    /// Cross-component digest channel — provider side. Always drawn so the
    /// relation bundle is uniform. Only *used* when `Sha256Eval::expose_digest`
    /// is set (the combined-proof path). See [`DigestRelation`].
    pub digest: DigestRelation,
    /// Cross-component credential-field channel — provider side. Always drawn so
    /// the relation bundle is uniform. Only *used* when a non-empty field
    /// exposure is configured (the predicate-binding path). See
    /// [`FieldRelation`].
    pub field: FieldRelation,
}

impl Sha256Relations {
    /// Draw fresh `LookupElements` for every channel.
    ///
    /// A different draw order changes verifier challenges and invalidates proofs.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range: RangeRelations::draw(channel),
            digest: DigestRelation::draw(channel),
            field: FieldRelation::draw(channel),
        }
    }

    pub fn draw_sha_tables_provider(channel: &mut impl Channel) -> Self {
        Self {
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
            range: shared.range.get(),
            digest: DigestRelation::draw(channel),
            field: FieldRelation::draw(channel),
        }
    }

    /// Constant-channel set for tests that do not use a prover transcript.
    pub fn dummy() -> Self {
        Self {
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
