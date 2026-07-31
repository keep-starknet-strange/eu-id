//! LogUp relations for the SHA-256 component.
//!
//! The component uses three relation groups:
//! - [`RangeRelations`] checks carries and bytes.
//! - [`Sha256Digest`] sends the 32-byte digest to another component.
//! - [`Sha256Field`] sends credential bytes to another component.
//!
//! The SHA-256 component consumes range-table rows. The table components
//! produce the same rows. The digest and field relations connect this
//! component to their consumers.

use air_core::relations::SharedRelation;
use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

/// Each range relation contains one base-field value.
pub const RANGE_REL_SIZE: usize = 1;

relation!(Range2Relation, RANGE_REL_SIZE);
relation!(Range4Relation, RANGE_REL_SIZE);
relation!(Range5Relation, RANGE_REL_SIZE);
relation!(Range8Relation, RANGE_REL_SIZE);

/// The four range-check channels for `Sha256Eval`.
///
/// `range_2`, `range_4`, and `range_5` check addition carries.
/// `range_8` checks digest bytes.
#[derive(Clone, Debug, PartialEq)]
pub struct RangeRelations {
    pub range_2: Range2Relation,
    pub range_4: Range4Relation,
    pub range_5: Range5Relation,
    pub range_8: Range8Relation,
}

impl RangeRelations {
    /// Draw one challenge for each range relation.
    ///
    /// This function uses the same order as the range tables.
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

/// Number of bytes in the digest relation.
pub const DIGEST_REL_SIZE: usize = crate::constants::DIGEST_BYTES;

/// Shared digest relation for the provider and the consumer.
pub use air_core::relations::DigestBytesRelation as Sha256Digest;

// The provider and consumer must use the same tuple size.
const _: () = assert!(DIGEST_REL_SIZE == air_core::relations::DIGEST_BYTES_ARITY);

/// Digest relation for the SHA-256 provider.
///
/// The last block yields the 32 digest bytes when digest exposure is active.
/// A consumer must use the same relation. The AIR converts each 16-bit digest
/// limb to two big-endian bytes. It also checks each byte with `Range_8`.
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

/// Shared credential-field relation for providers and consumers.
///
/// Each tuple is `(field_id, byte_index, value)`.
pub use air_core::relations::FieldBytesRelation as Sha256Field;

// The provider and consumer must use the same tuple size.
pub const FIELD_REL_SIZE: usize = air_core::relations::FIELD_BYTES_ARITY;

/// Credential-field relation for the SHA-256 provider.
///
/// A configured field exposure yields one tuple for each exposed byte.
/// A composed consumer requires the same tuples. Full padded-stream exposure
/// gets the bytes from the constrained message bits and emits them in stream
/// order.
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

/// All LogUp channels in the SHA-256 transcript. The AIR consumes the four
/// range-check channels and optional cross-component digest and field
/// channels.
#[derive(Clone, Debug, PartialEq)]
pub struct Sha256Relations {
    pub range: RangeRelations,
    /// Cross-component digest channel — provider side. Always drawn so the
    /// relation bundle is uniform; only *used* when `Sha256Eval::expose_digest`
    /// is set (the combined-proof path). See [`DigestRelation`].
    pub digest: DigestRelation,
    /// Cross-component credential-field channel — provider side. Always drawn so
    /// the relation bundle is uniform; only *used* when a non-empty field
    /// exposure is configured. See [`FieldRelation`].
    pub field: FieldRelation,
}

impl Sha256Relations {
    /// Draw fresh `LookupElements` for each channel. The fixed order is:
    /// range channels, digest, and field. Prove and verify must use this order.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            range: RangeRelations::draw(channel),
            // Prove and verify always draw the digest relation here.
            digest: DigestRelation::draw(channel),
            // Prove and verify always draw the field relation last.
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

    /// Return fixed relations for tests.
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

    /// Each range relation has one value.
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

    /// The digest relation has 32 values.
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

    /// The field relation has three values.
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
