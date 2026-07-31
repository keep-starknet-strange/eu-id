//! Cross-module LogUp relations shared by composed circuits.
//!
//! Each module draws its own `LookupElements` challenge from the shared
//! transcript. A provider and a consumer can balance tuples only when they use
//! the same challenge. A [`SharedRelation`] gives both modules the same drawn
//! relation.
//!
//! This module defines two byte relations:
//!
//! - [`DigestBytesRelation`] transfers one 32-byte digest.
//! - [`FieldBytesRelation`] transfers tagged, indexed bytes.

use std::cell::RefCell;
use std::rc::Rc;

use stwo_constraint_framework::relation;

/// Number of base-field cells in the cross-module digest relation. A SHA-256
/// digest has 32 bytes. This value must equal
/// `stwo_sha256::constants::DIGEST_BYTES`.
pub const DIGEST_BYTES_ARITY: usize = 32;

relation!(DigestBytesRelation, DIGEST_BYTES_ARITY);

/// Shared handle for a cross-module relation.
///
/// The provider stores the drawn relation with [`set`]. The consumer reads it
/// with [`get`]. The orchestrator draws all relations before it builds an
/// interaction trace, so the relation is available when the consumer needs it.
/// Prove and verify use the same module order.
///
/// The provider and consumer are separate module objects. An [`Rc`] with
/// interior mutability lets both objects use one handle. The orchestrator is
/// single-threaded, so the handle does not need `Sync`.
///
/// [`set`]: SharedRelation::set
/// [`get`]: SharedRelation::get
pub struct SharedRelation<R>(Rc<RefCell<Option<R>>>);

impl<R> Clone for SharedRelation<R> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<R> Default for SharedRelation<R> {
    fn default() -> Self {
        Self(Rc::new(RefCell::new(None)))
    }
}

impl<R: Clone> SharedRelation<R> {
    /// Create an empty handle. Clone it into the provider and consumer modules.
    pub fn new() -> Self {
        Self::default()
    }

    /// Store the drawn relation. Called by the provider module once, during its
    /// `draw_relations`.
    pub fn set(&self, relation: R) {
        *self.0.borrow_mut() = Some(relation);
    }

    /// Read the drawn relation. This function panics if the provider has not
    /// drawn the relation.
    pub fn get(&self) -> R {
        self.0
            .borrow()
            .clone()
            .expect("shared relation read before it was drawn")
    }

    /// Whether the relation has been drawn yet.
    pub fn is_set(&self) -> bool {
        self.0.borrow().is_some()
    }
}

/// Shared handle for a 32-byte digest relation.
pub type SharedDigestRelation = SharedRelation<DigestBytesRelation>;

/// Number of base-field cells in a tagged-byte relation.
/// Each row is `(field_id, byte_index, value)`.
pub const FIELD_BYTES_ARITY: usize = 3;

relation!(FieldBytesRelation, FIELD_BYTES_ARITY);

/// Shared handle for a tagged-byte relation.
pub type SharedFieldRelation = SharedRelation<FieldBytesRelation>;

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::channel::Blake2sChannel;
    use stwo_constraint_framework::Relation;

    #[test]
    fn digest_relation_has_arity_32() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        let r = DigestBytesRelation::dummy();
        assert_eq!(
            <DigestBytesRelation as Relation<BaseField, SecureField>>::get_size(&r),
            DIGEST_BYTES_ARITY,
        );
        assert_eq!(DIGEST_BYTES_ARITY, 32);
    }

    #[test]
    fn shared_handle_round_trips_the_drawn_relation() {
        let handle = SharedDigestRelation::new();
        assert!(!handle.is_set());
        let mut channel = Blake2sChannel::default();
        let drawn = DigestBytesRelation::draw(&mut channel);
        handle.set(drawn.clone());
        assert!(handle.is_set());
        // A clone of the handle sees the same relation (shared storage).
        assert_eq!(handle.clone().get(), drawn);
    }

    #[test]
    #[should_panic(expected = "read before it was drawn")]
    fn get_before_set_panics() {
        let _ = SharedDigestRelation::new().get();
    }

    #[test]
    fn field_relation_has_arity_3() {
        use stwo::core::fields::m31::BaseField;
        use stwo::core::fields::qm31::SecureField;
        let r = FieldBytesRelation::dummy();
        assert_eq!(
            <FieldBytesRelation as Relation<BaseField, SecureField>>::get_size(&r),
            FIELD_BYTES_ARITY,
        );
        assert_eq!(FIELD_BYTES_ARITY, 3);
    }

    #[test]
    fn shared_field_handle_round_trips_the_drawn_relation() {
        let handle = SharedFieldRelation::new();
        assert!(!handle.is_set());
        let mut channel = Blake2sChannel::default();
        let drawn = FieldBytesRelation::draw(&mut channel);
        handle.set(drawn.clone());
        assert!(handle.is_set());
        assert_eq!(handle.clone().get(), drawn);
    }
}
