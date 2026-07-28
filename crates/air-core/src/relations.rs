//! Cross-module LogUp relations shared by composed circuits.
//!
//! A relation drawn inside one module's `draw_relations` is private to that
//! module — its `LookupElements` challenge is sampled at that module's point in
//! the shared transcript. For two *different* modules to balance a yield against
//! a require they must combine over the **same** drawn `LookupElements`. That is
//! what lives here: relation types both a provider crate and a consumer crate
//! can name, plus a [`SharedDigestRelation`] handle the orchestrator uses to
//! hand the single drawn instance from the module that draws it to the module
//! that reads it.
//!
//! Today this hosts two byte-level bridges:
//!
//! - the SHA→consumer **digest byte bridge**: SHA-256 yields its 32-byte
//!   final-block digest; ML-DSA verifier modules require those bytes at their
//!   hash-binding boundaries.
//! - the SHA→predicate **credential-field byte bridge**: SHA-256 yields the byte
//!   windows of the signed credential's fields (date of birth, nationality);
//!   each predicate requires exactly those bytes so the attribute it reasons
//!   about is the one that was signed.
//!
//! Both reuse the same shape — expose some trace bytes as an 8-bit LogUp
//! relation, share the drawn `LookupElements` via a [`SharedRelation`] handle.

use std::cell::RefCell;
use std::rc::Rc;

use stwo_constraint_framework::relation;

/// Number of base-field cells in the cross-module digest relation — the 32
/// bytes of a SHA-256 digest. Must equal `stwo_sha256::constants::DIGEST_BYTES`.
pub const DIGEST_BYTES_ARITY: usize = 32;

relation!(DigestBytesRelation, DIGEST_BYTES_ARITY);

/// Shared handle for a cross-module relation, generic over the relation type.
///
/// The orchestrator ([`crate::prove`] / [`crate::verify`]) drives every module
/// through `draw_relations` in module order against one channel. The **provider**
/// module draws the relation inside its bundle and [`set`]s it here; the
/// **consumer** module reads it back with [`get`] during its interaction +
/// component phases, which the orchestrator runs only *after* every module has
/// drawn — so the handle is always populated by the time the consumer needs it.
/// The same handle is reconstructed identically on prove and verify, so the
/// challenge is deterministic.
///
/// Interior mutability behind an [`Rc`] because the producer and consumer are
/// two distinct module objects; the orchestrator drives them single-threaded, so
/// no `Sync` is required. `Clone` and `Default` are hand-written so they do not
/// demand `R: Clone` / `R: Default` (the `Rc` is always cloneable).
///
/// Live instances include [`SharedDigestRelation`] (SHA → digest consumer) and
/// [`SharedFieldRelation`] (SHA → credential-field consumers).
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
    /// A fresh, empty handle. Create one per proof in the orchestrator and clone
    /// it into the provider and consumer modules.
    pub fn new() -> Self {
        Self::default()
    }

    /// Store the drawn relation. Called by the provider module once, during its
    /// `draw_relations`.
    pub fn set(&self, relation: R) {
        *self.0.borrow_mut() = Some(relation);
    }

    /// Read the drawn relation. Panics if called before the provider has drawn
    /// it — a wiring bug (the orchestrator guarantees all `draw_relations` run
    /// before any consumer interaction/component phase).
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

/// The SHA → consumer digest-byte channel handle.
pub type SharedDigestRelation = SharedRelation<DigestBytesRelation>;

/// Number of base-field cells in the cross-module credential-field relation:
/// `(field_id, byte_index, value)`. The SHA preimage field-exposure provider
/// yields one such tuple per exposed credential byte; each predicate consumer
/// requires exactly the tuples of the field it binds. Keying on
/// `(field_id, byte_index)` lets one shared channel carry
/// every field's bytes without an index column — the producer and consumer pin
/// the same position by emitting the same first two cells.
pub const FIELD_BYTES_ARITY: usize = 3;

relation!(FieldBytesRelation, FIELD_BYTES_ARITY);

/// The SHA → predicate credential-field channel handle. One shared channel
/// carries every exposed field byte; the `field_id` cell distinguishes which
/// credential field a byte belongs to.
pub type SharedFieldRelation = SharedRelation<FieldBytesRelation>;

/// Opaque credential-field tags carried in the first cell of a
/// [`FieldBytesRelation`] tuple. They are assigned by the credential layer and
/// are part of the frozen cross-module contract — the SHA producer is agnostic
/// to their meaning (it yields whatever tags its field-exposure spec lists), and
/// each predicate consumer requires the tag of the field it binds. The MVP
/// credential exposes exactly these two fields (`docs/credential-format.md`).
pub mod field_id {
    /// The date-of-birth window (`year_hi, year_lo, month, day`), bound by the
    /// age predicate.
    pub const DOB: u32 = 0;
    /// The nationality window (`code_hi, code_lo`), bound by the nationality
    /// predicate.
    pub const NATIONALITY: u32 = 1;
    // ids 2–15 reserved (legacy); mdoc dynamic fields allocate from 16+.
}

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

    #[test]
    fn credential_field_ids_are_distinct() {
        assert_ne!(field_id::DOB, field_id::NATIONALITY);
        assert!(field_id::DOB < 2);
        assert!(field_id::NATIONALITY < 2);
    }
}
