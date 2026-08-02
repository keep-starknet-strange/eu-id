//! LogUp relations for the Keccak and SHAKE AIR.
//!
//! [`KeccakStateRelation`] binds each committed sponge input to the state that
//! the Keccak proof uses. [`HashIoRelation`] connects byte streams to the
//! sponge. [`Xor3`] and [`Conv`] connect the sponge to their fixed lookup
//! tables.
//!
//! Each `relation!(_, N)` declares a struct wrapping `LookupElements<N>`; `N`
//! is the base-field arity of one lookup tuple. Stwo's macro implements
//! `Relation::combine`, collapsing an `&[F]` of `N` cells into the extension
//! key the interaction column reads.

#![allow(non_camel_case_types)]

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

use crate::constants::N_BYTES_IN_STATE;

// ───────────────────────────── Interface relations ─────────────────────────

/// Arity of [`KeccakStateRelation`]: permutation ID and 200 spread state bytes.
///
/// The tuple is `(perm_id, s_0, ..., s_199)`. The sponge emits its computed
/// input state and consumes the state that its committed nibble columns
/// encode. The permutation ID prevents a row from using another row's state.
pub const KECCAK_STATE_ARITY: usize = 1 + N_BYTES_IN_STATE;

relation!(KeccakStateRelation, KECCAK_STATE_ARITY);

/// Arity of [`HashIoRelation`]: `(stream_id, byte_pos, byte)`.
pub const HASH_IO_ARITY: usize = 3;

relation!(HashIoRelation, HASH_IO_ARITY);

// ───────────────────────────── Internal relations ──────────────────────────

/// Arity of the XOR and byte-conversion lookup tuples.
pub const BYTE_LOOKUP_ARITY: usize = 2;

// `(key, spread(xor))`, where `key` is the sum of up to three spread bytes.
relation!(Xor3, BYTE_LOOKUP_ARITY);

// `(byte, spread(byte))`.
relation!(Conv, BYTE_LOOKUP_ARITY);

/// Shared handle for the single [`KeccakRelations`] value in a composed proof.
///
/// The [`crate::service::KeccakServiceProver`] / `Verifier` module draws the
/// relations during `draw_relations` and stores them here. Consumer modules
/// read the handle during their `draw_relations` calls. Air-core runs those
/// calls after the service call.
pub type SharedKeccakRelations = air_core::relations::SharedRelation<KeccakRelations>;

/// Every relation the Keccak AIR draws, held together so prove and verify draw
/// them from the shared transcript in one deterministic order.
#[derive(Clone, Debug)]
pub struct KeccakRelations {
    pub keccak_state: KeccakStateRelation,
    pub hash_io: HashIoRelation,
    pub xor3: Xor3,
    pub conv: Conv,
}

impl KeccakRelations {
    /// Draw every relation from the shared channel, in a fixed order.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            keccak_state: KeccakStateRelation::draw(channel),
            hash_io: HashIoRelation::draw(channel),
            xor3: Xor3::draw(channel),
            conv: Conv::draw(channel),
        }
    }

    /// Constant channels for AIR tests without a real transcript (mirrors the
    /// Stwo Blake example's `dummy()` pattern).
    pub fn dummy() -> Self {
        Self {
            keccak_state: KeccakStateRelation::dummy(),
            hash_io: HashIoRelation::dummy(),
            xor3: Xor3::dummy(),
            conv: Conv::dummy(),
        }
    }
}
