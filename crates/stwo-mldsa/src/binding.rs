//! Shared LogUp relations for ML-DSA components.
//!
//! This module defines each cross-component relation once. The composed AIR
//! and the standalone tests use the same relation types.
//!
//! ## Contracts
//!
//! | relation | arity | tuple | producer (−?) | consumer (+?) | stream_id |
//! |----------|-------|-------|----------|----------|-----------|
//! | `WCell` | 2 | `(w_bind_id, w)` | coeffs W rows (−1, yield) | decomp (+1, use) | — |
//! | `CCell` | 2 | `(c_bind_id, c)` | coeffs C rows (−1, yield) | sampleinball (+1, use) | — |
//! | `HashIo`| 3 | `(stream_id, byte_pos, byte)` | see sign convention below | | see below |
//! | `MsgLink`| 3 | `(field_id, byte_index, byte)` | msglink producer (−1, yield) | µ-absorb bridge (+1, use) | — |
//!
//! `w_bind_id = i·N + m` uniquely keys each of the `k·N` w-coefficients;
//! `c_bind_id = m` keys the `N` challenge coefficients. Each tuple uses the
//! matching coefficient cell.
//!
//! ### Shared `HashIo` relation
//!
//! The byte-I/O contract is [`stwo_keccak::relations::HashIoRelation`] verbatim:
//! `(stream_id, byte_pos, byte)`. We re-export it (rather than declaring a second
//! structurally-identical `relation!`) so the mldsa consumer/producer components
//! and the keccak sponge instances draw and combine against **the same relation
//! type**. A separate `relation!` would have separate `LookupElements` and
//! would not cancel across the module boundary.
//!
//! Sponge sign convention (from `stwo_keccak::sponge_v`): the sponge **consumes
//! (−)** each absorb byte and **yields (+)** each squeeze byte. Therefore an
//! absorb-byte producer yields (+) and a squeeze-byte consumer requires (−):
//! - [`STREAM_ID_CTILDE_ABSORB`] — decomp's 768 `w1Encode(w1')` bytes yielded (+),
//!   the c̃-chain sponge consumes (−) at a `µ_len`-offset absorb position.
//! - [`STREAM_ID_SIB_SQUEEZE`] — the SampleInBall-chain sponge yields (+) each
//!   squeeze byte; the FSM consumes (−).
//! - Private message-rep (µ) / c̃-seam stream ids are declared in
//!   [`crate::statement`] (composition-layer namespacing), disjoint from these
//!   two. Public messages use a verifier-native µ constant instead.
//!
//! ### Permutation identifiers
//!
//! [`stwo_keccak::sponge_v::JobList`] assigns one global sequence of
//! permutation identifiers to the concatenated job list. This prevents chains
//! from sharing a [`stwo_keccak::relations::KeccakStateRelation`] identifier.

use stwo_constraint_framework::relation;

/// `(w_bind_id, w)`.
pub const WCELL_ARITY: usize = 2;
relation!(WCellRelation, WCELL_ARITY);

/// `(c_bind_id, c)`.
pub const CCELL_ARITY: usize = 2;
relation!(CCellRelation, CCELL_ARITY);

/// `(rho_byte_index, byte)` — the private `rho` cells committed by ExpandA
/// and consumed by the private MSO device-key binding.
pub const RHO_CELL_ARITY: usize = 2;
relation!(RhoCellRelation, RHO_CELL_ARITY);

/// `(poly, coefficient_index, lo9, hi1)` — one private `t1` coefficient.
///
/// The public-key encoder splits each canonical ten-bit ML-DSA `t1`
/// coefficient as `coefficient = lo9 + 2^9 * hi1`. It yields the tuple and
/// the private-key evaluation component consumes it.
pub const T1_CELL_ARITY: usize = 4;
relation!(T1CellRelation, T1_CELL_ARITY);

/// `(matrix_poly, ntt_stage, coefficient_index, limb0, limb1)`.
///
/// ExpandA yields accepted coefficients at stage zero. The inverse-NTT
/// component consumes those cells. Each NTT stage uses the same tuple shape.
/// C7b: the value limbs are a 12/11-bit split (`limb0 < 4096`,
/// `limb1 < 2048`), base 4096 -- not the earlier 8/8/7-bit byte split.
pub const NTT_CELL_ARITY: usize = 5;
relation!(NttCellRelation, NTT_CELL_ARITY);

/// Shared handles for the public-key and inverse-NTT components.
pub type SharedRhoCellRelation = air_core::relations::SharedRelation<RhoCellRelation>;
pub type SharedT1CellRelation = air_core::relations::SharedRelation<T1CellRelation>;
pub type SharedNttCellRelation = air_core::relations::SharedRelation<NttCellRelation>;

/// `(field_id, byte_index, byte)` — the message-byte relation for `M`'s bytes.
///
/// The `stwo-sha256` `FieldExposure` producer
/// ([`stwo_sha256::field_exposure`]) already yields arbitrary multi-block
/// `(field_id, byte_index, byte)` windows, each byte range-checked to `[0,256)`
/// in the AIR. `MsgLinkRelation` uses the same tuple shape.
/// [`crate::msglink`] provides an enabled public-byte producer for standalone
/// proofs.
pub const MSGLINK_ARITY: usize = 3;
relation!(MsgLinkRelation, MSGLINK_ARITY);

/// `(stream_id, byte_pos, byte)` — re-export of the stwo-keccak byte-I/O
/// contract. Using keccak's type (not a fresh `relation!`) is what lets a mldsa
/// consumer/producer balance against the sponge's yields/consumes.
pub use stwo_keccak::relations::HashIoRelation;

/// Byte arity of [`HashIoRelation`] (mirrors [`stwo_keccak::relations::HASH_IO_ARITY`]).
pub const HASH_IO_ARITY: usize = stwo_keccak::relations::HASH_IO_ARITY;

/// Stream id for the `c̃`-absorb bytes decomp emits (`w1Encode(w1')`, 768 bytes),
/// yielded (+) by decomp and consumed (−) by the c̃-chain sponge absorb.
pub const STREAM_ID_CTILDE_ABSORB: u32 = 0;

/// Stream id for the SampleInBall squeeze stream: yielded (+) by the SIB-chain
/// sponge, consumed (−) by the FSM.
pub const STREAM_ID_SIB_SQUEEZE: u32 = 1;
