//! Cross-component LogUp binding relations shared by `coeffs` (yield side),
//! `decomp` / `sampleinball` (consume side), the `msglink` message-byte producer,
//! and the remaining stwo-keccak sponge jobs (M6 composed statement). Kept in
//! one place so the composed `MlDsaAir` and the standalone M5 tests wire the
//! SAME relation instances.
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
//! `c_bind_id = m` keys the `N` challenge coefficients. Both cells are the
//! coeffs `recomp_cell` (w) / `digit[0]` (c) of the matching group (worksheet §3.4).
//!
//! ### `HashIo` — re-exported from stwo-keccak (single source of truth)
//!
//! The byte-I/O contract is [`stwo_keccak::relations::HashIoRelation`] verbatim:
//! `(stream_id, byte_pos, byte)`. We re-export it (rather than declaring a second
//! structurally-identical `relation!`) so the mldsa consumer/producer components
//! and the keccak sponge instances draw and combine against **the same relation
//! type** — a distinct `relation!` would have distinct `LookupElements` and never
//! cancel across the module boundary.
//!
//! Sponge sign convention (from `stwo_keccak::sponge`): the sponge **consumes
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
//! ### `perm_id` namespacing (M3 carry-forward)
//!
//! Each sponge instance is assigned a disjoint `perm_id_base` so their
//! Keccak-f[1600] permutation chains never collide on the shared
//! [`stwo_keccak::relations::KeccakStateRelation`]. The composition owns this;
//! see [`crate::statement::PermIdPlan`].

use stwo_constraint_framework::relation;

/// `(w_bind_id, w)`.
pub const WCELL_ARITY: usize = 2;
relation!(WCellRelation, WCELL_ARITY);

/// `(c_bind_id, c)`.
pub const CCELL_ARITY: usize = 2;
relation!(CCellRelation, CCELL_ARITY);

/// `(rho_byte_index, byte)` — the private `rho` cells committed by ExpandA
/// and consumed by the eventual private public-key binding.
pub const RHO_CELL_ARITY: usize = 2;
relation!(RhoCellRelation, RHO_CELL_ARITY);

/// `(matrix_poly, ntt_stage, coefficient_index, limb0, limb1, limb2)`.
///
/// ExpandA yields accepted coefficients at stage zero. The inverse-NTT
/// component consumes those cells and reuses the same tuple shape for later
/// stages.
pub const NTT_CELL_ARITY: usize = 6;
relation!(NttCellRelation, NTT_CELL_ARITY);

/// Shared handles published by ExpandA for the later public-key and inverse-NTT
/// components.
pub type SharedRhoCellRelation = air_core::relations::SharedRelation<RhoCellRelation>;
pub type SharedNttCellRelation = air_core::relations::SharedRelation<NttCellRelation>;

/// `(field_id, byte_index, byte)` — the message-byte relation for `M`'s bytes.
///
/// REUSE NOTE (M6 decision): stwo-sha256's `FieldExposure` producer
/// ([`stwo_sha256::field_exposure`]) already yields arbitrary multi-block
/// `(field_id, byte_index, byte)` windows, each byte range-checked to `[0,256)`
/// in-AIR. `MsgLinkRelation` deliberately mirrors that exact
/// `(field_id, byte_index, byte)` shape so M7 can drop the SHA-side producer in
/// as the yield source with no relation change. For M6-standalone,
/// [`crate::msglink`] provides an enabler-gated public-byte producer with the
/// same shape and range-check (the "M7 swap point").
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
