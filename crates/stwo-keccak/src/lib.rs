//! Keccak-f[1600] / SHAKE-256 AIR over stwo/M31, derived from falcon-air's
//! `crates/shake256` with redesigned rotation tables and a variable-length
//! sponge.
//!
//! Populated by the M3 workstream; exposes `KeccakStateRelation` (permutation
//! chaining) and `HashIoRelation` (byte-stream I/O) to consumers.
#![feature(iter_array_chunks)]
#![feature(raw_slice_split)]
// Keccak's theta/rho/pi/chi steps index several fixed-size lane arrays by a
// shared `(x, y)` coordinate; explicit range loops mirror the FIPS-202 spec and
// read more clearly than zipped iterators here. Byte-limb block copies likewise
// stay as indexed loops for parity with the spec's little-endian layout.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

pub mod constants;
pub mod keccak;
pub mod keccak_round;
pub mod relations;
pub mod round_gkr;
pub mod service;
pub mod sponge;
pub mod sponge_v;
pub mod tables;
pub mod tables_air;
pub mod utils;
