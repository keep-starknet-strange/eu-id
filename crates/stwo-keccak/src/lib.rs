//! `Keccak-f[1600]` and SHAKE AIR over stwo/M31.
//!
//! The crate exposes `KeccakStateRelation` for permutation chaining and
//! `HashIoRelation` for byte-stream input and output.
// Keccak's theta/rho/pi/chi steps index several fixed-size lane arrays by a
// shared `(x, y)` coordinate; explicit range loops mirror the FIPS-202 spec and
// read more clearly than zipped iterators here. Byte-limb block copies likewise
// stay as indexed loops for parity with the spec's little-endian layout.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

pub mod constants;
pub mod layered_gkr;
pub mod relations;
pub mod service;
pub mod sponge;
pub mod sponge_v;
pub mod tables;
pub mod tables_air;
pub mod utils;
