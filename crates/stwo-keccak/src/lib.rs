//! Keccak-f[1600] and SHAKE AIR over stwo/M31.
//!
//! ## Interface
//!
//! The crate exposes `KeccakStateRelation` for permutation chaining and
//! `HashIoRelation` for byte-stream input and output.
#![feature(iter_array_chunks)]
#![feature(raw_slice_split)]
// Keccak's theta/rho/pi/chi steps index several fixed-size lane arrays by a
// shared `(x, y)` coordinate. Explicit range loops mirror the FIPS-202 spec
// and read more clearly than zipped iterators here. Byte-limb block copies
// stay as indexed loops for parity with the spec's little-endian layout.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

pub mod carrier;
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
