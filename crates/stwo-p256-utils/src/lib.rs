//! Verification utilities for the P-256 STARK AIR.
//!
//! - [`constants`]: limb-width constants shared with the AIR.
//! - [`solinas`]: Solinas reduction matrix for
//!   `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`.
//!
//! The crate intentionally has no dependency on `stwo` or any prover library.

pub mod constants;
pub mod scalar_arithmetic;
pub mod solinas;
