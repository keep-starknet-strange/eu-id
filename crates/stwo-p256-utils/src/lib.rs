//! Verification utilities for the P-256 STARK AIR.
//!
//! This crate contains the compile-time / verification-time artifacts that
//! the AIR depends on but that are not runtime prover code:
//!
//! - [`constants`]: limb-width / M31 / curve constants shared across the workspace.
//! - [`headroom`]: per-equation M31 headroom audit infrastructure. Decides
//!   whether each arithmetic row family fits centered M31 directly or requires
//!   a split. Self-declared blocker per the AIR spec.
//! - [`solinas`]: Solinas reduction matrix for `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`.
//! - [`carry_range`]: derives the `SignedCarryRange` bound per equation family
//!   from the headroom audit.
//! - [`rcb_analyzer`]: symbolic simulator for RCB Algorithm 5 (mixed add, a=−3)
//!   and Algorithm 6 (doubling, a=−3). Produces per-line limb coefficient bounds
//!   used by the headroom audit.
//! - [`selector_tables`]: generators and cross-checks for the Selector16Decode,
//!   FinalSelector, and Selector4x4 preprocessed tables.
//! - [`curve_limbs`]: limb-decomposed P-256 curve constants (p, n, a, b, G,
//!   [2]G, [3]G) precomputed once and verified.
//!
//! The crate intentionally has no dependency on `stwo` or any prover library,
//! so its tests run in seconds and its outputs can be consumed by `build.rs`
//! to emit Rust constants into the main AIR crate.

pub mod carry_range;
pub mod constants;
pub mod curve_limbs;
pub mod headroom;
pub mod rcb_analyzer;
pub mod selector_tables;
pub mod solinas;
