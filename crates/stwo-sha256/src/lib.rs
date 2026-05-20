//! SHA-256 AIR over the M31 field for the eu-id credential pipeline.
//!
//! Two SHA-256 invocations show up inside the credential proof: the
//! `IssuerSignedItem` digest committed by the `MobileSecurityObject`, and the
//! COSE `Sig_structure` digest that is the `z` input to ECDSA verification.
//! Both can be multi-block; both must expose the digest as M31 columns so the
//! integration layer can LogUp-bind them.
//!
//! Module layout (see `research/sha256-air-design.md` for the design):
//!
//! - [`constants`] — round constants `K[0..63]` and initial hash value `IV`.
//! - [`partitions`] — the validated bit-index partitions for `Σ0`/`Σ1`/`σ0`/`σ1`.
//! - [`types`] — 32-bit-word ↔ M31 limb representation, working state, block
//!   bytes, and the witness records the trace generator consumes.
//! - [`native`] — pure SHA-256 reference (padding, schedule, compression,
//!   multi-block) tested against the `sha2` crate. The out-of-circuit oracle.
//! - [`tables`] — preprocessed lookup-table content: `Σ`/`σ` decode tables,
//!   packed `Maj`/`Ch` table, `xor_8` table, split-and-pack tables.
//! - [`witness`] — full witness emitter — every value the trace stores per row.
//! - [`trace`] — column layout and materialisation from a witness.
//! - [`constraints`] — `FrameworkEval` AIR: linear constraints (IV binding,
//!   mod-2³² adds, schedule recurrence, multi-block chaining, padding) plus the
//!   lookup-relation hooks for the `Σ`/`σ`/`Maj`/`Ch`/`xor` tables.
//! - [`stark`] — prover/verifier entry points for the standalone component.

pub mod constants;
pub mod constraints;
pub mod native;
pub mod partitions;
pub mod stark;
pub mod tables;
pub mod trace;
pub mod types;
pub mod witness;
