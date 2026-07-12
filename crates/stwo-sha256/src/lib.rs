//! SHA-256 AIR over the M31 field for the eu-id credential pipeline.
//!
//! Two SHA-256 invocations show up inside the credential proof: the
//! `IssuerSignedItem` digest committed by the `MobileSecurityObject`, and the
//! COSE `Sig_structure` digest that is the `z` input to ECDSA verification.
//! Both can be multi-block; both must expose the digest as M31 columns so the
//! integration layer can LogUp-bind them.
//!
//! Module layout (see `docs/research/sha256-air-design.md` for the design):
//!
//! - [`constants`] — round constants `K[0..63]` and initial hash value `IV`.
//! - [`partitions`] — the validated bit-index partitions for `Σ0`/`Σ1`/`σ0`/`σ1`.
//! - [`types`] — 32-bit-word ↔ M31 limb representation, working state, block
//!   bytes, and the witness records the trace generator consumes.
//! - [`headroom`] — M31 headroom audit for every mod-2³² limb-add family the
//!   AIR emits (schedule recurrence, `T1`, round short adds, finalization),
//!   plus the per-family carry-range bounds (`RANGE_2`, `RANGE_4`, `RANGE_5`)
//!   that downstream lookup wiring consumes. Mirrors the
//!   `stwo-p256-utils::headroom` API for the eventual shared-crate
//!   migration.
//! - [`native`] — pure SHA-256 reference (padding, schedule, compression,
//!   multi-block) tested against the `sha2` crate. The out-of-circuit oracle.
//! - [`relations`] — LogUp relation tags: `Σ`/`σ` decode (8), packed Maj/Ch
//!   (2), chunk-wise `xor_8` (1), split-and-pack (8), and `Range_k`
//!   (`Range_2`/`Range_4`/`Range_5`/`Range_16`, 4) — bundled as
//!   `Sha256Relations`.
//! - [`tables`] — preprocessed lookup-table content: `Σ`/`σ` decode tables,
//!   packed `Maj`/`Ch` table, `xor_8` table, split-and-pack tables.
//! - [`tables_local`] — local fallback for the workspace-shared range-check
//!   tables (`Range_2`, `Range_4`, `Range_5`, `Range_16`). Shipped until the
//!   ECDSA stream's `stwo-p256-utils` crate is on `main`; mirrors that
//!   crate's API so migration is a one-import swap (see the module-level
//!   docs for the upstream-context survey and API-shape rationale).
//! - [`field_exposure`] — optional spec for exposing credential-field byte
//!   windows of the preimage as a LogUp provider, the
//!   producer half of the SHA→predicate `CRED_FIELD ↔ PREDICATE_INPUT` binding.
//! - [`witness`] — full witness emitter — every value the trace stores per row.
//! - [`trace`] — column layout and materialisation from a witness.
//! - [`multiplicities`] — per-row LogUp multiplicity vectors keyed against
//!   every preprocessed lookup table the AIR consumes.
//! - [`preprocessed`] — `CircleEvaluation`s for every preprocessed lookup
//!   table column (tree[0] of the proof's commitment scheme).
//! - [`components`] — producer-side `FrameworkEval` components, one per
//!   preprocessed lookup table.
//! - [`constraints`] — `FrameworkEval` AIR: linear constraints (IV binding,
//!   mod-2³² adds, schedule recurrence, multi-block chaining, padding) plus the
//!   lookup-relation hooks for the `Σ`/`σ`/`Maj`/`Ch`/`xor`/`Range_k` tables.
//! - [`interaction`] — LogUp interaction-trace generator + `InteractionClaim`
//!   aggregator across the consumer and every producer component.
//! - [`stark`] — prover/verifier entry points for the standalone component.

pub mod air;
pub mod components;
pub mod constants;
pub mod constraints;
pub mod field_exposure;
#[cfg(feature = "gkr-spike")]
pub mod gkr_lookups;
#[cfg(feature = "gkr-spike")]
pub mod gkr_spike;
pub mod headroom;
pub mod interaction;
pub mod multiplicities;
pub mod native;
pub mod partitions;
pub mod preprocessed;
pub mod relations;
pub mod shared_tables;
pub mod slots;
pub mod stark;
pub mod tables;
pub mod tables_local;
pub mod trace;
pub mod types;
pub mod witness;
