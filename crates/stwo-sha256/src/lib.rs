//! SHA-256 AIR over the M31 field for the eu-id credential pipeline.
//!
//! The credential proof uses SHA-256 for issuer item digests and the COSE
//! `Sig_structure` digest. Both inputs can have multiple blocks. Shared LogUp
//! relations bind selected bytes and digest values to consumer components.
//!
//! The main implementation modules are:
//!
//! - [`native`], [`witness`], and [`trace`] construct the reference values and
//!   committed trace.
//! - [`constraints`] checks SHA rounds, schedule, chaining, and FIPS padding.
//! - [`tables_local`], [`components`], [`multiplicities`], and [`interaction`]
//!   implement the active range checks and LogUp balance.
//! - [`field_exposure`] and [`relations`] define composition interfaces.
//! - [`air`] and [`stark`] provide module and standalone proof entry points.
//!
//! See `docs/research/sha256-air-design.md` for the active design and security
//! boundary.

pub mod air;
pub mod claim_mask;
pub mod components;
pub mod constants;
pub mod constraints;
pub mod field_exposure;
pub mod headroom;
pub mod interaction;
pub mod multiplicities;
pub mod native;
pub mod preprocessed;
pub mod relations;
pub mod shared_tables;
pub mod stark;
pub mod tables_local;
pub mod trace;
pub mod types;
pub mod witness;
