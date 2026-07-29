//! In-circuit ML-DSA-65 (FIPS 204) issuer-signature verification over stwo/M31.
//!
//! Design basis: `tasks/parity/S5-mldsa-air-design.md`.
//!
//! This crate now contains both the native reference/witness path and the AIR
//! components used by the composed ML-DSA statement:
//!
//! - [`constants`]: FIPS 204 ML-DSA-65 parameters, pinned with citations.
//! - [`reference`]: from-scratch ML-DSA-65 verification with exposed internals,
//!   cross-checked against RustCrypto and NIST ACVP vectors.
//! - [`types`]: [`types::MlDsaVerifyInput`], the serializable verification input.
//! - [`witness`]: [`witness::generate_witness`], which materializes the values
//!   committed by the integer-lift, decomp/hint, SampleInBall, and SHAKE glue.
//! - [`coeffs`], [`decomp`], [`sampleinball`], [`sponge_link`], [`msglink`],
//!   and [`statement`]: the composed AIR/proof surface used by the host circuit.

pub mod air_util;
pub mod balancer;
pub mod binding;
pub mod coeffs;
pub mod constants;
pub mod decomp;
pub mod expand_a;
pub mod msglink;
pub mod proof;
pub mod reference;
pub mod sampleinball;
pub mod sponge_link;
pub mod statement;
pub mod types;
pub mod verifier_native;
pub mod witness;

pub use reference::{verify, verify_internals, MlDsaError, RejectReason, VerifyTrace};

/// Re-export: the keccak-service types appear in this crate's public hosted
/// API (`MlDsaProver::hosted` takes a `SharedKeccakRelations`; hosts build the
/// proof-wide `KeccakServiceProver`/`Verifier`), so hosts get the exact same
/// crate version without a separate dependency edge.
pub use stwo_keccak;
pub use types::MlDsaVerifyInput;
pub use witness::{generate_witness, MlDsaWitness, WitnessError};
