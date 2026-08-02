//! In-circuit ML-DSA-44 and ML-DSA-65 (FIPS 204) verification over stwo/M31.
//!
//! This crate contains the native reference and witness path and the AIR
//! components for a composed ML-DSA statement:
//!
//! - [`constants`]: maximum-shape ML-DSA-65 parameters, pinned with citations.
//! - [`reference`]: from-scratch ML-DSA verification with exposed internals,
//!   cross-checked against RustCrypto and NIST ACVP vectors.
//! - [`types`]: full prover/native input plus the keyless hosted verifier input.
//! - [`witness`]: [`witness::generate_witness`], which materializes the values
//!   committed by the integer-lift, decomp/hint, SampleInBall, and SHAKE glue.
//! - [`private_key_eval`]: inverse-NTT, packed-`t1`, and complete private-key
//!   folded-identity AIR.
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
pub mod private_key_eval;
pub mod profile;
pub mod proof;
pub mod reference;
pub mod sampleinball;
pub mod sponge_link;
pub mod statement;
pub mod types;
pub mod verifier_native;
pub mod witness;

pub use reference::{verify, verify_internals, MlDsaError, RejectReason, VerifyTrace};

/// Re-export the Keccak service types used by the hosted API.
pub use types::{MlDsaPrivateKeyPublicInput, MlDsaVerifyInput};
pub use witness::{generate_witness, MlDsaWitness, WitnessError};
