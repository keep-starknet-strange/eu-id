//! In-circuit ML-DSA-65 (FIPS 204) issuer-signature verification over stwo/M31.
//!
//! Design basis: `tasks/parity/S5-mldsa-air-design.md`; implementation plan
//! milestones M1..M8.
//!
//! **Milestone M1 (this crate, so far)** is the native reference layer only —
//! no AIR/circuit code yet:
//! - [`constants`]: every FIPS 204 ML-DSA-65 parameter, pinned with citations.
//! - [`reference`]: a from-scratch FIPS 204 ML-DSA-65 *verify* implementation
//!   with exposed internals ([`reference::verify::VerifyTrace`]), cross-checked
//!   against the RustCrypto `ml-dsa` oracle and NIST ACVP vectors in `tests/`.
//!
//! **Milestone M2** adds the native (still no-AIR) proving support:
//! - [`types`]: [`types::MlDsaVerifyInput`], the serializable public/private
//!   verification input mirroring `stwo-p256`'s `EcdsaVerifyInput`.
//! - [`witness`]: [`witness::generate_witness`], which runs the M1 reference and
//!   materializes every value the S5a integer-lift AIR (M4/M5) commits — the
//!   ℤ[X] products, quotients, balanced base-2^9 digits, per-limb carries, and
//!   decomp/hint/SHAKE witnesses — per `tasks/parity/S5a-integer-lift-worksheet.md`.

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
#[doc(hidden)]
pub mod toy_horner; // M4 de-risking spike; removed once mldsa_coeffs lands.
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
