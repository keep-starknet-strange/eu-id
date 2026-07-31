//! FIPS 204 ML-DSA-65 verification reference with exposed internals.
//!
//! This module implements verification but not signing.
//! [`verify::VerifyTrace`] exposes values used by the witness generator. Each
//! sponge invocation records its absorb and squeeze byte streams.

pub mod decompose;
pub mod encoding;
pub mod error;
pub mod expand_a;
pub mod ntt;
pub mod sample_in_ball;
pub mod sponge;
pub mod verify;

pub use error::{MlDsaError, RejectReason};
pub use verify::{verify, verify_internals, verify_internals_with_context, VerifyTrace};
