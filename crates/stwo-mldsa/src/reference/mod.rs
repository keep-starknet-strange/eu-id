//! From-scratch FIPS 204 ML-DSA-65 **verification** reference with exposed
//! internals.
//!
//! This is the native (out-of-circuit) ground truth for the whole ML-DSA
//! integration effort. It implements verification only (no signing);
//! signatures for tests come from the oracle crate.
//!
//! Every intermediate the future witness generator (M2+) needs is exposed on
//! [`verify::VerifyTrace`], and every sponge invocation records its absorb /
//! squeeze byte stream ([`sponge::SpongeTranscript`]).

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
