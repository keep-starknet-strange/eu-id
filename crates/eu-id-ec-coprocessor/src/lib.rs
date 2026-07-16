//! Native F_p256 coprocessor primitives for the S4-lite track.

pub mod channel;
pub mod circle_fft;
pub mod circuit;
pub mod ecdsa;
pub mod field;
#[cfg(test)]
mod gates;
pub mod ligero;
pub mod mac;
pub mod merkle;
pub mod mle;
pub mod rs;
pub mod sumcheck;

pub use channel::{CoprocessorChannel, TranscriptSeed};
pub use circuit::{Circuit, CircuitError, Layer, QuadTerm};
pub use field::Fp;
pub use mle::{eq_eval, Mle, MleError};
