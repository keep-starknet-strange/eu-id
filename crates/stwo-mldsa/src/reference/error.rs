//! Error and reject-reason types for the ML-DSA reference verifier.

/// A hard decoding/structural error: the input is malformed and cannot be
/// interpreted as an ML-DSA public key or signature. Distinct from a
/// *cryptographic* rejection (a well-formed but non-verifying signature), which
/// is carried by [`RejectReason`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MlDsaError {
    /// Public key was not exactly `PK_BYTES` long.
    BadPublicKeyLength {
        /// Expected length (`PK_BYTES`).
        expected: usize,
        /// Actual length received.
        got: usize,
    },
    /// Signature was not exactly `SIG_BYTES` long.
    BadSignatureLength {
        /// Expected length (`SIG_BYTES`).
        expected: usize,
        /// Actual length received.
        got: usize,
    },
    /// The hint `h` failed `HintBitUnpack` validation (Algorithm 21):
    /// non-increasing indices within a polynomial, a decreasing end pointer, or
    /// non-zero padding.
    MalformedHint,
    /// A supplied signing context exceeded 255 bytes (Algorithm 3 rejects).
    ContextTooLong {
        /// The offending context length.
        got: usize,
    },
    /// The circuit profile's fixed SampleInBall squeeze resource ended before
    /// all challenge positions were placed.
    SampleInBallExhausted {
        /// Challenge positions placed before exhaustion.
        accepted: usize,
        /// Challenge positions required (`τ`).
        required: usize,
        /// Squeeze bytes consumed before exhaustion.
        squeeze_bytes: usize,
    },
}

impl core::fmt::Display for MlDsaError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BadPublicKeyLength { expected, got } => {
                write!(f, "public key length {got} != expected {expected}")
            }
            Self::BadSignatureLength { expected, got } => {
                write!(f, "signature length {got} != expected {expected}")
            }
            Self::MalformedHint => write!(f, "hint failed HintBitUnpack validation"),
            Self::ContextTooLong { got } => write!(f, "context length {got} exceeds 255"),
            Self::SampleInBallExhausted {
                accepted,
                required,
                squeeze_bytes,
            } => write!(
                f,
                "SampleInBall accepted {accepted} of {required} placements within {squeeze_bytes} bytes"
            ),
        }
    }
}

impl std::error::Error for MlDsaError {}

/// Why a *well-formed* signature was accepted or rejected. Populated in the
/// [`super::verify::VerifyTrace`] so callers (and the witness generator) see the
/// precise gate that decided the verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RejectReason {
    /// The signature verified: `c̃ == c̃'` and the `z` norm bound held.
    Accepted,
    /// `‖z‖_∞ ≥ γ1 − β` (Algorithm 8, step: `‖z‖_∞ < γ1 − β`).
    ZNormOutOfBound,
    /// The recomputed commitment hash disagreed: `c̃ != c̃'`.
    CommitmentMismatch,
}
