//! Prover and verifier entry points for the standalone SHA-256 component.
//!
//! This is the wiring stub. The trace generator ([`crate::trace`]), the AIR
//! evaluator ([`crate::constraints::Sha256Eval`]), the witness emitter
//! ([`crate::witness`]) and the preprocessed table generators
//! ([`crate::tables`]) are all in place — what remains is the LogUp /
//! range-check plumbing for the `Σ`/`σ`/`Maj`/`Ch`/`xor_8` relations, which
//! must reuse the shared foundation from the ECDSA stream (see §9.4 of the
//! validated design).
//!
//! Until that foundation lands, the prove/verify entry points return
//! [`Sha256ProveError::AwaitingSharedFoundation`] / `verify` likewise —
//! callers can integrate against this surface and the error becomes "ready"
//! once the lookup wiring drops in. The matching pattern in
//! `crate::stwo_p256::stark` is `todo!()`; we prefer an explicit
//! `Result::Err` so downstream integration code can compile and depend on
//! this API now.

use crate::constants::DIGEST_BYTES;
use crate::trace::Layout;
use crate::types::{Digest, Sha256Witness};
use crate::witness::compute_sha256_witness;

/// Tuning knobs for the prover. Defaults pick a sensible starting point;
/// the laptop benchmark (the post-week-2 go/no-go gate in the roadmap)
/// is what pins the final values.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// `log2` of the number of trace rows. Each row is one padded block.
    /// `log_n_rows = trace::min_log_size(witness.blocks.len())` is the
    /// minimum legal value; pass a larger value to absorb future blocks
    /// into the same component without re-generating preprocessed tables.
    pub log_n_rows: u32,
    /// Group width `W` for the packed `Maj`/`Ch` table. `6` minimises
    /// preprocessed memory for our partitions (with one-bit padding for
    /// the smallest groups); `7` is the minimum that needs no padding.
    /// Pinned by the mobile benchmark.
    pub group_width: u32,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self {
            log_n_rows: 4,
            group_width: 6,
        }
    }
}

/// A STARK proof that a private message hashes to the public `digest`.
///
/// The `proof` field holds the underlying Stwo `StarkProof<…>` once the
/// LogUp wiring is in place. We expose the public-input surface (`digest`)
/// independently so the integration stream can bind it via LogUp even if
/// the proof bytes themselves change shape.
#[derive(Clone, Debug)]
pub struct Sha256Proof {
    /// The 32-byte digest that the prover claims the (private) message
    /// hashes to. Exposed as a public input.
    pub digest: [u8; DIGEST_BYTES],
    /// Number of blocks in the padded preimage.
    pub n_blocks: usize,
    /// `log2` of the trace's row count.
    pub log_n_rows: u32,
    // The underlying Stwo proof bytes drop in here once the wiring lands.
    // pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

/// Errors that can be returned by [`prove_sha256`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256ProveError {
    /// Caller asked for a row count below what the message requires.
    TraceTooSmall {
        requested_log_n_rows: u32,
        required_log_n_rows: u32,
    },
    /// The lookup-relation wiring (and the shared range/LogUp helpers it
    /// reuses) is not in place yet. Trace generation succeeds; the prover
    /// stops short of the LogUp setup.
    AwaitingSharedFoundation,
}

impl core::fmt::Display for Sha256ProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::TraceTooSmall { requested_log_n_rows, required_log_n_rows } => write!(
                f,
                "log_n_rows = {requested_log_n_rows} too small; this message requires log_n_rows ≥ {required_log_n_rows}"
            ),
            Self::AwaitingSharedFoundation => write!(
                f,
                "LogUp / range-check foundation (shared with the ECDSA stream) is not yet wired"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Sha256ProveError {}

/// Errors that can be returned by [`verify_sha256_proof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256VerifyError {
    /// The Stwo verifier rejected the proof. The wrapped string is its
    /// error message; this variant gets a concrete type once the wiring
    /// lands and we can import the Stwo error directly.
    StarkRejected(String),
    /// The lookup-relation wiring is not in place — see
    /// [`Sha256ProveError::AwaitingSharedFoundation`].
    AwaitingSharedFoundation,
}

impl core::fmt::Display for Sha256VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StarkRejected(msg) => write!(f, "Stwo verifier rejected proof: {msg}"),
            Self::AwaitingSharedFoundation => write!(
                f,
                "LogUp / range-check foundation (shared with the ECDSA stream) is not yet wired"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Sha256VerifyError {}

/// Generate the witness, the trace, and (once the foundation lands) the
/// underlying STARK proof.
///
/// On success returns the public `Sha256Proof`. While the shared LogUp
/// foundation is missing this returns [`Sha256ProveError::AwaitingSharedFoundation`];
/// callers that need the digest the prover *would* have produced can read it
/// from [`native_digest`] (or [`public_inputs_for`]) in the meantime.
pub fn prove_sha256(
    message: &[u8],
    config: &ProverConfig,
) -> Result<Sha256Proof, Sha256ProveError> {
    let witness = compute_sha256_witness(message);
    let required = crate::trace::min_log_size(witness.blocks.len());
    if config.log_n_rows < required {
        return Err(Sha256ProveError::TraceTooSmall {
            requested_log_n_rows: config.log_n_rows,
            required_log_n_rows: required,
        });
    }

    // Generate the trace; this is the part that is *complete*. We materialise
    // it so the prover-readiness signal (no panics, correct shape) is real.
    let trace = crate::trace::generate_trace(&witness, config.log_n_rows);
    debug_assert_eq!(trace.len(), Layout::TOTAL_COLS);

    // The next step is the LogUp interaction trace — the shared
    // range-check / `Σ`/`σ`/`Maj`/`Ch`/`xor_8` plumbing. Once the shared
    // foundation lands this is where we:
    //
    //   1. Build the preprocessed-table commitment from `crate::tables`.
    //   2. Draw `InteractionElements` from the channel.
    //   3. Generate the interaction trace from the lookup data the AIR
    //      evaluator emits via `eval.add_to_relation(...)`.
    //   4. Commit + run the Stwo prover with `Sha256Eval` as the component.
    //
    // Today, we honestly surface the missing step rather than fabricate a
    // half-soundness.
    Err(Sha256ProveError::AwaitingSharedFoundation)
}

/// Verify a `Sha256Proof`. Mirrors [`prove_sha256`]'s blocked state.
pub fn verify_sha256_proof(_proof: &Sha256Proof) -> Result<(), Sha256VerifyError> {
    Err(Sha256VerifyError::AwaitingSharedFoundation)
}

/// Native (out-of-circuit) digest. Useful for integration tests and as the
/// claimed public input the prover stamps into a `Sha256Proof`.
pub fn native_digest(message: &[u8]) -> Digest {
    crate::native::hash(message)
}

/// Convenience: derive the public input shape (digest + block count) the
/// prover *would* commit to, without running the (currently blocked)
/// prover. Used by the integration stream to assemble its Big-AIR public
/// input contract.
pub fn public_inputs_for(message: &[u8]) -> Sha256PublicInputs {
    let padded = crate::native::pad_message(message);
    let n_blocks = padded.len() / crate::constants::BLOCK_BYTES;
    Sha256PublicInputs {
        digest: native_digest(message).0,
        n_blocks,
    }
}

/// Public-input contract for the SHA-256 component.
///
/// The digest is the only output bound across components by LogUp
/// (interface contract item 1 in the validated design). `n_blocks` is
/// surfaced so the integration stream can size its multi-block witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sha256PublicInputs {
    pub digest: [u8; DIGEST_BYTES],
    pub n_blocks: usize,
}

/// Helper consumed by integration tests: pad, witness, trace — but don't
/// attempt the (blocked) prover stage. Returns the witness so a caller can
/// hand-inspect intermediate values.
pub fn build_trace_for(
    message: &[u8],
    config: &ProverConfig,
) -> Result<(Sha256Witness, Vec<Vec<stwo::core::fields::m31::BaseField>>), Sha256ProveError> {
    let witness = compute_sha256_witness(message);
    let required = crate::trace::min_log_size(witness.blocks.len());
    if config.log_n_rows < required {
        return Err(Sha256ProveError::TraceTooSmall {
            requested_log_n_rows: config.log_n_rows,
            required_log_n_rows: required,
        });
    }
    let trace = crate::trace::generate_trace(&witness, config.log_n_rows);
    Ok((witness, trace))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prove_returns_awaiting_foundation_today() {
        let config = ProverConfig {
            log_n_rows: 4,
            ..ProverConfig::default()
        };
        let err = prove_sha256(b"abc", &config).unwrap_err();
        assert_eq!(err, Sha256ProveError::AwaitingSharedFoundation);
    }

    #[test]
    fn prove_rejects_too_small_trace() {
        // 5000-byte message → many blocks; log_n_rows = 4 (16 rows) is too small.
        let msg = vec![0u8; 5000];
        let config = ProverConfig {
            log_n_rows: 4,
            ..ProverConfig::default()
        };
        match prove_sha256(&msg, &config) {
            Err(Sha256ProveError::TraceTooSmall { .. }) => {}
            other => panic!("expected TraceTooSmall, got {other:?}"),
        }
    }

    #[test]
    fn build_trace_returns_a_full_trace() {
        let msg = b"the quick brown fox jumps over the lazy dog";
        let config = ProverConfig::default();
        let (witness, trace) = build_trace_for(msg, &config).unwrap();
        assert_eq!(trace.len(), Layout::TOTAL_COLS);
        // And the digest we'd stamp into Sha256Proof matches sha2.
        let pubs = public_inputs_for(msg);
        assert_eq!(pubs.digest, native_digest(msg).0);
        assert_eq!(pubs.n_blocks, witness.blocks.len());
    }

    #[test]
    fn public_inputs_for_empty_and_boundary() {
        // 0 bytes → 1 block.
        let pubs = public_inputs_for(b"");
        assert_eq!(pubs.n_blocks, 1);

        // Exactly 56 bytes → 2 blocks (length field doesn't fit with 0x80).
        let pubs = public_inputs_for(&[0u8; 56]);
        assert_eq!(pubs.n_blocks, 2);

        // 55 bytes → 1 block.
        let pubs = public_inputs_for(&[0u8; 55]);
        assert_eq!(pubs.n_blocks, 1);
    }

    #[test]
    fn verify_returns_awaiting_foundation_today() {
        let proof = Sha256Proof {
            digest: [0u8; 32],
            n_blocks: 1,
            log_n_rows: 4,
        };
        assert_eq!(
            verify_sha256_proof(&proof).unwrap_err(),
            Sha256VerifyError::AwaitingSharedFoundation
        );
    }
}
