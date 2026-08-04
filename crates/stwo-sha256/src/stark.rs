//! Prover and verifier entry points for the standalone SHA-256 component.
//!
//! This module connects the range tables, round selectors, base trace, and
//! interaction traces. It generates a Stwo proof for one SHA consumer and four
//! `Range_k` producers.
//!
//! The component composition follows the Blake example in
//! `stwo/examples/blake/air.rs`. The AIR checks all four `Range_k` carry and
//! terminal-byte channels. It checks the SHA Boolean functions directly from
//! bit planes.
//!
//! Call every `mix_into` in the same order in the prover and verifier. A
//! different order gives the verifier different challenges.

use num_traits::Zero;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError as StwoVerificationError;
use stwo::prover::backend::simd::m31::LOG_N_LANES;

use crate::air::{Sha256Prover, Sha256Verifier};
use crate::constants::DIGEST_BYTES;
use crate::interaction::InteractionClaim;
use crate::types::{Digest, Sha256Witness};
use crate::witness::compute_sha256_witness;

/// Tuning knobs for the prover.
///
/// `Default` picks the *smallest* legal value for each knob — enough to
/// prove a single padded block on the SIMD backend. Callers proving
/// anything longer **must** override `log_n_rows`. See its field doc for
/// the canonical recipe. The laptop benchmark pins the production values.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// `log2` of the SHA-256 component's trace row count. Each row is one
    /// round of one padded block (64 rows per block).
    ///
    /// **Must satisfy `log_n_rows ≥ trace::min_log_size(witness.blocks.len())`**
    /// or [`prove_sha256`] returns [`Sha256ProveError::TraceTooSmall`]. The
    /// SIMD backend additionally requires `log_n_rows ≥ LOG_N_LANES = 4`
    /// (one packed lane of rows). Below that, [`prove_sha256`] returns
    /// [`Sha256ProveError::LogSizeBelowSimdMin`].
    ///
    /// Caller recipe for any non-trivial message:
    /// ```rust,no_run
    /// use stwo_sha256::stark::ProverConfig;
    /// use stwo_sha256::trace::min_log_size;
    /// use stwo_sha256::witness::compute_sha256_witness;
    ///
    /// let message = b"a current SHA-256 message";
    /// let witness = compute_sha256_witness(message);
    /// let config = ProverConfig {
    ///     log_n_rows: min_log_size(witness.blocks.len()),
    ///     ..ProverConfig::default()
    /// };
    /// assert_eq!(config.log_n_rows, min_log_size(witness.blocks.len()));
    /// ```
    /// `examples/prove_demo.rs` shows this pattern end-to-end. Passing a
    /// value larger than `min_log_size` absorbs additional padding rows
    /// without re-generating the preprocessed tables — useful when
    /// batching variable-length messages into a single component.
    ///
    /// **`Default` sets this to `min_log_size(1) = 7`** — one padded block
    /// (64 rows) plus padding. Larger messages must override. See the
    /// recipe above.
    pub log_n_rows: u32,
    /// Stwo PCS configuration (FRI + PoW parameters). Use
    /// `PcsConfig::default()` for the smallest sensible test config.
    /// Production proofs raise `pow_bits` and `n_queries`.
    pub pcs_config: PcsConfig,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self {
            log_n_rows: crate::trace::min_log_size(1), // = 7: one block + padding
            pcs_config: PcsConfig::default(),
        }
    }
}

/// A STARK proof for a SHA-256 execution trace.
///
/// The `digest` and `n_blocks` fields contain metadata from the witness. The
/// standalone AIR does not bind either field to the proof. The verifier does
/// not mix these fields into its channel or compare them with the trace.
///
/// The optional digest provider emits the digest bytes on a shared LogUp
/// relation. A composed proof must include a matching consumer to bind those
/// bytes. Treat the fields on this standalone type as information from the
/// prover.
#[derive(Clone, Debug)]
pub struct Sha256Proof {
    /// The 32-byte digest the prover claims the (private) message hashes
    /// to. Witness-derived metadata. Not a cryptographic public input in
    /// this standalone component — see the type-level doc-comment for the
    /// binding plan.
    pub digest: [u8; DIGEST_BYTES],
    /// Number of blocks in the padded preimage. Witness-derived metadata.
    /// Not verifier-checked in this standalone component.
    pub n_blocks: usize,
    /// `log2` of the SHA-256 trace's row count.
    pub log_n_rows: u32,
    /// Per-component LogUp claimed sums. The total **must** be zero for
    /// the verifier to accept — the soundness backbone of the
    /// consumer ⇄ producer LogUp balance.
    pub interaction_claim: InteractionClaim,
    /// Stwo PCS configuration that the prover used. The verifier uses this
    /// value to reconstruct the same `CommitmentSchemeVerifier`.
    pub pcs_config: PcsConfig,
    /// The underlying Stwo STARK proof (Merkle commitments, FRI proof,
    /// OODS values, PoW nonce).
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

/// Errors from [`prove_sha256`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256ProveError {
    /// Caller asked for a row count below what the message requires.
    TraceTooSmall {
        requested_log_n_rows: u32,
        required_log_n_rows: u32,
    },
    /// Caller's `log_n_rows` is below `LOG_N_LANES = 4`. The SIMD backend
    /// requires at least one packed lane of rows.
    LogSizeBelowSimdMin {
        requested_log_n_rows: u32,
        simd_min: u32,
    },
    /// Stwo's underlying `prove` rejected the inputs — typically a
    /// constraint that does not vanish on the trace. Wrapped string is
    /// the upstream error.
    StwoProveFailed(String),
}

impl core::fmt::Display for Sha256ProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::TraceTooSmall { requested_log_n_rows, required_log_n_rows } => write!(
                f,
                "log_n_rows = {requested_log_n_rows} too small; this message requires log_n_rows ≥ {required_log_n_rows}"
            ),
            Self::LogSizeBelowSimdMin { requested_log_n_rows, simd_min } => write!(
                f,
                "log_n_rows = {requested_log_n_rows} below SIMD minimum {simd_min}"
            ),
            Self::StwoProveFailed(msg) => write!(f, "Stwo prover error: {msg}"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Sha256ProveError {}

/// Errors from [`verify_sha256_proof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256VerifyError {
    /// The Stwo verifier rejects the proof.
    StarkRejected(String),
    /// The per-component LogUp claimed sums do not total zero.
    LogupSumNonZero,
    /// `proof.log_n_rows` is outside the supported `[min, max]` range. The
    /// verifier rejects it before allocation. This gate prevents an excessive
    /// allocation of `2^log_n_rows` trace rows.
    UnsupportedLogNRows { log_n_rows: u32, min: u32, max: u32 },
}

impl core::fmt::Display for Sha256VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StarkRejected(msg) => write!(f, "Stwo verifier rejected proof: {msg}"),
            Self::LogupSumNonZero => write!(
                f,
                "LogUp claimed-sums total is non-zero: consumer ⇄ producer balance broken"
            ),
            Self::UnsupportedLogNRows {
                log_n_rows,
                min,
                max,
            } => write!(
                f,
                "proof.log_n_rows = {log_n_rows} outside supported range [{min}, {max}]"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Sha256VerifyError {}

/// Generate the witness, the trace, and the underlying STARK proof.
pub fn prove_sha256(
    message: &[u8],
    config: &ProverConfig,
) -> Result<Sha256Proof, Sha256ProveError> {
    let witness = compute_sha256_witness(message);
    prove_sha256_from_witness(&witness, config)
}

/// Generate a proof directly from a pre-built [`Sha256Witness`].
///
/// This function runs the same pipeline as [`prove_sha256`]. It accepts a
/// witness from a credential builder or another caller. Negative tests can
/// also change this witness before they start the prover.
pub fn prove_sha256_from_witness(
    witness: &Sha256Witness,
    config: &ProverConfig,
) -> Result<Sha256Proof, Sha256ProveError> {
    let required = crate::trace::min_log_size(witness.blocks.len());
    if config.log_n_rows < required {
        return Err(Sha256ProveError::TraceTooSmall {
            requested_log_n_rows: config.log_n_rows,
            required_log_n_rows: required,
        });
    }
    if config.log_n_rows < LOG_N_LANES {
        return Err(Sha256ProveError::LogSizeBelowSimdMin {
            requested_log_n_rows: config.log_n_rows,
            simd_min: LOG_N_LANES,
        });
    }

    prove_sha256_inner(witness, config)
        .map_err(|e| Sha256ProveError::StwoProveFailed(format!("{e:?}")))
}

/// Run the prover after the caller validates `config`.
///
/// [`Sha256Prover`] controls the preprocessed tables, base trace,
/// multiplicities, interaction trace, and components. This wrapper sends that
/// module to [`air_core::prove`].
fn prove_sha256_inner(
    witness: &Sha256Witness,
    config: &ProverConfig,
) -> Result<Sha256Proof, stwo::prover::ProvingError> {
    let log_n_rows = config.log_n_rows;
    let pcs_config = config.pcs_config;

    let mut prover = Sha256Prover::new(witness, log_n_rows);
    let stark_proof = air_core::prove(&mut [&mut prover], pcs_config)?;
    let interaction_claim = prover.interaction_claim().clone();
    let digest = witness.digest_from_blocks();
    Ok(Sha256Proof {
        digest: digest.0,
        n_blocks: witness.blocks.len(),
        log_n_rows,
        interaction_claim,
        pcs_config,
        stark_proof,
    })
}

/// Largest `log_n_rows` that the verifier accepts.
///
/// One block uses 64 trace rows. Thus, `2^MAX_LOG_N_ROWS` rows correspond to
/// approximately 1 GiB of padded input. This denial-of-service guard is not a
/// protocol limit. It limits allocations from an untrusted value such as `63`.
/// The lower limit is `LOG_N_LANES`.
pub const MAX_LOG_N_ROWS: u32 = 30;

/// Check the proof size parameters before allocation or table construction.
///
/// `log_n_rows` must be in `[LOG_N_LANES, MAX_LOG_N_ROWS]`. These limits
/// prevent an excessive allocation.
fn validate_verify_params(log_n_rows: u32) -> Result<(), Sha256VerifyError> {
    if !(LOG_N_LANES..=MAX_LOG_N_ROWS).contains(&log_n_rows) {
        return Err(Sha256VerifyError::UnsupportedLogNRows {
            log_n_rows,
            min: LOG_N_LANES,
            max: MAX_LOG_N_ROWS,
        });
    }
    Ok(())
}

/// Verify a `Sha256Proof`.
pub fn verify_sha256_proof(proof: &Sha256Proof) -> Result<(), Sha256VerifyError> {
    // ---- Structural-parameter gate ----
    // Reject malformed sizes before allocation or table construction.
    // This prevents an untrusted proof from panicking the table builder or
    // requesting excessive memory.
    validate_verify_params(proof.log_n_rows)?;

    // ---- Soundness gate: claimed sums must total zero ----
    // The orchestrator also enforces this through its global LogUp balance.
    // Check it here first. A broken balance then returns the typed
    // `LogupSumNonZero` error instead of a generic structural error.
    if !proof.interaction_claim.total().is_zero() {
        return Err(Sha256VerifyError::LogupSumNonZero);
    }

    // The transcript re-derivation, tree commitments, and component
    // reconstruction now live in [`Sha256Verifier`] + the shared
    // [`air_core::verify`] orchestrator.
    let mut verifier = Sha256Verifier::new(proof.log_n_rows, proof.interaction_claim.clone());
    air_core::verify(&mut [&mut verifier], &proof.stark_proof)
        .map_err(|e: StwoVerificationError| Sha256VerifyError::StarkRejected(format!("{e:?}")))
}

/// Native (out-of-circuit) digest. Useful for integration tests and as
/// the claimed public input the prover stamps into a `Sha256Proof`.
pub fn native_digest(message: &[u8]) -> Digest {
    crate::native::hash(message)
}

/// Public-input contract for the SHA-256 component.
///
/// Two construction paths:
/// - [`public_inputs_for`] — derives the contract from a message
///   without running the prover. Used by the integration stream to
///   assemble its Big-AIR public input contract ahead of proving.
/// - [`Sha256Proof::public_inputs`] — extracts the contract from a
///   proof. Used after proving. The returned value equals
///   `public_inputs_for(message)` for the same message.
///
/// The standalone component does not bind `digest` or `n_blocks` to the AIR.
/// See [`Sha256Proof`]. The optional digest provider emits the digest bytes on
/// a shared LogUp channel. A matching consumer can bind those bytes in a
/// composed proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sha256PublicInputs {
    pub digest: [u8; DIGEST_BYTES],
    pub n_blocks: usize,
}

/// Derive the public input shape (digest + block count) the prover
/// *would* commit to, without running the prover. Equivalent to
/// `prove_sha256(message, &config).map(|p| p.public_inputs())` but
/// avoids the prover cost.
pub fn public_inputs_for(message: &[u8]) -> Sha256PublicInputs {
    let padded = crate::native::pad_message(message);
    let n_blocks = padded.len() / crate::constants::BLOCK_BYTES;
    Sha256PublicInputs {
        digest: native_digest(message).0,
        n_blocks,
    }
}

impl Sha256Proof {
    /// Extract the public-input contract this proof carries. The returned
    /// value equals `public_inputs_for(message)` for the message the
    /// prover ran on. See [`Sha256PublicInputs`] for the contract shape
    /// and the standalone-component caveat about cryptographic binding.
    pub fn public_inputs(&self) -> Sha256PublicInputs {
        Sha256PublicInputs {
            digest: self.digest,
            n_blocks: self.n_blocks,
        }
    }
}

/// Helper consumed by integration tests: pad, witness, trace — but do not
/// run the prover.
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
    use crate::trace::Layout;

    #[test]
    fn prove_rejects_too_small_trace() {
        let msg = vec![0u8; 5000]; // many blocks ⇒ log_n_rows = 4 too small.
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
        let pubs = public_inputs_for(msg);
        assert_eq!(pubs.digest, native_digest(msg).0);
        assert_eq!(pubs.n_blocks, witness.blocks.len());
    }

    #[test]
    fn public_inputs_for_empty_and_boundary() {
        let pubs = public_inputs_for(b"");
        assert_eq!(pubs.n_blocks, 1);
        let pubs = public_inputs_for(&[0u8; 56]);
        assert_eq!(pubs.n_blocks, 2);
        let pubs = public_inputs_for(&[0u8; 55]);
        assert_eq!(pubs.n_blocks, 1);
    }

    /// Integration callers can give [`prove_sha256_from_witness`] an existing
    /// [`Sha256Witness`]. The success case needs a real proof and has ignored
    /// test coverage. This fast test checks the validation gate.
    #[test]
    fn prove_sha256_from_witness_rejects_too_small_log_n_rows() {
        // 5 000-byte message ⇒ well above the `1 << LOG_N_LANES` row
        // budget, so the `LOG_N_LANES`-sized default cannot fit it.
        let witness = compute_sha256_witness(&[0u8; 5000]);
        assert!(
            witness.blocks.len() > (1usize << LOG_N_LANES),
            "test premise: message must exceed the LOG_N_LANES = 4 row budget",
        );
        let config = ProverConfig {
            log_n_rows: LOG_N_LANES,
            ..ProverConfig::default()
        };
        match prove_sha256_from_witness(&witness, &config) {
            Err(Sha256ProveError::TraceTooSmall {
                requested_log_n_rows,
                required_log_n_rows,
            }) => {
                assert_eq!(requested_log_n_rows, LOG_N_LANES);
                assert!(required_log_n_rows > LOG_N_LANES);
            }
            other => panic!("expected TraceTooSmall, got {other:?}"),
        }
    }

    /// Pin the `public_inputs_for(msg) == Sha256Proof::public_inputs()` contract.
    /// Exercise every message shape used by downstream callers. Use the
    /// witness-derived shape instead of the ignored prover. `prove_sha256_inner`
    /// copies the witness digest and block count into the proof.
    #[test]
    fn public_inputs_for_matches_proof_public_inputs_shape() {
        // Synthesize the proof metadata without running the prover.
        // `Sha256Proof::public_inputs()` reads only the proof's metadata fields.
        // Therefore, matching digest and block-count fields exercise the contract.
        for msg in [&b""[..], b"abc", &[0u8; 56], &[0u8; 1024]] {
            let from_message = public_inputs_for(msg);
            let witness = compute_sha256_witness(msg);
            let digest = witness.digest_from_blocks();
            let from_proof = Sha256PublicInputs {
                digest: digest.0,
                n_blocks: witness.blocks.len(),
            };
            assert_eq!(from_message, from_proof, "msg = {msg:?}");
        }
    }

    /// Check that the structural gate accepts valid values and rejects other
    /// values with a typed error. The pure helper does not need a real
    /// `StarkProof`.
    #[test]
    fn verify_params_gate_accepts_range_and_rejects_outliers() {
        assert_eq!(validate_verify_params(LOG_N_LANES), Ok(()));
        assert_eq!(validate_verify_params(MAX_LOG_N_ROWS), Ok(()));

        // log_n_rows below the SIMD floor, and above the DoS ceiling — the
        // unbounded value (e.g. 63) the audit flagged as an instant OOM.
        assert!(matches!(
            validate_verify_params(LOG_N_LANES - 1),
            Err(Sha256VerifyError::UnsupportedLogNRows { .. })
        ));
        assert_eq!(
            validate_verify_params(MAX_LOG_N_ROWS + 1),
            Err(Sha256VerifyError::UnsupportedLogNRows {
                log_n_rows: MAX_LOG_N_ROWS + 1,
                min: LOG_N_LANES,
                max: MAX_LOG_N_ROWS,
            }),
        );
        assert!(matches!(
            validate_verify_params(63),
            Err(Sha256VerifyError::UnsupportedLogNRows { .. })
        ));
    }
}
