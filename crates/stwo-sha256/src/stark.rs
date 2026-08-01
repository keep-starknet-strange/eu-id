//! Prover and verifier entry points for the standalone SHA-256 component.
//!
//! The proof contains the preprocessed trace, the main SHA trace, the digest
//! bridge, the interaction trace, and the four `Range_k` producer components.
//!
//! The prover and verifier must call each `mix_into` operation in the same
//! order. A different order produces different transcript challenges.

use num_traits::Zero;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError as StwoVerificationError;
use stwo::prover::backend::simd::m31::LOG_N_LANES;

use crate::air::{Sha256Prover, Sha256Verifier};
use crate::components::RANGE_TABLES;
use crate::constants::DIGEST_BYTES;
use crate::interaction::InteractionClaim;
use crate::types::{Digest, Sha256Witness};
use crate::witness::compute_sha256_witness;

/// Tuning knobs for the prover.
///
/// `Default` selects the smallest legal value for each parameter. It can prove
/// one padded block on the SIMD backend. Longer messages need a larger
/// `log_n_rows`.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// `log2` of the SHA-256 component's trace row count. Each padded block
    /// uses three seed rows and 64 round rows.
    ///
    /// **Must satisfy `log_n_rows ≥ trace::min_log_size(witness.blocks.len())`**
    /// or [`prove_sha256`] returns [`Sha256ProveError::TraceTooSmall`]. The
    /// SIMD backend additionally requires `log_n_rows ≥ LOG_N_LANES = 4`
    /// (one packed lane of rows); below that, [`prove_sha256`] returns
    /// [`Sha256ProveError::LogSizeBelowSimdMin`].
    ///
    /// Caller recipe for any non-trivial message:
    /// ```text
    /// let witness = compute_sha256_witness(&message);
    /// let config = ProverConfig {
    ///     log_n_rows: trace::min_log_size(witness.blocks.len()),
    ///     ..ProverConfig::default()
    /// };
    /// ```
    /// `examples/prove_demo.rs` shows this pattern. A larger value adds
    /// padding rows. This supports fixed-size traces for messages of different
    /// lengths.
    ///
    /// `Default` sets this to `min_log_size(1) = 7`. This size contains one
    /// padded block and at least one disabled row. Larger messages need a
    /// larger value.
    pub log_n_rows: u32,
    /// Stwo PCS configuration for FRI and proof of work.
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

/// A STARK proof that a private message produces a SHA-256 trace whose
/// last-block `h_out` columns form a valid digest.
///
/// The standalone verifier does not bind `digest` or `n_blocks` to the AIR.
/// These fields contain witness-derived metadata. Composed proofs use the
/// digest provider relation to bind the trace digest to another component.
#[derive(Clone, Debug)]
pub struct Sha256Proof {
    /// The witness-derived 32-byte digest. The standalone verifier does not
    /// check this field.
    pub digest: [u8; DIGEST_BYTES],
    /// Number of blocks in the padded preimage. Witness-derived metadata;
    /// not verifier-checked in this standalone component.
    pub n_blocks: usize,
    /// `log2` of the SHA-256 trace's row count.
    pub log_n_rows: u32,
    /// Per-component LogUp claimed sums. The total must be zero.
    pub interaction_claim: InteractionClaim,
    /// Stwo PCS configuration the proof was generated with. Surfaced so
    /// the verifier can reconstruct the same `CommitmentSchemeVerifier`.
    pub pcs_config: PcsConfig,
    /// The underlying Stwo STARK proof (Merkle commitments, FRI proof,
    /// OODS values, PoW nonce).
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

/// Errors that can be returned by [`prove_sha256`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256ProveError {
    /// Caller asked for a row count below what the message requires.
    TraceTooSmall {
        requested_log_n_rows: u32,
        required_log_n_rows: u32,
    },
    /// Caller's `log_n_rows` is below `LOG_N_LANES = 4`; the SIMD backend
    /// requires at least one packed lane of rows.
    LogSizeBelowSimdMin {
        requested_log_n_rows: u32,
        simd_min: u32,
    },
    /// Stwo rejected the prover input. The string contains the upstream error.
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

impl std::error::Error for Sha256ProveError {}

/// Errors that can be returned by [`verify_sha256_proof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256VerifyError {
    /// The Stwo verifier rejected the proof.
    StarkRejected(String),
    /// The per-component LogUp claimed sums do not sum to zero.
    LogupSumNonZero,
    /// `proof.log_n_rows` is outside the supported `[min, max]` range.
    /// Rejected before any allocation so a malformed proof cannot drive an
    /// out-of-memory allocation on the verify path (the trace row count is
    /// `2^log_n_rows`).
    UnsupportedLogNRows { log_n_rows: u32, min: u32, max: u32 },
    /// The standalone claim does not contain one claim per range table.
    InvalidRangeClaimCount { expected: usize, actual: usize },
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
            Self::InvalidRangeClaimCount { expected, actual } => write!(
                f,
                "proof contains {actual} range claims; expected {expected}"
            ),
        }
    }
}

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
/// This function accepts a witness instead of a message. Credential builders
/// and negative tests can supply the witness directly.
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

/// Prove with a validated configuration.
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
/// Each padded block uses 67 rows. The limit permits about 1 GiB of padded
/// preimage data. This limit prevents excessive allocation from an untrusted
/// proof. It is not a protocol limit.
pub const MAX_LOG_N_ROWS: u32 = 30;

/// Validate proof size parameters before allocation.
///
/// `log_n_rows` must be in `[LOG_N_LANES, MAX_LOG_N_ROWS]`. An invalid
/// `log_n_rows` value could cause excessive allocation during verification.
fn validate_log_n_rows(log_n_rows: u32) -> Result<(), Sha256VerifyError> {
    if !(LOG_N_LANES..=MAX_LOG_N_ROWS).contains(&log_n_rows) {
        return Err(Sha256VerifyError::UnsupportedLogNRows {
            log_n_rows,
            min: LOG_N_LANES,
            max: MAX_LOG_N_ROWS,
        });
    }
    Ok(())
}

/// Validate the standalone component-claim shape before component creation.
fn validate_interaction_claim_shape(claim: &InteractionClaim) -> Result<(), Sha256VerifyError> {
    let expected = RANGE_TABLES.len();
    let actual = claim.range.len();
    if actual != expected {
        return Err(Sha256VerifyError::InvalidRangeClaimCount { expected, actual });
    }
    Ok(())
}

/// Verify a `Sha256Proof`.
pub fn verify_sha256_proof(proof: &Sha256Proof) -> Result<(), Sha256VerifyError> {
    // Reject invalid sizes before allocation.
    validate_log_n_rows(proof.log_n_rows)?;
    validate_interaction_claim_shape(&proof.interaction_claim)?;

    // Return the specific balance error before generic proof verification.
    if !proof.interaction_claim.total().is_zero() {
        return Err(Sha256VerifyError::LogupSumNonZero);
    }

    let mut verifier = Sha256Verifier::new(proof.log_n_rows, proof.interaction_claim.clone());
    air_core::verify(&mut [&mut verifier], &proof.stark_proof)
        .map_err(|e: StwoVerificationError| Sha256VerifyError::StarkRejected(format!("{e:?}")))
}

/// Compute a native digest for tests and proof metadata.
pub fn native_digest(message: &[u8]) -> Digest {
    crate::native::hash(message)
}

/// Public-input contract for the SHA-256 component.
///
/// [`public_inputs_for`] derives this metadata from a message.
/// [`Sha256Proof::public_inputs`] reads it from a proof.
///
/// The standalone verifier does not bind this metadata to the AIR. Composed
/// proofs use the optional digest provider relation for that binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sha256PublicInputs {
    pub digest: [u8; DIGEST_BYTES],
    pub n_blocks: usize,
}

/// Derive the digest and padded block count without running the prover.
pub fn public_inputs_for(message: &[u8]) -> Sha256PublicInputs {
    let padded = crate::native::pad_message(message);
    let n_blocks = padded.len() / crate::constants::BLOCK_BYTES;
    Sha256PublicInputs {
        digest: native_digest(message).0,
        n_blocks,
    }
}

impl Sha256Proof {
    /// Read the witness-derived digest and block count from this proof.
    pub fn public_inputs(&self) -> Sha256PublicInputs {
        Sha256PublicInputs {
            digest: self.digest,
            n_blocks: self.n_blocks,
        }
    }
}

/// Build a witness and trace without running the prover.
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

    /// This test checks the validation gate through
    /// `prove_sha256_from_witness`. It does not generate a proof.
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

    /// Pins the `public_inputs_for(msg) == Sha256Proof::public_inputs()`
    /// contract for every message a downstream caller might use. We
    /// drive it against the witness-derived shape instead of running
    /// the prover (which is `#[ignore]`d everywhere else), since the
    /// proof's `digest` / `n_blocks` fields are populated from the
    /// witness verbatim in `prove_sha256_inner`.
    #[test]
    fn public_inputs_for_matches_proof_public_inputs_shape() {
        // A proof we can synthesise without running the prover: every
        // field of `Sha256Proof::public_inputs()` reads from the proof's
        // own metadata fields, so building a stand-in struct with the
        // same `digest` / `n_blocks` exercises the contract.
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

    /// The structural-parameter gate accepts the supported range and rejects
    /// an invalid `log_n_rows` with a typed error. It runs before allocation.
    #[test]
    fn log_size_gate_accepts_range_and_rejects_outliers() {
        assert_eq!(validate_log_n_rows(LOG_N_LANES), Ok(()));
        assert_eq!(validate_log_n_rows(MAX_LOG_N_ROWS), Ok(()));

        // Reject values below the SIMD floor and above the allocation limit.
        assert!(matches!(
            validate_log_n_rows(LOG_N_LANES - 1),
            Err(Sha256VerifyError::UnsupportedLogNRows { .. })
        ));
        assert_eq!(
            validate_log_n_rows(MAX_LOG_N_ROWS + 1),
            Err(Sha256VerifyError::UnsupportedLogNRows {
                log_n_rows: MAX_LOG_N_ROWS + 1,
                min: LOG_N_LANES,
                max: MAX_LOG_N_ROWS,
            }),
        );
        assert!(matches!(
            validate_log_n_rows(63),
            Err(Sha256VerifyError::UnsupportedLogNRows { .. })
        ));
    }

    #[test]
    fn interaction_claim_shape_rejects_missing_or_extra_range_claims() {
        use stwo::core::fields::qm31::SecureField;

        fn claim_with_range_count(range_count: usize) -> InteractionClaim {
            let zero = crate::interaction::ComponentClaim {
                claimed_sum: SecureField::zero(),
            };
            InteractionClaim {
                sha256: zero.clone(),
                digest_bridge: zero.clone(),
                range: vec![zero; range_count],
            }
        }

        let expected = RANGE_TABLES.len();
        assert_eq!(
            validate_interaction_claim_shape(&claim_with_range_count(expected)),
            Ok(())
        );
        for actual in [expected - 1, expected + 1] {
            assert_eq!(
                validate_interaction_claim_shape(&claim_with_range_count(actual)),
                Err(Sha256VerifyError::InvalidRangeClaimCount { expected, actual })
            );
        }
    }
}
