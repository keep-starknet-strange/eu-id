//! Prover and verifier entry points for the standalone SHA-256 component.
//!
//! Full plumbing: preprocessed-trace commitment of every lookup table
//! (`crate::preprocessed`), base-trace commitment of the Sha256Eval trace
//! plus the producer-side multiplicity columns, interaction trace per
//! component (`crate::interaction`), and finally Stwo's `prove<SimdBackend>`
//! over the 23 components in `crate::components` (1 consumer + 8 σ/Σ
//! decode + 1 packed Maj/Ch + 1 `xor_8` + 8 split-and-pack + 4 `Range_k`).
//!
//! Component composition pattern matches `../sha256-air/src/lib.rs`
//! (structural reference) and the Blake example in
//! `stwo/examples/blake/air.rs`. Constraint-layer soundness covers
//! every lookup the AIR consumes: Σ/σ decode, packed Maj/Ch, `xor_8`,
//! split-and-pack, and the four `Range_k` carry / terminal-limb channels.
//!
//! Order discipline: every `mix_into` on the channel **must** happen in
//! the same order on the prover and verifier sides — drift silently
//! breaks the verifier's challenge re-derivation.

use num_traits::Zero;
#[cfg(feature = "gkr-spike")]
use stwo::core::channel::Blake2sChannel;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError as StwoVerificationError;
use stwo::prover::backend::simd::m31::LOG_N_LANES;

use crate::air::{Sha256Prover, Sha256Verifier};
use crate::constants::DIGEST_BYTES;
#[cfg(feature = "gkr-spike")]
use crate::gkr_spike::{
    prove_xor_8_gkr, verify_xor_8_gkr, xor_8_output_claims_balance, Xor8GkrProofWire,
};
use crate::interaction::InteractionClaim;
#[cfg(feature = "gkr-spike")]
use crate::relations::Sha256Relations;
use crate::types::{Digest, Sha256Witness};
use crate::witness::compute_sha256_witness;

/// Tuning knobs for the prover.
///
/// `Default` picks the *smallest* legal value for each knob — enough to
/// prove a single padded block on the SIMD backend. Callers proving
/// anything longer **must** override `log_n_rows`; see its field doc for
/// the canonical recipe. The laptop benchmark pins the production values.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// `log2` of the SHA-256 component's trace row count. Each row is one
    /// round of one padded block (64 rows per block).
    ///
    /// **Must satisfy `log_n_rows ≥ trace::min_log_size(witness.blocks.len())`**
    /// or [`prove_sha256`] returns [`Sha256ProveError::TraceTooSmall`]. The
    /// SIMD backend additionally requires `log_n_rows ≥ LOG_N_LANES = 4`
    /// (one packed lane of rows); below that, [`prove_sha256`] returns
    /// [`Sha256ProveError::LogSizeBelowSimdMin`].
    ///
    /// Caller recipe for any non-trivial message:
    /// ```ignore
    /// let witness = compute_sha256_witness(&message);
    /// let config = ProverConfig {
    ///     log_n_rows: trace::min_log_size(witness.blocks.len()),
    ///     ..ProverConfig::default()
    /// };
    /// ```
    /// `examples/prove_demo.rs` shows this pattern end-to-end. Passing a
    /// value larger than `min_log_size` absorbs additional padding rows
    /// without re-generating the preprocessed tables — useful when
    /// batching variable-length messages into a single component.
    ///
    /// **`Default` sets this to `min_log_size(1) = 7`** — one padded block
    /// (64 rows) plus padding. Larger messages must override; see the
    /// recipe above.
    pub log_n_rows: u32,
    /// Group width `W` for the packed `Maj`/`Ch` table. The default is
    /// `MAX_ROUND_GROUP_BITS = 6`: the round partitions subdivide their two
    /// 7-bit groups into ≤6-bit sub-groups (design §9.2), so every packed
    /// group is `≤ 6` bits and the table is `2^(3·6) = 2¹⁸ ≈ 262 k` rows —
    /// an 8× shrink from the old `W = 7` `2²¹` table that dominated prove
    /// cost. The packed-table size is `2^(3W)` rows.
    pub group_width: u32,
    /// Stwo PCS configuration (FRI + PoW parameters). Use
    /// `PcsConfig::default()` for the smallest sensible test config;
    /// production proofs raise `pow_bits` and `n_queries`.
    pub pcs_config: PcsConfig,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self {
            log_n_rows: crate::trace::min_log_size(1), // = 7: one block + padding
            group_width: crate::partitions::MAX_ROUND_GROUP_BITS,
            pcs_config: PcsConfig::default(),
        }
    }
}

/// A STARK proof that a private message produces a SHA-256 trace whose
/// last-block `h_out` columns form a valid digest.
///
/// **Note on `digest` and `n_blocks`.** Both are surfaced on the proof
/// struct as witness-derived metadata so callers can read what the prover
/// claims, but neither is cryptographically bound to the AIR by this
/// standalone component: the verifier does not mix `digest`/`n_blocks`
/// into its channel and does not compare them to the trace's `h_out`
/// columns. Binding the digest to a verifier-checked public input lands
/// with the integration-layer LogUp surface
/// (`elementDigest ↔ valueDigests`, `Sig_structure digest ↔ ECDSA z`).
/// Until then, treat `digest` as informational: it is only as trustworthy
/// as the prover.
#[derive(Clone, Debug)]
pub struct Sha256Proof {
    /// The 32-byte digest the prover claims the (private) message hashes
    /// to. Witness-derived metadata; not a cryptographic public input in
    /// this standalone component — see the type-level doc-comment for the
    /// binding plan.
    pub digest: [u8; DIGEST_BYTES],
    /// Number of blocks in the padded preimage. Witness-derived metadata;
    /// not verifier-checked in this standalone component.
    pub n_blocks: usize,
    /// `log2` of the SHA-256 trace's row count.
    pub log_n_rows: u32,
    /// Group width `W` of the packed Maj/Ch table this proof was generated
    /// against. The verifier reads it back to reconstruct the matching
    /// `MajChEval`'s `log_size = 3W`.
    pub group_width: u32,
    /// Per-component LogUp claimed sums. The total **must** be zero for
    /// the verifier to accept — the soundness backbone of the
    /// consumer ⇄ producer LogUp balance.
    pub interaction_claim: InteractionClaim,
    /// Stwo PCS configuration the proof was generated with. Surfaced so
    /// the verifier can reconstruct the same `CommitmentSchemeVerifier`.
    pub pcs_config: PcsConfig,
    /// The underlying Stwo STARK proof (Merkle commitments, FRI proof,
    /// OODS values, PoW nonce).
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
    /// Feature-gated side proof replacing the committed `xor_8` LogUp columns.
    #[cfg(feature = "gkr-spike")]
    pub xor_8_gkr_proof: Xor8GkrProofWire,
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

/// Errors that can be returned by [`verify_sha256_proof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sha256VerifyError {
    /// The Stwo verifier rejected the proof.
    StarkRejected(String),
    /// Per-component LogUp claimed sums do not sum to zero — the
    /// consumer ⇄ producer balance is broken.
    LogupSumNonZero,
    /// `proof.group_width` is outside the supported `[min, max]` range.
    /// Rejected before any allocation so a malformed proof cannot drive a
    /// `panic!` inside the preprocessed-table builder (`build_maj_ch_table`).
    UnsupportedGroupWidth {
        group_width: u32,
        min: u32,
        max: u32,
    },
    /// `proof.log_n_rows` is outside the supported `[min, max]` range.
    /// Rejected before any allocation so a malformed proof cannot drive an
    /// out-of-memory allocation on the verify path (the trace row count is
    /// `2^log_n_rows`).
    UnsupportedLogNRows { log_n_rows: u32, min: u32, max: u32 },
    #[cfg(feature = "gkr-spike")]
    Xor8GkrUnbalanced,
    #[cfg(feature = "gkr-spike")]
    Xor8GkrRejected(String),
}

impl core::fmt::Display for Sha256VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StarkRejected(msg) => write!(f, "Stwo verifier rejected proof: {msg}"),
            Self::LogupSumNonZero => write!(
                f,
                "LogUp claimed-sums total is non-zero: consumer ⇄ producer balance broken"
            ),
            Self::UnsupportedGroupWidth {
                group_width,
                min,
                max,
            } => write!(
                f,
                "proof.group_width = {group_width} outside supported range [{min}, {max}]"
            ),
            Self::UnsupportedLogNRows {
                log_n_rows,
                min,
                max,
            } => write!(
                f,
                "proof.log_n_rows = {log_n_rows} outside supported range [{min}, {max}]"
            ),
            #[cfg(feature = "gkr-spike")]
            Self::Xor8GkrUnbalanced => write!(f, "xor_8 GKR output claims do not balance"),
            #[cfg(feature = "gkr-spike")]
            Self::Xor8GkrRejected(msg) => write!(f, "xor_8 GKR proof rejected: {msg}"),
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
/// Same pipeline as [`prove_sha256`] but lets callers supply the witness
/// directly — useful for integration-stream pipelines (where the witness
/// comes from the credential builder rather than a raw message) and for
/// negative tests that mutate the witness before proving to exercise the
/// soundness gates.
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

/// Inner prover — assumes `config` has been validated. Split out so the
/// `?`/error-mapping at the boundary stays tidy.
///
/// The four-phase plumbing (preprocessed tables, base trace + producer
/// multiplicities, per-component interaction trace, component assembly) now
/// lives in [`Sha256Prover`]; this is the thin one-module wrapper that runs it
/// through the shared [`air_core::prove`] orchestrator.
fn prove_sha256_inner(
    witness: &Sha256Witness,
    config: &ProverConfig,
) -> Result<Sha256Proof, stwo::prover::ProvingError> {
    let log_n_rows = config.log_n_rows;
    let group_width = config.group_width;
    let pcs_config = config.pcs_config;

    let mut prover = Sha256Prover::new(witness, log_n_rows, group_width);
    let stark_proof = air_core::prove(&mut [&mut prover], pcs_config)?;
    let interaction_claim = prover.interaction_claim().clone();
    #[cfg(feature = "gkr-spike")]
    let xor_8_gkr_proof = {
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let gkr = prove_xor_8_gkr(
            &relations,
            witness,
            log_n_rows,
            &mut Blake2sChannel::default(),
        );
        Xor8GkrProofWire::from(&gkr.proof)
    };

    let digest = witness.digest_from_blocks();
    Ok(Sha256Proof {
        digest: digest.0,
        n_blocks: witness.blocks.len(),
        log_n_rows,
        group_width,
        interaction_claim,
        pcs_config,
        stark_proof,
        #[cfg(feature = "gkr-spike")]
        xor_8_gkr_proof,
    })
}

/// Largest `log_n_rows` the verifier will accept. Each trace row is one
/// padded 64-byte block, so `2^MAX_LOG_N_ROWS` blocks is on the order of
/// `64 GiB` of preimage — far beyond any proof a real prover would produce.
/// This is a denial-of-service guard, **not** a protocol limit: it bounds
/// verifier-side allocation against a malformed/malicious `proof.log_n_rows`
/// (e.g. `63` → instant OOM) and can be raised if a legitimate use ever
/// approaches it. The floor is `LOG_N_LANES` (the SIMD backend's
/// one-packed-lane minimum the prover itself enforces).
pub const MAX_LOG_N_ROWS: u32 = 30;

/// Validate the structural size parameters a proof carries **before** any
/// allocation or table build. Split out as a pure function so the gate can
/// be unit-tested without constructing a full [`Sha256Proof`] (which needs
/// a real `StarkProof`).
///
/// `group_width` must lie in `[MAX_ROUND_GROUP_BITS, MAX_GROUP_WIDTH]` — the
/// same range [`crate::tables::build_maj_ch_table`] asserts — and
/// `log_n_rows` in `[LOG_N_LANES, MAX_LOG_N_ROWS]`. Out-of-range values
/// would otherwise panic the table builder (`group_width`) or drive an
/// OOM (`log_n_rows`) on the untrusted verify path.
fn validate_verify_params(group_width: u32, log_n_rows: u32) -> Result<(), Sha256VerifyError> {
    let min_w = crate::partitions::MAX_ROUND_GROUP_BITS;
    let max_w = crate::tables::MAX_GROUP_WIDTH;
    if !(min_w..=max_w).contains(&group_width) {
        return Err(Sha256VerifyError::UnsupportedGroupWidth {
            group_width,
            min: min_w,
            max: max_w,
        });
    }
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
    // Reject malformed sizes before any allocation or table build, so a
    // malicious proof cannot panic the preprocessed-table builder or drive
    // an out-of-memory allocation on the untrusted verify path.
    validate_verify_params(proof.group_width, proof.log_n_rows)?;

    // ---- Soundness gate: claimed sums must total zero ----
    // The orchestrator also enforces this (its global LogUp balance), but we
    // check it up front so a broken balance surfaces as the typed
    // `LogupSumNonZero` rather than a generic structural rejection.
    if !proof.interaction_claim.total().is_zero() {
        return Err(Sha256VerifyError::LogupSumNonZero);
    }

    #[cfg(feature = "gkr-spike")]
    {
        let xor_8_gkr_proof = proof.xor_8_gkr_proof.clone().into();
        if !xor_8_output_claims_balance(&xor_8_gkr_proof) {
            return Err(Sha256VerifyError::Xor8GkrUnbalanced);
        }
        verify_xor_8_gkr(&xor_8_gkr_proof, &mut Blake2sChannel::default())
            .map_err(|e| Sha256VerifyError::Xor8GkrRejected(format!("{e:?}")))?;
    }

    // The transcript re-derivation, tree commitments, and component
    // reconstruction now live in [`Sha256Verifier`] + the shared
    // [`air_core::verify`] orchestrator.
    let mut verifier = Sha256Verifier::new(
        proof.log_n_rows,
        proof.group_width,
        proof.interaction_claim.clone(),
    );
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
///   proof. Used after proving; the returned value equals
///   `public_inputs_for(message)` for the same message.
///
/// The standalone component does not cryptographically bind `digest` /
/// `n_blocks` to the AIR — see [`Sha256Proof`]'s doc-comment for the
/// binding approach. This type defines the *shape* the integration layer
/// pins: the opt-in digest provider (`with_digest_provider`) yields the
/// digest bytes on a shared LogUp channel for a consumer to bind against.
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

/// Helper consumed by integration tests: pad, witness, trace — but don't
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

    /// `prove_sha256_from_witness` is publicly exposed for integration
    /// callers that already hold a [`Sha256Witness`] (e.g. from the
    /// credential builder); its happy path requires a real proof and so
    /// lives in `#[ignore]`d tests. This fast test pins the validation
    /// gate without paying for proof generation, and exercises the
    /// witness-direct entry point so it has at least one debug-mode
    /// caller outside of `prove_sha256` itself.
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
    /// out-of-range `group_width` / `log_n_rows` with a typed error — never a
    /// panic or OOM. Exercised on the pure helper so it needs no real
    /// `StarkProof` (which the happy-path round-trip tests, all `#[ignore]`d,
    /// would require).
    #[test]
    fn verify_params_gate_accepts_range_and_rejects_outliers() {
        use crate::partitions::MAX_ROUND_GROUP_BITS;
        use crate::tables::MAX_GROUP_WIDTH;

        // Accepts the whole supported box [MAX_ROUND_GROUP_BITS, MAX_GROUP_WIDTH]
        // × [LOG_N_LANES, MAX_LOG_N_ROWS].
        for w in MAX_ROUND_GROUP_BITS..=MAX_GROUP_WIDTH {
            assert_eq!(validate_verify_params(w, LOG_N_LANES), Ok(()));
            assert_eq!(validate_verify_params(w, MAX_LOG_N_ROWS), Ok(()));
        }

        // group_width below the floor (would under-cover the witness keys)
        // and above the cap (would panic `build_maj_ch_table`).
        assert_eq!(
            validate_verify_params(MAX_ROUND_GROUP_BITS - 1, LOG_N_LANES),
            Err(Sha256VerifyError::UnsupportedGroupWidth {
                group_width: MAX_ROUND_GROUP_BITS - 1,
                min: MAX_ROUND_GROUP_BITS,
                max: MAX_GROUP_WIDTH,
            }),
        );
        assert!(matches!(
            validate_verify_params(MAX_GROUP_WIDTH + 1, LOG_N_LANES),
            Err(Sha256VerifyError::UnsupportedGroupWidth { .. })
        ));

        // log_n_rows below the SIMD floor, and above the DoS ceiling — the
        // unbounded value (e.g. 63) the audit flagged as an instant OOM.
        assert!(matches!(
            validate_verify_params(MAX_ROUND_GROUP_BITS, LOG_N_LANES - 1),
            Err(Sha256VerifyError::UnsupportedLogNRows { .. })
        ));
        assert_eq!(
            validate_verify_params(MAX_ROUND_GROUP_BITS, MAX_LOG_N_ROWS + 1),
            Err(Sha256VerifyError::UnsupportedLogNRows {
                log_n_rows: MAX_LOG_N_ROWS + 1,
                min: LOG_N_LANES,
                max: MAX_LOG_N_ROWS,
            }),
        );
        assert!(matches!(
            validate_verify_params(MAX_ROUND_GROUP_BITS, 63),
            Err(Sha256VerifyError::UnsupportedLogNRows { .. })
        ));
    }
}
