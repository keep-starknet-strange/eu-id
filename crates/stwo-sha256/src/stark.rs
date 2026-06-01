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
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::{verify, VerificationError as StwoVerificationError};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

use crate::components::{
    all_preprocessed_column_ids, range_log_size, MajChEval, RangeKEval, RoundSplitPackEval,
    Sha256Relations, SigmaDecodeEval, SigmaSplitPackEval, Xor8Eval, DECODE_TABLES, RANGE_TABLES,
    ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::constants::DIGEST_BYTES;
use crate::constraints::Sha256Eval;
use crate::interaction::{generate_interaction_trace, InteractionClaim};
use crate::multiplicities::{
    decode_multiplicities, maj_ch_multiplicities, range_k_multiplicities,
    round_split_pack_multiplicities, sigma_split_pack_multiplicities, xor_8_multiplicities,
};
use crate::preprocessed::{
    generate_preprocessed_trace, maj_ch_log_size, preprocessed_log_sizes, LOG_SIZE_16,
};
use crate::trace::Layout;
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
    /// padded block.
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
    /// **`Default` sets this to `LOG_N_LANES = 4`** — the SIMD floor,
    /// fitting at most 16 padded blocks (~1 KiB of message). Larger
    /// messages must override; see the recipe above.
    pub log_n_rows: u32,
    /// Group width `W` for the packed `Maj`/`Ch` table. `7` is the minimum
    /// without subdividing the existing partitions' 7-bit groups; smaller
    /// `W` values require a partition rework (design §9.2 sketches the
    /// `W = 6` "subdivide 7-bit groups" path as a future micro-optimisation
    /// the laptop/mobile benchmark can pin). The packed-table size is
    /// `2^(3W)` rows; at `W = 7` that is `2²¹ ≈ 2.1 M` rows.
    pub group_width: u32,
    /// Stwo PCS configuration (FRI + PoW parameters). Use
    /// `PcsConfig::default()` for the smallest sensible test config;
    /// production proofs raise `pow_bits` and `n_queries`.
    pub pcs_config: PcsConfig,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self {
            log_n_rows: LOG_N_LANES, // = 4
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
fn prove_sha256_inner(
    witness: &Sha256Witness,
    config: &ProverConfig,
) -> Result<Sha256Proof, stwo::prover::ProvingError> {
    let log_n_rows = config.log_n_rows;
    let group_width = config.group_width;
    let pcs_config = config.pcs_config;

    // ---- Setup protocol & twiddles ----
    let channel = &mut Blake2sChannel::default();
    pcs_config.mix_into(channel);

    // Twiddles must cover the largest committed domain plus the FRI
    // blow-up. Among our 23 components, Maj/Ch is the biggest at `3W`
    // rows; everything else is ≤ 16. Use `+ 1` for the half-coset.
    let max_log_size = maj_ch_log_size(group_width)
        .max(LOG_SIZE_16)
        .max(log_n_rows);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_log_size + 1 + pcs_config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let mut commitment_scheme =
        CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(pcs_config, &twiddles);

    // ---- tree[0]: preprocessed trace ----
    let (preprocessed_evals, _ids, _log_sizes) =
        generate_preprocessed_trace(group_width, log_n_rows);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed_evals);
    tree_builder.commit(channel);

    // Mix stmt0 (the per-component log sizes) into the channel so the
    // verifier's challenge stream matches. We use `log_n_rows` and
    // `group_width` as the surface — the rest of the log sizes are pinned
    // by these via `LOG_SIZE_16` and `maj_ch_log_size(W)`.
    Stmt0 {
        log_n_rows,
        group_width,
    }
    .mix_into(channel);

    // ---- tree[1]: Sha256Eval base trace + producer multiplicity cols ----
    let mut base_trace: Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> =
        Vec::new();

    let sha_main = crate::trace::generate_trace(witness, log_n_rows);
    debug_assert_eq!(sha_main.len(), Layout::TOTAL_COLS);
    let sha_domain = CanonicCoset::new(log_n_rows).circle_domain();
    for col_vec in sha_main {
        let col: BaseColumn = col_vec.into_iter().collect();
        base_trace.push(CircleEvaluation::new(sha_domain, col));
    }

    // Multiplicity columns — same order as `Components::component_provers`.
    for &(f, h) in DECODE_TABLES {
        let mults = decode_multiplicities(witness, f, h);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    {
        let mc = maj_ch_multiplicities(witness, group_width);
        let log_size = maj_ch_log_size(group_width);
        base_trace.push(mult_col_to_eval(&mc.maj, log_size));
        base_trace.push(mult_col_to_eval(&mc.ch, log_size));
    }
    {
        let mults = xor_8_multiplicities(witness);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    for &(p, h) in ROUND_SPLIT_TABLES {
        let mults = round_split_pack_multiplicities(witness, p, h);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    for &(p, h) in SIGMA_SPLIT_TABLES {
        let mults = sigma_split_pack_multiplicities(witness, p, h);
        base_trace.push(mult_col_to_eval(&mults, LOG_SIZE_16));
    }
    for &kind in RANGE_TABLES {
        let mults = range_k_multiplicities(witness, kind);
        base_trace.push(mult_col_to_eval(&mults, range_log_size(kind)));
    }

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base_trace);
    tree_builder.commit(channel);

    // ---- Draw LogUp relations ----
    let relations = Sha256Relations::draw(channel);

    // ---- tree[2]: interaction trace per component ----
    let (interaction_evals, interaction_claim) =
        generate_interaction_trace(&relations, witness, log_n_rows, group_width);

    // Mix stmt1 (the per-component claimed sums) before committing the
    // interaction tree. Verifier mirrors this order.
    interaction_claim.mix_into(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction_evals);
    tree_builder.commit(channel);

    // ---- Build components and prove ----
    let components_owned =
        Sha256Components::new(&interaction_claim, &relations, log_n_rows, group_width);
    let component_provers = components_owned.component_provers();
    let stark_proof =
        prove::<SimdBackend, Blake2sMerkleChannel>(&component_provers, channel, commitment_scheme)?;

    let digest = witness.digest_from_blocks();
    Ok(Sha256Proof {
        digest: digest.0,
        n_blocks: witness.blocks.len(),
        log_n_rows,
        group_width,
        interaction_claim,
        pcs_config,
        stark_proof,
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
    if !proof.interaction_claim.total().is_zero() {
        return Err(Sha256VerifyError::LogupSumNonZero);
    }

    let pcs_config = proof.pcs_config;

    // ---- Setup ----
    let channel = &mut Blake2sChannel::default();
    pcs_config.mix_into(channel);
    let commitment_scheme_verifier =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

    // ---- tree[0]: preprocessed (re-derive log sizes from the proof) ----
    // Metadata only: the verifier needs the per-column log sizes to commit
    // `tree[0]`, never the column data. Rebuilding the lookup tables here
    // (millions of Maj/Ch rows) just to discard the evaluations would put
    // prover-scale work on every verify — see `preprocessed_log_sizes`.
    let preprocessed_log_sizes = preprocessed_log_sizes(proof.group_width, proof.log_n_rows);
    commitment_scheme_verifier.commit(
        proof.stark_proof.commitments[0],
        &preprocessed_log_sizes,
        channel,
    );

    Stmt0 {
        log_n_rows: proof.log_n_rows,
        group_width: proof.group_width,
    }
    .mix_into(channel);

    // ---- tree[1]: base trace log sizes ----
    let base_log_sizes = base_trace_log_sizes(proof.log_n_rows, proof.group_width);
    commitment_scheme_verifier.commit(proof.stark_proof.commitments[1], &base_log_sizes, channel);

    // ---- Draw relations (must match prover order) ----
    let relations = Sha256Relations::draw(channel);

    // ---- tree[2]: interaction trace log sizes ----
    proof.interaction_claim.mix_into(channel);
    let interaction_log_sizes = interaction_trace_log_sizes(
        proof.log_n_rows,
        proof.group_width,
        &proof.interaction_claim,
    );
    commitment_scheme_verifier.commit(
        proof.stark_proof.commitments[2],
        &interaction_log_sizes,
        channel,
    );

    // ---- Reconstruct components and verify ----
    let components_owned = Sha256Components::new(
        &proof.interaction_claim,
        &relations,
        proof.log_n_rows,
        proof.group_width,
    );
    let components = components_owned.components();

    verify(
        &components,
        channel,
        commitment_scheme_verifier,
        proof.stark_proof.clone(),
    )
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
/// binding plan. This type defines the *shape* the integration layer
/// will eventually pin.
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

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Per-proof "statement 0": fixes the component log-size surface so the
/// channel state agrees on both sides.
struct Stmt0 {
    log_n_rows: u32,
    group_width: u32,
}
impl Stmt0 {
    fn mix_into(&self, channel: &mut Blake2sChannel) {
        use stwo::core::channel::Channel;
        channel.mix_u64(self.log_n_rows as u64);
        channel.mix_u64(self.group_width as u64);
    }
}

/// Pack a `Vec<u32>` multiplicity vector into a SIMD `BaseColumn`-backed
/// `CircleEvaluation` at the given `log_size`. The vector's length must
/// equal `1 << log_size`.
fn mult_col_to_eval(
    mults: &[u32],
    log_size: u32,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    debug_assert_eq!(mults.len(), 1usize << log_size);
    let domain = CanonicCoset::new(log_size).circle_domain();
    let col: BaseColumn = mults.iter().map(|&m| BaseField::from(m)).collect();
    CircleEvaluation::new(domain, col)
}

/// log_sizes of every base-trace column in commit order. The Sha256Eval
/// block first (`TOTAL_COLS` × `log_n_rows`), then one mult col per
/// producer component.
fn base_trace_log_sizes(log_n_rows: u32, group_width: u32) -> Vec<u32> {
    let mut out = vec![log_n_rows; Layout::TOTAL_COLS];
    // 8 decode mults, each at log_size 16.
    out.extend(std::iter::repeat_n(LOG_SIZE_16, DECODE_TABLES.len()));
    // 2 Maj/Ch mults, each at log_size 3W.
    out.extend(std::iter::repeat_n(maj_ch_log_size(group_width), 2));
    // xor_8 mult.
    out.push(LOG_SIZE_16);
    // 4 round + 4 σ split-pack mults.
    out.extend(std::iter::repeat_n(LOG_SIZE_16, ROUND_SPLIT_TABLES.len()));
    out.extend(std::iter::repeat_n(LOG_SIZE_16, SIGMA_SPLIT_TABLES.len()));
    // 4 range mults, each at its own `range_log_size(kind)`.
    for &kind in RANGE_TABLES {
        out.push(range_log_size(kind));
    }
    out
}

/// log_sizes of every interaction-trace column in commit order. Each
/// component's column count is `(n_lookups + 1) / 2`. We infer the count
/// from the structural firing rule (matching the
/// `interaction::sha256_interaction` derivation).
fn interaction_trace_log_sizes(
    log_n_rows: u32,
    group_width: u32,
    _claim: &InteractionClaim,
) -> Vec<u32> {
    let mut out = Vec::new();

    // Each SecureField interaction column expands to SECURE_EXTENSION_DEGREE = 4
    // base-field columns at the same log_size.
    const EXT: usize = stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;

    // Sha256Eval consumer: 3464 lookups per block → 1732 paired columns.
    // Sized at log_n_rows. See `interaction::sha256_interaction` for the
    // per-block lookup-count breakdown.
    let sha_cols = num_paired_cols(3464);
    out.extend(std::iter::repeat_n(log_n_rows, sha_cols * EXT));
    // 8 decode producers: 1 lookup each → 1 column each at log_size 16.
    for _ in DECODE_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    }
    // Maj/Ch: 2 lookups → 1 paired column at log_size 3W.
    out.extend(std::iter::repeat_n(
        maj_ch_log_size(group_width),
        num_paired_cols(2) * EXT,
    ));
    // xor_8: 1 lookup → 1 column at log_size 16.
    out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    // 4 round split-pack: 1 lookup each.
    for _ in ROUND_SPLIT_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    }
    // 4 σ split-pack: 1 lookup each.
    for _ in SIGMA_SPLIT_TABLES {
        out.extend(std::iter::repeat_n(LOG_SIZE_16, num_paired_cols(1) * EXT));
    }
    // 4 Range_k producers: 1 lookup each, at the kind's own log_size.
    for &kind in RANGE_TABLES {
        out.extend(std::iter::repeat_n(
            range_log_size(kind),
            num_paired_cols(1) * EXT,
        ));
    }
    out
}

/// Number of interaction columns produced by `n_lookups` lookups under
/// pair-batching: `ceil(n_lookups / 2)`.
#[inline]
const fn num_paired_cols(n_lookups: usize) -> usize {
    n_lookups.div_ceil(2)
}

/// Aggregate of every `FrameworkComponent` in the proof, in commit order.
struct Sha256Components {
    sha256: FrameworkComponent<Sha256Eval>,
    decode: Vec<FrameworkComponent<SigmaDecodeEval>>, // 8
    maj_ch: FrameworkComponent<MajChEval>,
    xor_8: FrameworkComponent<Xor8Eval>,
    round_split_pack: Vec<FrameworkComponent<RoundSplitPackEval>>, // 4
    sigma_split_pack: Vec<FrameworkComponent<SigmaSplitPackEval>>, // 4
    range: Vec<FrameworkComponent<RangeKEval>>,                    // 4
}

impl Sha256Components {
    fn new(
        claim: &InteractionClaim,
        relations: &Sha256Relations,
        log_n_rows: u32,
        group_width: u32,
    ) -> Self {
        // The TraceLocationAllocator runs the same component order on
        // prover and verifier; it consumes preprocessed column IDs in
        // the order each component's `evaluate` reads them. We seed it with
        // the static list from `crate::components::all_preprocessed_column_ids`
        // — the single source of truth for column order — and let each
        // FrameworkComponent claim its slice.
        let alloc_ids = all_preprocessed_column_ids();
        let allocator = &mut TraceLocationAllocator::new_with_preprocessed_columns(&alloc_ids);

        let sha256 = FrameworkComponent::new(
            allocator,
            Sha256Eval {
                log_size: log_n_rows,
                relations: relations.clone(),
            },
            claim.sha256.claimed_sum,
        );

        let mut decode = Vec::with_capacity(8);
        for (i, &(f, h)) in DECODE_TABLES.iter().enumerate() {
            decode.push(FrameworkComponent::new(
                allocator,
                SigmaDecodeEval {
                    log_size: LOG_SIZE_16,
                    f,
                    half: h,
                    relations: relations.clone(),
                },
                claim.decode[i].claimed_sum,
            ));
        }
        let maj_ch = FrameworkComponent::new(
            allocator,
            MajChEval {
                log_size: maj_ch_log_size(group_width),
                relations: relations.clone(),
            },
            claim.maj_ch.claimed_sum,
        );
        let xor_8 = FrameworkComponent::new(
            allocator,
            Xor8Eval {
                log_size: LOG_SIZE_16,
                relations: relations.clone(),
            },
            claim.xor_8.claimed_sum,
        );
        let mut round_split_pack = Vec::with_capacity(4);
        for (i, &(p, h)) in ROUND_SPLIT_TABLES.iter().enumerate() {
            round_split_pack.push(FrameworkComponent::new(
                allocator,
                RoundSplitPackEval {
                    log_size: LOG_SIZE_16,
                    partition: p,
                    half: h,
                    relations: relations.clone(),
                },
                claim.round_split_pack[i].claimed_sum,
            ));
        }
        let mut sigma_split_pack = Vec::with_capacity(4);
        for (i, &(p, h)) in SIGMA_SPLIT_TABLES.iter().enumerate() {
            sigma_split_pack.push(FrameworkComponent::new(
                allocator,
                SigmaSplitPackEval {
                    log_size: LOG_SIZE_16,
                    partition: p,
                    half: h,
                    relations: relations.clone(),
                },
                claim.sigma_split_pack[i].claimed_sum,
            ));
        }
        let mut range = Vec::with_capacity(4);
        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            range.push(FrameworkComponent::new(
                allocator,
                RangeKEval {
                    log_size: range_log_size(kind),
                    kind,
                    relations: relations.clone(),
                },
                claim.range[i].claimed_sum,
            ));
        }

        Self {
            sha256,
            decode,
            maj_ch,
            xor_8,
            round_split_pack,
            sigma_split_pack,
            range,
        }
    }

    fn components(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = Vec::new();
        out.push(&self.sha256);
        for c in &self.decode {
            out.push(c);
        }
        out.push(&self.maj_ch);
        out.push(&self.xor_8);
        for c in &self.round_split_pack {
            out.push(c);
        }
        for c in &self.sigma_split_pack {
            out.push(c);
        }
        for c in &self.range {
            out.push(c);
        }
        out
    }

    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = Vec::new();
        out.push(&self.sha256);
        for c in &self.decode {
            out.push(c);
        }
        out.push(&self.maj_ch);
        out.push(&self.xor_8);
        for c in &self.round_split_pack {
            out.push(c);
        }
        for c in &self.sigma_split_pack {
            out.push(c);
        }
        for c in &self.range {
            out.push(c);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
