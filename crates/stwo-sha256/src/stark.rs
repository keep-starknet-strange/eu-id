//! Prover and verifier entry points for the standalone SHA-256 component.
//!
//! Full plumbing: preprocessed-trace commitment of every lookup table
//! (`crate::preprocessed`), base-trace commitment of the Sha256Eval trace
//! plus the producer-side multiplicity columns, interaction trace per
//! component (`crate::interaction`), and finally Stwo's `prove<SimdBackend>`
//! over the 19 components in `crate::components`.
//!
//! Component composition pattern matches `../sha256-air/src/lib.rs`
//! (structural reference) and the Blake example in
//! `stwo/examples/blake/air.rs`. The constraint layer is sound for the
//! Σ/σ/Maj/Ch/xor_8/split-pack lookups; carry range-checks are still
//! deferred to roadmap 3.9.2 — they will slot into `Sha256Eval` above the
//! existing `finalize_logup_in_pairs()` call without disturbing this
//! pipeline.
//!
//! Order discipline: every `mix_into` on the channel **must** happen in
//! the same order on the prover and verifier sides — drift silently
//! breaks the verifier's challenge re-derivation.

use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec};
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
    all_preprocessed_column_ids, MajChEval, RoundSplitPackEval, Sha256Relations, SigmaDecodeEval,
    SigmaSplitPackEval, Xor8Eval, DECODE_TABLES, ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::constants::DIGEST_BYTES;
use crate::constraints::Sha256Eval;
use crate::interaction::{generate_interaction_trace, InteractionClaim};
use crate::multiplicities::{
    decode_multiplicities, maj_ch_multiplicities, round_split_pack_multiplicities,
    sigma_split_pack_multiplicities, xor_8_multiplicities,
};
use crate::preprocessed::{generate_preprocessed_trace, maj_ch_log_size, LOG_SIZE_16};
use crate::trace::Layout;
use crate::types::{Digest, Sha256Witness};
use crate::witness::compute_sha256_witness;

/// Tuning knobs for the prover. Defaults pick a sensible starting point;
/// the laptop benchmark (the post-week-2 go/no-go gate in the roadmap)
/// is what pins the final values.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// `log2` of the SHA-256 component's trace row count. Each row is one
    /// padded block. `log_n_rows = trace::min_log_size(witness.blocks.len())`
    /// is the minimum legal value; pass a larger value to absorb future
    /// blocks into the same component without re-generating preprocessed
    /// tables. Must be `≥ LOG_N_LANES = 4` for the SIMD backend.
    pub log_n_rows: u32,
    /// Group width `W` for the packed `Maj`/`Ch` table. `7` is the minimum
    /// without subdividing the existing partitions' 7-bit groups; smaller
    /// `W` values require a partition rework (design §9.2 sketches the
    /// `W = 6` "subdivide 7-bit groups" path as a future micro-optimisation
    /// the laptop/mobile benchmark — 3.9.12 — can pin). The packed-table
    /// size is `2^(3W)` rows; at `W = 7` that is `2²¹ ≈ 2.1 M` rows.
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

/// A STARK proof that a private message hashes to the public `digest`.
///
/// `digest` and `n_blocks` are the public-input surface; the integration
/// stream binds the digest into the Big AIR via LogUp.
#[derive(Clone, Debug)]
pub struct Sha256Proof {
    /// The 32-byte digest that the prover claims the (private) message
    /// hashes to. Exposed as a public input.
    pub digest: [u8; DIGEST_BYTES],
    /// Number of blocks in the padded preimage.
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
}

impl core::fmt::Display for Sha256VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StarkRejected(msg) => write!(f, "Stwo verifier rejected proof: {msg}"),
            Self::LogupSumNonZero => write!(
                f,
                "LogUp claimed-sums total is non-zero: consumer ⇄ producer balance broken"
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

    prove_sha256_inner(&witness, config)
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
    // blow-up. Among our 19 components, Maj/Ch is the biggest at `3W`
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
    let (preprocessed_evals, preprocessed_ids, _log_sizes) =
        generate_preprocessed_trace(group_width);
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
    let components_owned = Sha256Components::new(
        &interaction_claim,
        &relations,
        log_n_rows,
        group_width,
        &preprocessed_ids,
    );
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

/// Verify a `Sha256Proof`.
pub fn verify_sha256_proof(proof: &Sha256Proof) -> Result<(), Sha256VerifyError> {
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
    let (_, preprocessed_ids, preprocessed_log_sizes) =
        generate_preprocessed_trace(proof.group_width);
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
        &preprocessed_ids,
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

/// Convenience: derive the public input shape (digest + block count) the
/// prover *would* commit to, without running the prover. Used by the
/// integration stream to assemble its Big-AIR public input contract.
pub fn public_inputs_for(message: &[u8]) -> Sha256PublicInputs {
    let padded = crate::native::pad_message(message);
    let n_blocks = padded.len() / crate::constants::BLOCK_BYTES;
    Sha256PublicInputs {
        digest: native_digest(message).0,
        n_blocks,
    }
}

/// Public-input contract for the SHA-256 component.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sha256PublicInputs {
    pub digest: [u8; DIGEST_BYTES],
    pub n_blocks: usize,
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

    // Sha256Eval consumer: 2824 lookups per block → 1412 paired columns.
    // Sized at log_n_rows.
    let sha_cols = num_paired_cols(2824);
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
}

impl Sha256Components {
    fn new(
        claim: &InteractionClaim,
        relations: &Sha256Relations,
        log_n_rows: u32,
        group_width: u32,
        preprocessed_ids: &[stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId],
    ) -> Self {
        // The TraceLocationAllocator runs the same component order on
        // prover and verifier; it consumes preprocessed column IDs in
        // the order each component's `evaluate` reads them. We seed it
        // with the static list from `crate::components::all_preprocessed_column_ids`
        // and let each FrameworkComponent claim its slice.
        let _ = preprocessed_ids; // pinned by `all_preprocessed_column_ids` call below
        let alloc_ids = all_preprocessed_column_ids(group_width);
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

        Self {
            sha256,
            decode,
            maj_ch,
            xor_8,
            round_split_pack,
            sigma_split_pack,
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
        out
    }
}

// Silence-warnings hook for imports that the body uses through trait
// methods only.
#[allow(dead_code)]
fn _imports_pinned() {
    let _ = SecureField::zero();
    let _: TreeVec<Vec<u32>> = TreeVec::default();
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
}
