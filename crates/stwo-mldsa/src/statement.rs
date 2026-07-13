//! `MlDsaAir` — the composed in-circuit ML-DSA-65 statement (M6).
//!
//! ONE air-core module pair ([`MlDsaProver`] impl `Air`+`AirProver`,
//! [`MlDsaVerifier`] impl `Air`) proves the entire ML-DSA-65 verification via a
//! single [`air_core::prove`] / [`air_core::verify`] call. It stitches together:
//!
//!   * `coeffs` — the tall bivariate-Horner integer-lift component (yields the
//!     W-cell / C-cell bindings + verifier-native fold).
//!   * `decomp` — [DECOMP]+[HINT]; consumes W-cells, yields the 768 `w1Encode`
//!     bytes into the c̃-absorb stream.
//!   * `sib`         — SampleInBall FSM; consumes C-cells + the SIB squeeze stream.
//!   * `msglink`     — the public message-byte producer (M7 swap point).
//!   * bridges / prefix / sinks ([`crate::sponge_link`]) that move bytes between
//!     the three HashIo streams and close the squeeze balance.
//!
//! Since S1, the three SHAKE-256 sponge chains (µ, c̃, SIB) are NOT proven by
//! this module: they are jobs of the proof-wide
//! [`stwo_keccak::service::KeccakServiceProver`], which owns the rotated
//! sponge + keccak + round + tables ONCE for all hosted instances and
//! publishes the drawn [`KeccakRelations`] through a
//! [`SharedKeccakRelations`] handle this module consumes. The instance exposes
//! its sponge job shapes via [`keccak_job_shapes`] / [`MlDsaProver::keccak_jobs`]
//! so the host can build the service, and takes an explicit per-instance
//! `stream_base` so HashIo stream ids stay globally unique under the ONE
//! shared relation set.
//!
//! ## Fixed component commit order (POSITIONAL across every method)
//!
//! ```text
//!  1. coeffs                       8. prefix producer
//!  2. coeffs rc tables ×5          9. msg bridge
//!  3. decomp                      10. mu→ct bridge
//!  4. decomp rc tables ×4         11. w1enc bridge
//!  5. sib                         12. ct→sib bridge
//!  6. sib rc tables ×3            13. mu sink
//!  7. msglink (standalone only)   14. ct sink
//!                                 15. sib sink
//! ```
//!
//! Any drift between `layout()`, `claimed_sums()`, `write_trace()`,
//! `write_interaction()`, `build_components()`, `components()` breaks
//! verification. Every component keeps `max_constraint_log_degree_bound ==
//! log_size + 1`; the module-level bound only sizes the twiddles.

use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, ProvingError, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{FrameworkComponent, Relation, TraceLocationAllocator};

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use stwo_keccak::relations::{KeccakRelations, SharedKeccakRelations};
use stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_keccak::sponge::Shape;

use crate::air_util::{m31, padded_log_size, ColEval};
use crate::binding::{
    CCellRelation, HashIoRelation, MsgLinkRelation, WCellRelation, STREAM_ID_CTILDE_ABSORB,
    STREAM_ID_SIB_SQUEEZE,
};
use crate::constants::{K, N};
use crate::msglink::{self, MsgLinkEval, MSG_FIELD_ID};
use crate::sponge_link::{
    BridgeEval, PubMsgEval, PublicPrefixEval, SqueezeSinkEval, SrcRelation, BRIDGE_BASE_COLS,
    BRIDGE_INTERACTION_COLS, PREFIX_BASE_COLS, PUBMSG_BASE_COLS, PUBMSG_INTERACTION_COLS,
    SINK_BASE_COLS, SINK_INTERACTION_COLS,
};
use crate::types::MlDsaVerifyInput;
use crate::verifier_native::{compute_public_evals, folded_check, ClaimedEvals};
use crate::witness::{generate_witness, MlDsaWitness, WitnessError};

use crate::coeffs::relations::CoeffsRelations;
use crate::coeffs::tables as coeffs_tables;
use crate::coeffs::{self, CoeffsEval};

use crate::decomp::relations::DecompRelations;
use crate::decomp::tables as decomp_tables;
use crate::decomp::{self, DecompEval};

use crate::sampleinball::relations::SibRelations;
use crate::sampleinball::tables as sib_tables;
use crate::sampleinball::{self, SibEval};

// =============================================================================
// Composition-layer stream-id namespacing.
// =============================================================================
//
// Since S1 every hosted ML-DSA instance shares ONE drawn HashIo relation (the
// service's), so stream ids must be globally unique per instance. Each id is
// `stream_base + OFFSET`; the per-instance `stream_base` is an explicit
// constructor parameter (deterministic, mixed into the transcript). The
// offsets keep the legacy single-instance values at `stream_base = 0`. The
// decomp / sib offsets ([`STREAM_ID_CTILDE_ABSORB`] = 0,
// [`STREAM_ID_SIB_SQUEEZE`] = 1) live in `binding.rs`. A stream base must
// therefore be a multiple of at least 16 to keep instances disjoint.

/// µ-chain absorb stream offset (`tr ‖ 0x00 ‖ 0x00 ‖ M`).
pub const MU_ABSORB: u32 = 10;
/// µ-chain squeeze stream offset.
pub const MU_SQUEEZE: u32 = 11;
/// c̃-chain absorb stream offset (`µ ‖ w1Encode(w1')`).
pub const CT_ABSORB: u32 = 12;
/// c̃-chain squeeze stream offset.
pub const CT_SQUEEZE: u32 = 13;
/// SIB-chain absorb stream offset (`c̃`).
pub const SIB_ABSORB: u32 = 14;

/// Minimum spacing between two instances' `stream_base` values (offsets 0..15
/// are in use per instance).
pub const STREAM_BASE_STRIDE: u32 = 16;

/// SHAKE-256 rate in bytes (block length of a squeeze).
const RATE: usize = 136;

/// The `field_id` the HOST yields the whole ML-DSA message (Sig_structure)
/// window under, on the shared [`FieldBytesRelation`], in hosted mode. The mdoc
/// issuer SHA pass exposes the µ-absorb message bytes under this id; the mldsa
/// msg bridge requires them under the same id. Distinct from the standalone
/// `MSG_FIELD_ID` (which keys the self-drawn `MsgLinkRelation`).
pub const HOSTED_MSG_FIELD_ID: u32 = 0;

// =============================================================================
// Perm-id namespacing plan (extended from the M6 placeholder).
// =============================================================================

/// Disjoint `perm_id_base` assignment across the three SHAKE-256 sponge chains
/// (M3 carry-forward): each chain's Keccak-f[1600] permutation ids are offset so
/// the shared [`stwo_keccak::relations::KeccakStateRelation`] never crosses
/// chains. The base of chain `n+1` is the running perm count after chain `n`.
///
/// Since S1 the assignment is executed by
/// [`stwo_keccak::sponge_v::JobList::new`] over the proof-wide concatenated
/// job list (this struct documents the per-instance invariant and remains the
/// reference for the disjointness argument).
#[derive(Clone, Copy, Debug)]
pub struct PermIdPlan {
    pub mu_base: usize,
    pub c_tilde_base: usize,
    pub sib_base: usize,
}

impl PermIdPlan {
    /// Build the plan from each chain's permutation count, laid out contiguously
    /// and disjointly: µ occupies `[0, n_mu)`, c̃ `[n_mu, n_mu+n_ct)`, SIB the rest.
    pub fn new(n_mu: usize, n_c_tilde: usize) -> Self {
        Self {
            mu_base: 0,
            c_tilde_base: n_mu,
            sib_base: n_mu + n_c_tilde,
        }
    }

    /// Build the plan directly from the three sponge shapes (the composition's
    /// single source of truth for perm bases).
    pub fn from_shapes(mu: &Shape, ct: &Shape) -> Self {
        Self::new(mu.n_perms(), ct.n_perms())
    }
}

// =============================================================================
// Public proof struct.
// =============================================================================

/// The public statement + all prover claims of a composed ML-DSA-65 proof.
///
/// The verifier reconstructs every component's shape from `input` +
/// `sib_stream_len` + the claimed sums, with NO witness.
#[derive(Clone, Serialize, Deserialize)]
pub struct MlDsaProof {
    pub input: MlDsaVerifyInput,
    /// The 30 claimed `P̂(r,s)` group evaluations (coeffs), in poly_id order.
    pub group_evals: Vec<SecureField>,
    /// Every component's claimed sum, in commit order, then `native_use_sum` LAST.
    pub claimed_sums: Vec<SecureField>,
    /// The honest SIB squeeze stream length (public — sizes the SIB squeeze +
    /// its sink; the verifier derives the SIB shape's `n_squeeze` from it).
    pub sib_stream_len: usize,
    /// The FULL native SIB squeeze length (`witness.sponge.sample_in_ball_squeezed.len()`
    /// = `136 · n_squeeze_sib(sib_stream_len)`, block-aligned on-demand squeeze).
    /// Public — sizes the sib component's log size.
    /// Reveals nothing secret; it is a length, not a value.
    pub sib_squeezed_len: usize,
    /// The keccak service module's claimed sums (`[sponge_v, keccak, round,
    /// tables ×9]`) — the standalone proof composes `[service, mldsa]`.
    pub service_claimed_sums: Vec<SecureField>,
    /// Per-module opaque post-interaction payloads (module order == prove
    /// order): the service's round-GKR proof blob first, an empty entry for
    /// the mldsa module. Gated fail-closed in `verify_mldsa`.
    pub post_interaction_payloads: Vec<Vec<u8>>,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

// =============================================================================
// Shared shape derivation (identical prover / verifier).
// =============================================================================

/// The three sponge shapes for a statement, derived from PUBLIC data only.
///
/// * µ:  absorbs `tr ‖ 0x00 ‖ 0x00 ‖ M` (len `66 + |M|`), squeezes 1 block.
/// * c̃:  absorbs `µ ‖ w1Encode(w1')` (len 832 = 64 + 768), squeezes 1 block.
/// * SIB: absorbs `c̃` (48 bytes), squeezes `ceil(sib_stream_len / 136)` blocks.
struct Shapes {
    mu: Shape,
    ct: Shape,
    sib: Shape,
}

fn n_squeeze_sib(sib_stream_len: usize) -> usize {
    sib_stream_len.div_ceil(RATE).max(1)
}

/// The instance's three sponge job shapes, stream ids offset by `stream_base`.
/// Perm-id bases stay 0 — the proof-wide [`stwo_keccak::sponge_v::JobList`]
/// stamps the global plan over the concatenated job list.
fn shapes(message_len: usize, sib_stream_len: usize, stream_base: u32) -> Shapes {
    let b = stream_base;
    let mu = Shape::new(66 + message_len, 1, b + MU_ABSORB, b + MU_SQUEEZE);
    let ct = Shape::new(64 + 768, 1, b + CT_ABSORB, b + CT_SQUEEZE);
    let sib = Shape::new(
        48,
        n_squeeze_sib(sib_stream_len),
        b + SIB_ABSORB,
        b + STREAM_ID_SIB_SQUEEZE,
    );
    Shapes { mu, ct, sib }
}

/// PUBLIC: the sponge job shapes this instance contributes to the proof-wide
/// keccak service, in job order (µ, c̃, SIB). Both the host's prover and
/// verifier derive these from public data only.
pub fn keccak_job_shapes(
    message_len: usize,
    sib_stream_len: usize,
    stream_base: u32,
) -> Vec<Shape> {
    let sh = shapes(message_len, sib_stream_len, stream_base);
    vec![sh.mu, sh.ct, sh.sib]
}

// =============================================================================
// Component log sizes (public-derivable).
// =============================================================================

fn coeffs_log_size() -> u32 {
    padded_log_size(coeffs::layout::active_rows())
}
fn decomp_log_size() -> u32 {
    padded_log_size(decomp::N_PAIRS)
}
/// The sib component's log size (replicate `sampleinball/proof.rs::sib_log_size`).
/// `sib_squeezed_len` is the FULL SIB squeeze length (`136·n_squeeze_sib`).
fn sib_log_size(sib_squeezed_len: usize) -> u32 {
    padded_log_size((sib_squeezed_len + N).max(sampleinball::N_ACCESSES))
}

// =============================================================================
// Shared relations (ONE draw fn used by both sides, fixed order).
// =============================================================================

/// The full relation set of the composed statement.
#[derive(Clone)]
struct Relations {
    rho_rlc: SecureField,
    r: SecureField,
    s: SecureField,
    keccak: KeccakRelations,
    msglink: MsgLinkRelation,
    /// Hosted mode: the shared message-source relation read from the host handle
    /// (`None` in standalone mode, where the self-drawn `msglink` producer is used).
    shared_field: Option<FieldBytesRelation>,
    coeffs: CoeffsRelations,
    decomp: DecompRelations,
    sib: SibRelations,
}

/// Draw every relation in the identical order both sides use. `wcell` / `ccell`
/// are drawn once here and threaded into the coeffs (yield) and decomp/sib
/// (consume) `draw_with` constructors; `keccak.hash_io` is the shared byte-I/O
/// relation for the bridges, sinks, prefix, decomp, and sib — READ from the
/// keccak service's handle (the service module drew it earlier in module
/// order), never drawn here.
fn draw_relations_common(
    channel: &mut Blake2sChannel,
    hosted_field: Option<&SharedFieldRelation>,
    keccak_handle: &SharedKeccakRelations,
) -> Relations {
    let rho_rlc = channel.draw_secure_felt();
    let r = channel.draw_secure_felt();
    let s = channel.draw_secure_felt();

    let keccak = keccak_handle.get();

    let wcell = WCellRelation::draw(channel);
    let ccell = CCellRelation::draw(channel);
    // Standalone: draw the self-owned msglink producer relation. Hosted: the msg
    // source is the host's already-drawn shared FieldBytesRelation, so we draw
    // NOTHING here (the transcript slot belongs to the host) and read the handle.
    let (msglink, shared_field) = match hosted_field {
        None => (MsgLinkRelation::draw(channel), None),
        Some(handle) => (MsgLinkRelation::dummy(), Some(handle.get())),
    };

    let coeffs = CoeffsRelations::draw_with(channel, wcell.clone(), ccell.clone());
    let decomp = DecompRelations::draw_with(channel, wcell, keccak.hash_io.clone());
    let sib = SibRelations::draw_with(channel, ccell, keccak.hash_io.clone());

    Relations {
        rho_rlc,
        r,
        s,
        keccak,
        msglink,
        shared_field,
        coeffs,
        decomp,
        sib,
    }
}

/// The verifier-native EvalAtRs USE sum: `+Σ_id 1/combine(poly_id, coords)`
/// (copy of `crate::proof::native_use_sum`).
fn native_use_sum(group_evals: &[SecureField], relations: &CoeffsRelations) -> SecureField {
    let one = SecureField::from(m31(1));
    let mut sum = SecureField::zero();
    for (poly_id, eval) in group_evals.iter().enumerate() {
        let coords = eval.to_m31_array();
        let tuple = [
            m31(poly_id as u32),
            coords[0],
            coords[1],
            coords[2],
            coords[3],
        ];
        let denom: SecureField = relations.eval.combine(&tuple);
        sum += one / denom;
    }
    sum
}

// =============================================================================
// mix_public (identical both sides).
// =============================================================================

fn mix_public(
    channel: &mut Blake2sChannel,
    input: &MlDsaVerifyInput,
    sib_stream_len: usize,
    namespace: &str,
    private_message: bool,
    stream_base: u32,
) {
    // Instance role/domain separation: two hosted instances with compatible
    // shapes must still produce disjoint transcripts, so a device claim tree
    // can never be replayed against the revocation slot (or vice versa).
    channel.mix_u64(namespace.len() as u64);
    for b in namespace.as_bytes() {
        channel.mix_u64(*b as u64);
    }
    // ρ bytes.
    for b in &input.rho {
        channel.mix_u64(*b as u64);
    }
    // t1 coeffs (copy of proof.rs::mix_public).
    for i in 0..K {
        for m in 0..N {
            channel.mix_u64(input.t1[i][m] as u64);
        }
    }
    // tr bytes.
    for b in &input.tr {
        channel.mix_u64(*b as u64);
    }
    // Message length + bytes. Private-message mode (revocation: the signed
    // bytes carry the PRIVATE id_lo/id_hi bounds) mixes only the length: the
    // bytes never appear in the statement and flow exclusively through the
    // host's FieldBytesRelation into the in-circuit µ absorption, exactly like
    // the already-private c̃/µ streams below.
    channel.mix_u64(input.message.len() as u64);
    if !private_message {
        for b in &input.message {
            channel.mix_u64(*b as u64);
        }
    }
    // public SIB stream length.
    channel.mix_u64(sib_stream_len as u64);
    // The per-instance stream-id base: pins every HashIo stream id this
    // instance's bridges/sinks/decomp/sib use under the SHARED relation set.
    // (The sponge job shapes themselves are mixed ONCE by the keccak service.)
    channel.mix_u64(stream_base as u64);
    // NOTE: c̃ and µ stay PRIVATE — never mixed; they flow only through HashIo.
    // group_evals are mixed with the claimed sums (post base-commit).
}

// =============================================================================
// Bridge / sink / prefix descriptors (public-derivable shapes).
// =============================================================================

fn bridge_log_size(len: usize) -> u32 {
    padded_log_size(len).max(LOG_N_LANES)
}

/// The public-prefix producer: `tr ‖ 0x00 ‖ 0x00` (66 bytes) into µ-absorb@0.
fn prefix_eval(
    input: &MlDsaVerifyInput,
    stream_base: u32,
    hash_io: &HashIoRelation,
) -> PublicPrefixEval {
    let mut bytes = Vec::with_capacity(66);
    bytes.extend_from_slice(&input.tr);
    bytes.push(0x00);
    bytes.push(0x00);
    PublicPrefixEval {
        dst_stream: stream_base + MU_ABSORB,
        dst_off: 0,
        bytes,
        hash_io: hash_io.clone(),
    }
}

/// The message slot at commit order 9: a msg BRIDGE (standalone / hosted
/// private message — source MsgLink or the host's shared FieldBytesRelation),
/// or the PUBLIC-message producer (S4: hosted public message — the bytes are
/// preprocessed content, no source consumption, no byte conveyor upstream).
enum MsgSlot {
    Bridge(Box<BridgeEval>),
    Public(PubMsgEval),
}

impl MsgSlot {
    fn preprocessed_ids(&self) -> Vec<PreProcessedColumnId> {
        match self {
            MsgSlot::Bridge(b) => b.preprocessed_ids(),
            MsgSlot::Public(p) => p.preprocessed_ids(),
        }
    }
    fn gen_preprocessed(&self) -> Vec<ColEval> {
        match self {
            MsgSlot::Bridge(b) => b.gen_preprocessed(),
            MsgSlot::Public(p) => p.gen_preprocessed(),
        }
    }
    /// Base trace; `message` is the msg-bridge byte payload (unused by the
    /// public producer, whose bytes are preprocessed).
    fn gen_base(&self, message: &[u8]) -> Vec<ColEval> {
        match self {
            MsgSlot::Bridge(b) => b.gen_base(message),
            MsgSlot::Public(p) => p.gen_base(),
        }
    }
    fn gen_interaction(&self, message: &[u8]) -> (Vec<ColEval>, SecureField) {
        match self {
            MsgSlot::Bridge(b) => b.gen_interaction(message),
            MsgSlot::Public(p) => p.gen_interaction(),
        }
    }
}

/// The commit-order-9 message slot descriptor. In public-message mode the
/// producer carries the PUBLIC bytes; otherwise the msg bridge sources from
/// the standalone MsgLink producer or the host's shared FieldBytesRelation.
fn msg_slot(
    ns: &str,
    message: &[u8],
    stream_base: u32,
    public_message: bool,
    msglink: &MsgLinkRelation,
    shared_field: Option<&FieldBytesRelation>,
    hash_io: &HashIoRelation,
) -> MsgSlot {
    let b = stream_base;
    if public_message {
        return MsgSlot::Public(PubMsgEval {
            ns: ns.to_string(),
            log_size: bridge_log_size(message.len()),
            dst_stream: b + MU_ABSORB,
            dst_off: 66,
            bytes: message.to_vec(),
            hash_io: hash_io.clone(),
        });
    }
    // msg bridge → MU_ABSORB@66, len |M|. Source is the standalone MsgLink
    // producer, OR (hosted) the host's shared FieldBytesRelation.
    let msg_src = match shared_field {
        None => SrcRelation::MsgLink(msglink.clone(), MSG_FIELD_ID),
        Some(field) => SrcRelation::FieldBytes(field.clone(), HOSTED_MSG_FIELD_ID),
    };
    MsgSlot::Bridge(Box::new(BridgeEval {
        tag: "msg",
        ns: ns.to_string(),
        log_size: bridge_log_size(message.len()),
        src: msg_src,
        dst_stream: b + MU_ABSORB,
        dst_off: 66,
        len: message.len(),
        hash_io: hash_io.clone(),
    }))
}

/// The three fixed bridges (order 10..12).
fn bridge_evals(ns: &str, stream_base: u32, hash_io: &HashIoRelation) -> [BridgeEval; 3] {
    let b = stream_base;
    // 10. µ→c̃ bridge: HashIo(MU_SQUEEZE, off 0) → CT_ABSORB@0, len 64.
    let mu_ct = BridgeEval {
        tag: "mu_ct",
        ns: ns.to_string(),
        log_size: bridge_log_size(64),
        src: SrcRelation::HashIo(hash_io.clone(), b + MU_SQUEEZE, 0),
        dst_stream: b + CT_ABSORB,
        dst_off: 0,
        len: 64,
        hash_io: hash_io.clone(),
    };
    // 11. w1Encode bridge: HashIo(ctilde_absorb, off 0) → CT_ABSORB@64, len 768.
    let w1enc = BridgeEval {
        tag: "w1enc",
        ns: ns.to_string(),
        log_size: bridge_log_size(768),
        src: SrcRelation::HashIo(hash_io.clone(), b + STREAM_ID_CTILDE_ABSORB, 0),
        dst_stream: b + CT_ABSORB,
        dst_off: 64,
        len: 768,
        hash_io: hash_io.clone(),
    };
    // 12. c̃→SIB bridge: HashIo(CT_SQUEEZE, off 0) → SIB_ABSORB@0, len 48.
    let ct_sib = BridgeEval {
        tag: "ct_sib",
        ns: ns.to_string(),
        log_size: bridge_log_size(48),
        src: SrcRelation::HashIo(hash_io.clone(), b + CT_SQUEEZE, 0),
        dst_stream: b + SIB_ABSORB,
        dst_off: 0,
        len: 48,
        hash_io: hash_io.clone(),
    };
    [mu_ct, w1enc, ct_sib]
}

/// The three squeeze sinks (order 13..15): consume the unused squeeze tails.
fn sink_evals(
    ns: &str,
    message_len: usize,
    sib_stream_len: usize,
    stream_base: u32,
    hash_io: &HashIoRelation,
) -> [SqueezeSinkEval; 3] {
    let b = stream_base;
    let sh = shapes(message_len, sib_stream_len, b);
    // 13. µ sink: MU_SQUEEZE, off 64, len 136·n_squeeze_mu − 64.
    let mu_len = RATE * sh.mu.n_squeeze - 64;
    let mu = SqueezeSinkEval {
        tag: "mu",
        ns: ns.to_string(),
        log_size: bridge_log_size(mu_len),
        stream: b + MU_SQUEEZE,
        off: 64,
        len: mu_len,
        hash_io: hash_io.clone(),
    };
    // 14. c̃ sink: CT_SQUEEZE, off 48, len 136·n_squeeze_ct − 48.
    let ct_len = RATE * sh.ct.n_squeeze - 48;
    let ct = SqueezeSinkEval {
        tag: "ct",
        ns: ns.to_string(),
        log_size: bridge_log_size(ct_len),
        stream: b + CT_SQUEEZE,
        off: 48,
        len: ct_len,
        hash_io: hash_io.clone(),
    };
    // 15. SIB sink: SIB_SQUEEZE, off sib_stream_len, len 136·n_squeeze_sib − sib_stream_len.
    let sib_len = RATE * sh.sib.n_squeeze - sib_stream_len;
    let sib = SqueezeSinkEval {
        tag: "sib",
        ns: ns.to_string(),
        log_size: bridge_log_size(sib_len),
        stream: b + STREAM_ID_SIB_SQUEEZE,
        off: sib_stream_len as u32,
        len: sib_len,
        hash_io: hash_io.clone(),
    };
    [mu, ct, sib]
}

// =============================================================================
// Preprocessed ids + generation (positional).
// =============================================================================

/// Preprocessed column ids in commit order. msglink + prefix contribute NONE;
/// the keccak side (sponges/keccak/round/tables) lives in the SERVICE module
/// since S1 and contributes nothing here; bridges + sinks do.
///
/// This is called BEFORE relations are drawn (air-core commits the preprocessed
/// tree first), so the bridge/sink descriptors use `dummy()` relations — their
/// `preprocessed_ids()` read only `tag` + public shape, never the relation (and
/// never the stream ids, so `stream_base = 0` here is shape-neutral).
fn all_preprocessed_ids(
    ns: &str,
    input: &MlDsaVerifyInput,
    sib_stream_len: usize,
    public_message: bool,
) -> Vec<PreProcessedColumnId> {
    let hash_io = HashIoRelation::dummy();
    let msglink = MsgLinkRelation::dummy();
    let mut ids = Vec::new();
    // coeffs (+ its rc kinds).
    ids.extend(coeffs::coeffs_preprocessed_ids());
    for kind in coeffs_tables::RcKind::ALL {
        ids.push(kind.value_column_id());
    }
    // decomp (+ its rc kinds).
    ids.extend(decomp::decomp_preprocessed_ids());
    for kind in decomp_tables::RcKind::ALL {
        ids.push(kind.value_column_id());
    }
    // sib (+ its rc kinds).
    ids.extend(sampleinball::sib_preprocessed_ids_ns(ns));
    for kind in sib_tables::RcKind::ALL {
        ids.push(kind.value_column_id());
    }
    // msg slot + 3 bridges + 3 sinks.
    ids.extend(
        msg_slot(
            ns,
            &input.message,
            0,
            public_message,
            &msglink,
            None,
            &hash_io,
        )
        .preprocessed_ids(),
    );
    for b in bridge_evals(ns, 0, &hash_io) {
        ids.extend(b.preprocessed_ids());
    }
    for s in sink_evals(ns, input.message.len(), sib_stream_len, 0, &hash_io) {
        ids.extend(s.preprocessed_ids());
    }
    ids
}

fn all_preprocessed_log_sizes(
    input: &MlDsaVerifyInput,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
    public_message: bool,
) -> Vec<u32> {
    let mut sizes = Vec::new();
    let cls = coeffs_log_size();
    sizes.extend(vec![cls; coeffs::coeffs_preprocessed_ids().len()]);
    for kind in coeffs_tables::RcKind::ALL {
        sizes.push(kind.log_size());
    }
    let dls = decomp_log_size();
    sizes.extend(vec![dls; decomp::decomp_preprocessed_ids().len()]);
    for kind in decomp_tables::RcKind::ALL {
        sizes.push(kind.log_size());
    }
    let sls = sib_log_size(sib_squeezed_len);
    sizes.extend(vec![sls; sampleinball::sib_preprocessed_ids().len()]);
    for kind in sib_tables::RcKind::ALL {
        sizes.push(kind.log_size());
    }
    // msg slot: the public producer has 3 preprocessed cols, the bridge 2.
    let msg_pre_cols = if public_message {
        PUBMSG_PREPROCESSED_COLS
    } else {
        2
    };
    sizes.extend(vec![bridge_log_size(input.message.len()); msg_pre_cols]);
    for len in bridge_lens() {
        // each bridge contributes 2 preprocessed cols at its log_size.
        sizes.push(bridge_log_size(len));
        sizes.push(bridge_log_size(len));
    }
    for len in sink_lens(input.message.len(), sib_stream_len) {
        sizes.push(bridge_log_size(len));
        sizes.push(bridge_log_size(len));
    }
    sizes
}

/// Preprocessed column count of the public-message producer (`active`, `pos`,
/// `byte`).
const PUBMSG_PREPROCESSED_COLS: usize = 3;

fn bridge_lens() -> [usize; 3] {
    [64, 768, 48]
}
fn sink_lens(message_len: usize, sib_stream_len: usize) -> [usize; 3] {
    let sh = shapes(message_len, sib_stream_len, 0);
    [
        RATE * sh.mu.n_squeeze - 64,
        RATE * sh.ct.n_squeeze - 48,
        RATE * sh.sib.n_squeeze - sib_stream_len,
    ]
}

/// Generate every preprocessed column in commit order (prover-only; runs BEFORE
/// relations are drawn, so bridge/sink descriptors use `dummy()` relations —
/// their `gen_preprocessed()` reads only `tag` + public shape).
///
/// The sib preprocessed columns depend on the witness only through
/// `stream_len(witness)`.
fn gen_all_preprocessed(
    witness: &MlDsaWitness,
    input: &MlDsaVerifyInput,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
    public_message: bool,
) -> Vec<ColEval> {
    let hash_io = HashIoRelation::dummy();
    let msglink = MsgLinkRelation::dummy();
    let mut cols = Vec::new();
    let cls = coeffs_log_size();
    cols.extend(coeffs::gen_coeffs_preprocessed(cls));
    for kind in coeffs_tables::RcKind::ALL {
        cols.push(coeffs_tables::gen_table_preprocessed(kind));
    }
    let dls = decomp_log_size();
    cols.extend(decomp::gen_decomp_preprocessed(dls));
    for kind in decomp_tables::RcKind::ALL {
        cols.push(decomp_tables::gen_table_preprocessed(kind));
    }
    let sls = sib_log_size(sib_squeezed_len);
    cols.extend(sampleinball::gen_sib_preprocessed(witness, sls));
    for kind in sib_tables::RcKind::ALL {
        cols.push(sib_tables::gen_table_preprocessed(kind));
    }
    cols.extend(
        msg_slot(
            "",
            &input.message,
            0,
            public_message,
            &msglink,
            None,
            &hash_io,
        )
        .gen_preprocessed(),
    );
    for b in bridge_evals("", 0, &hash_io) {
        cols.extend(b.gen_preprocessed());
    }
    for s in sink_evals("", input.message.len(), sib_stream_len, 0, &hash_io) {
        cols.extend(s.gen_preprocessed());
    }
    cols
}

// =============================================================================
// Prover / verifier state.
// =============================================================================

/// The built commit-order-9 message slot component (see [`MsgSlot`]).
enum MsgSlotComponent {
    Bridge(FrameworkComponent<BridgeEval>),
    Public(FrameworkComponent<PubMsgEval>),
}

impl MsgSlotComponent {
    fn as_component(&self) -> &dyn Component {
        match self {
            MsgSlotComponent::Bridge(c) => c,
            MsgSlotComponent::Public(c) => c,
        }
    }
    fn as_prover(&self) -> &dyn ComponentProver<SimdBackend> {
        match self {
            MsgSlotComponent::Bridge(c) => c,
            MsgSlotComponent::Public(c) => c,
        }
    }
}

struct Built {
    coeffs: FrameworkComponent<CoeffsEval>,
    coeffs_rc: Vec<FrameworkComponent<coeffs_tables::RcTableEval>>,
    decomp: FrameworkComponent<DecompEval>,
    decomp_rc: Vec<FrameworkComponent<decomp_tables::RcTableEval>>,
    sib: FrameworkComponent<SibEval>,
    sib_rc: Vec<FrameworkComponent<sib_tables::RcTableEval>>,
    /// Standalone msglink producer; `None` in hosted mode (dropped from the
    /// commit order — the msg bridge sources from the host's shared relation).
    msglink: Option<FrameworkComponent<MsgLinkEval>>,
    prefix: FrameworkComponent<PublicPrefixEval>,
    /// Commit order 9: the msg bridge OR the public-message producer.
    msg: MsgSlotComponent,
    bridges: Vec<FrameworkComponent<BridgeEval>>,
    sinks: Vec<FrameworkComponent<SqueezeSinkEval>>,
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.coeffs];
        out.extend(self.coeffs_rc.iter().map(|c| c as &dyn Component));
        out.push(&self.decomp);
        out.extend(self.decomp_rc.iter().map(|c| c as &dyn Component));
        out.push(&self.sib);
        out.extend(self.sib_rc.iter().map(|c| c as &dyn Component));
        if let Some(m) = &self.msglink {
            out.push(m);
        }
        out.push(&self.prefix);
        out.push(self.msg.as_component());
        out.extend(self.bridges.iter().map(|c| c as &dyn Component));
        out.extend(self.sinks.iter().map(|c| c as &dyn Component));
        out
    }
    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = vec![&self.coeffs];
        out.extend(
            self.coeffs_rc
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.push(&self.decomp);
        out.extend(
            self.decomp_rc
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.push(&self.sib);
        out.extend(
            self.sib_rc
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        if let Some(m) = &self.msglink {
            out.push(m);
        }
        out.push(&self.prefix);
        out.push(self.msg.as_prover());
        out.extend(
            self.bridges
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out.extend(
            self.sinks
                .iter()
                .map(|c| c as &dyn ComponentProver<SimdBackend>),
        );
        out
    }
}

/// The claimed sums bag, in commit order (rc tables individually), then
/// `native_use_sum` appended LAST.
#[derive(Clone, Default)]
struct Claims {
    /// Hosted mode drops the `msglink` claim from `ordered()` / `from_flat()`.
    hosted: bool,
    coeffs: SecureField,
    coeffs_rc: Vec<SecureField>,
    decomp: SecureField,
    decomp_rc: Vec<SecureField>,
    sib: SecureField,
    sib_rc: Vec<SecureField>,
    msglink: SecureField,
    prefix: SecureField,
    bridges: Vec<SecureField>,
    sinks: Vec<SecureField>,
    native_use: SecureField,
}

impl Claims {
    fn ordered(&self) -> Vec<SecureField> {
        let mut v = vec![self.coeffs];
        v.extend(self.coeffs_rc.iter().copied());
        v.push(self.decomp);
        v.extend(self.decomp_rc.iter().copied());
        v.push(self.sib);
        v.extend(self.sib_rc.iter().copied());
        if !self.hosted {
            v.push(self.msglink);
        }
        v.push(self.prefix);
        v.extend(self.bridges.iter().copied());
        v.extend(self.sinks.iter().copied());
        v.push(self.native_use);
        v
    }

    /// Reconstruct the bag from a flat vector (verifier side). Table counts are
    /// derived from the public component structure. `hosted` omits the msglink slot.
    fn from_flat(flat: &[SecureField], hosted: bool) -> Self {
        let mut it = flat.iter().copied();
        let mut next = || it.next().expect("claimed sums length mismatch");
        let coeffs = next();
        let coeffs_rc = (0..coeffs_tables::RcKind::ALL.len())
            .map(|_| next())
            .collect();
        let decomp = next();
        let decomp_rc = (0..decomp_tables::RcKind::ALL.len())
            .map(|_| next())
            .collect();
        let sib = next();
        let sib_rc = (0..sib_tables::RcKind::ALL.len()).map(|_| next()).collect();
        let msglink = if hosted { SecureField::zero() } else { next() };
        let prefix = next();
        let bridges = (0..4).map(|_| next()).collect();
        let sinks = (0..3).map(|_| next()).collect();
        let native_use = next();
        Self {
            hosted,
            coeffs,
            coeffs_rc,
            decomp,
            decomp_rc,
            sib,
            sib_rc,
            msglink,
            prefix,
            bridges,
            sinks,
            native_use,
        }
    }
}

// =============================================================================
// Trace / interaction layouts (positional, public-derivable).
// =============================================================================

/// Everything the layout builders need that is public-derivable from
/// `(input, sib_stream_len, sib_squeezed_len)`.
struct LayoutCtx {
    hosted: bool,
    /// Hosted PUBLIC-message mode: the msg-bridge slot is the public-message
    /// producer (S4).
    public_message: bool,
    message_len: usize,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
}

impl LayoutCtx {
    fn new(
        input: &MlDsaVerifyInput,
        sib_stream_len: usize,
        sib_squeezed_len: usize,
        hosted: bool,
        public_message: bool,
    ) -> Self {
        Self {
            hosted,
            public_message,
            message_len: input.message.len(),
            sib_stream_len,
            sib_squeezed_len,
        }
    }
}

fn module_trace_layout(ctx: &LayoutCtx) -> Vec<u32> {
    let mut t = Vec::new();
    // 1. coeffs + 2. rc ×5.
    t.extend(vec![coeffs_log_size(); coeffs::N_BASE_COLS]);
    for kind in coeffs_tables::RcKind::ALL {
        t.push(kind.log_size());
    }
    // 3. decomp + 4. rc ×4.
    t.extend(vec![decomp_log_size(); decomp::N_BASE_COLS]);
    for kind in decomp_tables::RcKind::ALL {
        t.push(kind.log_size());
    }
    // 5. sib + 6. rc ×3.
    let sls = sib_log_size(ctx.sib_squeezed_len);
    t.extend(vec![sls; sampleinball::N_BASE_COLS]);
    for kind in sib_tables::RcKind::ALL {
        t.push(kind.log_size());
    }
    // 7. msglink (standalone only).
    if !ctx.hosted {
        t.extend(vec![msglink::MSGLINK_LOG_SIZE; msglink::N_BASE_COLS]);
    }
    // 8. prefix.
    t.extend(vec![crate::sponge_link::LINK_LOG_SIZE; PREFIX_BASE_COLS]);
    // 9. msg slot (public producer: 1 enabler col; bridge: enabler + byte).
    let msg_cols = if ctx.public_message {
        PUBMSG_BASE_COLS
    } else {
        BRIDGE_BASE_COLS
    };
    t.extend(vec![bridge_log_size(ctx.message_len); msg_cols]);
    // 10-12. bridges ×3.
    for len in bridge_lens() {
        let ls = bridge_log_size(len);
        t.extend(vec![ls; BRIDGE_BASE_COLS]);
    }
    // 13-15. sinks ×3.
    for len in sink_lens(ctx.message_len, ctx.sib_stream_len) {
        let ls = bridge_log_size(len);
        t.extend(vec![ls; SINK_BASE_COLS]);
    }
    t
}

fn module_interaction_layout(ctx: &LayoutCtx) -> Vec<u32> {
    let mut i = Vec::new();
    // 1. coeffs + 2. rc ×5.
    i.extend(vec![coeffs_log_size(); coeffs::N_INTERACTION_COLS]);
    for kind in coeffs_tables::RcKind::ALL {
        for _ in 0..coeffs_tables::RC_TABLE_INTERACTION_COLS {
            i.push(kind.log_size());
        }
    }
    // 3. decomp + 4. rc ×4.
    i.extend(vec![decomp_log_size(); decomp::N_INTERACTION_COLS]);
    for kind in decomp_tables::RcKind::ALL {
        for _ in 0..decomp_tables::RC_TABLE_INTERACTION_COLS {
            i.push(kind.log_size());
        }
    }
    // 5. sib + 6. rc ×3.
    let sls = sib_log_size(ctx.sib_squeezed_len);
    i.extend(vec![sls; sampleinball::N_INTERACTION_COLS]);
    for kind in sib_tables::RcKind::ALL {
        for _ in 0..sib_tables::RC_TABLE_INTERACTION_COLS {
            i.push(kind.log_size());
        }
    }
    // 7. msglink (standalone only).
    if !ctx.hosted {
        i.extend(vec![
            msglink::MSGLINK_LOG_SIZE;
            msglink::n_interaction_cols(ctx.message_len)
        ]);
    }
    // 8. prefix.
    i.extend(vec![
        crate::sponge_link::LINK_LOG_SIZE;
        prefix_n_interaction(ctx.message_len)
    ]);
    // 9. msg slot (public producer: one yield; bridge: require + yield).
    let msg_cols = if ctx.public_message {
        PUBMSG_INTERACTION_COLS
    } else {
        BRIDGE_INTERACTION_COLS
    };
    i.extend(vec![bridge_log_size(ctx.message_len); msg_cols]);
    // 10-12. bridges ×3.
    for len in bridge_lens() {
        let ls = bridge_log_size(len);
        i.extend(vec![ls; BRIDGE_INTERACTION_COLS]);
    }
    // 13-15. sinks ×3.
    for len in sink_lens(ctx.message_len, ctx.sib_stream_len) {
        let ls = bridge_log_size(len);
        i.extend(vec![ls; SINK_INTERACTION_COLS]);
    }
    i
}

/// The prefix producer's interaction column count: ONE batched accumulator
/// column for all 66 prefix bytes `tr ‖ 0x00 ‖ 0x00` (constant denominators —
/// see `PublicPrefixEval::n_interaction_cols`).
fn prefix_n_interaction(_message_len: usize) -> usize {
    stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE
}

fn layout_for(ctx: &LayoutCtx, input: &MlDsaVerifyInput) -> TreeLayout {
    TreeLayout {
        preprocessed: all_preprocessed_log_sizes(
            input,
            ctx.sib_stream_len,
            ctx.sib_squeezed_len,
            ctx.public_message,
        ),
        trace: module_trace_layout(ctx),
        interaction: module_interaction_layout(ctx),
    }
}

// =============================================================================
// Sponge outputs (native recompute — the sponges are proven in the SERVICE).
// =============================================================================

/// The FULL squeeze block stream of a SHAKE-256 job (`136 · n_squeeze` bytes):
/// what the in-service sponge yields on the job's squeeze stream, and hence
/// what the bridges + sinks must move/consume.
fn full_squeeze(absorbed: &[u8], n_squeeze: usize) -> Vec<u8> {
    crate::reference::sponge::shake256(&[absorbed], RATE * n_squeeze).0
}

/// The three jobs' full squeeze outputs (µ, c̃, SIB order), from the witness's
/// absorb transcripts.
fn sponge_outputs(witness: &MlDsaWitness) -> [Vec<u8>; 3] {
    let n_sq_sib = n_squeeze_sib(sampleinball::stream_len(witness));
    [
        full_squeeze(&witness.sponge.mu_absorbed, 1),
        full_squeeze(&witness.sponge.c_tilde_absorbed, 1),
        full_squeeze(&witness.sponge.sample_in_ball_absorbed, n_sq_sib),
    ]
}

// =============================================================================
// build_components (shared).
// =============================================================================

#[allow(clippy::too_many_arguments)]
fn build_components(
    allocator: &mut TraceLocationAllocator,
    ns: &str,
    stream_base: u32,
    ctx: &LayoutCtx,
    input: &MlDsaVerifyInput,
    rel: &Relations,
    claims: &Claims,
) -> Built {
    // 1. coeffs.
    let coeffs = FrameworkComponent::new(
        allocator,
        CoeffsEval {
            log_size: coeffs_log_size(),
            r: rel.r,
            s: rel.s,
            relations: rel.coeffs.clone(),
        },
        claims.coeffs,
    );
    // 2. coeffs rc ×5.
    let coeffs_rc = coeffs_tables::RcKind::ALL
        .iter()
        .enumerate()
        .map(|(idx, kind)| {
            FrameworkComponent::new(
                allocator,
                coeffs_tables::RcTableEval {
                    kind: *kind,
                    relation: rel.coeffs.rc(*kind).clone(),
                },
                claims.coeffs_rc[idx],
            )
        })
        .collect();
    // 3. decomp.
    let decomp = FrameworkComponent::new(
        allocator,
        DecompEval {
            log_size: decomp_log_size(),
            ct_stream: stream_base + STREAM_ID_CTILDE_ABSORB,
            relations: rel.decomp.clone(),
        },
        claims.decomp,
    );
    // 4. decomp rc ×4.
    let decomp_rc = decomp_tables::RcKind::ALL
        .iter()
        .enumerate()
        .map(|(idx, kind)| {
            FrameworkComponent::new(
                allocator,
                decomp_tables::RcTableEval {
                    kind: *kind,
                    relation: decomp_rc_relation(&rel.decomp, *kind).clone(),
                },
                claims.decomp_rc[idx],
            )
        })
        .collect();
    // 5. sib.
    let sib = FrameworkComponent::new(
        allocator,
        SibEval {
            log_size: sib_log_size(ctx.sib_squeezed_len),
            ns: ns.to_string(),
            sib_stream: stream_base + STREAM_ID_SIB_SQUEEZE,
            relations: rel.sib.clone(),
        },
        claims.sib,
    );
    // 6. sib rc ×3.
    let sib_rc = sib_tables::RcKind::ALL
        .iter()
        .enumerate()
        .map(|(idx, kind)| {
            FrameworkComponent::new(
                allocator,
                sib_tables::RcTableEval {
                    kind: *kind,
                    relation: sib_rc_relation(&rel.sib, *kind).clone(),
                },
                claims.sib_rc[idx],
            )
        })
        .collect();
    // 7. msglink (standalone only; hosted mode drops it).
    let msglink = (!claims.hosted).then(|| {
        FrameworkComponent::new(
            allocator,
            MsgLinkEval {
                message: input.message.clone(),
                msglink: rel.msglink.clone(),
            },
            claims.msglink,
        )
    });
    // 8. prefix.
    let prefix = FrameworkComponent::new(
        allocator,
        prefix_eval(input, stream_base, &rel.keccak.hash_io),
        claims.prefix,
    );
    // 9. msg slot (claims slot bridges[0] — positional across modes).
    let msg = match msg_slot(
        ns,
        &input.message,
        stream_base,
        ctx.public_message,
        &rel.msglink,
        rel.shared_field.as_ref(),
        &rel.keccak.hash_io,
    ) {
        MsgSlot::Bridge(b) => {
            MsgSlotComponent::Bridge(FrameworkComponent::new(allocator, *b, claims.bridges[0]))
        }
        MsgSlot::Public(p) => {
            MsgSlotComponent::Public(FrameworkComponent::new(allocator, p, claims.bridges[0]))
        }
    };
    // 10-12. bridges ×3 (claims slots bridges[1..=3]).
    let bridge_descs = bridge_evals(ns, stream_base, &rel.keccak.hash_io);
    let bridges = bridge_descs
        .into_iter()
        .enumerate()
        .map(|(idx, b)| FrameworkComponent::new(allocator, b, claims.bridges[idx + 1]))
        .collect();
    // 13-15. sinks ×3.
    let sink_descs = sink_evals(
        ns,
        input.message.len(),
        ctx.sib_stream_len,
        stream_base,
        &rel.keccak.hash_io,
    );
    let sinks = sink_descs
        .into_iter()
        .enumerate()
        .map(|(idx, s)| FrameworkComponent::new(allocator, s, claims.sinks[idx]))
        .collect();

    Built {
        coeffs,
        coeffs_rc,
        decomp,
        decomp_rc,
        sib,
        sib_rc,
        msglink,
        prefix,
        msg,
        bridges,
        sinks,
    }
}

fn decomp_rc_relation(
    r: &DecompRelations,
    kind: decomp_tables::RcKind,
) -> &crate::decomp::relations::RcRelation {
    match kind {
        decomp_tables::RcKind::Rc4 => &r.rc4,
        decomp_tables::RcKind::Rc13 => &r.rc13,
        decomp_tables::RcKind::Rc7 => &r.rc7,
        decomp_tables::RcKind::Rc8 => &r.rc8,
    }
}
fn sib_rc_relation(
    r: &SibRelations,
    kind: sib_tables::RcKind,
) -> &crate::sampleinball::relations::RcRelation {
    match kind {
        sib_tables::RcKind::Rc8 => &r.rc8,
        sib_tables::RcKind::Rc9 => &r.rc9,
        sib_tables::RcKind::Rc11 => &r.rc11,
    }
}

// =============================================================================
// Prover.
// =============================================================================

pub struct MlDsaProver {
    witness: MlDsaWitness,
    input: MlDsaVerifyInput,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
    ctx: LayoutCtx,
    /// Hosted mode: the host's shared message-source relation handle. `None` for
    /// standalone (the self-drawn `msglink` producer).
    shared_field: Option<SharedFieldRelation>,
    /// The keccak service's shared relations handle (REQUIRED — the service
    /// module must be composed before this one and draw into it).
    keccak_handle: SharedKeccakRelations,
    /// Instance namespace: role/domain tag mixed into the transcript and
    /// prefixed onto every witness/shape-dependent preprocessed id (SIB
    /// schedule, bridges, sinks). "" = legacy single-instance ids. REQUIRED
    /// (distinct per instance) when a proof hosts more than one ML-DSA module.
    namespace: String,
    /// Per-instance stream-id base (multiples of [`STREAM_BASE_STRIDE`]):
    /// keeps this instance's HashIo stream ids disjoint from every other
    /// instance under the ONE shared relation set. Mixed into the transcript.
    stream_base: u32,
    /// Private-message mode: mix only `message.len()` into the transcript; the
    /// bytes flow exclusively through the host's FieldBytesRelation.
    private_message: bool,
    relations: Option<Relations>,
    // rc multiplicity columns stashed between write_trace and write_interaction.
    coeffs_rc_mult: Vec<ColEval>,
    decomp_rc_mult: Vec<ColEval>,
    sib_rc_mult: Vec<ColEval>,
    // bridge byte payloads stashed for the interaction phase.
    decomp_w1_bytes: Vec<u8>,
    group_evals: Vec<SecureField>,
    claims: Claims,
    built: Option<Built>,
}

impl MlDsaProver {
    fn relations(&self) -> &Relations {
        self.relations.as_ref().expect("relations drawn")
    }

    /// Build a prover. `shared_field = None` → standalone (self-drawn `msglink`
    /// producer, current commit order). `shared_field = Some(handle)` → hosted:
    /// the `msglink` component is dropped and the msg bridge sources the message
    /// bytes from the host's shared [`FieldBytesRelation`] under
    /// [`HOSTED_MSG_FIELD_ID`]. `keccak_handle` is the proof-wide keccak
    /// service's relations handle: the service module (built from this
    /// instance's [`MlDsaProver::keccak_jobs`], among others) MUST be composed
    /// BEFORE this module so its `draw_relations` populates the handle
    /// (`air_core::prove` runs all modules' `draw_relations` in module order,
    /// before any interaction phase).
    pub fn new(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        shared_field: Option<SharedFieldRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(witness, input, shared_field, false, keccak_handle)
    }

    fn build(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        shared_field: Option<SharedFieldRelation>,
        public_message: bool,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        let hosted = shared_field.is_some() || public_message;
        let sib_stream_len = sampleinball::stream_len(&witness);
        let sib_squeezed_len = witness.sponge.sample_in_ball_squeezed.len();
        let ctx = LayoutCtx::new(
            &input,
            sib_stream_len,
            sib_squeezed_len,
            hosted,
            public_message,
        );
        let claims = Claims {
            hosted,
            ..Claims::default()
        };

        Self {
            witness,
            input,
            sib_stream_len,
            sib_squeezed_len,
            ctx,
            shared_field,
            keccak_handle,
            namespace: String::new(),
            stream_base: 0,
            private_message: false,
            relations: None,
            coeffs_rc_mult: Vec::new(),
            decomp_rc_mult: Vec::new(),
            sib_rc_mult: Vec::new(),
            decomp_w1_bytes: Vec::new(),
            group_evals: Vec::new(),
            claims,
            built: None,
        }
    }

    /// Hosted-mode constructor (`shared_field` provided by the host).
    pub fn hosted(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        shared_field: SharedFieldRelation,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::new(witness, input, Some(shared_field), keccak_handle)
    }

    /// Hosted PUBLIC-message constructor (S4): the message bytes are a PUBLIC
    /// statement input, yielded into the µ-absorb stream by the in-module
    /// public-message producer — NO shared field relation, NO upstream byte
    /// conveyor (SHA) required. Must not be combined with
    /// [`Self::with_private_message`].
    pub fn hosted_public(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(witness, input, None, true, keccak_handle)
    }

    /// Set the per-instance stream-id base (see the `stream_base` field).
    /// Prover and verifier must agree per role; use multiples of
    /// [`STREAM_BASE_STRIDE`].
    pub fn with_stream_base(mut self, base: u32) -> Self {
        self.stream_base = base;
        self
    }

    /// The sponge job shapes + witness byte streams this instance contributes
    /// to the proof-wide keccak service, in job order (µ, c̃, SIB).
    pub fn keccak_jobs(&self) -> (Vec<Shape>, Vec<Vec<u8>>) {
        let shapes = keccak_job_shapes(
            self.input.message.len(),
            self.sib_stream_len,
            self.stream_base,
        );
        let streams = vec![
            self.witness.sponge.mu_absorbed.clone(),
            self.witness.sponge.c_tilde_absorbed.clone(),
            self.witness.sponge.sample_in_ball_absorbed.clone(),
        ];
        (shapes, streams)
    }

    /// Set the instance namespace (see the `namespace` field). Prover and
    /// verifier must agree per role.
    pub fn with_instance_namespace(mut self, ns: impl Into<String>) -> Self {
        self.namespace = ns.into();
        self
    }

    /// Enable private-message mode (see the `private_message` field). Prover
    /// and verifier must agree per role.
    pub fn with_private_message(mut self) -> Self {
        self.private_message = true;
        self
    }

    // ---- getters the host stores in its proof struct + uses to reconstruct ----

    /// The 30 claimed `P̂(r,s)` group evaluations (available after proving).
    pub fn group_evals(&self) -> &[SecureField] {
        &self.group_evals
    }
    /// The ordered claimed sums (WITHOUT the msglink slot in hosted mode).
    pub fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }
    /// The honest SIB squeeze stream length.
    pub fn sib_stream_len(&self) -> usize {
        self.sib_stream_len
    }
    /// The full native SIB squeeze length.
    pub fn sib_squeezed_len(&self) -> usize {
        self.sib_squeezed_len
    }
    /// The public statement input.
    pub fn input(&self) -> &MlDsaVerifyInput {
        &self.input
    }
}

/// The byte payloads the three fixed bridges move, in bridge order (mu→ct,
/// w1enc, ct→sib). Requires the sponge outputs (for µ/c̃ squeeze bytes) and the
/// decomp w1Encode bytes. (The msg slot's payload is `input.message`.)
fn bridge_bytes(outputs: &[Vec<u8>; 3], w1_bytes: &[u8]) -> [Vec<u8>; 3] {
    [
        outputs[0][..64].to_vec(), // mu→ct
        w1_bytes.to_vec(),         // w1enc (768)
        outputs[1][..48].to_vec(), // ct→sib
    ]
}

/// The byte payloads the three sinks consume, in sink order (µ, c̃, SIB).
fn sink_bytes(outputs: &[Vec<u8>; 3], sib_stream_len: usize) -> [Vec<u8>; 3] {
    [
        outputs[0][64..].to_vec(),
        outputs[1][48..].to_vec(),
        outputs[2][sib_stream_len..].to_vec(),
    ]
}

impl Air for MlDsaProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(
            channel,
            &self.input,
            self.sib_stream_len,
            &self.namespace,
            self.private_message,
            self.stream_base,
        );
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(draw_relations_common(
            channel,
            self.shared_field.as_ref(),
            &self.keccak_handle,
        ));
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.ctx, &self.input)
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }
    fn mix_claimed_sums(&self, channel: &mut Blake2sChannel) {
        channel.mix_felts(&self.group_evals);
        channel.mix_felts(&self.claimed_sums());
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids(
            &self.namespace,
            &self.input,
            self.sib_stream_len,
            self.ctx.public_message,
        )
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(
            allocator,
            &self.namespace,
            self.stream_base,
            &self.ctx,
            &self.input,
            &rel,
            &self.claims,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
    }
}

impl AirProver for MlDsaProver {
    fn max_log_size(&self) -> u32 {
        coeffs_log_size()
            .max(decomp_log_size())
            .max(sib_log_size(self.sib_squeezed_len))
            .max(coeffs_tables::RcKind::Rc13.log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 1
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed(
            &self.witness,
            &self.input,
            self.sib_stream_len,
            self.sib_squeezed_len,
            self.ctx.public_message,
        ));
    }
    /// Partial preprocessed writes: with multiple hosted ML-DSA instances, the
    /// fixed-content tables (coeffs/decomp layout, rc values, keccak tables)
    /// keep global ids and tree-0 dedups them first-writer-wins, so a later
    /// instance must write only its namespaced (witness/shape-dependent)
    /// columns. `selected_ids` is this module's id list filtered to first-seen,
    /// in commit order (air-core `select_first_preprocessed_ids`).
    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let ids = all_preprocessed_ids(
            &self.namespace,
            &self.input,
            self.sib_stream_len,
            self.ctx.public_message,
        );
        let cols = gen_all_preprocessed(
            &self.witness,
            &self.input,
            self.sib_stream_len,
            self.sib_squeezed_len,
            self.ctx.public_message,
        );
        assert_eq!(
            ids.len(),
            cols.len(),
            "mldsa preprocessed ids/cols length mismatch"
        );
        let selected: std::collections::HashSet<&PreProcessedColumnId> =
            selected_ids.iter().collect();
        let (picked_ids, picked_cols): (Vec<_>, Vec<_>) = ids
            .into_iter()
            .zip(cols)
            .filter(|(id, _)| selected.contains(id))
            .unzip();
        assert_eq!(
            picked_ids.as_slice(),
            selected_ids,
            "selected preprocessed ids must be this module's ids filtered first-writer-wins, in commit order"
        );
        tb.extend_evals(picked_cols);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let ids = all_preprocessed_ids(
            &self.namespace,
            &self.input,
            self.sib_stream_len,
            self.ctx.public_message,
        );
        let cols = gen_all_preprocessed(
            &self.witness,
            &self.input,
            self.sib_stream_len,
            self.sib_squeezed_len,
            self.ctx.public_message,
        );
        fingerprint_preprocessed_columns("mldsa_statement", &ids, &cols)
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut evals = Vec::new();

        // 1. coeffs base + 2. rc mult (dry-run interaction for use counts).
        let cls = coeffs_log_size();
        evals.extend(coeffs::gen_coeffs_base_trace(&self.witness, cls));
        let coeffs_dry = coeffs::gen_coeffs_interaction(
            &self.witness,
            cls,
            SecureField::zero(),
            SecureField::zero(),
            &CoeffsRelations::dummy(),
        );
        self.coeffs_rc_mult = coeffs_tables::RcKind::ALL
            .iter()
            .map(|kind| {
                coeffs_tables::gen_table_multiplicities(*kind, coeffs_dry.rc_uses.for_kind(*kind))
            })
            .collect();
        evals.extend(self.coeffs_rc_mult.clone());

        // 3. decomp base + 4. rc mult (stash w1Encode bytes for the w1enc bridge).
        let dls = decomp_log_size();
        evals.extend(decomp::gen_decomp_base_trace(&self.witness, dls));
        let decomp_dry = decomp::gen_decomp_interaction(
            &self.witness,
            dls,
            self.stream_base + STREAM_ID_CTILDE_ABSORB,
            &DecompRelations::dummy(),
        );
        self.decomp_w1_bytes = decomp_dry.w1_encode_bytes.clone();
        self.decomp_rc_mult = decomp_tables::RcKind::ALL
            .iter()
            .map(|kind| {
                decomp_tables::gen_table_multiplicities(*kind, decomp_dry.rc_uses.for_kind(*kind))
            })
            .collect();
        evals.extend(self.decomp_rc_mult.clone());

        // 5. sib base + 6. rc mult.
        let sls = sib_log_size(self.sib_squeezed_len);
        evals.extend(sampleinball::gen_sib_base_trace(&self.witness, sls));
        let sib_dry = sampleinball::gen_sib_interaction(
            &self.witness,
            sls,
            self.stream_base + STREAM_ID_SIB_SQUEEZE,
            &SibRelations::dummy(),
        );
        self.sib_rc_mult = sib_tables::RcKind::ALL
            .iter()
            .map(|kind| {
                sib_tables::gen_table_multiplicities(*kind, sib_dry.rc_uses.for_kind(*kind))
            })
            .collect();
        evals.extend(self.sib_rc_mult.clone());

        // 7. msglink (standalone only).
        if !self.ctx.hosted {
            evals.extend(msglink::gen_msglink_base_trace());
        }

        // 8. prefix.
        // Base traces run in Tree 1, BEFORE relations are drawn. The prefix /
        // bridge / sink base traces (enabler + byte columns) do NOT depend on any
        // relation, so descriptors are built with `dummy()` relations here.
        let dummy_hash_io = HashIoRelation::dummy();
        let dummy_msglink = MsgLinkRelation::dummy();
        evals.extend(prefix_eval(&self.input, self.stream_base, &dummy_hash_io).gen_base());

        // 9. msg slot base + 10-12. bridges base (the sponge outputs are
        // recomputed natively — the sponges themselves are proven in the
        // keccak SERVICE module).
        let outputs = sponge_outputs(&self.witness);
        let slot = msg_slot(
            &self.namespace,
            &self.input.message,
            self.stream_base,
            self.ctx.public_message,
            &dummy_msglink,
            None,
            &dummy_hash_io,
        );
        evals.extend(slot.gen_base(&self.input.message));
        let bbytes = bridge_bytes(&outputs, &self.decomp_w1_bytes);
        let bridge_descs = bridge_evals(&self.namespace, self.stream_base, &dummy_hash_io);
        for (b, bytes) in bridge_descs.iter().zip(bbytes.iter()) {
            evals.extend(b.gen_base(bytes));
        }

        // PROVER SANITY: the sponge output prefixes match the witness transcript.
        assert_eq!(
            outputs[0][..64],
            self.witness.sponge.mu_squeezed[..64],
            "µ squeeze prefix mismatch"
        );
        assert_eq!(
            outputs[1][..48],
            self.input.c_tilde[..],
            "c̃ squeeze prefix mismatch"
        );
        assert_eq!(
            outputs[2][..self.sib_stream_len],
            self.witness.sponge.sample_in_ball_squeezed[..self.sib_stream_len],
            "SIB squeeze prefix mismatch"
        );

        // 13-15. sinks base.
        let sbytes = sink_bytes(&outputs, self.sib_stream_len);
        let sink_descs = sink_evals(
            &self.namespace,
            self.input.message.len(),
            self.sib_stream_len,
            self.stream_base,
            &dummy_hash_io,
        );
        for (s, bytes) in sink_descs.iter().zip(sbytes.iter()) {
            evals.extend(s.gen_base(bytes));
        }

        tb.extend_evals(evals);
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let rel = self.relations().clone();
        let mut evals = Vec::new();

        // 1. coeffs interaction (stash group_evals + claimed).
        let cls = coeffs_log_size();
        let coeffs_int =
            coeffs::gen_coeffs_interaction(&self.witness, cls, rel.r, rel.s, &rel.coeffs);
        self.claims.coeffs = coeffs_int.claimed_sum;
        self.group_evals = coeffs_int.group_evals.clone();
        evals.extend(coeffs_int.trace);
        // 2. coeffs rc ×5.
        self.claims.coeffs_rc.clear();
        for (idx, kind) in coeffs_tables::RcKind::ALL.iter().enumerate() {
            let (tr, sum) = coeffs_tables::gen_table_interaction(
                *kind,
                &self.coeffs_rc_mult[idx],
                rel.coeffs.rc(*kind),
            );
            evals.extend(tr);
            self.claims.coeffs_rc.push(sum);
        }

        // 3. decomp interaction.
        let dls = decomp_log_size();
        let decomp_int = decomp::gen_decomp_interaction(
            &self.witness,
            dls,
            self.stream_base + STREAM_ID_CTILDE_ABSORB,
            &rel.decomp,
        );
        self.claims.decomp = decomp_int.claimed_sum;
        evals.extend(decomp_int.trace);
        // 4. decomp rc ×4.
        self.claims.decomp_rc.clear();
        for (idx, kind) in decomp_tables::RcKind::ALL.iter().enumerate() {
            let (tr, sum) = decomp_tables::gen_table_interaction(
                *kind,
                &self.decomp_rc_mult[idx],
                decomp_rc_relation(&rel.decomp, *kind),
            );
            evals.extend(tr);
            self.claims.decomp_rc.push(sum);
        }

        // 5. sib interaction.
        let sls = sib_log_size(self.sib_squeezed_len);
        let sib_int = sampleinball::gen_sib_interaction(
            &self.witness,
            sls,
            self.stream_base + STREAM_ID_SIB_SQUEEZE,
            &rel.sib,
        );
        self.claims.sib = sib_int.claimed_sum;
        evals.extend(sib_int.trace);
        // 6. sib rc ×3.
        self.claims.sib_rc.clear();
        for (idx, kind) in sib_tables::RcKind::ALL.iter().enumerate() {
            let (tr, sum) = sib_tables::gen_table_interaction(
                *kind,
                &self.sib_rc_mult[idx],
                sib_rc_relation(&rel.sib, *kind),
            );
            evals.extend(tr);
            self.claims.sib_rc.push(sum);
        }

        // 7. msglink (standalone only; hosted mode sources the msg bridge from
        // the host's shared relation and commits no msglink component).
        if !self.ctx.hosted {
            let (msg_tr, msg_sum) =
                msglink::gen_msglink_interaction(&self.input.message, &rel.msglink);
            self.claims.msglink = msg_sum;
            evals.extend(msg_tr);
        }

        // 8. prefix.
        let (prefix_tr, prefix_sum) =
            prefix_eval(&self.input, self.stream_base, &rel.keccak.hash_io).gen_interaction();
        self.claims.prefix = prefix_sum;
        evals.extend(prefix_tr);

        // 9. msg slot + 10-12. bridges (claims.bridges[0] is the msg slot —
        // positional across modes).
        let outputs = sponge_outputs(&self.witness);
        self.claims.bridges.clear();
        let slot = msg_slot(
            &self.namespace,
            &self.input.message,
            self.stream_base,
            self.ctx.public_message,
            &rel.msglink,
            rel.shared_field.as_ref(),
            &rel.keccak.hash_io,
        );
        let (slot_tr, slot_sum) = slot.gen_interaction(&self.input.message);
        self.claims.bridges.push(slot_sum);
        evals.extend(slot_tr);
        let bbytes = bridge_bytes(&outputs, &self.decomp_w1_bytes);
        let bridge_descs = bridge_evals(&self.namespace, self.stream_base, &rel.keccak.hash_io);
        for (b, bytes) in bridge_descs.iter().zip(bbytes.iter()) {
            let (tr, sum) = b.gen_interaction(bytes);
            self.claims.bridges.push(sum);
            evals.extend(tr);
        }

        // 13-15. sinks.
        let sbytes = sink_bytes(&outputs, self.sib_stream_len);
        let sink_descs = sink_evals(
            &self.namespace,
            self.input.message.len(),
            self.sib_stream_len,
            self.stream_base,
            &rel.keccak.hash_io,
        );
        self.claims.sinks.clear();
        for (s, bytes) in sink_descs.iter().zip(sbytes.iter()) {
            let (tr, sum) = s.gen_interaction(bytes);
            self.claims.sinks.push(sum);
            evals.extend(tr);
        }

        tb.extend_evals(evals);

        // native_use_sum (folded verifier term) appended LAST.
        self.claims.native_use = native_use_sum(&self.group_evals, &rel.coeffs);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built.as_ref().expect("built").ordered_prover()
    }
}

// =============================================================================
// Verifier.
// =============================================================================

pub struct MlDsaVerifier {
    input: MlDsaVerifyInput,
    sib_stream_len: usize,
    ctx: LayoutCtx,
    /// Hosted mode: the host's shared message-source relation handle.
    shared_field: Option<SharedFieldRelation>,
    /// The keccak service's shared relations handle (must be populated by the
    /// service module, composed before this one).
    keccak_handle: SharedKeccakRelations,
    /// Instance namespace (must match the prover's per role).
    namespace: String,
    /// Per-instance stream-id base (must match the prover's per role).
    stream_base: u32,
    /// Private-message mode (must match the prover's per role).
    private_message: bool,
    group_evals: Vec<SecureField>,
    claims: Claims,
    relations: Option<Relations>,
    fold_ok: bool,
    built: Option<Built>,
}

impl MlDsaVerifier {
    fn relations(&self) -> &Relations {
        self.relations.as_ref().expect("relations drawn")
    }

    /// Reconstruct a verifier from the public proof data. `shared_field = None` →
    /// standalone; `Some(handle)` → hosted (drops the msglink claim slot, sources
    /// the msg bridge from the host's shared [`FieldBytesRelation`]). The
    /// `group_evals` / `claimed_sums` / `sib_*_len` come from the host's proof
    /// struct (the mldsa prover's getters). Composed AFTER the keccak service
    /// module (and, hosted, after the host module that draws + sets `handle`).
    pub fn new(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        sib_stream_len: usize,
        sib_squeezed_len: usize,
        shared_field: Option<SharedFieldRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(
            input,
            group_evals,
            claimed_sums,
            sib_stream_len,
            sib_squeezed_len,
            shared_field,
            false,
            keccak_handle,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn build(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        sib_stream_len: usize,
        sib_squeezed_len: usize,
        shared_field: Option<SharedFieldRelation>,
        public_message: bool,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        let hosted = shared_field.is_some() || public_message;
        let ctx = LayoutCtx::new(
            &input,
            sib_stream_len,
            sib_squeezed_len,
            hosted,
            public_message,
        );
        let claims = Claims::from_flat(&claimed_sums, hosted);
        Self {
            input,
            sib_stream_len,
            ctx,
            shared_field,
            keccak_handle,
            namespace: String::new(),
            stream_base: 0,
            private_message: false,
            group_evals,
            claims,
            relations: None,
            fold_ok: false,
            built: None,
        }
    }

    /// Hosted-mode constructor (`shared_field` provided by the host).
    #[allow(clippy::too_many_arguments)]
    pub fn hosted(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        sib_stream_len: usize,
        sib_squeezed_len: usize,
        shared_field: SharedFieldRelation,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::new(
            input,
            group_evals,
            claimed_sums,
            sib_stream_len,
            sib_squeezed_len,
            Some(shared_field),
            keccak_handle,
        )
    }

    /// Hosted PUBLIC-message constructor (S4) — mirror of
    /// [`MlDsaProver::hosted_public`].
    pub fn hosted_public(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        sib_stream_len: usize,
        sib_squeezed_len: usize,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(
            input,
            group_evals,
            claimed_sums,
            sib_stream_len,
            sib_squeezed_len,
            None,
            true,
            keccak_handle,
        )
    }

    /// Set the instance namespace (must match the prover's per role).
    pub fn with_instance_namespace(mut self, ns: impl Into<String>) -> Self {
        self.namespace = ns.into();
        self
    }

    /// Set the per-instance stream-id base (must match the prover's per role).
    pub fn with_stream_base(mut self, base: u32) -> Self {
        self.stream_base = base;
        self
    }

    /// Enable private-message mode (must match the prover's per role).
    pub fn with_private_message(mut self) -> Self {
        self.private_message = true;
        self
    }
}

impl Air for MlDsaVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(
            channel,
            &self.input,
            self.sib_stream_len,
            &self.namespace,
            self.private_message,
            self.stream_base,
        );
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let rel = draw_relations_common(channel, self.shared_field.as_ref(), &self.keccak_handle);
        // native_use + folded identity (mirror CoeffsVerifier).
        self.claims.native_use = native_use_sum(&self.group_evals, &rel.coeffs);
        let public = compute_public_evals(&self.input, rel.r, rel.s);
        let fold = folded_check(
            &public,
            &ClaimedEvals(&self.group_evals),
            rel.rho_rlc,
            rel.r,
            rel.s,
        );
        self.fold_ok = fold == SecureField::zero();
        self.relations = Some(rel);
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.ctx, &self.input)
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }
    fn mix_claimed_sums(&self, channel: &mut Blake2sChannel) {
        channel.mix_felts(&self.group_evals);
        channel.mix_felts(&self.claimed_sums());
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        all_preprocessed_ids(
            &self.namespace,
            &self.input,
            self.sib_stream_len,
            self.ctx.public_message,
        )
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(
            allocator,
            &self.namespace,
            self.stream_base,
            &self.ctx,
            &self.input,
            &rel,
            &self.claims,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
    }
    fn verify_post_interaction(
        &mut self,
        _channel: &mut Blake2sChannel,
    ) -> Result<(), VerificationError> {
        // The verifier-native fold (‡): closes the coeffs group-eval binding.
        // In hosted mode the host's `air_core::verify` enforces it here
        // automatically; standalone `verify_mldsa` also checks `fold_ok`.
        if self.fold_ok {
            Ok(())
        } else {
            Err(VerificationError::InvalidStructure(
                "mldsa_statement: folded identity (‡) is nonzero".into(),
            ))
        }
    }
}

// =============================================================================
// Entry points.
// =============================================================================

pub fn prove_mldsa(
    witness: MlDsaWitness,
    input: MlDsaVerifyInput,
    config: PcsConfig,
) -> Result<MlDsaProof, ProvingError> {
    let sib_stream_len = sampleinball::stream_len(&witness);
    let sib_squeezed_len = witness.sponge.sample_in_ball_squeezed.len();
    // The standalone path instantiates a PRIVATE keccak service for this one
    // instance's three sponge jobs; the composition is `[service, mldsa]`.
    let handle = SharedKeccakRelations::new();
    let mut prover = MlDsaProver::new(witness, input.clone(), None, handle.clone());
    let (job_shapes, job_streams) = prover.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, handle);
    let (stark_proof, post_interaction_payloads) =
        air_core::prove_with_post_interaction(&mut [&mut service, &mut prover], config)?;
    Ok(MlDsaProof {
        input,
        group_evals: prover.group_evals,
        claimed_sums: prover.claims.ordered(),
        sib_stream_len,
        sib_squeezed_len,
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    })
}

/// Public layout probe for benchmarks: the committed [`TreeLayout`]
/// (preprocessed / trace / interaction column log-sizes) a proof would commit
/// for the given public parameters. Summing `2^log_size` over all three gives
/// the total committed M31-cell count; interaction QM31 columns are
/// pre-expanded to 4 M31 columns in the layout.
pub fn debug_layout(
    input: &MlDsaVerifyInput,
    sib_stream_len: usize,
    sib_squeezed_len: usize,
) -> TreeLayout {
    let ctx = LayoutCtx::new(input, sib_stream_len, sib_squeezed_len, false, false);
    layout_for(&ctx, input)
}

/// The number of group evaluations every proof carries (the 30 coeffs poly
/// groups). Hosts gate `group_evals.len()` on this before construction.
pub fn n_group_evals() -> usize {
    coeffs::layout::N_GROUPS
}

/// The exact `claimed_sums` length a HOSTED proof carries (msglink slot
/// dropped; `native_use` appended last; the keccak side lives in the SERVICE
/// module and contributes [`stwo_keccak::service::service_claimed_sums_len`]
/// separately). Hosts gate the flat vector's length on this before
/// construction — `Claims::from_flat` panics on a short vector.
pub fn hosted_claimed_sums_len() -> usize {
    1 + coeffs_tables::RcKind::ALL.len()          // coeffs + rc
        + 1 + decomp_tables::RcKind::ALL.len()    // decomp + rc
        + 1 + sib_tables::RcKind::ALL.len()       // sib + rc
        + 1                                       // prefix
        + 4 + 3                                   // bridges + sinks
        + 1 // native_use
}

/// Compute the expected tree-0 (preprocessed) commitment root for a standalone
/// ML-DSA statement, by rebuilding the prover-side [`MlDsaProver`] from the
/// public `input` and running exactly the prover's tree-0 commit path
/// ([`air_core::compute_preprocessed_root_uncached`]).
///
/// The `sampleinball` schedule preprocessed columns depend on the witness
/// through `stream_len(witness)` — the SIB rejection-sampling squeeze length,
/// which varies per signature while its padded `sib_log_size` (and hence the
/// preprocessed *id + log_size* shape key) stays fixed. So the content is NOT
/// determined by the id alone, and the per-shape *cached*
/// [`air_core::compute_preprocessed_root`] would return the first witness's
/// root for every later one (a fail-closed completeness bug, exactly the P-256
/// hinted-mul schedule case). The **uncached** variant rebuilds tree-0 on every
/// call, pinning this specific statement's schedule. `generate_witness` is used
/// only to materialize that schedule; no private witness value leaks into the
/// root beyond the public SIB stream length carried in the proof.
///
/// # Soundness
///
/// This root — not the prover-side 64-bit `DefaultHasher` column fingerprint —
/// is the tree-0 soundness pin (F-ROOT class): the Blake2s Merkle root binds
/// the contents, order, and sizes of every preprocessed range table, schedule,
/// and constant column at once. [`verify_mldsa`] recomputes it from the public
/// input and rejects fail-closed on mismatch, so a proof carrying a forged
/// preprocessed tree never reaches the STARK verifier.
pub fn mldsa_expected_preprocessed_root(
    input: &MlDsaVerifyInput,
    config: PcsConfig,
) -> Result<air_core::CommitmentRoot, WitnessError> {
    let witness = generate_witness(input)?;
    let handle = SharedKeccakRelations::new();
    let mut prover = MlDsaProver::new(witness, input.clone(), None, handle.clone());
    let (job_shapes, job_streams) = prover.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, handle);
    Ok(air_core::compute_preprocessed_root_uncached(
        &mut [&mut service, &mut prover],
        config,
    ))
}

pub fn verify_mldsa(proof: &MlDsaProof) -> Result<(), VerificationError> {
    let handle = SharedKeccakRelations::new();
    let job_shapes = keccak_job_shapes(proof.input.message.len(), proof.sib_stream_len, 0);
    if proof.service_claimed_sums.len() != stwo_keccak::service::service_claimed_sums_len() {
        return Err(VerificationError::InvalidStructure(
            "ML-DSA statement: bad service claimed-sums length".to_string(),
        ));
    }
    // Payload shape gate, fail-closed: exactly one entry per module
    // ([service, mldsa]); only the service slot carries a (non-empty) GKR
    // blob. The blob content itself is verified inside the service module's
    // verify_post_interaction (decode + claim binding + sumcheck replay).
    if proof.post_interaction_payloads.len() != 2
        || proof.post_interaction_payloads[0].is_empty()
        || !proof.post_interaction_payloads[1].is_empty()
    {
        return Err(VerificationError::InvalidStructure(
            "ML-DSA statement: bad post-interaction payload shape".to_string(),
        ));
    }
    let mut service = KeccakServiceVerifier::new(
        job_shapes,
        proof.service_claimed_sums.clone(),
        handle.clone(),
    );
    let mut verifier = MlDsaVerifier::new(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        proof.sib_stream_len,
        proof.sib_squeezed_len,
        None,
        handle,
    );
    // Pin the preprocessed (tree-0) root before any transcript work: recompute
    // it from the public statement shape and reject a forged preprocessed tree
    // fail-closed (F-ROOT hardening). `generate_witness` cannot fail for a
    // proof whose `input` a prover already accepted; a genuine failure here is
    // a malformed public input, mapped to `InvalidStructure`.
    let expected_root = mldsa_expected_preprocessed_root(&proof.input, proof.stark_proof.config)
        .map_err(|_| {
            VerificationError::InvalidStructure(
                "ML-DSA statement: could not derive expected preprocessed root".to_string(),
            )
        })?;
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut service, &mut verifier],
        &proof.stark_proof,
        Some(expected_root),
        &proof.post_interaction_payloads,
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => {
            VerificationError::InvalidStructure(
                "ML-DSA statement: preprocessed root mismatch (forged tree-0)".to_string(),
            )
        }
    })?;
    // fold_ok is enforced inside verify_post_interaction (via air_core::verify).
    Ok(())
}
