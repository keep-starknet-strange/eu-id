//! `MlDsaAir` — the composed in-circuit ML-DSA-65 statement (M6).
//!
//! ONE air-core module pair ([`MlDsaProver`] impl `Air`+`AirProver`,
//! [`MlDsaVerifier`] impl `Air`) proves the entire ML-DSA-65 verification via a
//! single [`air_core::prove`] / [`air_core::verify`] call. It stitches together:
//!
//!   * verifier-native `ExpandA(ρ)` — deterministic from the transcript-mixed
//!     public key and consumed directly by the folded identity.
//!   * `coeffs` — the tall bivariate-Horner integer-lift component (yields the
//!     W-cell / C-cell bindings + constrained public fold).
//!   * `decomp` — [DECOMP]+[HINT]; consumes W-cells, yields the 768 `w1Encode`
//!     bytes into the c̃-absorb stream.
//!   * `sib`         — SampleInBall FSM; consumes C-cells + the SIB squeeze stream.
//!   * `msglink`     — the public message-byte producer (M7 swap point).
//!   * public-byte links / bridges / sinks ([`crate::sponge_link`]) that feed
//!     verifier-native `tr`/µ constants, move bytes between the remaining
//!     HashIo streams, and close every squeeze balance.
//!
//! The remaining SHAKE-256 signature chains are jobs of the proof-wide
//! [`stwo_keccak::service::KeccakServiceProver`], which owns the rotated
//! sponge + keccak + round + tables ONCE for all hosted instances and
//! publishes the drawn [`KeccakRelations`] through a
//! [`SharedKeccakRelations`] handle this module consumes. The instance exposes
//! its sponge job shapes via [`keccak_job_shapes`] / [`MlDsaProver::keccak_jobs`]
//! so the host can build the service, and takes an explicit per-instance
//! `stream_base` so HashIo stream ids stay globally unique under the ONE
//! shared relation set.
//!
//! Any drift between `layout()`, `claimed_sums()`, `write_trace()`,
//! `write_interaction()`, `build_components()`, `components()` breaks
//! verification.

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
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, Relation, TraceLocationAllocator,
};

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use stwo_keccak::relations::{KeccakRelations, SharedKeccakRelations};
use stwo_keccak::service::{KeccakServiceProver, KeccakServiceVerifier};
use stwo_keccak::sponge::Shape;

use crate::air_util::{col_eval, m31, padded_log_size, ColEval};
use crate::binding::{
    CCellRelation, HashIoRelation, MsgLinkRelation, WCellRelation, STREAM_ID_CTILDE_ABSORB,
    STREAM_ID_SIB_SQUEEZE,
};
use crate::constants::{K, N};
use crate::msglink::{self, MsgLinkEval, MSG_FIELD_ID};
use crate::sponge_link::{
    BridgeEval, PublicPrefixEval, SqueezeSinkEval, SrcRelation, BRIDGE_BASE_COLS,
    BRIDGE_INTERACTION_COLS, PREFIX_BASE_COLS, SINK_BASE_COLS, SINK_INTERACTION_COLS,
};
use crate::types::MlDsaVerifyInput;
use crate::verifier_native::{compute_public_evals, folded_check, ClaimedEvals};
use crate::witness::MlDsaWitness;

use crate::coeffs::relations::{CoeffsRelations, SharedRangeRelation};
use crate::coeffs::tables as coeffs_tables;
use crate::coeffs::{self, CoeffsEval, RcUses};

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
// [`STREAM_ID_SIB_SQUEEZE`] = 1) live in `binding.rs`. Bases retain the
// protocol's 128-wide namespace stride.

/// Private µ-chain absorb stream offset (`tr ‖ 0x00 ‖ 0x00 ‖ M`).
pub const MU_ABSORB: u32 = 10;
/// Private µ-chain squeeze stream offset.
pub const MU_SQUEEZE: u32 = 11;
/// c̃-chain absorb stream offset (`µ ‖ w1Encode(w1')`).
pub const CT_ABSORB: u32 = 12;
/// c̃-chain squeeze stream offset.
pub const CT_SQUEEZE: u32 = 13;
/// SIB-chain absorb stream offset (`c̃`).
pub const SIB_ABSORB: u32 = 14;
/// Minimum spacing between two instances' `stream_base` values.
pub const STREAM_BASE_STRIDE: u32 = 128;

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

/// Disjoint `perm_id_base` assignment across the remaining SHAKE-256 sponge
/// chains (M3 carry-forward): each chain's Keccak-f[1600] permutation ids are
/// offset so the shared [`stwo_keccak::relations::KeccakStateRelation`] never
/// crosses chains. Public-message instances omit the µ chain (`n_mu = 0`).
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

    /// Build the plan directly from the optional private-µ and c̃ sponge shapes.
    pub fn from_shapes(mu: Option<&Shape>, ct: &Shape) -> Self {
        Self::new(mu.map_or(0, Shape::n_perms), ct.n_perms())
    }
}

// =============================================================================
// Public proof struct.
// =============================================================================

/// The public statement + all prover claims of a composed ML-DSA-65 proof.
///
/// The verifier reconstructs every component's shape from public inputs,
/// public lengths, and claimed sums, with no witness.
#[derive(Clone, Serialize, Deserialize)]
pub struct MlDsaProof {
    pub input: MlDsaVerifyInput,
    /// The 30 claimed `P̂(r,s)` group evaluations (coeffs), in poly_id order.
    pub group_evals: Vec<SecureField>,
    /// Every component's claimed sum, in commit order, then `native_use_sum` LAST.
    pub claimed_sums: Vec<SecureField>,
    /// The keccak service module's claimed sums (`[sponge_v, keccak, round,
    /// tables ×9]`) — the standalone proof composes `[service, mldsa]`.
    pub service_claimed_sums: Vec<SecureField>,
    /// Opaque post-interaction payloads; production carries the Keccak
    /// service's round-GKR proof in its module slot.
    pub post_interaction_payloads: Vec<Vec<u8>>,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

// =============================================================================
// Shared shape derivation (identical prover / verifier).
// =============================================================================

/// The remaining sponge shapes for a statement, derived from PUBLIC data only.
///
/// * µ:  private-message mode only; absorbs `tr ‖ 0x00 ‖ 0x00 ‖ M`
///   (len `66 + |M|`), squeezes 1 block.
/// * c̃:  absorbs `µ ‖ w1Encode(w1')` (len 832 = 64 + 768), squeezes 1 block.
/// * SIB: absorbs `c̃` (48 bytes), squeezes the fixed five-block resource cap.
struct Shapes {
    mu: Option<Shape>,
    ct: Shape,
    sib: Shape,
}

/// The instance's SHAKE256 signature-job shapes, stream ids offset by
/// `stream_base`. `native_mu` omits the private µ job.
/// Perm-id bases stay 0 — the proof-wide [`stwo_keccak::sponge_v::JobList`]
/// stamps the global plan over the concatenated job list.
fn shapes(message_len: usize, stream_base: u32, native_mu: bool) -> Shapes {
    let b = stream_base;
    let mu = (!native_mu).then(|| Shape::new(66 + message_len, 1, b + MU_ABSORB, b + MU_SQUEEZE));
    let ct = Shape::new(64 + 768, 1, b + CT_ABSORB, b + CT_SQUEEZE);
    let sib = Shape::new(
        48,
        sampleinball::MAX_SIB_SQUEEZE_BLOCKS,
        b + SIB_ABSORB,
        b + STREAM_ID_SIB_SQUEEZE,
    );
    Shapes { mu, ct, sib }
}

/// PUBLIC: all sponge jobs contributed to the proof-wide service: optional
/// private µ, then c̃ and SIB. `native_mu = true` is the hosted-public
/// issuer/device shape; `false` is standalone/private revocation.
pub fn keccak_job_shapes(message_len: usize, stream_base: u32, native_mu: bool) -> Vec<Shape> {
    let sh = shapes(message_len, stream_base, native_mu);
    sh.mu.into_iter().chain([sh.ct, sh.sib]).collect()
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
/// The fixed five-block SIB component log size.
fn sib_log_size() -> u32 {
    padded_log_size((sampleinball::MAX_SIB_SQUEEZE_BYTES + N).max(sampleinball::N_ACCESSES))
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
    shared_range: Option<&SharedRangeRelation>,
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

    let coeffs = match shared_range {
        Some(handle) => {
            CoeffsRelations::draw_with_range(channel, handle.get(), wcell.clone(), ccell.clone())
        }
        None => CoeffsRelations::draw_with(channel, wcell.clone(), ccell.clone()),
    };
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

/// Verifier-native `tr = SHAKE256(pkEncode(ρ,t1), 64)`.
///
/// This is the only source of `tr` used by the composed statement. Constructors
/// overwrite the compatibility field `input.tr` with this value before mixing
/// or building any component.
pub fn native_tr(input: &MlDsaVerifyInput) -> [u8; 64] {
    let bytes = full_squeeze(&input.encode_pk(), 1);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&bytes[..64]);
    tr
}

/// Verifier-native public-message `µ = SHAKE256(tr ‖ 0x00 ‖ 0x00 ‖ M, 64)`.
/// `tr` is recomputed from `pkEncode`; no carried `input.tr` byte is trusted.
pub fn native_public_mu(input: &MlDsaVerifyInput) -> [u8; 64] {
    let mut absorbed = Vec::with_capacity(66 + input.message.len());
    absorbed.extend_from_slice(&native_tr(input));
    absorbed.extend_from_slice(&[0x00, 0x00]);
    absorbed.extend_from_slice(&input.message);
    let bytes = full_squeeze(&absorbed, 1);
    let mut mu = [0u8; 64];
    mu.copy_from_slice(&bytes[..64]);
    mu
}

/// Public constants feeding the next in-circuit sponge:
///
/// - private-message mode: native `tr ‖ 0x00 ‖ 0x00` into µ-absorb;
/// - public-message mode: native µ directly into c̃-absorb.
fn prefix_eval(
    input: &MlDsaVerifyInput,
    stream_base: u32,
    native_mu: bool,
    hash_io: &HashIoRelation,
) -> PublicPrefixEval {
    let (dst_stream, bytes) = if native_mu {
        (stream_base + CT_ABSORB, native_public_mu(input).to_vec())
    } else {
        let mut bytes = Vec::with_capacity(66);
        bytes.extend_from_slice(&input.tr);
        bytes.extend_from_slice(&[0x00, 0x00]);
        (stream_base + MU_ABSORB, bytes)
    };
    PublicPrefixEval {
        dst_stream,
        dst_off: 0,
        bytes,
        yield_positive: true,
        hash_io: hash_io.clone(),
    }
}

/// The private/standalone message bridge into µ-absorb@66. Public-message mode
/// computes µ natively and omits this component entirely.
fn msg_bridge_eval(
    ns: &str,
    message_len: usize,
    stream_base: u32,
    msglink: &MsgLinkRelation,
    shared_field: Option<&FieldBytesRelation>,
    hash_io: &HashIoRelation,
) -> BridgeEval {
    let b = stream_base;
    let msg_src = match shared_field {
        None => SrcRelation::MsgLink(msglink.clone(), MSG_FIELD_ID),
        Some(field) => SrcRelation::FieldBytes(field.clone(), HOSTED_MSG_FIELD_ID),
    };
    BridgeEval {
        tag: "msg",
        ns: ns.to_string(),
        log_size: bridge_log_size(message_len),
        src: msg_src,
        dst_stream: b + MU_ABSORB,
        dst_off: 66,
        len: message_len,
        hash_io: hash_io.clone(),
    }
}

/// The remaining fixed bridges. Private mode starts with µ→c̃; native-µ mode
/// starts directly with w1Encode→c̃.
fn bridge_evals(
    ns: &str,
    stream_base: u32,
    native_mu: bool,
    hash_io: &HashIoRelation,
) -> Vec<BridgeEval> {
    let b = stream_base;
    let mut bridges = Vec::with_capacity(if native_mu { 2 } else { 3 });
    if !native_mu {
        bridges.push(BridgeEval {
            tag: "mu_ct",
            ns: ns.to_string(),
            log_size: bridge_log_size(64),
            src: SrcRelation::HashIo(hash_io.clone(), b + MU_SQUEEZE, 0),
            dst_stream: b + CT_ABSORB,
            dst_off: 0,
            len: 64,
            hash_io: hash_io.clone(),
        });
    }
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
    bridges.extend([w1enc, ct_sib]);
    bridges
}

/// Consume the remaining squeeze tails. Native-µ mode has only c̃ and SIB;
/// private mode also has µ.
fn sink_evals(
    ns: &str,
    message_len: usize,
    stream_base: u32,
    native_mu: bool,
    hash_io: &HashIoRelation,
) -> Vec<SqueezeSinkEval> {
    let b = stream_base;
    let sh = shapes(message_len, b, native_mu);
    let mut sinks = Vec::with_capacity(if native_mu { 1 } else { 2 });
    if let Some(mu) = sh.mu {
        let mu_len = RATE * mu.n_squeeze - 64;
        sinks.push(SqueezeSinkEval {
            tag: "mu",
            ns: ns.to_string(),
            log_size: bridge_log_size(mu_len),
            stream: b + MU_SQUEEZE,
            off: 64,
            len: mu_len,
            hash_io: hash_io.clone(),
        });
    }
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
    sinks.push(ct);
    sinks
}

// =============================================================================
// Preprocessed ids + generation (positional).
// =============================================================================

/// Preprocessed column ids in commit order. msglink + public links contribute NONE;
/// the keccak side (sponges/keccak/round/tables) lives in the SERVICE module
/// since S1 and contributes nothing here; private bridges + remaining sinks do.
///
/// This is called BEFORE relations are drawn (air-core commits the preprocessed
/// tree first), so the bridge/sink descriptors use `dummy()` relations — their
/// `preprocessed_ids()` read only `tag` + public shape, never the relation (and
/// never the stream ids, so `stream_base = 0` here is shape-neutral).
fn all_preprocessed_ids(
    ns: &str,
    input: &MlDsaVerifyInput,
    hosted: bool,
    public_message: bool,
) -> Vec<PreProcessedColumnId> {
    let hash_io = HashIoRelation::dummy();
    let msglink = MsgLinkRelation::dummy();
    let mut ids = Vec::new();
    // coeffs + its unified range table (standalone only; hosted uses the
    // proof-wide provider module).
    ids.extend(coeffs::coeffs_preprocessed_ids());
    if !hosted {
        ids.extend(coeffs_tables::range_table_preprocessed_ids());
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
    // Private message bridge, remaining fixed bridges, and sinks.
    if !public_message {
        ids.extend(
            msg_bridge_eval(ns, input.message.len(), 0, &msglink, None, &hash_io)
                .preprocessed_ids(),
        );
    }
    for b in bridge_evals(ns, 0, public_message, &hash_io) {
        ids.extend(b.preprocessed_ids());
    }
    for s in sink_evals(ns, input.message.len(), 0, public_message, &hash_io) {
        ids.extend(s.preprocessed_ids());
    }
    ids
}

fn all_preprocessed_log_sizes(
    input: &MlDsaVerifyInput,
    hosted: bool,
    public_message: bool,
) -> Vec<u32> {
    let mut sizes = Vec::new();
    let cls = coeffs_log_size();
    sizes.extend(vec![cls; coeffs::coeffs_preprocessed_ids().len()]);
    if !hosted {
        sizes.extend(vec![
            coeffs_tables::range_table_log_size();
            coeffs_tables::range_table_preprocessed_ids().len()
        ]);
    }
    let dls = decomp_log_size();
    sizes.extend(vec![dls; decomp::decomp_preprocessed_ids().len()]);
    for kind in decomp_tables::RcKind::ALL {
        sizes.push(kind.log_size());
    }
    let sls = sib_log_size();
    sizes.extend(vec![sls; sampleinball::sib_preprocessed_ids().len()]);
    for kind in sib_tables::RcKind::ALL {
        sizes.push(kind.log_size());
    }
    if !public_message {
        sizes.extend(vec![bridge_log_size(input.message.len()); 2]);
    }
    for len in bridge_lens(public_message) {
        sizes.extend(vec![bridge_log_size(len); 2]);
    }
    for len in sink_lens(input.message.len(), public_message) {
        sizes.extend(vec![bridge_log_size(len); 2]);
    }
    sizes
}

fn bridge_lens(native_mu: bool) -> Vec<usize> {
    if native_mu {
        vec![768, 48]
    } else {
        vec![64, 768, 48]
    }
}
fn sink_lens(message_len: usize, native_mu: bool) -> Vec<usize> {
    let sh = shapes(message_len, 0, native_mu);
    sh.mu
        .into_iter()
        .map(|mu| RATE * mu.n_squeeze - 64)
        .chain([RATE * sh.ct.n_squeeze - 48])
        .collect()
}

/// Generate every preprocessed column in commit order (prover-only; runs BEFORE
/// relations are drawn, so bridge/sink descriptors use `dummy()` relations —
/// their `gen_preprocessed()` reads only `tag` + public shape).
///
/// The SIB schedule is fixed at the five-block resource cap; no signature
/// witness enters tree 0.
fn gen_all_preprocessed(
    input: &MlDsaVerifyInput,
    hosted: bool,
    public_message: bool,
) -> Vec<ColEval> {
    let hash_io = HashIoRelation::dummy();
    let msglink = MsgLinkRelation::dummy();
    let mut cols = Vec::new();
    let cls = coeffs_log_size();
    cols.extend(coeffs::gen_coeffs_preprocessed(cls));
    if !hosted {
        cols.extend(coeffs_tables::gen_range_table_preprocessed());
    }
    let dls = decomp_log_size();
    cols.extend(decomp::gen_decomp_preprocessed(dls));
    for kind in decomp_tables::RcKind::ALL {
        cols.push(decomp_tables::gen_table_preprocessed(kind));
    }
    let sls = sib_log_size();
    cols.extend(sampleinball::gen_sib_preprocessed(sls));
    for kind in sib_tables::RcKind::ALL {
        cols.push(sib_tables::gen_table_preprocessed(kind));
    }
    if !public_message {
        cols.extend(
            msg_bridge_eval("", input.message.len(), 0, &msglink, None, &hash_io)
                .gen_preprocessed(),
        );
    }
    for b in bridge_evals("", 0, public_message, &hash_io) {
        cols.extend(b.gen_preprocessed());
    }
    for s in sink_evals("", input.message.len(), 0, public_message, &hash_io) {
        cols.extend(s.gen_preprocessed());
    }
    cols
}

// =============================================================================
// Prover / verifier state.
// =============================================================================

/// Enforces the ML-DSA folded identity as an outer-STARK constraint. Matrix,
/// `t1`, and `q` terms are deterministic from transcript-mixed public inputs.
/// Every QM31 coordinate must vanish in the quotient polynomial.
#[derive(Clone)]
struct PublicFoldEval {
    value: SecureField,
}

impl FrameworkEval for PublicFoldEval {
    fn log_size(&self) -> u32 {
        LOG_N_LANES
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let marker = eval.next_trace_mask();
        eval.add_constraint(marker);
        for coordinate in self.value.to_m31_array() {
            eval.add_constraint(E::F::from(coordinate));
        }
        eval
    }
}

struct Built {
    public_fold: FrameworkComponent<PublicFoldEval>,
    coeffs: FrameworkComponent<CoeffsEval>,
    /// Standalone-only range provider; hosted instances consume the proof-wide
    /// shared table instead.
    coeffs_rc: Option<FrameworkComponent<coeffs_tables::RangeTableEval>>,
    decomp: FrameworkComponent<DecompEval>,
    decomp_rc: Vec<FrameworkComponent<decomp_tables::RcTableEval>>,
    sib: FrameworkComponent<SibEval>,
    sib_rc: Vec<FrameworkComponent<sib_tables::RcTableEval>>,
    /// Standalone msglink producer; `None` in hosted mode (dropped from the
    /// commit order — the msg bridge sources from the host's shared relation).
    msglink: Option<FrameworkComponent<MsgLinkEval>>,
    prefix: FrameworkComponent<PublicPrefixEval>,
    /// Private/standalone message bridge; native-µ public mode omits it.
    msg: Option<FrameworkComponent<BridgeEval>>,
    bridges: Vec<FrameworkComponent<BridgeEval>>,
    sinks: Vec<FrameworkComponent<SqueezeSinkEval>>,
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = vec![&self.public_fold];
        out.push(&self.coeffs);
        if let Some(component) = &self.coeffs_rc {
            out.push(component);
        }
        out.push(&self.decomp);
        out.extend(self.decomp_rc.iter().map(|c| c as &dyn Component));
        out.push(&self.sib);
        out.extend(self.sib_rc.iter().map(|c| c as &dyn Component));
        if let Some(m) = &self.msglink {
            out.push(m);
        }
        out.push(&self.prefix);
        if let Some(msg) = &self.msg {
            out.push(msg);
        }
        out.extend(self.bridges.iter().map(|c| c as &dyn Component));
        out.extend(self.sinks.iter().map(|c| c as &dyn Component));
        out
    }
    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = vec![&self.public_fold];
        out.push(&self.coeffs);
        if let Some(component) = &self.coeffs_rc {
            out.push(component);
        }
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
        if let Some(msg) = &self.msg {
            out.push(msg);
        }
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
    fn from_flat(flat: &[SecureField], hosted: bool, native_mu: bool) -> Self {
        let mut it = flat.iter().copied();
        let mut next = || it.next().expect("claimed sums length mismatch");
        let coeffs = next();
        let coeffs_rc = if hosted { Vec::new() } else { vec![next()] };
        let decomp = next();
        let decomp_rc = (0..decomp_tables::RcKind::ALL.len())
            .map(|_| next())
            .collect();
        let sib = next();
        let sib_rc = (0..sib_tables::RcKind::ALL.len()).map(|_| next()).collect();
        let msglink = if hosted { SecureField::zero() } else { next() };
        let prefix = next();
        let bridges = (0..if native_mu { 2 } else { 4 }).map(|_| next()).collect();
        let sinks = (0..if native_mu { 1 } else { 2 }).map(|_| next()).collect();
        let native_use = next();
        assert!(it.next().is_none(), "claimed sums length mismatch");
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

/// Everything the layout builders need that is public-derivable from `input`.
struct LayoutCtx {
    hosted: bool,
    /// Hosted PUBLIC-message mode: µ is verifier-native and the µ sponge plus
    /// message bridge are omitted.
    public_message: bool,
    message_len: usize,
}

impl LayoutCtx {
    fn new(input: &MlDsaVerifyInput, hosted: bool, public_message: bool) -> Self {
        Self {
            hosted,
            public_message,
            message_len: input.message.len(),
        }
    }
}

fn module_trace_layout(ctx: &LayoutCtx) -> Vec<u32> {
    // Public folded-identity component marker (pinned to zero).
    let mut t = vec![LOG_N_LANES];
    // 1. coeffs + 2. unified range table (standalone only).
    t.extend(vec![coeffs_log_size(); coeffs::N_BASE_COLS]);
    if !ctx.hosted {
        t.push(coeffs_tables::range_table_log_size());
    }
    // 3. decomp + 4. rc ×4.
    t.extend(vec![decomp_log_size(); decomp::N_BASE_COLS]);
    for kind in decomp_tables::RcKind::ALL {
        t.push(kind.log_size());
    }
    // 5. sib + 6. rc ×3.
    let sls = sib_log_size();
    t.extend(vec![sls; sampleinball::N_BASE_COLS]);
    for kind in sib_tables::RcKind::ALL {
        t.push(kind.log_size());
    }
    // 7. msglink (standalone only).
    if !ctx.hosted {
        t.extend(vec![msglink::MSGLINK_LOG_SIZE; msglink::N_BASE_COLS]);
    }
    // Verifier-native prefix: private tr‖00‖00 or public µ.
    t.extend(vec![crate::sponge_link::LINK_LOG_SIZE; PREFIX_BASE_COLS]);
    // Private/standalone message bridge.
    if !ctx.public_message {
        t.extend(vec![bridge_log_size(ctx.message_len); BRIDGE_BASE_COLS]);
    }
    for len in bridge_lens(ctx.public_message) {
        let ls = bridge_log_size(len);
        t.extend(vec![ls; BRIDGE_BASE_COLS]);
    }
    for len in sink_lens(ctx.message_len, ctx.public_message) {
        let ls = bridge_log_size(len);
        t.extend(vec![ls; SINK_BASE_COLS]);
    }
    t
}

fn module_interaction_layout(ctx: &LayoutCtx) -> Vec<u32> {
    let mut i = Vec::new();
    // 1. coeffs + 2. unified range table (standalone only).
    i.extend(vec![coeffs_log_size(); coeffs::N_INTERACTION_COLS]);
    if !ctx.hosted {
        i.extend(vec![
            coeffs_tables::range_table_log_size();
            coeffs_tables::RANGE_TABLE_INTERACTION_COLS
        ]);
    }
    // 3. decomp + 4. rc ×4.
    i.extend(vec![decomp_log_size(); decomp::N_INTERACTION_COLS]);
    for kind in decomp_tables::RcKind::ALL {
        for _ in 0..decomp_tables::RC_TABLE_INTERACTION_COLS {
            i.push(kind.log_size());
        }
    }
    // 5. sib + 6. rc ×3.
    let sls = sib_log_size();
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
    // Verifier-native prefix: private tr‖00‖00 or public µ.
    i.extend(vec![
        crate::sponge_link::LINK_LOG_SIZE;
        prefix_n_interaction()
    ]);
    if !ctx.public_message {
        i.extend(vec![
            bridge_log_size(ctx.message_len);
            BRIDGE_INTERACTION_COLS
        ]);
    }
    for len in bridge_lens(ctx.public_message) {
        let ls = bridge_log_size(len);
        i.extend(vec![ls; BRIDGE_INTERACTION_COLS]);
    }
    for len in sink_lens(ctx.message_len, ctx.public_message) {
        let ls = bridge_log_size(len);
        i.extend(vec![ls; SINK_INTERACTION_COLS]);
    }
    i
}

/// The native-prefix producer's interaction column count: one batched
/// accumulator for either 66 private-µ prefix bytes or 64 public µ bytes.
fn prefix_n_interaction() -> usize {
    stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE
}

fn layout_for(ctx: &LayoutCtx, input: &MlDsaVerifyInput) -> TreeLayout {
    TreeLayout {
        preprocessed: all_preprocessed_log_sizes(input, ctx.hosted, ctx.public_message),
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

struct SpongeOutputs {
    mu: Option<Vec<u8>>,
    ct: Vec<u8>,
    sib: Vec<u8>,
}

/// Full squeeze outputs for the in-service jobs. Public-message mode computes
/// µ natively and therefore has no µ service output.
fn sponge_outputs(witness: &MlDsaWitness, native_mu: bool) -> SpongeOutputs {
    SpongeOutputs {
        mu: (!native_mu).then(|| full_squeeze(&witness.sponge.mu_absorbed, 1)),
        ct: full_squeeze(&witness.sponge.c_tilde_absorbed, 1),
        sib: full_squeeze(
            &witness.sponge.sample_in_ball_absorbed,
            sampleinball::MAX_SIB_SQUEEZE_BLOCKS,
        ),
    }
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
    group_evals: &[SecureField],
    rel: &Relations,
    claims: &Claims,
) -> Built {
    let public_evals = compute_public_evals(input, rel.r, rel.s);
    let public_fold_value = folded_check(
        &public_evals,
        &ClaimedEvals(group_evals),
        rel.rho_rlc,
        rel.r,
        rel.s,
    );
    let public_fold = FrameworkComponent::new(
        allocator,
        PublicFoldEval {
            value: public_fold_value,
        },
        SecureField::zero(),
    );
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
    // 2. unified coeffs range table (standalone only).
    let coeffs_rc = (!ctx.hosted).then(|| {
        FrameworkComponent::new(
            allocator,
            coeffs_tables::RangeTableEval {
                relation: rel.coeffs.range.clone(),
            },
            claims.coeffs_rc[0],
        )
    });
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
            log_size: sib_log_size(),
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
    // Verifier-native private tr prefix or public µ prefix.
    let prefix = FrameworkComponent::new(
        allocator,
        prefix_eval(input, stream_base, ctx.public_message, &rel.keccak.hash_io),
        claims.prefix,
    );
    let msg = (!ctx.public_message).then(|| {
        FrameworkComponent::new(
            allocator,
            msg_bridge_eval(
                ns,
                input.message.len(),
                stream_base,
                &rel.msglink,
                rel.shared_field.as_ref(),
                &rel.keccak.hash_io,
            ),
            claims.bridges[0],
        )
    });
    let bridge_claim_offset = usize::from(msg.is_some());
    let bridge_descs = bridge_evals(ns, stream_base, ctx.public_message, &rel.keccak.hash_io);
    let bridges = bridge_descs
        .into_iter()
        .enumerate()
        .map(|(idx, b)| {
            FrameworkComponent::new(allocator, b, claims.bridges[idx + bridge_claim_offset])
        })
        .collect();
    let sink_descs = sink_evals(
        ns,
        input.message.len(),
        stream_base,
        ctx.public_message,
        &rel.keccak.hash_io,
    );
    let sinks = sink_descs
        .into_iter()
        .enumerate()
        .map(|(idx, s)| FrameworkComponent::new(allocator, s, claims.sinks[idx]))
        .collect();

    Built {
        public_fold,
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
    ctx: LayoutCtx,
    /// Hosted mode: the host's shared message-source relation handle. `None` for
    /// standalone (the self-drawn `msglink` producer).
    shared_field: Option<SharedFieldRelation>,
    /// The keccak service's shared relations handle (REQUIRED — the service
    /// module must be composed before this one and draw into it).
    keccak_handle: SharedKeccakRelations,
    /// Hosted mode: the proof-wide range relation published by the shared
    /// table provider. Standalone mode draws and provides its own relation.
    shared_range: Option<SharedRangeRelation>,
    /// Instance namespace: role/domain tag mixed into the transcript and
    /// prefixed onto every instance-local preprocessed id (SIB schedule,
    /// bridges, sinks). "" = legacy single-instance ids. REQUIRED
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
    coeffs_rc_uses: RcUses,
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

    /// Build a standalone prover. Hosted callers must use [`Self::hosted`] or
    /// [`Self::hosted_public`] so the proof-wide range provider is wired too.
    pub fn new(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        shared_field: Option<SharedFieldRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        assert!(
            shared_field.is_none(),
            "hosted ML-DSA requires a shared range provider; use MlDsaProver::hosted"
        );
        Self::build(witness, input, shared_field, false, None, keccak_handle)
    }

    fn build(
        witness: MlDsaWitness,
        mut input: MlDsaVerifyInput,
        shared_field: Option<SharedFieldRelation>,
        public_message: bool,
        shared_range: Option<SharedRangeRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        input.tr = native_tr(&input);
        let hosted = shared_field.is_some() || public_message;
        let ctx = LayoutCtx::new(&input, hosted, public_message);
        let coeffs_rc_uses = coeffs::gen_coeffs_interaction(
            &witness,
            coeffs_log_size(),
            SecureField::zero(),
            SecureField::zero(),
            &CoeffsRelations::dummy(),
        )
        .rc_uses;
        let claims = Claims {
            hosted,
            ..Claims::default()
        };

        Self {
            witness,
            input,
            ctx,
            shared_field,
            keccak_handle,
            shared_range,
            namespace: String::new(),
            stream_base: 0,
            private_message: false,
            relations: None,
            coeffs_rc_mult: Vec::new(),
            coeffs_rc_uses,
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
        shared_range: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(
            witness,
            input,
            Some(shared_field),
            false,
            Some(shared_range),
            keccak_handle,
        )
    }

    /// Hosted PUBLIC-message constructor (S4): tr and µ are recomputed
    /// natively from the public key and message, and µ is constrained directly
    /// as the c̃-absorb prefix. No shared field relation or upstream byte
    /// conveyor is required. Must not be combined with
    /// [`Self::with_private_message`].
    pub fn hosted_public(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        shared_range: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(
            witness,
            input,
            None,
            true,
            Some(shared_range),
            keccak_handle,
        )
    }

    /// Range-use multiplicities contributed by this instance to the shared
    /// hosted table.
    pub fn range_uses(&self) -> &RcUses {
        &self.coeffs_rc_uses
    }

    /// Set the per-instance stream-id base (see the `stream_base` field).
    /// Prover and verifier must agree per role; use multiples of
    /// [`STREAM_BASE_STRIDE`].
    pub fn with_stream_base(mut self, base: u32) -> Self {
        self.stream_base = base;
        self
    }

    /// The sponge job shapes + witness byte streams this instance contributes
    /// to the proof-wide service: optional private µ, then c̃ and SIB.
    pub fn keccak_jobs(&self) -> (Vec<Shape>, Vec<Vec<u8>>) {
        let shapes = keccak_job_shapes(
            self.input.message.len(),
            self.stream_base,
            self.ctx.public_message,
        );
        let mut streams = Vec::with_capacity(shapes.len());
        if !self.ctx.public_message {
            streams.push(self.witness.sponge.mu_absorbed.clone());
        }
        streams.extend([
            self.witness.sponge.c_tilde_absorbed.clone(),
            self.witness.sponge.sample_in_ball_absorbed.clone(),
        ]);
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
    /// The public statement input.
    pub fn input(&self) -> &MlDsaVerifyInput {
        &self.input
    }
}

/// Byte payloads for the fixed bridges. Private mode includes µ→c̃; both modes
/// include w1Encode→c̃ and c̃→SIB.
fn bridge_bytes(outputs: &SpongeOutputs, w1_bytes: &[u8]) -> Vec<Vec<u8>> {
    outputs
        .mu
        .iter()
        .map(|mu| mu[..64].to_vec())
        .chain([w1_bytes.to_vec(), outputs.ct[..48].to_vec()])
        .collect()
}

/// Byte payloads for the remaining sinks: optional µ, then c̃.
fn sink_bytes(outputs: &SpongeOutputs) -> Vec<Vec<u8>> {
    outputs
        .mu
        .iter()
        .map(|mu| mu[64..].to_vec())
        .chain([outputs.ct[48..].to_vec()])
        .collect()
}

impl Air for MlDsaProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(
            channel,
            &self.input,
            &self.namespace,
            self.private_message,
            self.stream_base,
        );
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(draw_relations_common(
            channel,
            self.shared_field.as_ref(),
            self.shared_range.as_ref(),
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
            self.ctx.hosted,
            self.ctx.public_message,
        )
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_all_preprocessed(
            &self.input,
            self.ctx.hosted,
            self.ctx.public_message,
        ))
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(
            allocator,
            &self.namespace,
            self.stream_base,
            &self.ctx,
            &self.input,
            &self.group_evals,
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
            .max(sib_log_size())
            .max(coeffs_tables::range_table_log_size())
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 2
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed(
            &self.input,
            self.ctx.hosted,
            self.ctx.public_message,
        ));
    }
    /// Partial preprocessed writes: with multiple hosted ML-DSA instances, the
    /// fixed-content tables (coeffs/decomp/SIB layouts, rc values, keccak tables)
    /// keep global ids and tree-0 dedups them first-writer-wins, so a later
    /// instance writes only its namespaced instance-local columns. `selected_ids`
    /// is this module's id list filtered to first-seen,
    /// in commit order (air-core `select_first_preprocessed_ids`).
    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let ids = all_preprocessed_ids(
            &self.namespace,
            &self.input,
            self.ctx.hosted,
            self.ctx.public_message,
        );
        let cols = gen_all_preprocessed(&self.input, self.ctx.hosted, self.ctx.public_message);
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
            self.ctx.hosted,
            self.ctx.public_message,
        );
        let cols = gen_all_preprocessed(&self.input, self.ctx.hosted, self.ctx.public_message);
        fingerprint_preprocessed_columns("mldsa_statement", &ids, &cols)
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut evals = vec![col_eval(LOG_N_LANES, vec![m31(0); 1usize << LOG_N_LANES])];

        // 1. coeffs base + 2. unified range multiplicity (standalone only).
        let cls = coeffs_log_size();
        evals.extend(coeffs::gen_coeffs_base_trace(&self.witness, cls));
        self.coeffs_rc_mult.clear();
        if !self.ctx.hosted {
            self.coeffs_rc_mult = vec![coeffs_tables::gen_range_table_multiplicities([
                self.coeffs_rc_uses.for_kind(coeffs_tables::RcKind::Rc9),
                self.coeffs_rc_uses.for_kind(coeffs_tables::RcKind::Rc13),
                self.coeffs_rc_uses.for_kind(coeffs_tables::RcKind::Rc8),
                self.coeffs_rc_uses.for_kind(coeffs_tables::RcKind::Rc7),
                self.coeffs_rc_uses.for_kind(coeffs_tables::RcKind::Ternary),
            ])];
            evals.extend(self.coeffs_rc_mult.clone());
        }

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
        let sls = sib_log_size();
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

        // Verifier-native private tr prefix or public µ prefix. Base traces run
        // before relations are drawn, so use dummy relation descriptors.
        let dummy_hash_io = HashIoRelation::dummy();
        let dummy_msglink = MsgLinkRelation::dummy();
        evals.extend(
            prefix_eval(
                &self.input,
                self.stream_base,
                self.ctx.public_message,
                &dummy_hash_io,
            )
            .gen_base(),
        );

        let outputs = sponge_outputs(&self.witness, self.ctx.public_message);
        if !self.ctx.public_message {
            evals.extend(
                msg_bridge_eval(
                    &self.namespace,
                    self.input.message.len(),
                    self.stream_base,
                    &dummy_msglink,
                    None,
                    &dummy_hash_io,
                )
                .gen_base(&self.input.message),
            );
        }
        let bbytes = bridge_bytes(&outputs, &self.decomp_w1_bytes);
        let bridge_descs = bridge_evals(
            &self.namespace,
            self.stream_base,
            self.ctx.public_message,
            &dummy_hash_io,
        );
        for (b, bytes) in bridge_descs.iter().zip(bbytes.iter()) {
            evals.extend(b.gen_base(bytes));
        }

        // Private µ remains an in-service witness and keeps its sanity check.
        // Native/public µ deliberately has no prover-side equality assertion:
        // disagreement is rejected by the c̃ absorb constraint, not a panic.
        if let Some(mu) = &outputs.mu {
            assert_eq!(mu[..64], self.witness.sponge.mu_squeezed[..64]);
        }
        assert_eq!(
            outputs.ct[..48],
            self.input.c_tilde[..],
            "c̃ squeeze prefix mismatch"
        );
        assert_eq!(
            outputs.sib.len(),
            sampleinball::MAX_SIB_SQUEEZE_BYTES,
            "SIB squeeze must fill the fixed five-block resource cap"
        );

        let sbytes = sink_bytes(&outputs);
        let sink_descs = sink_evals(
            &self.namespace,
            self.input.message.len(),
            self.stream_base,
            self.ctx.public_message,
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
        // 2. unified coeffs range table (standalone only).
        self.claims.coeffs_rc.clear();
        if !self.ctx.hosted {
            let (tr, sum) = coeffs_tables::gen_range_table_interaction(
                &self.coeffs_rc_mult[0],
                &rel.coeffs.range,
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
        let sls = sib_log_size();
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

        let (prefix_tr, prefix_sum) = prefix_eval(
            &self.input,
            self.stream_base,
            self.ctx.public_message,
            &rel.keccak.hash_io,
        )
        .gen_interaction();
        self.claims.prefix = prefix_sum;
        evals.extend(prefix_tr);

        let outputs = sponge_outputs(&self.witness, self.ctx.public_message);
        self.claims.bridges.clear();
        if !self.ctx.public_message {
            let (msg_tr, msg_sum) = msg_bridge_eval(
                &self.namespace,
                self.input.message.len(),
                self.stream_base,
                &rel.msglink,
                rel.shared_field.as_ref(),
                &rel.keccak.hash_io,
            )
            .gen_interaction(&self.input.message);
            self.claims.bridges.push(msg_sum);
            evals.extend(msg_tr);
        }
        let bbytes = bridge_bytes(&outputs, &self.decomp_w1_bytes);
        let bridge_descs = bridge_evals(
            &self.namespace,
            self.stream_base,
            self.ctx.public_message,
            &rel.keccak.hash_io,
        );
        for (b, bytes) in bridge_descs.iter().zip(bbytes.iter()) {
            let (tr, sum) = b.gen_interaction(bytes);
            self.claims.bridges.push(sum);
            evals.extend(tr);
        }

        let sbytes = sink_bytes(&outputs);
        let sink_descs = sink_evals(
            &self.namespace,
            self.input.message.len(),
            self.stream_base,
            self.ctx.public_message,
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
    ctx: LayoutCtx,
    /// Hosted mode: the host's shared message-source relation handle.
    shared_field: Option<SharedFieldRelation>,
    /// The keccak service's shared relations handle (must be populated by the
    /// service module, composed before this one).
    keccak_handle: SharedKeccakRelations,
    /// Hosted mode: the proof-wide range relation handle.
    shared_range: Option<SharedRangeRelation>,
    /// Instance namespace (must match the prover's per role).
    namespace: String,
    /// Per-instance stream-id base (must match the prover's per role).
    stream_base: u32,
    /// Private-message mode (must match the prover's per role).
    private_message: bool,
    group_evals: Vec<SecureField>,
    claims: Claims,
    relations: Option<Relations>,
    built: Option<Built>,
}

impl MlDsaVerifier {
    fn relations(&self) -> &Relations {
        self.relations.as_ref().expect("relations drawn")
    }

    /// Reconstruct a standalone verifier. Hosted callers must use
    /// [`Self::hosted`] or [`Self::hosted_public`] so the proof-wide range
    /// provider is wired too.
    pub fn new(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        shared_field: Option<SharedFieldRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        assert!(
            shared_field.is_none(),
            "hosted ML-DSA requires a shared range provider; use MlDsaVerifier::hosted"
        );
        Self::build(
            input,
            group_evals,
            claimed_sums,
            shared_field,
            false,
            None,
            keccak_handle,
        )
    }

    fn build(
        mut input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        shared_field: Option<SharedFieldRelation>,
        public_message: bool,
        shared_range: Option<SharedRangeRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        input.tr = native_tr(&input);
        let hosted = shared_field.is_some() || public_message;
        let ctx = LayoutCtx::new(&input, hosted, public_message);
        let claims = Claims::from_flat(&claimed_sums, hosted, public_message);
        Self {
            input,
            ctx,
            shared_field,
            keccak_handle,
            shared_range,
            namespace: String::new(),
            stream_base: 0,
            private_message: false,
            group_evals,
            claims,
            relations: None,
            built: None,
        }
    }

    /// Hosted-mode constructor (`shared_field` provided by the host).
    pub fn hosted(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        shared_field: SharedFieldRelation,
        shared_range: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(
            input,
            group_evals,
            claimed_sums,
            Some(shared_field),
            false,
            Some(shared_range),
            keccak_handle,
        )
    }

    /// Hosted PUBLIC-message constructor (S4) — mirror of
    /// [`MlDsaProver::hosted_public`].
    pub fn hosted_public(
        input: MlDsaVerifyInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        shared_range: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        Self::build(
            input,
            group_evals,
            claimed_sums,
            None,
            true,
            Some(shared_range),
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
            &self.namespace,
            self.private_message,
            self.stream_base,
        );
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let rel = draw_relations_common(
            channel,
            self.shared_field.as_ref(),
            self.shared_range.as_ref(),
            &self.keccak_handle,
        );
        self.claims.native_use = native_use_sum(&self.group_evals, &rel.coeffs);
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
            self.ctx.hosted,
            self.ctx.public_message,
        )
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_all_preprocessed(
            &self.input,
            self.ctx.hosted,
            self.ctx.public_message,
        ))
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(
            allocator,
            &self.namespace,
            self.stream_base,
            &self.ctx,
            &self.input,
            &self.group_evals,
            &rel,
            &self.claims,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("built").ordered()
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
    input
        .validate_public_key()
        .map_err(|_| ProvingError::ConstraintsNotSatisfied)?;
    sampleinball::validate_stream(&witness).map_err(|_| ProvingError::ConstraintsNotSatisfied)?;
    // The standalone path instantiates a PRIVATE keccak service for this one
    // instance's private µ, c̃, and SIB jobs; the composition is
    // `[service, mldsa]`.
    let handle = SharedKeccakRelations::new();
    let mut prover = MlDsaProver::new(witness, input.clone(), None, handle.clone());
    let (job_shapes, job_streams) = prover.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, handle);
    let (stark_proof, post_interaction_payloads) =
        air_core::prove_with_post_interaction(&mut [&mut service, &mut prover], config)?;
    Ok(MlDsaProof {
        input: prover.input.clone(),
        group_evals: prover.group_evals,
        claimed_sums: prover.claims.ordered(),
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
pub fn debug_layout(input: &MlDsaVerifyInput) -> TreeLayout {
    let ctx = LayoutCtx::new(input, false, false);
    layout_for(&ctx, input)
}

/// The number of group evaluations every proof carries (the 30 coeffs poly
/// groups). Hosts gate `group_evals.len()` on this before construction.
pub fn n_group_evals() -> usize {
    coeffs::layout::N_GROUPS
}

fn claimed_sums_len(hosted: bool, native_mu: bool) -> usize {
    1 + usize::from(!hosted) * coeffs_tables::RANGE_TABLE_COMPONENTS
        + 1
        + decomp_tables::RcKind::ALL.len()
        + 1
        + sib_tables::RcKind::ALL.len()
        + usize::from(!hosted)
        + 1 // native tr/private prefix or native public µ prefix
        + if native_mu { 2 } else { 4 } // msg + fixed bridges
        + if native_mu { 1 } else { 2 } // sinks
        + 1 // coeffs native use
}

/// Exact claimed-sum length for hosted private-message/revocation mode.
pub fn hosted_claimed_sums_len() -> usize {
    claimed_sums_len(true, false)
}

/// Exact claimed-sum length for hosted-public issuer/device native-µ mode.
pub fn hosted_public_claimed_sums_len() -> usize {
    claimed_sums_len(true, true)
}

pub fn verify_mldsa(
    proof: &MlDsaProof,
    expected_config: PcsConfig,
) -> Result<(), VerificationError> {
    if proof.stark_proof.config != expected_config {
        return Err(VerificationError::InvalidStructure(
            "ML-DSA statement: unexpected PCS config".to_string(),
        ));
    }
    proof.input.validate_public_key().map_err(|message| {
        VerificationError::InvalidStructure(format!("ML-DSA statement: {message}"))
    })?;
    if proof.group_evals.len() != n_group_evals()
        || proof.claimed_sums.len() != claimed_sums_len(false, false)
    {
        return Err(VerificationError::InvalidStructure(
            "ML-DSA statement: bad claim shape".to_string(),
        ));
    }
    let handle = SharedKeccakRelations::new();
    let job_shapes = keccak_job_shapes(proof.input.message.len(), 0, false);
    if proof.service_claimed_sums.len() != stwo_keccak::service::service_claimed_sums_len() {
        return Err(VerificationError::InvalidStructure(
            "ML-DSA statement: bad service claimed-sums length".to_string(),
        ));
    }
    // The keccak service's round LogUp is GKR-offloaded: the payload-aware
    // verify entry distributes `post_interaction_payloads` to each module in
    // prove order; the service's `verify_post_interaction` fails closed on a
    // missing/corrupt blob (an empty blob fails GKR decode).
    let mut service = KeccakServiceVerifier::new(
        job_shapes,
        proof.service_claimed_sums.clone(),
        handle.clone(),
    );
    let mut verifier = MlDsaVerifier::new(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        None,
        handle,
    );
    let expected_root = air_core::compute_canonical_preprocessed_root(
        &mut [&mut service, &mut verifier],
        expected_config,
    )?;
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
    // The public folded identity is enforced by `PublicFoldEval` in the outer
    // STARK component list.
    Ok(())
}
