//! `MlDsaAir` composes in-circuit ML-DSA-65 verification.
//!
//! One air-core module pair ([`MlDsaProver`] impl `Air`+`AirProver`,
//! [`MlDsaVerifier`] impl `Air`) proves the entire ML-DSA-65 verification via a
//! single [`air_core::prove`] / [`air_core::verify`] call. It stitches together:
//!
//!   * public-key modes evaluate `ExpandA(ρ)` verifier-natively. Hosted
//!     private-key mode instead consumes private `NttCell` / `T1Cell` bindings,
//!     proves the inverse NTT and all 36 public-key polynomial evaluations,
//!     then closes the complete 66-term folded identity in the AIR.
//!   * `coeffs` — the tall bivariate-Horner integer-lift component (yields the
//!     W-cell / C-cell bindings + constrained public fold).
//!   * `decomp` — [DECOMP]+[HINT]; consumes W-cells, yields the 768 `w1Encode`
//!     bytes into the c̃-absorb stream.
//!   * `sib`         — SampleInBall FSM; consumes C-cells + the SIB squeeze stream.
//!   * `msglink` — the public message-byte producer for standalone mode.
//!   * public-byte links / bridges / sinks ([`crate::sponge_link`]) that feed
//!     public prefixes, move bytes between the remaining HashIo streams, and
//!     close every squeeze balance. Hosted-private-key mode computes `tr` in
//!     the shared Keccak service from private `pkEncode` bytes in field 1.
//!
//! The remaining SHAKE-256 signature chains are jobs of the proof-wide
//! [`stwo_keccak::service::KeccakServiceProver`], which owns the vertical
//! sponge, Keccak, round, and table components once for all hosted instances and
//! publishes the drawn [`KeccakRelations`] through a
//! [`SharedKeccakRelations`] handle this module consumes. The instance exposes
//! its sponge job shapes via [`keccak_job_shapes`] / [`MlDsaProver::keccak_jobs`]
//! so the host can build the service, and takes an explicit per-instance
//! `stream_base` so HashIo stream identifiers stay globally unique under the
//! shared relation set.
//!
//! `layout()`, `claimed_sums()`, `write_trace()`, `write_interaction()`,
//! `build_components()`, and `components()` must use the same component order.

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
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
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
use crate::private_key_eval::{
    self, PrivateDeviceEvals, PrivateKeyBase, PrivateKeyEvalBindings, PrivateKeyEvalClaims,
    PrivateKeyEvalError, PrivateKeyEvalRelations, PrivateKeyEvalWitness, PrivateKeyTraceComponents,
};
use crate::sponge_link::{
    BridgeEval, PublicPrefixEval, SqueezeSinkEval, SrcRelation, BRIDGE_BASE_COLS,
    BRIDGE_INTERACTION_COLS, PREFIX_BASE_COLS, SINK_BASE_COLS, SINK_INTERACTION_COLS,
};
use crate::types::{MlDsaPrivateKeyPublicInput, MlDsaVerifyInput};
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
// Every hosted ML-DSA instance shares the service's HashIo relation. Thus,
// stream identifiers must be unique for each instance. Each identifier is
// `stream_base + OFFSET`; the per-instance `stream_base` is an explicit
// constructor parameter (deterministic, mixed into the transcript). The
// offsets at `stream_base = 0` are the unprefixed identifiers. The decomp and
// SIB offsets ([`STREAM_ID_CTILDE_ABSORB`] = 0,
// [`STREAM_ID_SIB_SQUEEZE`] = 1) live in `binding.rs`. Bases retain the
// protocol's 128-wide namespace stride.

/// Private µ-chain absorb stream offset (`tr ‖ 0x00 ‖ 0x00 ‖ M`).
pub const MU_ABSORB: u32 = 10;
/// Private µ-chain squeeze stream offset.
pub const MU_SQUEEZE: u32 = 11;
/// Private-key `tr = SHAKE256(pkEncode)` absorb stream offset.
pub const TR_ABSORB: u32 = 8;
/// Private-key `tr` squeeze stream offset.
pub const TR_SQUEEZE: u32 = 9;
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

/// Fixed maximum byte length of the request-derived device COSE
/// `Sig_structure` in the TS13 demo profile.
///
/// The measured request corpus selects 1024 bytes. Hosted-private-key proofs
/// allocate this entire window so request length cannot change their tree
/// layout, preprocessed root, or Keccak permutation schedule.
pub const DEVICE_SIG_STRUCTURE_CAPACITY: usize = 1_024;

/// Field identifier for the hosted ML-DSA message on the shared
/// [`FieldBytesRelation`].
///
/// The host yields the complete `Sig_structure` under this identifier. The µ
/// bridge consumes the same tuples.
pub const HOSTED_MSG_FIELD_ID: u32 = 0;
/// The normalized private `pkEncode` field yielded by the mdoc key binder.
///
/// This field uses the host-drawn [`FieldBytesRelation`] with
/// [`HOSTED_MSG_FIELD_ID`]. The different field identifier separates the byte
/// domains. This design does not draw another relation and does not cause a
/// cycle in module order.
pub const HOSTED_DEVICE_PK_FIELD_ID: u32 = 1;

/// Transcript tag for hosted private-key statements.
const HOSTED_PRIVATE_KEY_MODE_TAG: u64 = 0x4d4c_4453_4150_4b01;

// Permutation-id layout for the composed SHAKE chains.

/// Models the contiguous permutation-id ranges of the SHAKE-256 chains.
/// Public-message instances omit the µ chain (`n_mu = 0`).
///
/// The actual assignment is performed by
/// [`stwo_keccak::sponge_v::JobList::new`] over the proof-wide concatenated
/// job list. Tests use this struct to check the same range boundaries.
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
    /// Opaque post-interaction payloads. The Keccak service stores its
    /// round-GKR proof in its module slot.
    pub post_interaction_payloads: Vec<Vec<u8>>,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

// =============================================================================
// Shared shape derivation (identical prover / verifier).
// =============================================================================

/// The sponge shapes for a statement, derived from PUBLIC lengths/mode only.
///
/// * tr: private-public-key mode only; absorbs `pkEncode` (1,952 bytes),
///   squeezes 1 block.
/// * µ:  private-message mode only; absorbs `tr ‖ 0x00 ‖ 0x00 ‖ M`
///   (len `66 + |M|`), squeezes 1 block.
/// * c̃:  absorbs `µ ‖ w1Encode(w1')` (len 832 = 64 + 768), squeezes 1 block.
/// * SIB: absorbs `c̃` (48 bytes), squeezes the fixed five-block resource cap.
struct Shapes {
    tr: Option<Shape>,
    mu: Option<Shape>,
    ct: Shape,
    sib: Shape,
}

fn validate_device_message_capacity(message_len: usize) -> Result<(), PrivateKeyEvalError> {
    if message_len > DEVICE_SIG_STRUCTURE_CAPACITY {
        return Err(PrivateKeyEvalError::MessageExceedsCapacity {
            message_len,
            message_capacity: DEVICE_SIG_STRUCTURE_CAPACITY,
        });
    }
    Ok(())
}

/// The instance's SHAKE256 signature-job shapes, stream ids offset by
/// `stream_base`. `native_mu` omits the private µ job.
/// Permutation-id bases stay 0. The proof-wide [`stwo_keccak::sponge_v::JobList`]
/// stamps the global plan over the concatenated job list.
fn shapes(message_len: usize, stream_base: u32, native_mu: bool, private_key: bool) -> Shapes {
    debug_assert!(!(native_mu && private_key));
    let b = stream_base;
    let tr = private_key
        .then(|| Shape::new(crate::constants::PK_BYTES, 1, b + TR_ABSORB, b + TR_SQUEEZE));
    let mu = (!native_mu).then(|| {
        if private_key {
            Shape::with_message_capacity(
                66 + message_len,
                66 + DEVICE_SIG_STRUCTURE_CAPACITY,
                1,
                b + MU_ABSORB,
                b + MU_SQUEEZE,
            )
            .expect("hosted-private-key message capacity was validated")
        } else {
            Shape::new(66 + message_len, 1, b + MU_ABSORB, b + MU_SQUEEZE)
        }
    });
    let ct = Shape::new(64 + 768, 1, b + CT_ABSORB, b + CT_SQUEEZE);
    let sib = Shape::new(
        48,
        sampleinball::MAX_SIB_SQUEEZE_BLOCKS,
        b + SIB_ABSORB,
        b + STREAM_ID_SIB_SQUEEZE,
    );
    Shapes { tr, mu, ct, sib }
}

/// PUBLIC: all sponge jobs contributed to the proof-wide service: optional
/// private µ, then c̃ and SIB. `native_mu = true` is the hosted-public
/// issuer/device shape; `false` is standalone/private revocation.
pub fn keccak_job_shapes(message_len: usize, stream_base: u32, native_mu: bool) -> Vec<Shape> {
    let sh = shapes(message_len, stream_base, native_mu, false);
    sh.tr
        .into_iter()
        .chain(sh.mu)
        .chain([sh.ct, sh.sib])
        .collect()
}

/// Sponge jobs for a hosted public-message statement whose public key is
/// private: in-circuit `tr`, then in-circuit µ, c̃, and SIB.
pub fn hosted_private_key_keccak_job_shapes(message_len: usize, stream_base: u32) -> Vec<Shape> {
    try_hosted_private_key_keccak_job_shapes(message_len, stream_base)
        .expect("hosted-private-key message exceeds DEVICE_SIG_STRUCTURE_CAPACITY")
}

/// Checked form of [`hosted_private_key_keccak_job_shapes`], for public
/// request validation before a prover or verifier is constructed.
pub fn try_hosted_private_key_keccak_job_shapes(
    message_len: usize,
    stream_base: u32,
) -> Result<Vec<Shape>, PrivateKeyEvalError> {
    validate_device_message_capacity(message_len)?;
    let sh = shapes(message_len, stream_base, false, true);
    Ok(sh
        .tr
        .into_iter()
        .chain(sh.mu)
        .chain([sh.ct, sh.sib])
        .collect())
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
    private_key: Option<PrivateKeyEvalRelations>,
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
    private_key_bindings: Option<&PrivateKeyEvalBindings>,
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
    let private_key = private_key_bindings.map(|bindings| {
        PrivateKeyEvalRelations::from_bindings(bindings, coeffs.eval.clone(), coeffs.range.clone())
    });
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
        private_key,
        decomp,
        sib,
    }
}

// =============================================================================
// mix_public (identical both sides).
// =============================================================================

fn mix_public(
    channel: &mut Blake2sChannel,
    input: Option<&MlDsaVerifyInput>,
    message: &[u8],
    namespace: &str,
    private_message: bool,
    private_key: bool,
    stream_base: u32,
) {
    // Mix the instance role into the transcript. This prevents replay between
    // same-shaped device and revocation instances.
    channel.mix_u64(namespace.len() as u64);
    for b in namespace.as_bytes() {
        channel.mix_u64(*b as u64);
    }
    if private_key {
        channel.mix_u64(HOSTED_PRIVATE_KEY_MODE_TAG);
    } else {
        let input = input.expect("public-key statement requires the public key");
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
    }
    // Message length + bytes. Private-message mode (revocation: the signed
    // bytes carry the PRIVATE id_lo/id_hi bounds) mixes only the length: the
    // bytes never appear in the statement and flow exclusively through the
    // host's FieldBytesRelation into the in-circuit µ absorption, exactly like
    // the already-private c̃/µ streams below.
    channel.mix_u64(message.len() as u64);
    if !private_message {
        for b in message {
            channel.mix_u64(*b as u64);
        }
    }
    // The per-instance stream-id base: pins every HashIo stream id this
    // instance's bridges/sinks/decomp/sib use under the SHARED relation set.
    // (The sponge job shapes themselves are mixed ONCE by the keccak service.)
    channel.mix_u64(stream_base as u64);
    // c̃ and µ are not mixed as public values. They flow only through HashIo.
    // The transcript is transparent and can expose witness-derived data.
    // group_evals are mixed with the claimed sums after the base commitment.
}

// =============================================================================
// Bridge / sink / prefix descriptors (public-derivable shapes).
// =============================================================================

fn bridge_log_size(len: usize) -> u32 {
    padded_log_size(len).max(LOG_N_LANES)
}

/// Verifier-native `tr = SHAKE256(pkEncode(ρ,t1), 64)`.
///
/// Public-key constructors write this value to `input.tr` before they mix the
/// transcript or build a component. Hosted private-key mode computes `tr` only
/// as a private service witness.
pub fn native_tr(input: &MlDsaVerifyInput) -> [u8; 64] {
    let bytes = full_squeeze(&input.encode_pk(), 1);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&bytes[..64]);
    tr
}

/// Verifier-native public-message `µ = SHAKE256(tr ‖ 0x00 ‖ 0x00 ‖ M, 64)`.
/// This function derives `tr` from `pkEncode`.
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
/// - private-key mode: public `0x00 ‖ 0x00 ‖ M` into µ-absorb@64; the
///   in-circuit tr→µ bridge supplies positions 0..64.
fn prefix_eval(
    input: Option<&MlDsaVerifyInput>,
    message: &[u8],
    stream_base: u32,
    native_mu: bool,
    private_key: bool,
    hash_io: &HashIoRelation,
) -> PublicPrefixEval {
    let (dst_stream, dst_off, bytes) = if private_key {
        let mut bytes = Vec::with_capacity(2 + message.len());
        bytes.extend_from_slice(&[0x00, 0x00]);
        bytes.extend_from_slice(message);
        (stream_base + MU_ABSORB, 64, bytes)
    } else if native_mu {
        let input = input.expect("native µ requires the public key");
        (stream_base + CT_ABSORB, 0, native_public_mu(input).to_vec())
    } else {
        let input = input.expect("private-message prefix requires the public key");
        let mut bytes = Vec::with_capacity(66);
        bytes.extend_from_slice(&input.tr);
        bytes.extend_from_slice(&[0x00, 0x00]);
        (stream_base + MU_ABSORB, 0, bytes)
    };
    PublicPrefixEval {
        dst_stream,
        dst_off,
        entry_capacity: if private_key {
            2 + DEVICE_SIG_STRUCTURE_CAPACITY
        } else {
            bytes.len()
        },
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

/// Fixed sponge bridges. Private-public-key mode prepends pk→tr and tr→µ;
/// private-µ modes include µ→c̃; native-µ mode starts at w1Encode→c̃.
fn bridge_evals(
    ns: &str,
    stream_base: u32,
    native_mu: bool,
    private_key: bool,
    shared_field: Option<&FieldBytesRelation>,
    hash_io: &HashIoRelation,
) -> Vec<BridgeEval> {
    let b = stream_base;
    let mut bridges = Vec::with_capacity(if private_key {
        5
    } else if native_mu {
        2
    } else {
        3
    });
    if private_key {
        let field = shared_field.expect("private-key mode requires a hosted field relation");
        bridges.push(BridgeEval {
            tag: "pk_tr",
            ns: ns.to_string(),
            log_size: bridge_log_size(crate::constants::PK_BYTES),
            src: SrcRelation::FieldBytes(field.clone(), HOSTED_DEVICE_PK_FIELD_ID),
            dst_stream: b + TR_ABSORB,
            dst_off: 0,
            len: crate::constants::PK_BYTES,
            hash_io: hash_io.clone(),
        });
        bridges.push(BridgeEval {
            tag: "tr_mu",
            ns: ns.to_string(),
            log_size: bridge_log_size(64),
            src: SrcRelation::HashIo(hash_io.clone(), b + TR_SQUEEZE, 0),
            dst_stream: b + MU_ABSORB,
            dst_off: 0,
            len: 64,
            hash_io: hash_io.clone(),
        });
    }
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

/// Consume squeeze tails not used by bridges or domain components. Native-µ
/// mode needs only the c̃ tail; private µ adds its tail, and private-key mode
/// adds the `tr` tail too.
fn sink_evals(
    ns: &str,
    message_len: usize,
    stream_base: u32,
    native_mu: bool,
    private_key: bool,
    hash_io: &HashIoRelation,
) -> Vec<SqueezeSinkEval> {
    let b = stream_base;
    let sh = shapes(message_len, b, native_mu, private_key);
    let mut sinks = Vec::with_capacity(if private_key {
        3
    } else if native_mu {
        1
    } else {
        2
    });
    if let Some(tr) = sh.tr {
        let tr_len = RATE * tr.n_squeeze - 64;
        sinks.push(SqueezeSinkEval {
            tag: "tr",
            ns: ns.to_string(),
            log_size: bridge_log_size(tr_len),
            stream: b + TR_SQUEEZE,
            off: 64,
            len: tr_len,
            hash_io: hash_io.clone(),
        });
    }
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

/// Preprocessed column identifiers in commit order. Message links and public
/// links contribute no columns. The Keccak service owns the sponge, Keccak,
/// round, and table columns. Private bridges and remaining sinks contribute
/// columns here.
///
/// This is called BEFORE relations are drawn (air-core commits the preprocessed
/// tree first), so the bridge/sink descriptors use `dummy()` relations — their
/// `preprocessed_ids()` read only `tag` + public shape, never the relation (and
/// never the stream ids, so `stream_base = 0` here is shape-neutral).
fn all_preprocessed_ids(
    ns: &str,
    message_len: usize,
    hosted: bool,
    public_message: bool,
    private_key: bool,
) -> Vec<PreProcessedColumnId> {
    let hash_io = HashIoRelation::dummy();
    let field = private_key.then(FieldBytesRelation::dummy);
    let msglink = MsgLinkRelation::dummy();
    let native_mu = public_message && !private_key;
    let mut ids = Vec::new();
    // coeffs + its unified range table (standalone only; hosted uses the
    // proof-wide provider module).
    ids.extend(coeffs::coeffs_preprocessed_ids());
    if !hosted {
        ids.extend(coeffs_tables::range_table_preprocessed_ids());
    }
    if private_key {
        ids.extend(private_key_eval::preprocessed_ids());
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
            msg_bridge_eval(ns, message_len, 0, &msglink, None, &hash_io).preprocessed_ids(),
        );
    }
    for b in bridge_evals(ns, 0, native_mu, private_key, field.as_ref(), &hash_io) {
        ids.extend(b.preprocessed_ids());
    }
    for s in sink_evals(ns, message_len, 0, native_mu, private_key, &hash_io) {
        ids.extend(s.preprocessed_ids());
    }
    ids
}

fn all_preprocessed_log_sizes(
    message_len: usize,
    hosted: bool,
    public_message: bool,
    private_key: bool,
) -> Vec<u32> {
    let native_mu = public_message && !private_key;
    let mut sizes = Vec::new();
    let cls = coeffs_log_size();
    sizes.extend(vec![cls; coeffs::coeffs_preprocessed_ids().len()]);
    if !hosted {
        sizes.extend(vec![
            coeffs_tables::range_table_log_size();
            coeffs_tables::range_table_preprocessed_ids().len()
        ]);
    }
    if private_key {
        sizes.extend(private_key_eval::preprocessed_log_sizes());
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
        sizes.extend(vec![bridge_log_size(message_len); 2]);
    }
    for len in bridge_lens(native_mu, private_key) {
        sizes.extend(vec![bridge_log_size(len); 2]);
    }
    for len in sink_lens(message_len, native_mu, private_key) {
        sizes.extend(vec![bridge_log_size(len); 2]);
    }
    sizes
}

fn bridge_lens(native_mu: bool, private_key: bool) -> Vec<usize> {
    if private_key {
        vec![crate::constants::PK_BYTES, 64, 64, 768, 48]
    } else if native_mu {
        vec![768, 48]
    } else {
        vec![64, 768, 48]
    }
}
fn sink_lens(message_len: usize, native_mu: bool, private_key: bool) -> Vec<usize> {
    let sh = shapes(message_len, 0, native_mu, private_key);
    sh.tr
        .into_iter()
        .map(|tr| RATE * tr.n_squeeze - 64)
        .chain(sh.mu.into_iter().map(|mu| RATE * mu.n_squeeze - 64))
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
    message_len: usize,
    hosted: bool,
    public_message: bool,
    private_key: bool,
) -> Vec<ColEval> {
    let hash_io = HashIoRelation::dummy();
    let field = private_key.then(FieldBytesRelation::dummy);
    let msglink = MsgLinkRelation::dummy();
    let native_mu = public_message && !private_key;
    let mut cols = Vec::new();
    let cls = coeffs_log_size();
    cols.extend(coeffs::gen_coeffs_preprocessed(cls));
    if !hosted {
        cols.extend(coeffs_tables::gen_range_table_preprocessed());
    }
    if private_key {
        cols.extend(private_key_eval::gen_preprocessed());
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
            msg_bridge_eval("", message_len, 0, &msglink, None, &hash_io).gen_preprocessed(),
        );
    }
    for b in bridge_evals("", 0, native_mu, private_key, field.as_ref(), &hash_io) {
        cols.extend(b.gen_preprocessed());
    }
    for s in sink_evals("", message_len, 0, native_mu, private_key, &hash_io) {
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
    public_fold: Option<FrameworkComponent<PublicFoldEval>>,
    coeffs: FrameworkComponent<CoeffsEval>,
    private_key: Option<PrivateKeyTraceComponents>,
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
    private_fold: Option<FrameworkComponent<private_key_eval::PrivateFoldEval>>,
}

impl Built {
    fn ordered(&self) -> Vec<&dyn Component> {
        let mut out: Vec<&dyn Component> = Vec::new();
        if let Some(public_fold) = &self.public_fold {
            out.push(public_fold);
        }
        out.push(&self.coeffs);
        if let Some(private_key) = &self.private_key {
            out.extend(private_key.trace_components());
        }
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
        if let Some(private_fold) = &self.private_fold {
            out.push(private_fold);
        }
        out
    }
    fn ordered_prover(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut out: Vec<&dyn ComponentProver<SimdBackend>> = Vec::new();
        if let Some(public_fold) = &self.public_fold {
            out.push(public_fold);
        }
        out.push(&self.coeffs);
        if let Some(private_key) = &self.private_key {
            out.extend(private_key.trace_prover_components());
        }
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
        if let Some(private_fold) = &self.private_fold {
            out.push(private_fold);
        }
        out
    }
}

/// The claimed-sum bag in component order. The final entry is the private
/// fold claim in private-key mode and `native_use_sum` otherwise.
#[derive(Clone, Default)]
struct Claims {
    /// Hosted mode drops the `msglink` claim from `ordered()` / `from_flat()`.
    hosted: bool,
    coeffs: SecureField,
    private_key: Option<PrivateKeyEvalClaims>,
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
        if let Some(private_key) = &self.private_key {
            v.extend([
                private_key.ntt.butterfly,
                private_key.ntt.scaling,
                private_key.t1,
            ]);
        }
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
        if let Some(private_key) = &self.private_key {
            v.push(private_key.fold);
        } else {
            v.push(self.native_use);
        }
        v
    }

    /// Reconstruct the bag from a flat vector (verifier side). Table counts are
    /// derived from the public component structure. `hosted` omits the msglink slot.
    fn from_flat(flat: &[SecureField], ctx: &LayoutCtx) -> Self {
        let mut it = flat.iter().copied();
        let mut next = || it.next().expect("claimed sums length mismatch");
        let coeffs = next();
        let private_key = ctx.private_key.then(|| PrivateKeyEvalClaims {
            ntt: private_key_eval::NttClaims {
                butterfly: next(),
                scaling: next(),
            },
            t1: next(),
            fold: SecureField::zero(),
        });
        let coeffs_rc = if ctx.hosted { Vec::new() } else { vec![next()] };
        let decomp = next();
        let decomp_rc = (0..decomp_tables::RcKind::ALL.len())
            .map(|_| next())
            .collect();
        let sib = next();
        let sib_rc = (0..sib_tables::RcKind::ALL.len()).map(|_| next()).collect();
        let msglink = if ctx.hosted {
            SecureField::zero()
        } else {
            next()
        };
        let prefix = next();
        let bridges = (0..ctx.bridge_claims_len()).map(|_| next()).collect();
        let sinks = (0..ctx.sink_claims_len()).map(|_| next()).collect();
        let (private_key, native_use) = match private_key {
            Some(mut private_key) => {
                private_key.fold = next();
                (Some(private_key), SecureField::zero())
            }
            None => (None, next()),
        };
        assert!(it.next().is_none(), "claimed sums length mismatch");
        Self {
            hosted: ctx.hosted,
            coeffs,
            private_key,
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
    /// message bridge are omitted unless `private_key` requires in-circuit µ.
    public_message: bool,
    /// Hosted private-key mode: tr and µ are both service jobs and pk bytes
    /// enter through the host's shared FieldBytes relation.
    private_key: bool,
    message_len: usize,
}

impl LayoutCtx {
    fn new(message_len: usize, hosted: bool, public_message: bool, private_key: bool) -> Self {
        Self {
            hosted,
            public_message,
            private_key,
            message_len,
        }
    }

    fn native_mu(&self) -> bool {
        self.public_message && !self.private_key
    }

    fn bridge_claims_len(&self) -> usize {
        usize::from(!self.public_message) + bridge_lens(self.native_mu(), self.private_key).len()
    }

    fn sink_claims_len(&self) -> usize {
        sink_lens(self.message_len, self.native_mu(), self.private_key).len()
    }
}

fn module_trace_layout(ctx: &LayoutCtx) -> Vec<u32> {
    // Public mode has a folded-identity marker; private-key mode proves the
    // device evaluations and closes the fold without a base column.
    let mut t = if ctx.private_key {
        Vec::new()
    } else {
        vec![LOG_N_LANES]
    };
    // 1. coeffs + 2. unified range table (standalone only).
    t.extend(vec![coeffs_log_size(); coeffs::N_BASE_COLS]);
    if ctx.private_key {
        t.extend(private_key_eval::trace_layout());
    }
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
    // Public prefix: tr‖00‖00, native µ, or private-key mode's 00‖00‖M.
    t.extend(vec![crate::sponge_link::LINK_LOG_SIZE; PREFIX_BASE_COLS]);
    // Private/standalone message bridge.
    if !ctx.public_message {
        t.extend(vec![bridge_log_size(ctx.message_len); BRIDGE_BASE_COLS]);
    }
    for len in bridge_lens(ctx.native_mu(), ctx.private_key) {
        let ls = bridge_log_size(len);
        t.extend(vec![ls; BRIDGE_BASE_COLS]);
    }
    for len in sink_lens(ctx.message_len, ctx.native_mu(), ctx.private_key) {
        let ls = bridge_log_size(len);
        t.extend(vec![ls; SINK_BASE_COLS]);
    }
    t
}

fn module_interaction_layout(ctx: &LayoutCtx) -> Vec<u32> {
    let mut i = Vec::new();
    // 1. coeffs + 2. unified range table (standalone only).
    i.extend(vec![coeffs_log_size(); coeffs::N_INTERACTION_COLS]);
    if ctx.private_key {
        i.extend(private_key_eval::interaction_layout());
    }
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
    // Public prefix: tr‖00‖00, native µ, or private-key mode's 00‖00‖M.
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
    for len in bridge_lens(ctx.native_mu(), ctx.private_key) {
        let ls = bridge_log_size(len);
        i.extend(vec![ls; BRIDGE_INTERACTION_COLS]);
    }
    for len in sink_lens(ctx.message_len, ctx.native_mu(), ctx.private_key) {
        let ls = bridge_log_size(len);
        i.extend(vec![ls; SINK_INTERACTION_COLS]);
    }
    if ctx.private_key {
        i.extend(private_key_eval::fold_interaction_layout());
    }
    i
}

/// The public-prefix producer's interaction column count: one batched
/// accumulator independent of the selected prefix length.
fn prefix_n_interaction() -> usize {
    stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE
}

fn layout_for(ctx: &LayoutCtx) -> TreeLayout {
    TreeLayout {
        preprocessed: all_preprocessed_log_sizes(
            ctx.message_len,
            ctx.hosted,
            ctx.public_message,
            ctx.private_key,
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

#[derive(Debug, PartialEq, Eq)]
struct SpongeOutputs {
    tr: Option<Vec<u8>>,
    mu: Option<Vec<u8>>,
    ct: Vec<u8>,
}

/// Full squeeze outputs for the in-service jobs. Public-message mode computes
/// µ natively and therefore has no µ service output unless the key is private.
fn sponge_outputs(
    witness: &MlDsaWitness,
    input: &MlDsaVerifyInput,
    native_mu: bool,
    private_key: bool,
) -> SpongeOutputs {
    SpongeOutputs {
        tr: private_key.then(|| full_squeeze(&input.encode_pk(), 1)),
        mu: (!native_mu).then(|| full_squeeze(&witness.sponge.mu_absorbed, 1)),
        ct: full_squeeze(&witness.sponge.c_tilde_absorbed, 1),
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
    input: Option<&MlDsaVerifyInput>,
    message: &[u8],
    group_evals: &[SecureField],
    rel: &Relations,
    claims: &Claims,
) -> Built {
    let private_device_evals = ctx.private_key.then(|| {
        PrivateDeviceEvals::try_from_slice(group_evals)
            .expect("private-key group evaluations were shape-checked")
    });
    let public_fold = (!ctx.private_key).then(|| {
        let input = input.expect("public folded identity requires the public key");
        let public_evals = compute_public_evals(input, rel.r, rel.s);
        let public_fold_value = folded_check(
            &public_evals,
            &ClaimedEvals(group_evals),
            rel.rho_rlc,
            rel.r,
            rel.s,
        );
        FrameworkComponent::new(
            allocator,
            PublicFoldEval {
                value: public_fold_value,
            },
            SecureField::zero(),
        )
    });
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
    let private_key = ctx.private_key.then(|| {
        PrivateKeyTraceComponents::new(
            allocator,
            rel.r,
            rel.s,
            rel.private_key
                .clone()
                .expect("private-key relations were drawn"),
            claims
                .private_key
                .as_ref()
                .expect("private-key claims were parsed"),
        )
    });
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
        let input = input.expect("standalone message link requires the public input");
        FrameworkComponent::new(
            allocator,
            MsgLinkEval {
                message: input.message.clone(),
                msglink: rel.msglink.clone(),
            },
            claims.msglink,
        )
    });
    // Public prefix for the selected message/key mode.
    let prefix = FrameworkComponent::new(
        allocator,
        prefix_eval(
            input,
            message,
            stream_base,
            ctx.native_mu(),
            ctx.private_key,
            &rel.keccak.hash_io,
        ),
        claims.prefix,
    );
    let msg = (!ctx.public_message).then(|| {
        FrameworkComponent::new(
            allocator,
            msg_bridge_eval(
                ns,
                message.len(),
                stream_base,
                &rel.msglink,
                rel.shared_field.as_ref(),
                &rel.keccak.hash_io,
            ),
            claims.bridges[0],
        )
    });
    let bridge_claim_offset = usize::from(msg.is_some());
    let bridge_descs = bridge_evals(
        ns,
        stream_base,
        ctx.native_mu(),
        ctx.private_key,
        rel.shared_field.as_ref(),
        &rel.keccak.hash_io,
    );
    let bridges = bridge_descs
        .into_iter()
        .enumerate()
        .map(|(idx, b)| {
            FrameworkComponent::new(allocator, b, claims.bridges[idx + bridge_claim_offset])
        })
        .collect();
    let sink_descs = sink_evals(
        ns,
        message.len(),
        stream_base,
        ctx.native_mu(),
        ctx.private_key,
        &rel.keccak.hash_io,
    );
    let sinks = sink_descs
        .into_iter()
        .enumerate()
        .map(|(idx, s)| FrameworkComponent::new(allocator, s, claims.sinks[idx]))
        .collect();
    let private_fold = ctx.private_key.then(|| {
        private_key_eval::build_fold_component(
            allocator,
            rel.rho_rlc,
            rel.r,
            rel.s,
            rel.private_key
                .clone()
                .expect("private-key relations were drawn"),
            private_device_evals.expect("private-key evaluations were parsed"),
            claims
                .private_key
                .as_ref()
                .expect("private-key claims were parsed")
                .fold,
        )
    });

    Built {
        public_fold,
        coeffs,
        private_key,
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
        private_fold,
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
    /// Shared Keccak-service relations. The service module must draw these
    /// relations before this module uses them.
    keccak_handle: SharedKeccakRelations,
    /// Hosted mode: the proof-wide range relation published by the shared
    /// table provider. Standalone mode draws and provides its own relation.
    shared_range: Option<SharedRangeRelation>,
    /// Instance role and domain tag. It is mixed into the transcript and
    /// prefixes each instance-local preprocessed identifier. An empty value
    /// leaves the identifiers unprefixed.
    /// Use a distinct value for each instance when a proof hosts more than one
    /// ML-DSA module.
    namespace: String,
    /// Per-instance stream-id base (multiples of [`STREAM_BASE_STRIDE`]):
    /// keeps this instance's HashIo stream ids disjoint from every other
    /// instance under the shared relation set. Mixed into the transcript.
    stream_base: u32,
    /// Private-message mode: mix only `message.len()` into the transcript; the
    /// bytes flow exclusively through the host's FieldBytesRelation.
    private_message: bool,
    private_key_bindings: Option<PrivateKeyEvalBindings>,
    private_key_witness: Option<PrivateKeyEvalWitness>,
    private_key_base: Option<PrivateKeyBase>,
    private_device_evals: Option<PrivateDeviceEvals>,
    relations: Option<Relations>,
    // Range-check multiplicity columns stored between trace phases.
    coeffs_rc_mult: Vec<ColEval>,
    coeffs_rc_uses: RcUses,
    decomp_rc_mult: Vec<ColEval>,
    sib_rc_mult: Vec<ColEval>,
    // Bridge byte payloads stored for the interaction phase.
    decomp_w1_bytes: Vec<u8>,
    sponge_outputs: SpongeOutputs,
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
        Self::build(
            witness,
            input,
            shared_field,
            false,
            false,
            None,
            keccak_handle,
        )
    }

    fn build(
        witness: MlDsaWitness,
        mut input: MlDsaVerifyInput,
        shared_field: Option<SharedFieldRelation>,
        public_message: bool,
        private_key: bool,
        shared_range: Option<SharedRangeRelation>,
        keccak_handle: SharedKeccakRelations,
    ) -> Self {
        input.tr = if private_key {
            [0; 64]
        } else {
            native_tr(&input)
        };
        let hosted = shared_field.is_some() || public_message;
        let ctx = LayoutCtx::new(input.message.len(), hosted, public_message, private_key);
        let coeffs_rc_uses = coeffs::gen_coeffs_rc_uses(&witness);
        let sponge_outputs = sponge_outputs(&witness, &input, ctx.native_mu(), private_key);
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
            private_key_bindings: None,
            private_key_witness: None,
            private_key_base: None,
            private_device_evals: None,
            relations: None,
            coeffs_rc_mult: Vec::new(),
            coeffs_rc_uses,
            decomp_rc_mult: Vec::new(),
            sib_rc_mult: Vec::new(),
            decomp_w1_bytes: Vec::new(),
            sponge_outputs,
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
            false,
            Some(shared_range),
            keccak_handle,
        )
    }

    /// Hosted public-message constructor. It recomputes tr and µ
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
            false,
            Some(shared_range),
            keccak_handle,
        )
    }

    /// Hosted public-message constructor for a private device public key.
    ///
    /// The normalized encoded public key is consumed from shared
    /// [`FieldBytesRelation`] field id [`HOSTED_DEVICE_PK_FIELD_ID`], and both
    /// `tr` and µ are constrained as proof-wide Keccak service jobs. The NTT
    /// and packed-`t1` bindings feed the private-key evaluation AIR, so neither
    /// `rho`, `t1`, nor derived `tr` enters [`Air::mix_public`] or the verifier
    /// API.
    pub fn hosted_private_key(
        witness: MlDsaWitness,
        input: MlDsaVerifyInput,
        shared_field: SharedFieldRelation,
        shared_range: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
        bindings: PrivateKeyEvalBindings,
    ) -> Result<Self, PrivateKeyEvalError> {
        validate_device_message_capacity(input.message.len())?;
        let private_key_witness = PrivateKeyEvalWitness::from_input(&input)?;
        let private_key_base = private_key_eval::gen_private_key_base(&private_key_witness);
        let mut prover = Self::build(
            witness,
            input,
            Some(shared_field),
            true,
            true,
            Some(shared_range),
            keccak_handle,
        );
        prover
            .coeffs_rc_uses
            .add_assign(&private_key_base.range_uses);
        prover.private_key_bindings = Some(bindings);
        prover.private_key_witness = Some(private_key_witness);
        prover.private_key_base = Some(private_key_base);
        Ok(prover)
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
    /// to the proof-wide service: optional private-key `tr`, optional private
    /// µ, then c̃ and SIB.
    pub fn keccak_jobs(&self) -> (Vec<Shape>, Vec<Vec<u8>>) {
        let job_shapes = shapes(
            self.input.message.len(),
            self.stream_base,
            self.ctx.native_mu(),
            self.ctx.private_key,
        );
        let shapes: Vec<_> = job_shapes
            .tr
            .into_iter()
            .chain(job_shapes.mu)
            .chain([job_shapes.ct, job_shapes.sib])
            .collect();
        let mut streams = Vec::with_capacity(shapes.len());
        if self.ctx.private_key {
            streams.push(self.input.encode_pk());
        }
        if !self.ctx.native_mu() {
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
        assert!(
            !self.ctx.private_key,
            "hosted private-key mode requires a public message"
        );
        self.private_message = true;
        self
    }

    // ---- getters the host stores in its proof struct + uses to reconstruct ----

    /// Claimed evaluations after proving: 30 in public-key modes, 66 in
    /// private-key mode.
    pub fn group_evals(&self) -> &[SecureField] {
        &self.group_evals
    }
    /// The ordered claimed sums (WITHOUT the msglink slot in hosted mode).
    pub fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.ordered()
    }
    /// Prover-side decoded input. In hosted-private-key mode this is private
    /// witness material and must not be copied into the proof envelope; use
    /// [`Self::private_key_public_input`] for the verifier-visible statement.
    pub fn input(&self) -> &MlDsaVerifyInput {
        &self.input
    }

    /// The verifier-visible statement for private-key mode.
    pub fn private_key_public_input(&self) -> MlDsaPrivateKeyPublicInput {
        assert!(self.ctx.private_key, "not a private-key statement");
        MlDsaPrivateKeyPublicInput {
            message: self.input.message.clone(),
        }
    }
}

/// Byte payloads for the fixed bridges, in [`bridge_evals`] order.
fn bridge_bytes(outputs: &SpongeOutputs, pk_bytes: Option<&[u8]>, w1_bytes: &[u8]) -> Vec<Vec<u8>> {
    let mut bytes = Vec::new();
    if let Some(tr) = &outputs.tr {
        bytes.push(
            pk_bytes
                .expect("private-key bridge requires encoded public-key bytes")
                .to_vec(),
        );
        bytes.push(tr[..64].to_vec());
    }
    if let Some(mu) = &outputs.mu {
        bytes.push(mu[..64].to_vec());
    }
    bytes.extend([w1_bytes.to_vec(), outputs.ct[..48].to_vec()]);
    bytes
}

/// Byte payloads for the remaining sinks: optional `tr`, optional µ, then c̃.
fn sink_bytes(outputs: &SpongeOutputs) -> Vec<Vec<u8>> {
    let mut bytes = Vec::new();
    if let Some(tr) = &outputs.tr {
        bytes.push(tr[64..].to_vec());
    }
    if let Some(mu) = &outputs.mu {
        bytes.push(mu[64..].to_vec());
    }
    bytes.push(outputs.ct[48..].to_vec());
    bytes
}

impl Air for MlDsaProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(
            channel,
            Some(&self.input),
            &self.input.message,
            &self.namespace,
            self.private_message,
            self.ctx.private_key,
            self.stream_base,
        );
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(draw_relations_common(
            channel,
            self.shared_field.as_ref(),
            self.shared_range.as_ref(),
            &self.keccak_handle,
            self.private_key_bindings.as_ref(),
        ));
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.ctx)
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
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        )
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_all_preprocessed(
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        ))
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(
            allocator,
            &self.namespace,
            self.stream_base,
            &self.ctx,
            Some(&self.input),
            &self.input.message,
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
        let base_max = coeffs_log_size()
            .max(decomp_log_size())
            .max(sib_log_size())
            .max(coeffs_tables::range_table_log_size());
        if self.ctx.private_key {
            base_max.max(private_key_eval::NTT_BUTTERFLY_LOG_SIZE)
        } else {
            base_max
        }
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 2
    }
    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_all_preprocessed(
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
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
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        );
        let cols = gen_all_preprocessed(
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
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
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        );
        let cols = gen_all_preprocessed(
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        );
        fingerprint_preprocessed_columns("mldsa_statement", &ids, &cols)
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut evals = if self.ctx.private_key {
            Vec::new()
        } else {
            vec![col_eval(LOG_N_LANES, vec![m31(0); 1usize << LOG_N_LANES])]
        };

        // 1. coeffs base + 2. unified range multiplicity (standalone only).
        let cls = coeffs_log_size();
        evals.extend(coeffs::gen_coeffs_base_trace(&self.witness, cls));
        if self.ctx.private_key {
            evals.extend(
                self.private_key_base
                    .take()
                    .expect("private-key base trace was prepared")
                    .trace,
            );
        }
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
        let decomp_metadata = decomp::gen_decomp_metadata(&self.witness);
        self.decomp_w1_bytes = decomp_metadata.w1_encode_bytes;
        self.decomp_rc_mult = decomp_tables::RcKind::ALL
            .iter()
            .map(|kind| {
                decomp_tables::gen_table_multiplicities(
                    *kind,
                    decomp_metadata.rc_uses.for_kind(*kind),
                )
            })
            .collect();
        evals.extend(self.decomp_rc_mult.clone());

        // 5. sib base + 6. rc mult.
        let sls = sib_log_size();
        evals.extend(sampleinball::gen_sib_base_trace(&self.witness, sls));
        let sib_metadata = sampleinball::gen_sib_metadata(&self.witness);
        self.sib_rc_mult = sib_tables::RcKind::ALL
            .iter()
            .map(|kind| {
                sib_tables::gen_table_multiplicities(*kind, sib_metadata.rc_uses.for_kind(*kind))
            })
            .collect();
        evals.extend(self.sib_rc_mult.clone());

        // 7. msglink (standalone only).
        if !self.ctx.hosted {
            evals.extend(msglink::gen_msglink_base_trace());
        }

        // Public prefix for the selected message/key mode. Base traces run
        // before relations are drawn, so use dummy relation descriptors.
        let dummy_hash_io = HashIoRelation::dummy();
        let dummy_msglink = MsgLinkRelation::dummy();
        evals.extend(
            prefix_eval(
                Some(&self.input),
                &self.input.message,
                self.stream_base,
                self.ctx.native_mu(),
                self.ctx.private_key,
                &dummy_hash_io,
            )
            .gen_base(),
        );

        let outputs = &self.sponge_outputs;
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
        let pk_bytes = self.ctx.private_key.then(|| self.input.encode_pk());
        let dummy_field = self.ctx.private_key.then(FieldBytesRelation::dummy);
        let bbytes = bridge_bytes(outputs, pk_bytes.as_deref(), &self.decomp_w1_bytes);
        let bridge_descs = bridge_evals(
            &self.namespace,
            self.stream_base,
            self.ctx.native_mu(),
            self.ctx.private_key,
            dummy_field.as_ref(),
            &dummy_hash_io,
        );
        for (b, bytes) in bridge_descs.iter().zip(bbytes.iter()) {
            evals.extend(b.gen_base(bytes));
        }

        // Private tr and µ remain in-service witnesses and keep their sanity
        // checks. Native/public µ deliberately has no prover-side equality
        // assertion: disagreement is rejected by the c̃ absorb constraint.
        if let Some(tr) = &outputs.tr {
            assert_eq!(
                tr[..64],
                self.witness.sponge.mu_absorbed[..64],
                "tr squeeze prefix mismatch"
            );
        }
        if let Some(mu) = &outputs.mu {
            assert_eq!(mu[..64], self.witness.sponge.mu_squeezed[..64]);
        }
        assert_eq!(
            outputs.ct[..48],
            self.input.c_tilde[..],
            "c̃ squeeze prefix mismatch"
        );
        let sbytes = sink_bytes(outputs);
        let sink_descs = sink_evals(
            &self.namespace,
            self.input.message.len(),
            self.stream_base,
            self.ctx.native_mu(),
            self.ctx.private_key,
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
        evals.extend(coeffs_int.trace);
        if self.ctx.private_key {
            let private_key = private_key_eval::gen_private_key_interaction(
                self.private_key_witness
                    .as_ref()
                    .expect("private-key witness was prepared"),
                rel.r,
                rel.s,
                rel.private_key
                    .as_ref()
                    .expect("private-key relations were drawn"),
            );
            let private_device_evals = PrivateDeviceEvals::from_parts(
                &coeffs_int.group_evals,
                &private_key.a_evals,
                &private_key.t1_evals,
            )
            .expect("private-key evaluation groups have fixed lengths");
            self.claims.private_key = Some(PrivateKeyEvalClaims {
                ntt: private_key.ntt_claims,
                t1: private_key.t1_claim,
                fold: SecureField::zero(),
            });
            self.group_evals = private_device_evals.clone().into_vec();
            self.private_device_evals = Some(private_device_evals);
            evals.extend(private_key.trace);
        } else {
            self.group_evals = coeffs_int.group_evals;
        }
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
            Some(&self.input),
            &self.input.message,
            self.stream_base,
            self.ctx.native_mu(),
            self.ctx.private_key,
            &rel.keccak.hash_io,
        )
        .gen_interaction();
        self.claims.prefix = prefix_sum;
        evals.extend(prefix_tr);

        let outputs = &self.sponge_outputs;
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
        let pk_bytes = self.ctx.private_key.then(|| self.input.encode_pk());
        let bbytes = bridge_bytes(outputs, pk_bytes.as_deref(), &self.decomp_w1_bytes);
        let bridge_descs = bridge_evals(
            &self.namespace,
            self.stream_base,
            self.ctx.native_mu(),
            self.ctx.private_key,
            rel.shared_field.as_ref(),
            &rel.keccak.hash_io,
        );
        for (b, bytes) in bridge_descs.iter().zip(bbytes.iter()) {
            let (tr, sum) = b.gen_interaction(bytes);
            self.claims.bridges.push(sum);
            evals.extend(tr);
        }

        let sbytes = sink_bytes(outputs);
        let sink_descs = sink_evals(
            &self.namespace,
            self.input.message.len(),
            self.stream_base,
            self.ctx.native_mu(),
            self.ctx.private_key,
            &rel.keccak.hash_io,
        );
        self.claims.sinks.clear();
        for (s, bytes) in sink_descs.iter().zip(sbytes.iter()) {
            let (tr, sum) = s.gen_interaction(bytes);
            self.claims.sinks.push(sum);
            evals.extend(tr);
        }

        if self.ctx.private_key {
            let (fold_trace, fold_sum) = private_key_eval::gen_fold_interaction(
                self.private_device_evals
                    .as_ref()
                    .expect("private-key evaluations were generated"),
                &rel.coeffs.eval,
            );
            self.claims
                .private_key
                .as_mut()
                .expect("private-key claims were generated")
                .fold = fold_sum;
            evals.extend(fold_trace);
        } else {
            // The public native-use term closes the coeff-evaluation lookup.
            self.claims.native_use = crate::proof::native_use_sum(&self.group_evals, &rel.coeffs);
        }

        tb.extend_evals(evals);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built.as_ref().expect("built").ordered_prover()
    }
}

// =============================================================================
// Verifier.
// =============================================================================

enum VerifierStatementInput {
    Public(Box<MlDsaVerifyInput>),
    PrivateKey(MlDsaPrivateKeyPublicInput),
}

impl VerifierStatementInput {
    fn public_key(&self) -> Option<&MlDsaVerifyInput> {
        match self {
            Self::Public(input) => Some(input.as_ref()),
            Self::PrivateKey(_) => None,
        }
    }

    fn message(&self) -> &[u8] {
        match self {
            Self::Public(input) => &input.message,
            Self::PrivateKey(input) => &input.message,
        }
    }
}

pub struct MlDsaVerifier {
    input: VerifierStatementInput,
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
    private_key_bindings: Option<PrivateKeyEvalBindings>,
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

    #[allow(clippy::too_many_arguments)]
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
        let ctx = LayoutCtx::new(input.message.len(), hosted, public_message, false);
        let claims = Claims::from_flat(&claimed_sums, &ctx);
        Self {
            input: VerifierStatementInput::Public(Box::new(input)),
            ctx,
            shared_field,
            keccak_handle,
            shared_range,
            namespace: String::new(),
            stream_base: 0,
            private_message: false,
            private_key_bindings: None,
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

    /// Hosted public-message constructor that mirrors
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

    /// Hosted private-public-key mirror of
    /// [`MlDsaProver::hosted_private_key`].
    pub fn hosted_private_key(
        input: MlDsaPrivateKeyPublicInput,
        group_evals: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        shared_field: SharedFieldRelation,
        shared_range: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
        bindings: PrivateKeyEvalBindings,
    ) -> Result<Self, VerificationError> {
        validate_device_message_capacity(input.message.len()).map_err(|error| {
            VerificationError::InvalidStructure(format!("ML-DSA hosted private key: {error}"))
        })?;
        if group_evals.len() != n_private_key_group_evals() {
            return Err(VerificationError::InvalidStructure(format!(
                "ML-DSA hosted private key: expected {} group evaluations, got {}",
                n_private_key_group_evals(),
                group_evals.len()
            )));
        }
        if claimed_sums.len() != hosted_private_key_claimed_sums_len() {
            return Err(VerificationError::InvalidStructure(format!(
                "ML-DSA hosted private key: expected {} claimed sums, got {}",
                hosted_private_key_claimed_sums_len(),
                claimed_sums.len()
            )));
        }
        PrivateDeviceEvals::try_from_slice(&group_evals).map_err(|error| {
            VerificationError::InvalidStructure(format!("ML-DSA hosted private key: {error}"))
        })?;
        let ctx = LayoutCtx::new(input.message.len(), true, true, true);
        let claims = Claims::from_flat(&claimed_sums, &ctx);
        Ok(Self {
            input: VerifierStatementInput::PrivateKey(input),
            ctx,
            shared_field: Some(shared_field),
            keccak_handle,
            shared_range: Some(shared_range),
            namespace: String::new(),
            stream_base: 0,
            private_message: false,
            private_key_bindings: Some(bindings),
            group_evals,
            claims,
            relations: None,
            built: None,
        })
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
        assert!(
            !self.ctx.private_key,
            "hosted private-key mode requires a public message"
        );
        self.private_message = true;
        self
    }
}

impl Air for MlDsaVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(
            channel,
            self.input.public_key(),
            self.input.message(),
            &self.namespace,
            self.private_message,
            self.ctx.private_key,
            self.stream_base,
        );
    }
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let rel = draw_relations_common(
            channel,
            self.shared_field.as_ref(),
            self.shared_range.as_ref(),
            &self.keccak_handle,
            self.private_key_bindings.as_ref(),
        );
        if !self.ctx.private_key {
            self.claims.native_use = crate::proof::native_use_sum(&self.group_evals, &rel.coeffs);
        }
        self.relations = Some(rel);
    }
    fn layout(&self) -> TreeLayout {
        layout_for(&self.ctx)
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
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        )
    }
    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_all_preprocessed(
            self.ctx.message_len,
            self.ctx.hosted,
            self.ctx.public_message,
            self.ctx.private_key,
        ))
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let rel = self.relations().clone();
        self.built = Some(build_components(
            allocator,
            &self.namespace,
            self.stream_base,
            &self.ctx,
            self.input.public_key(),
            self.input.message(),
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
    let ctx = LayoutCtx::new(input.message.len(), false, false, false);
    layout_for(&ctx)
}

/// Exact committed column layout for hosted public-message/private-public-key
/// mode. Hosts can use this together with
/// [`hosted_private_key_claimed_sums_len`] to validate proof structure before
/// constructing [`MlDsaVerifier`].
pub fn hosted_private_key_layout(message_len: usize) -> TreeLayout {
    try_hosted_private_key_layout(message_len)
        .expect("hosted-private-key message exceeds DEVICE_SIG_STRUCTURE_CAPACITY")
}

/// Checked layout probe for untrusted public request lengths.
pub fn try_hosted_private_key_layout(
    message_len: usize,
) -> Result<TreeLayout, PrivateKeyEvalError> {
    validate_device_message_capacity(message_len)?;
    let ctx = LayoutCtx::new(message_len, true, true, true);
    Ok(layout_for(&ctx))
}

/// Number of coefficient-group evaluations in public-key modes.
pub fn n_group_evals() -> usize {
    coeffs::layout::N_GROUPS
}

/// Number of evaluations in private-key mode: 30 coefficient groups,
/// 30 matrix-polynomial evaluations, and six scaled-`t1` evaluations.
pub fn n_private_key_group_evals() -> usize {
    private_key_eval::PRIVATE_EVAL_COUNT
}

fn claimed_sums_len(hosted: bool, public_message: bool, private_key: bool) -> usize {
    let native_mu = public_message && !private_key;
    1 + usize::from(!hosted) * coeffs_tables::RANGE_TABLE_COMPONENTS
        + 1
        + decomp_tables::RcKind::ALL.len()
        + 1
        + sib_tables::RcKind::ALL.len()
        + usize::from(!hosted)
        + 1 // public prefix for the selected message/key mode
        + usize::from(!public_message)
        + bridge_lens(native_mu, private_key).len()
        + sink_lens(0, native_mu, private_key).len()
        + if private_key {
            // NTT butterfly, NTT scaling, t1, and the final fold replace the
            // public native-use claim.
            4
        } else {
            1
        }
}

/// Exact claimed-sum length for hosted private-message/revocation mode.
pub fn hosted_claimed_sums_len() -> usize {
    claimed_sums_len(true, false, false)
}

/// Exact claimed-sum length for hosted-public issuer/device native-µ mode.
pub fn hosted_public_claimed_sums_len() -> usize {
    claimed_sums_len(true, true, false)
}

/// Exact claimed-sum length for hosted public-message/private-public-key mode.
pub fn hosted_private_key_claimed_sums_len() -> usize {
    claimed_sums_len(true, true, true)
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
        || proof.claimed_sums.len() != claimed_sums_len(false, false, false)
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

#[cfg(test)]
mod tests {
    use ml_dsa::signature::{Keypair, Signer};
    use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};

    use super::*;
    use crate::reference::encoding::{pk_decode, sig_decode};
    use crate::reference::sponge::shake256;
    use crate::witness::generate_witness;

    fn witness_and_input() -> (MlDsaWitness, MlDsaVerifyInput) {
        let signing_key = SigningKey::<MlDsa65>::from_seed(&[0x53; 32].into());
        let verifying_key = signing_key.verifying_key();
        let message = b"cached-sponge-outputs".to_vec();
        let signature = signing_key.sign(&message);
        let pk: EncodedVerifyingKey<MlDsa65> = verifying_key.encode();
        let signature: EncodedSignature<MlDsa65> = signature.encode();
        let decoded_pk = pk_decode(pk.as_slice()).expect("pk_decode");
        let decoded_signature = sig_decode(signature.as_slice()).expect("sig_decode");
        let (tr, _) = shake256(&[pk.as_slice()], 64);
        let mut tr_array = [0u8; 64];
        tr_array.copy_from_slice(&tr);
        let input =
            MlDsaVerifyInput::from_decoded(&decoded_pk, &decoded_signature, tr_array, message);
        let witness = generate_witness(&input).expect("witness");
        (witness, input)
    }

    #[test]
    fn prover_cache_equals_fresh_sponge_outputs_in_both_message_modes() {
        let (witness, input) = witness_and_input();
        let expected_private = sponge_outputs(&witness, &input, false, false);
        let private = MlDsaProver::new(
            witness.clone(),
            input.clone(),
            None,
            SharedKeccakRelations::new(),
        );
        assert_eq!(private.sponge_outputs, expected_private);

        let expected_public = sponge_outputs(&witness, &input, true, false);
        let public = MlDsaProver::hosted_public(
            witness,
            input,
            SharedRangeRelation::new(),
            SharedKeccakRelations::new(),
        );
        assert_eq!(public.sponge_outputs, expected_public);
    }
}
