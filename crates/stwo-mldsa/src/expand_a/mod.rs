//! Fixed-shape AIR for FIPS 204 `ExpandA(rho)` rejection sampling.
//!
//! Each active matrix polynomial has one SHAKE-128 job. Each job absorbs
//! `rho || j || i`, uses a fixed six-block squeeze budget, and yields exactly
//! 256 accepted stage-zero NTT cells.
//! The fixed schedule is verifier-derived; candidate counts are private FSM
//! state and never enter the proof claim or preprocessed shape.

use std::fmt;

use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::P as M31_MODULUS;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator, ORIGINAL_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, m31, padded_log_size, ColEval};
use crate::binding::{
    HashIoRelation, NttCellRelation, RhoCellRelation, SharedNttCellRelation, SharedRhoCellRelation,
};
use crate::coeffs::relations::{RangeRelation, SharedRangeRelation};
use crate::coeffs::tables::RcKind;
use crate::coeffs::RcUses;
use crate::constants::{K, L, N, Q};
use crate::profile::MlDsaProfile;
use crate::sponge_link::ns_prefix;
use stwo_keccak::relations::SharedKeccakRelations;
use stwo_keccak::sponge::Shape;

/// Number of matrix polynomials (`k · l`, maximum shape).
pub const MATRIX_POLYS: usize = K * L;
/// SHAKE-128 rate in bytes.
pub const SHAKE128_RATE: usize = 168;
/// Rejection candidates per rate block: three bytes per candidate.
pub const CANDIDATES_PER_BLOCK: usize = SHAKE128_RATE / 3;
/// Fixed fail-closed resource cap.
///
/// Five blocks overflow across the maximum 30 streams with probability at most
/// `2^-127.485`, just above the proof-wide `2^-128` rail. Six blocks reduce
/// that union bound to `2^-542.030`.
pub const MAX_EXPAND_A_SQUEEZE_BLOCKS: usize = 6;
/// Fixed squeeze budget in bytes (six rate blocks).
pub const MAX_EXPAND_A_SQUEEZE_BYTES: usize = SHAKE128_RATE * MAX_EXPAND_A_SQUEEZE_BLOCKS;
/// Fixed candidate budget: `56 · 6 = 336` candidates per polynomial.
pub const MAX_CANDIDATES: usize = CANDIDATES_PER_BLOCK * MAX_EXPAND_A_SQUEEZE_BLOCKS;

/// First ExpandA stream id above the caller's `stream_base`.
pub const EXPAND_STREAM_OFFSET: u32 = 16;
/// Stream-id stride between consecutive polynomials (absorb id, then absorb
/// id + 1 = squeeze id).
pub const EXPAND_STREAM_STRIDE: u32 = 2;
const INVERSE_EXPAND_STREAM_STRIDE: u32 = (M31_MODULUS + 1) / EXPAND_STREAM_STRIDE;
/// Stream-id spacing the caller must leave between consecutive instances.
pub const REQUIRED_STREAM_STRIDE: u32 = 128;
const LAST_EXPAND_STREAM_OFFSET: u32 =
    EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * (MATRIX_POLYS as u32 - 1) + 1;
/// Largest field-safe `stream_base`: every derived stream id stays `< P`.
pub const MAX_EXPAND_STREAM_BASE: u32 = M31_MODULUS - 1 - LAST_EXPAND_STREAM_OFFSET;

/// Absorb active rows: 34 bytes per matrix polynomial.
pub const ABSORB_ACTIVE_ROWS: usize = MATRIX_POLYS * 34;
/// Absorb trace log size.
pub const ABSORB_LOG_SIZE: u32 = 10;
/// Rejection active rows: `MAX_CANDIDATES` per matrix polynomial.
pub const REJECTION_ACTIVE_ROWS: usize = MATRIX_POLYS * MAX_CANDIDATES;
/// Rejection trace log size.
pub const REJECTION_LOG_SIZE: u32 = 14;

fn absorb_active_rows(profile: MlDsaProfile) -> usize {
    profile.matrix_polys() * 34
}

fn absorb_log_size(profile: MlDsaProfile) -> u32 {
    padded_log_size(absorb_active_rows(profile))
}

fn rejection_active_rows(profile: MlDsaProfile) -> usize {
    profile.matrix_polys() * MAX_CANDIDATES
}

fn rejection_log_size(profile: MlDsaProfile) -> u32 {
    padded_log_size(rejection_active_rows(profile))
}

const LOGUP_BATCH: usize = 4;
const EXPAND_A_MIX_TAG: u64 = 0x4d4c_4453_4145_5850;

const ABSORB_PRE_NAMES: [&str; 6] = [
    "byte_pos",
    "absorb_stream",
    "rho_first",
    "rho_copy",
    "domain_gate",
    "domain_byte",
];

const REJECTION_PRE_NAMES: [&str; 5] = ["active", "first", "last", "byte_pos", "squeeze_stream"];

const COL_B0: usize = 0;
const COL_B1: usize = 1;
const COL_B2: usize = 2;
const COL_LOW7: usize = 3;
const COL_SAMPLE: usize = 4;
const COL_ACCEPT: usize = 5;
const COL_INDEX: usize = 6;
const COL_ACCEPT_SLACK0: usize = 7;
const COL_ACCEPT_SLACK1: usize = 8;
const COL_ACCEPT_SLACK2: usize = 9;
const COL_REJECT_DELTA: usize = 10;
/// C7b: `b1`'s 4+4-bit split (`b1 = lo4 + 16·hi4`), gated by `accept`.
/// Re-limbs the NTT cell yield from the 8/8/7-bit byte split (`b0,b1,low7`)
/// to the 12/11-bit split (`a0 = b0+256·lo4`, `a1 = hi4+16·low7`) ntt.rs now
/// uses, via OPTION (ii): no new canonicity slack, since `value < Q` is
/// already enforced in byte form.
const COL_LO4: usize = 11;
const COL_HI4: usize = 12;

/// Absorb base-column count (the absorbed byte).
pub const ABSORB_BASE_COLS: usize = 1;
/// Rejection base-column count.
pub const REJECTION_BASE_COLS: usize = 13;
/// Absorb LogUp entries per row (HashIo yield, rho-cell yield on poly 0).
pub const ABSORB_LOGUP_ENTRIES: usize = 2;
/// Rejection LogUp entries per row: 3 HashIo consumes + 8 range uses + 1 NTT
/// cell yield.
pub const REJECTION_LOGUP_ENTRIES: usize = 12;
/// Absorb interaction columns (one batched fraction).
pub const ABSORB_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;
/// Rejection interaction columns: batched LogUp (batch 4).
pub const REJECTION_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * REJECTION_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

#[doc(hidden)]
pub const TRACE_COL_B0: usize = COL_B0;
#[doc(hidden)]
pub const TRACE_COL_B1: usize = COL_B1;
#[doc(hidden)]
pub const TRACE_COL_B2: usize = COL_B2;
#[doc(hidden)]
pub const TRACE_COL_LOW7: usize = COL_LOW7;
#[doc(hidden)]
pub const TRACE_COL_SAMPLE: usize = COL_SAMPLE;
#[doc(hidden)]
pub const TRACE_COL_ACCEPT: usize = COL_ACCEPT;
#[doc(hidden)]
pub const TRACE_COL_INDEX: usize = COL_INDEX;
#[doc(hidden)]
pub const TRACE_COL_ACCEPT_SLACK0: usize = COL_ACCEPT_SLACK0;
#[doc(hidden)]
pub const TRACE_COL_ACCEPT_SLACK1: usize = COL_ACCEPT_SLACK1;
#[doc(hidden)]
pub const TRACE_COL_ACCEPT_SLACK2: usize = COL_ACCEPT_SLACK2;
#[doc(hidden)]
pub const TRACE_COL_REJECT_DELTA: usize = COL_REJECT_DELTA;

const _: () = assert!(ABSORB_ACTIVE_ROWS <= 1 << ABSORB_LOG_SIZE);
const _: () = assert!(REJECTION_ACTIVE_ROWS <= 1 << REJECTION_LOG_SIZE);
const _: () = assert!(LAST_EXPAND_STREAM_OFFSET < REQUIRED_STREAM_STRIDE);

/// Canonical block-aligned rejection prefixes for one `rho`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpandAWitness {
    /// The verifier-selected parameter set.
    pub profile: MlDsaProfile,
    /// The 32-byte matrix seed `rho`.
    pub rho: [u8; 32],
    /// One canonical block-aligned squeeze prefix per matrix polynomial.
    pub squeeze_streams: Vec<Vec<u8>>,
}

/// Fail-closed witness and fixed-resource validation errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpandAError {
    /// The witness holds the wrong number of squeeze streams.
    StreamCount {
        /// Expected stream count (`matrix_polys`).
        expected: usize,
        /// Actual stream count.
        actual: usize,
    },
    /// A squeeze stream is empty.
    EmptyStream {
        /// Offending polynomial index.
        poly: usize,
    },
    /// A squeeze stream length is not a multiple of the SHAKE-128 rate.
    StreamNotBlockAligned {
        /// Offending polynomial index.
        poly: usize,
        /// Offending stream length in bytes.
        len: usize,
    },
    /// A squeeze stream exceeds the six-block cap.
    StreamExceedsCap {
        /// Offending polynomial index.
        poly: usize,
        /// Offending stream length in bytes.
        len: usize,
    },
    /// Six blocks did not yield 256 accepted candidates.
    SqueezeCapExceeded {
        /// Offending polynomial index.
        poly: usize,
    },
    /// A squeeze stream is not the canonical block-aligned prefix.
    NonCanonicalLength {
        /// Offending polynomial index.
        poly: usize,
        /// Canonical length in bytes.
        expected: usize,
        /// Actual length in bytes.
        actual: usize,
    },
    /// A squeeze stream differs from canonical SHAKE-128 output.
    StreamMismatch {
        /// Offending polynomial index.
        poly: usize,
    },
    /// The stream base exceeds the field-safe maximum.
    InvalidStreamBase {
        /// Offending stream base.
        stream_base: u32,
        /// Maximum field-safe base (`MAX_EXPAND_STREAM_BASE`).
        max: u32,
    },
    /// A polynomial index is outside the profile's active range.
    PolynomialOutOfRange {
        /// Offending polynomial index.
        poly: usize,
    },
}

impl fmt::Display for ExpandAError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StreamCount { expected, actual } => {
                write!(f, "expected {expected} ExpandA streams, got {actual}")
            }
            Self::EmptyStream { poly } => write!(f, "ExpandA stream {poly} is empty"),
            Self::StreamNotBlockAligned { poly, len } => {
                write!(f, "ExpandA stream {poly} length {len} is not block aligned")
            }
            Self::StreamExceedsCap { poly, len } => {
                write!(
                    f,
                    "ExpandA stream {poly} length {len} exceeds the six-block cap"
                )
            }
            Self::SqueezeCapExceeded { poly } => {
                write!(
                    f,
                    "ExpandA stream {poly} has fewer than 256 accepts in six blocks"
                )
            }
            Self::NonCanonicalLength {
                poly,
                expected,
                actual,
            } => write!(
                f,
                "ExpandA stream {poly} has noncanonical length {actual}, expected {expected}"
            ),
            Self::StreamMismatch { poly } => {
                write!(
                    f,
                    "ExpandA stream {poly} does not match canonical SHAKE-128"
                )
            }
            Self::InvalidStreamBase { stream_base, max } => {
                write!(
                    f,
                    "ExpandA stream base {stream_base} exceeds the maximum field-safe base {max}"
                )
            }
            Self::PolynomialOutOfRange { poly } => {
                write!(
                    f,
                    "ExpandA polynomial index {poly} is outside 0..{MATRIX_POLYS}"
                )
            }
        }
    }
}

impl std::error::Error for ExpandAError {}

/// Shared output handles drawn and published by this module.
#[derive(Clone)]
pub struct ExpandABindings {
    /// Shared `rho`-cell handle this module publishes.
    pub rho: SharedRhoCellRelation,
    /// Shared NTT-cell handle this module publishes.
    pub ntt: SharedNttCellRelation,
}

impl ExpandABindings {
    /// Create both shared handles (undrawn).
    pub fn new() -> Self {
        Self {
            rho: SharedRhoCellRelation::new(),
            ntt: SharedNttCellRelation::new(),
        }
    }
}

impl Default for ExpandABindings {
    fn default() -> Self {
        Self::new()
    }
}

/// The public proof claim for private `ExpandA`. Both log sizes are constants.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpandAClaim {
    /// LogUp claimed sum of the absorb component.
    pub absorb_claimed_sum: SecureField,
    /// LogUp claimed sum of the rejection component.
    pub rejection_claimed_sum: SecureField,
}

/// Fixed preprocessing stack containing the attacked cell.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandAPreprocessedComponent {
    /// The absorb component's preprocessed stack.
    Absorb,
    /// The rejection component's preprocessed stack.
    Rejection,
}

/// Test-only mutation of one logical base-trace or preprocessing cell.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandATraceAttack {
    /// Overwrite one absorb base-trace cell.
    Absorb {
        /// Attacked row.
        row: usize,
        /// Injected value.
        value: u32,
    },
    /// Overwrite one rejection base-trace cell.
    Rejection {
        /// Attacked row.
        row: usize,
        /// Attacked column.
        column: usize,
        /// Injected value.
        value: u32,
    },
    /// Overwrite one preprocessed cell.
    Preprocessed {
        /// Attacked component's preprocessed stack.
        component: ExpandAPreprocessedComponent,
        /// Attacked row.
        row: usize,
        /// Attacked column.
        column: usize,
        /// Injected value.
        value: u32,
    },
}

/// The relations the ExpandA components draw on.
#[derive(Clone)]
pub struct ExpandARelations {
    /// Keccak byte-I/O relation for the absorb and squeeze streams.
    pub hash_io: HashIoRelation,
    /// Proof-wide range relation.
    pub range: RangeRelation,
    /// Private `rho` cell relation.
    pub rho: RhoCellRelation,
    /// Stage-zero NTT cell relation.
    pub ntt: NttCellRelation,
}

impl ExpandARelations {
    /// Dummy relations for sizing tests.
    pub fn dummy() -> Self {
        Self {
            hash_io: HashIoRelation::dummy(),
            range: RangeRelation::dummy(),
            rho: RhoCellRelation::dummy(),
            ntt: NttCellRelation::dummy(),
        }
    }
}

/// Reject a `stream_base` whose derived stream ids would wrap the M31 field.
pub fn validate_stream_base(stream_base: u32) -> Result<(), ExpandAError> {
    if stream_base > MAX_EXPAND_STREAM_BASE {
        return Err(ExpandAError::InvalidStreamBase {
            stream_base,
            max: MAX_EXPAND_STREAM_BASE,
        });
    }
    Ok(())
}

fn validate_poly(profile: MlDsaProfile, poly: usize) -> Result<u32, ExpandAError> {
    if poly >= profile.matrix_polys() {
        return Err(ExpandAError::PolynomialOutOfRange { poly });
    }
    Ok(poly as u32)
}

/// Absorb stream id for one matrix polynomial: `stream_base + 16 + 2·poly`.
pub fn absorb_stream_id(
    profile: MlDsaProfile,
    stream_base: u32,
    poly: usize,
) -> Result<u32, ExpandAError> {
    validate_stream_base(stream_base)?;
    let poly = validate_poly(profile, poly)?;
    Ok(stream_base + EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly)
}

/// Squeeze stream id for one matrix polynomial: the absorb id + 1.
pub fn squeeze_stream_id(
    profile: MlDsaProfile,
    stream_base: u32,
    poly: usize,
) -> Result<u32, ExpandAError> {
    Ok(absorb_stream_id(profile, stream_base, poly)? + 1)
}

fn validated_absorb_stream_id(stream_base: u32, poly: usize) -> u32 {
    stream_base + EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32
}

fn validated_squeeze_stream_id(stream_base: u32, poly: usize) -> u32 {
    validated_absorb_stream_id(stream_base, poly) + 1
}

fn absorb_input(profile: MlDsaProfile, rho: &[u8; 32], poly: usize) -> [u8; 34] {
    let mut input = [0u8; 34];
    input[..32].copy_from_slice(rho);
    input[32] = (poly % profile.l()) as u8;
    input[33] = (poly / profile.l()) as u8;
    input
}

fn fixed_squeeze_stream(profile: MlDsaProfile, rho: &[u8; 32], poly: usize) -> Vec<u8> {
    let input = absorb_input(profile, rho, poly);
    crate::reference::sponge::shake128(&[&input], MAX_EXPAND_A_SQUEEZE_BYTES).0
}

fn candidate(bytes: &[u8]) -> u32 {
    bytes[0] as u32 | (bytes[1] as u32) << 8 | ((bytes[2] as u32 & 0x7f) << 16)
}

fn consumed_candidates(stream: &[u8]) -> Option<usize> {
    let mut accepted = 0usize;
    for (index, bytes) in stream.chunks_exact(3).enumerate() {
        if candidate(bytes) < Q {
            accepted += 1;
            if accepted == N {
                return Some(index + 1);
            }
        }
    }
    None
}

fn require_consumed_candidates(stream: &[u8], poly: usize) -> Result<usize, ExpandAError> {
    consumed_candidates(stream).ok_or(ExpandAError::SqueezeCapExceeded { poly })
}

fn canonical_stream_from_full(
    full: Vec<u8>,
    poly: usize,
) -> Result<(Vec<u8>, usize), ExpandAError> {
    let consumed = require_consumed_candidates(&full, poly)?;
    let len = SHAKE128_RATE * consumed.div_ceil(CANDIDATES_PER_BLOCK);
    let prefix = full
        .get(..len)
        .ok_or(ExpandAError::SqueezeCapExceeded { poly })?;
    Ok((prefix.to_vec(), consumed))
}

fn canonical_stream(
    profile: MlDsaProfile,
    rho: &[u8; 32],
    poly: usize,
) -> Result<(Vec<u8>, usize), ExpandAError> {
    canonical_stream_from_full(fixed_squeeze_stream(profile, rho, poly), poly)
}

/// Construct the canonical block-aligned witness for the selected profile.
pub fn derive_expand_a_witness(
    profile: MlDsaProfile,
    rho: [u8; 32],
) -> Result<ExpandAWitness, ExpandAError> {
    let mut squeeze_streams = Vec::with_capacity(profile.matrix_polys());
    for poly in 0..profile.matrix_polys() {
        squeeze_streams.push(canonical_stream(profile, &rho, poly)?.0);
    }
    Ok(ExpandAWitness {
        profile,
        rho,
        squeeze_streams,
    })
}

/// Validate all stored on-demand prefixes and return their consumed-candidate counts.
fn validate_stream_with(
    witness: &ExpandAWitness,
    mut full_stream: impl FnMut(MlDsaProfile, &[u8; 32], usize) -> Vec<u8>,
) -> Result<Vec<usize>, ExpandAError> {
    let expected_streams = witness.profile.matrix_polys();
    if witness.squeeze_streams.len() != expected_streams {
        return Err(ExpandAError::StreamCount {
            expected: expected_streams,
            actual: witness.squeeze_streams.len(),
        });
    }
    let mut counts = vec![0usize; expected_streams];
    for (poly, stream) in witness.squeeze_streams.iter().enumerate() {
        if stream.is_empty() {
            return Err(ExpandAError::EmptyStream { poly });
        }
        if !stream.len().is_multiple_of(SHAKE128_RATE) {
            return Err(ExpandAError::StreamNotBlockAligned {
                poly,
                len: stream.len(),
            });
        }
        if stream.len() > MAX_EXPAND_A_SQUEEZE_BYTES {
            return Err(ExpandAError::StreamExceedsCap {
                poly,
                len: stream.len(),
            });
        }
        let (expected, consumed) =
            canonical_stream_from_full(full_stream(witness.profile, &witness.rho, poly), poly)?;
        if stream.len() != expected.len() {
            return Err(ExpandAError::NonCanonicalLength {
                poly,
                expected: expected.len(),
                actual: stream.len(),
            });
        }
        if stream != &expected {
            return Err(ExpandAError::StreamMismatch { poly });
        }
        counts[poly] = consumed;
    }
    Ok(counts)
}

/// Validate all stored prefixes against canonical SHAKE-128 and return their
/// consumed-candidate counts.
pub fn validate_stream(witness: &ExpandAWitness) -> Result<Vec<usize>, ExpandAError> {
    validate_stream_with(witness, fixed_squeeze_stream)
}

/// Public fixed service shapes in exact row-major matrix order.
pub fn shake128_job_shapes(
    profile: MlDsaProfile,
    stream_base: u32,
) -> Result<Vec<Shape>, ExpandAError> {
    validate_stream_base(stream_base)?;
    (0..profile.matrix_polys())
        .map(|poly| {
            Ok(Shape::shake128(
                34,
                MAX_EXPAND_A_SQUEEZE_BLOCKS,
                absorb_stream_id(profile, stream_base, poly)?,
                squeeze_stream_id(profile, stream_base, poly)?,
            ))
        })
        .collect()
}

/// Witness absorb messages paired positionally with [`shake128_job_shapes`].
pub fn shake128_absorb_streams(profile: MlDsaProfile, rho: &[u8; 32]) -> Vec<Vec<u8>> {
    (0..profile.matrix_polys())
        .map(|poly| absorb_input(profile, rho, poly).to_vec())
        .collect()
}

fn pre_id(ns: &str, component: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{}mldsa_expand_a_{component}_{name}", ns_prefix(ns)),
    }
}

fn absorb_preprocessed_ids(ns: &str) -> Vec<PreProcessedColumnId> {
    ABSORB_PRE_NAMES
        .iter()
        .map(|name| pre_id(ns, "absorb", name))
        .collect()
}

fn rejection_preprocessed_ids(ns: &str) -> Vec<PreProcessedColumnId> {
    REJECTION_PRE_NAMES
        .iter()
        .map(|name| pre_id(ns, "rejection", name))
        .collect()
}

/// Preprocessed ids for both components (absorb then rejection), in commit
/// order.
pub fn expand_a_preprocessed_ids(ns: &str) -> Vec<PreProcessedColumnId> {
    let mut ids = absorb_preprocessed_ids(ns);
    ids.extend(rejection_preprocessed_ids(ns));
    ids
}

fn gen_absorb_preprocessed(
    profile: MlDsaProfile,
    ns: &str,
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let log_size = absorb_log_size(profile);
    let rows = 1usize << log_size;
    let mut columns = vec![vec![m31(0); rows]; ABSORB_PRE_NAMES.len()];
    let matrix_polys = profile.matrix_polys();
    for pos in 0..34 {
        for poly in 0..matrix_polys {
            let row = pos * matrix_polys + poly;
            columns[0][row] = m31(pos as u32);
            columns[1][row] = m31(EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32);
            columns[2][row] = m31((pos < 32 && poly == 0) as u32);
            columns[3][row] = m31((pos < 32 && poly > 0) as u32);
            columns[4][row] = m31((pos >= 32) as u32);
            columns[5][row] = m31(match pos {
                32 => (poly % profile.l()) as u32,
                33 => (poly / profile.l()) as u32,
                _ => 0,
            });
        }
    }
    if let Some(ExpandATraceAttack::Preprocessed {
        component: ExpandAPreprocessedComponent::Absorb,
        row,
        column,
        value,
    }) = attack
    {
        columns[column][row] = m31(value);
    }
    let _ = ns;
    columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect()
}

fn gen_rejection_preprocessed(
    profile: MlDsaProfile,
    ns: &str,
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let log_size = rejection_log_size(profile);
    let rows = 1usize << log_size;
    let mut columns = vec![vec![m31(0); rows]; REJECTION_PRE_NAMES.len()];
    for poly in 0..profile.matrix_polys() {
        for candidate in 0..MAX_CANDIDATES {
            let row = poly * MAX_CANDIDATES + candidate;
            columns[0][row] = m31(1);
            columns[1][row] = m31((candidate == 0) as u32);
            columns[2][row] = m31((candidate + 1 == MAX_CANDIDATES) as u32);
            columns[3][row] = m31((3 * candidate) as u32);
            columns[4][row] = m31(EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32 + 1);
        }
    }
    if let Some(ExpandATraceAttack::Preprocessed {
        component: ExpandAPreprocessedComponent::Rejection,
        row,
        column,
        value,
    }) = attack
    {
        columns[column][row] = m31(value);
    }
    let _ = ns;
    columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect()
}

/// Generate the absorb and rejection preprocessed columns for the selected
/// profile.
pub fn gen_expand_a_preprocessed(profile: MlDsaProfile, ns: &str) -> Vec<ColEval> {
    gen_expand_a_preprocessed_with_attack(profile, ns, None)
}

fn gen_expand_a_preprocessed_with_attack(
    profile: MlDsaProfile,
    ns: &str,
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let mut columns = gen_absorb_preprocessed(profile, ns, attack);
    columns.extend(gen_rejection_preprocessed(profile, ns, attack));
    columns
}

#[derive(Clone, Copy)]
struct RejectionRow {
    bytes: [u32; 3],
    low7: u32,
    /// C7b: `b1`'s low/high nibble (`b1 = lo4 + 16·hi4`).
    lo4: u32,
    hi4: u32,
    sample: bool,
    accept: bool,
    index: u32,
    accept_slack: [u32; 3],
    reject_delta: u32,
}

fn split_u23(value: u32) -> [u32; 3] {
    [value & 0xff, (value >> 8) & 0xff, value >> 16]
}

fn build_rejection_rows(witness: &ExpandAWitness) -> Vec<RejectionRow> {
    let mut rows = Vec::with_capacity(rejection_active_rows(witness.profile));
    for poly in 0..witness.profile.matrix_polys() {
        let stream = fixed_squeeze_stream(witness.profile, &witness.rho, poly);
        let mut index = 0u32;
        for candidate_index in 0..MAX_CANDIDATES {
            let offset = 3 * candidate_index;
            let bytes = [
                stream[offset] as u32,
                stream[offset + 1] as u32,
                stream[offset + 2] as u32,
            ];
            let low7 = bytes[2] & 0x7f;
            let value = bytes[0] | bytes[1] << 8 | low7 << 16;
            let lo4 = bytes[1] & 0xf;
            let hi4 = bytes[1] >> 4;
            let sample = index < N as u32;
            let accept = sample && value < Q;
            let accept_slack = if accept {
                split_u23(Q - 1 - value)
            } else {
                [0; 3]
            };
            let reject_delta = if sample && !accept { value - Q } else { 0 };
            rows.push(RejectionRow {
                bytes,
                low7,
                lo4,
                hi4,
                sample,
                accept,
                index,
                accept_slack,
                reject_delta,
            });
            index += u32::from(accept);
        }
        assert_eq!(index, N as u32, "validated six-block ExpandA stream");
    }
    rows
}

fn rejection_range_uses(rows: &[RejectionRow]) -> RcUses {
    let mut uses = RcUses::new();
    for row in rows {
        uses.record(RcKind::Rc7, row.low7);
        if row.sample {
            uses.record(RcKind::Rc8, 255 - row.index);
        }
        if row.accept {
            uses.record(RcKind::Rc8, row.accept_slack[0]);
            uses.record(RcKind::Rc8, row.accept_slack[1]);
            uses.record(RcKind::Rc7, row.accept_slack[2]);
            // C7b: lo4/hi4 only need to be range-valid for accepted rows
            // (they feed the accept-gated NTT yield's 12/11-bit limbs);
            // mirrors accept_slack's accept-gated lookup pattern.
            uses.record(RcKind::Rc4, row.lo4);
            uses.record(RcKind::Rc4, row.hi4);
        } else if row.sample {
            uses.record(RcKind::Rc13, row.reject_delta);
        }
    }
    uses
}

fn gen_absorb_base_trace(
    witness: &ExpandAWitness,
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let log_size = absorb_log_size(witness.profile);
    let matrix_polys = witness.profile.matrix_polys();
    let mut byte = vec![m31(0); 1usize << log_size];
    for pos in 0..34 {
        for poly in 0..matrix_polys {
            byte[pos * matrix_polys + poly] =
                m31(absorb_input(witness.profile, &witness.rho, poly)[pos] as u32);
        }
    }
    if let Some(ExpandATraceAttack::Absorb { row, value }) = attack {
        byte[row] = m31(value);
    }
    vec![col_eval(log_size, byte)]
}

fn gen_rejection_base_trace(
    profile: MlDsaProfile,
    rows: &[RejectionRow],
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let log_size = rejection_log_size(profile);
    let n_rows = 1usize << log_size;
    let mut columns = vec![vec![m31(0); n_rows]; REJECTION_BASE_COLS];
    for (row, value) in rows.iter().enumerate() {
        columns[COL_B0][row] = m31(value.bytes[0]);
        columns[COL_B1][row] = m31(value.bytes[1]);
        columns[COL_B2][row] = m31(value.bytes[2]);
        columns[COL_LOW7][row] = m31(value.low7);
        columns[COL_SAMPLE][row] = m31(value.sample as u32);
        columns[COL_ACCEPT][row] = m31(value.accept as u32);
        columns[COL_INDEX][row] = m31(value.index);
        columns[COL_ACCEPT_SLACK0][row] = m31(value.accept_slack[0]);
        columns[COL_ACCEPT_SLACK1][row] = m31(value.accept_slack[1]);
        columns[COL_ACCEPT_SLACK2][row] = m31(value.accept_slack[2]);
        columns[COL_REJECT_DELTA][row] = m31(value.reject_delta);
        columns[COL_LO4][row] = m31(value.lo4);
        columns[COL_HI4][row] = m31(value.hi4);
    }
    if let Some(ExpandATraceAttack::Rejection { row, column, value }) = attack {
        columns[column][row] = m31(value);
    }
    columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect()
}

fn range_tuple<E: EvalAtRow>(value: E::F, kind: RcKind) -> [E::F; 2] {
    [value, E::F::from(m31(kind.bound_id()))]
}

#[derive(Clone)]
struct AbsorbEval {
    profile: MlDsaProfile,
    ns: String,
    stream_base: u32,
    relations: ExpandARelations,
}

impl FrameworkEval for AbsorbEval {
    fn log_size(&self) -> u32 {
        absorb_log_size(self.profile)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = |name: &str| pre_id(&self.ns, "absorb", name);
        let byte_pos = eval.get_preprocessed_column(id("byte_pos"));
        let absorb_stream = eval.get_preprocessed_column(id("absorb_stream"));
        let rho_first = eval.get_preprocessed_column(id("rho_first"));
        let rho_copy = eval.get_preprocessed_column(id("rho_copy"));
        let domain_gate = eval.get_preprocessed_column(id("domain_gate"));
        let domain_byte = eval.get_preprocessed_column(id("domain_byte"));
        let active = rho_first.clone() + rho_copy.clone() + domain_gate.clone();

        let byte_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
        let byte_prev = byte_mask[0].clone();
        let byte = byte_mask[1].clone();
        let one = E::F::one();

        eval.add_constraint(rho_copy * (byte.clone() - byte_prev));
        eval.add_constraint(domain_gate * (byte.clone() - domain_byte));
        eval.add_constraint((one - active.clone()) * byte.clone());

        eval.add_to_relation(RelationEntry::base(
            &self.relations.hash_io,
            active,
            &[
                E::F::from(m31(self.stream_base)) + absorb_stream,
                byte_pos.clone(),
                byte.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rho,
            rho_first,
            &[byte_pos, byte],
        ));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

#[derive(Clone)]
struct RejectionEval {
    profile: MlDsaProfile,
    ns: String,
    stream_base: u32,
    relations: ExpandARelations,
}

impl FrameworkEval for RejectionEval {
    fn log_size(&self) -> u32 {
        rejection_log_size(self.profile)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = |name: &str| pre_id(&self.ns, "rejection", name);
        let active = eval.get_preprocessed_column(id("active"));
        let first = eval.get_preprocessed_column(id("first"));
        let last = eval.get_preprocessed_column(id("last"));
        let byte_pos = eval.get_preprocessed_column(id("byte_pos"));
        let squeeze_stream = eval.get_preprocessed_column(id("squeeze_stream"));
        let not_first = active.clone() - first.clone();
        let poly = (squeeze_stream.clone() - E::F::from(m31(EXPAND_STREAM_OFFSET + 1)))
            * E::F::from(m31(INVERSE_EXPAND_STREAM_STRIDE));

        let b0 = eval.next_trace_mask();
        let b1 = eval.next_trace_mask();
        let b2 = eval.next_trace_mask();
        let low7 = eval.next_trace_mask();
        let sample = eval.next_trace_mask();
        let accept_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
        let accept_prev = accept_mask[0].clone();
        let accept = accept_mask[1].clone();
        let index_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
        let index_prev = index_mask[0].clone();
        let index = index_mask[1].clone();
        let slack = [
            eval.next_trace_mask(),
            eval.next_trace_mask(),
            eval.next_trace_mask(),
        ];
        let reject_delta = eval.next_trace_mask();
        // C7b: b1's 4+4-bit split, re-limbing the NTT yield to 12/11 bits.
        let lo4 = eval.next_trace_mask();
        let hi4 = eval.next_trace_mask();

        let one = E::F::one();
        let c16 = E::F::from(m31(16));
        let c128 = E::F::from(m31(128));
        let c255 = E::F::from(m31(255));
        let c256 = E::F::from(m31(256));
        let c65536 = E::F::from(m31(1 << 16));
        let q = E::F::from(m31(Q));
        let value = b0.clone() + c256.clone() * b1.clone() + c65536.clone() * low7.clone();
        let slack_value =
            slack[0].clone() + c256.clone() * slack[1].clone() + c65536 * slack[2].clone();
        let skip = sample.clone() - accept.clone();

        eval.add_constraint(sample.clone() * (one.clone() - sample.clone()));
        eval.add_constraint(accept.clone() * (one.clone() - accept.clone()));
        eval.add_constraint(accept.clone() * (one.clone() - sample.clone()));
        // b2 = low7 + 128·top with top ∈ {0,1} ⟺ (b2−low7) ∈ {0,128}: the same
        // fact without witnessing `top` as its own column (deleted; was only
        // ever used here).
        let top_gap = b2.clone() - low7.clone();
        eval.add_constraint(top_gap.clone() * (top_gap - c128));
        eval.add_constraint(
            accept.clone() * (value.clone() + slack_value - (q.clone() - one.clone())),
        );
        eval.add_constraint(skip.clone() * (value - q - reject_delta.clone()));
        eval.add_constraint(first * index.clone());
        eval.add_constraint(not_first * (index.clone() - index_prev - accept_prev));
        eval.add_constraint(
            (active.clone() - sample.clone()) * (index.clone() - E::F::from(m31(N as u32))),
        );
        eval.add_constraint(last * (index.clone() + accept.clone() - E::F::from(m31(N as u32))));

        for limb in &slack {
            eval.add_constraint((one.clone() - accept.clone()) * limb.clone());
        }
        eval.add_constraint((one.clone() - skip.clone()) * reject_delta.clone());
        // C7b: b1 = lo4 + 16·hi4, gated by accept (lo4/hi4 only feed the
        // accept-gated NTT yield below; no other consumer, so -- like
        // accept_slack -- the split need not hold on reject rows).
        eval.add_constraint(
            accept.clone() * (b1.clone() - lo4.clone() - c16.clone() * hi4.clone()),
        );
        let padding = one.clone() - active.clone();
        for cell in [
            b0.clone(),
            b1.clone(),
            b2.clone(),
            low7.clone(),
            sample.clone(),
            accept.clone(),
            index.clone(),
            slack[0].clone(),
            slack[1].clone(),
            slack[2].clone(),
            reject_delta.clone(),
            lo4.clone(),
            hi4.clone(),
        ] {
            eval.add_constraint(padding.clone() * cell);
        }

        let stream_base = E::F::from(m31(self.stream_base));
        for (limb, byte) in [b0.clone(), b1.clone(), b2].into_iter().enumerate() {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.hash_io,
                -active.clone(),
                &[
                    stream_base.clone() + squeeze_stream.clone(),
                    byte_pos.clone() + E::F::from(m31(limb as u32)),
                    byte,
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            active,
            &range_tuple::<E>(low7.clone(), RcKind::Rc7),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            sample.clone(),
            &range_tuple::<E>(c255 - index.clone(), RcKind::Rc8),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            accept.clone(),
            &range_tuple::<E>(slack[0].clone(), RcKind::Rc8),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            accept.clone(),
            &range_tuple::<E>(slack[1].clone(), RcKind::Rc8),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            accept.clone(),
            &range_tuple::<E>(slack[2].clone(), RcKind::Rc7),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            skip,
            &range_tuple::<E>(reject_delta, RcKind::Rc13),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            accept.clone(),
            &range_tuple::<E>(lo4.clone(), RcKind::Rc4),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            accept.clone(),
            &range_tuple::<E>(hi4.clone(), RcKind::Rc4),
        ));
        // C7b: yield the NTT cell in the 12/11-bit split instead of the
        // 8/8/7-bit byte split -- a0 = b0 + 256·lo4 (12 bits), a1 = hi4 +
        // 16·low7 (11 bits); a0 + 4096·a1 == b0 + 256·b1 + 65536·low7
        // (`value`, unchanged) since b1 = lo4 + 16·hi4.
        let a0 = b0 + c256 * lo4;
        let a1 = hi4 + c16 * low7;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.ntt,
            accept,
            &[poly, E::F::zero(), index, a0, a1],
        ));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

fn range_denominator(relation: &RangeRelation, value: u32, kind: RcKind) -> SecureField {
    relation.combine(&[m31(value), m31(kind.bound_id())])
}

fn combine_batch(entries: &[(SecureField, SecureField)]) -> (SecureField, SecureField) {
    let mut numerator = entries[0].0;
    let mut denominator = entries[0].1;
    for &(next_numerator, next_denominator) in &entries[1..] {
        numerator = next_denominator * numerator + next_numerator * denominator;
        denominator *= next_denominator;
    }
    (numerator, denominator)
}

fn gen_batched_logup(
    log_size: u32,
    rows: &[Vec<(SecureField, SecureField)>],
    entry_count: usize,
) -> (Vec<ColEval>, SecureField) {
    let row_lookup = circle_row_to_coset(log_size);
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut generator = LogupTraceGenerator::new(log_size);
    for start in (0..entry_count).step_by(LOGUP_BATCH) {
        let end = (start + LOGUP_BATCH).min(entry_count);
        let mut column = generator.new_col();
        for vec_row in 0..vec_rows {
            let mut numerators = [zero; N_LANES];
            let mut denominators = [one; N_LANES];
            for lane in 0..N_LANES {
                let coset = row_lookup[vec_row * N_LANES + lane];
                let (numerator, denominator) = combine_batch(&rows[coset][start..end]);
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            column.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        column.finalize_col();
    }
    generator.finalize_last()
}

fn gen_absorb_interaction(
    witness: &ExpandAWitness,
    stream_base: u32,
    relations: &ExpandARelations,
) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let log_size = absorb_log_size(witness.profile);
    let matrix_polys = witness.profile.matrix_polys();
    let mut rows = vec![vec![(zero, one); ABSORB_LOGUP_ENTRIES]; 1usize << log_size];
    for pos in 0..34 {
        for poly in 0..matrix_polys {
            let row = pos * matrix_polys + poly;
            let byte = absorb_input(witness.profile, &witness.rho, poly)[pos] as u32;
            rows[row][0] = (
                one,
                relations.hash_io.combine(&[
                    m31(validated_absorb_stream_id(stream_base, poly)),
                    m31(pos as u32),
                    m31(byte),
                ]),
            );
            if pos < 32 && poly == 0 {
                rows[row][1] = (one, relations.rho.combine(&[m31(pos as u32), m31(byte)]));
            }
        }
    }
    gen_batched_logup(log_size, &rows, ABSORB_LOGUP_ENTRIES)
}

fn gen_rejection_interaction(
    profile: MlDsaProfile,
    rows_data: &[RejectionRow],
    stream_base: u32,
    relations: &ExpandARelations,
) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let log_size = rejection_log_size(profile);
    let mut rows = vec![vec![(zero, one); REJECTION_LOGUP_ENTRIES]; 1usize << log_size];
    for (row, data) in rows_data.iter().enumerate() {
        let poly = row / MAX_CANDIDATES;
        let candidate = row % MAX_CANDIDATES;
        let mut entries = Vec::with_capacity(REJECTION_LOGUP_ENTRIES);
        for (limb, &byte) in data.bytes.iter().enumerate() {
            entries.push((
                -one,
                relations.hash_io.combine(&[
                    m31(validated_squeeze_stream_id(stream_base, poly)),
                    m31((3 * candidate + limb) as u32),
                    m31(byte),
                ]),
            ));
        }
        entries.push((
            one,
            range_denominator(&relations.range, data.low7, RcKind::Rc7),
        ));
        entries.push(if data.sample {
            (
                one,
                range_denominator(&relations.range, 255 - data.index, RcKind::Rc8),
            )
        } else {
            (zero, one)
        });
        for (limb, kind) in [RcKind::Rc8, RcKind::Rc8, RcKind::Rc7]
            .into_iter()
            .enumerate()
        {
            entries.push(if data.accept {
                (
                    one,
                    range_denominator(&relations.range, data.accept_slack[limb], kind),
                )
            } else {
                (zero, one)
            });
        }
        entries.push(if data.sample && !data.accept {
            (
                one,
                range_denominator(&relations.range, data.reject_delta, RcKind::Rc13),
            )
        } else {
            (zero, one)
        });
        // C7b: lo4/hi4 Rc4 lookups (gated by accept, mirroring accept_slack).
        entries.push(if data.accept {
            (
                one,
                range_denominator(&relations.range, data.lo4, RcKind::Rc4),
            )
        } else {
            (zero, one)
        });
        entries.push(if data.accept {
            (
                one,
                range_denominator(&relations.range, data.hi4, RcKind::Rc4),
            )
        } else {
            (zero, one)
        });
        entries.push(if data.accept {
            // C7b: yield the NTT cell in the 12/11-bit split instead of the
            // 8/8/7-bit byte split (see `RejectionEval::evaluate`).
            let a0 = data.bytes[0] + 256 * data.lo4;
            let a1 = data.hi4 + 16 * data.low7;
            (
                one,
                relations.ntt.combine(&[
                    m31(poly as u32),
                    m31(0),
                    m31(data.index),
                    m31(a0),
                    m31(a1),
                ]),
            )
        } else {
            (zero, one)
        });
        debug_assert_eq!(entries.len(), REJECTION_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    gen_batched_logup(log_size, &rows, REJECTION_LOGUP_ENTRIES)
}

type AbsorbComponent = FrameworkComponent<AbsorbEval>;
type RejectionComponent = FrameworkComponent<RejectionEval>;

struct Built {
    absorb: AbsorbComponent,
    rejection: RejectionComponent,
}

impl Built {
    fn components(&self) -> Vec<&dyn Component> {
        vec![&self.absorb, &self.rejection]
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.absorb, &self.rejection]
    }
}

#[allow(clippy::too_many_arguments)]
fn build_components(
    allocator: &mut TraceLocationAllocator,
    profile: MlDsaProfile,
    namespace: &str,
    stream_base: u32,
    relations: &ExpandARelations,
    claim: &ExpandAClaim,
) -> Built {
    Built {
        absorb: FrameworkComponent::new(
            allocator,
            AbsorbEval {
                profile,
                ns: namespace.to_owned(),
                stream_base,
                relations: relations.clone(),
            },
            claim.absorb_claimed_sum,
        ),
        rejection: FrameworkComponent::new(
            allocator,
            RejectionEval {
                profile,
                ns: namespace.to_owned(),
                stream_base,
                relations: relations.clone(),
            },
            claim.rejection_claimed_sum,
        ),
    }
}

fn layout(profile: MlDsaProfile) -> TreeLayout {
    let absorb_log_size = absorb_log_size(profile);
    let rejection_log_size = rejection_log_size(profile);
    let mut preprocessed = vec![absorb_log_size; ABSORB_PRE_NAMES.len()];
    preprocessed.extend(vec![rejection_log_size; REJECTION_PRE_NAMES.len()]);
    let mut trace = vec![absorb_log_size; ABSORB_BASE_COLS];
    trace.extend(vec![rejection_log_size; REJECTION_BASE_COLS]);
    let mut interaction = vec![absorb_log_size; ABSORB_INTERACTION_COLS];
    interaction.extend(vec![rejection_log_size; REJECTION_INTERACTION_COLS]);
    TreeLayout {
        preprocessed,
        trace,
        interaction,
    }
}

fn mix_public(
    channel: &mut Blake2sChannel,
    profile: MlDsaProfile,
    namespace: &str,
    stream_base: u32,
) {
    channel.mix_u64(EXPAND_A_MIX_TAG);
    channel.mix_u64(profile.transcript_tag());
    channel.mix_u64(namespace.len() as u64);
    for &byte in namespace.as_bytes() {
        channel.mix_u64(byte as u64);
    }
    channel.mix_u64(stream_base as u64);
    channel.mix_u64(MAX_EXPAND_A_SQUEEZE_BLOCKS as u64);
    channel.mix_u64(profile.matrix_polys() as u64);
}

fn draw_relations(
    channel: &mut Blake2sChannel,
    range_handle: &SharedRangeRelation,
    keccak_handle: &SharedKeccakRelations,
    bindings: &ExpandABindings,
) -> ExpandARelations {
    let rho = RhoCellRelation::draw(channel);
    bindings.rho.set(rho.clone());
    let ntt = NttCellRelation::draw(channel);
    bindings.ntt.set(ntt.clone());
    ExpandARelations {
        hash_io: keccak_handle.get().hash_io,
        range: range_handle.get(),
        rho,
        ntt,
    }
}

/// Prover module for private `ExpandA`.
///
/// The caller places the shared range table and Keccak service before this module.
pub struct ExpandAProver {
    profile: MlDsaProfile,
    witness: ExpandAWitness,
    rows: Vec<RejectionRow>,
    range_uses: RcUses,
    namespace: String,
    stream_base: u32,
    range_handle: SharedRangeRelation,
    keccak_handle: SharedKeccakRelations,
    bindings: ExpandABindings,
    relations: Option<ExpandARelations>,
    claim: ExpandAClaim,
    built: Option<Built>,
    trace_attack: Option<ExpandATraceAttack>,
}

impl ExpandAProver {
    /// Create the prover module; validates the witness fail-closed.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        profile: MlDsaProfile,
        witness: ExpandAWitness,
        namespace: impl Into<String>,
        stream_base: u32,
        range_handle: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
        bindings: ExpandABindings,
    ) -> Result<Self, ExpandAError> {
        validate_stream_base(stream_base)?;
        if witness.profile != profile {
            return Err(ExpandAError::StreamCount {
                expected: profile.matrix_polys(),
                actual: witness.squeeze_streams.len(),
            });
        }
        validate_stream(&witness)?;
        let rows = build_rejection_rows(&witness);
        let range_uses = rejection_range_uses(&rows);
        Ok(Self {
            profile,
            witness,
            rows,
            range_uses,
            namespace: namespace.into(),
            stream_base,
            range_handle,
            keccak_handle,
            bindings,
            relations: None,
            claim: ExpandAClaim::default(),
            built: None,
            trace_attack: None,
        })
    }

    /// The current public claim (both claimed sums).
    pub fn claim(&self) -> ExpandAClaim {
        self.claim.clone()
    }

    /// The range-table uses this module requires.
    pub fn range_uses(&self) -> &RcUses {
        &self.range_uses
    }

    /// The SHAKE-128 job shapes and absorb messages for the Keccak service.
    pub fn keccak_jobs(&self) -> Result<(Vec<Shape>, Vec<Vec<u8>>), ExpandAError> {
        Ok((
            shake128_job_shapes(self.profile, self.stream_base)?,
            shake128_absorb_streams(self.profile, &self.witness.rho),
        ))
    }

    #[doc(hidden)]
    pub fn with_trace_attack(mut self, attack: ExpandATraceAttack) -> Self {
        self.trace_attack = Some(attack);
        self
    }

    fn relations(&self) -> &ExpandARelations {
        self.relations.as_ref().expect("ExpandA relations drawn")
    }
}

impl Air for ExpandAProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(channel, self.profile, &self.namespace, self.stream_base);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(draw_relations(
            channel,
            &self.range_handle,
            &self.keccak_handle,
            &self.bindings,
        ));
    }

    fn layout(&self) -> TreeLayout {
        layout(self.profile)
    }

    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![
            self.claim.absorb_claimed_sum,
            self.claim.rejection_claimed_sum,
        ]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        expand_a_preprocessed_ids(&self.namespace)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_expand_a_preprocessed(self.profile, &self.namespace))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.profile,
            &self.namespace,
            self.stream_base,
            self.relations(),
            &self.claim,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("ExpandA built").components()
    }
}

impl AirProver for ExpandAProver {
    fn max_log_size(&self) -> u32 {
        rejection_log_size(self.profile)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_log_size() + 2
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_expand_a_preprocessed_with_attack(
            self.profile,
            &self.namespace,
            self.trace_attack,
        ));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let columns =
            gen_expand_a_preprocessed_with_attack(self.profile, &self.namespace, self.trace_attack);
        fingerprint_preprocessed_columns(
            "mldsa_expand_a",
            &expand_a_preprocessed_ids(&self.namespace),
            &columns,
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut trace = gen_absorb_base_trace(&self.witness, self.trace_attack);
        trace.extend(gen_rejection_base_trace(
            self.profile,
            &self.rows,
            self.trace_attack,
        ));
        tb.extend_evals(trace);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let relations = self.relations().clone();
        let (absorb_trace, absorb_claimed_sum) =
            gen_absorb_interaction(&self.witness, self.stream_base, &relations);
        let (rejection_trace, rejection_claimed_sum) =
            gen_rejection_interaction(self.profile, &self.rows, self.stream_base, &relations);
        self.claim = ExpandAClaim {
            absorb_claimed_sum,
            rejection_claimed_sum,
        };
        let mut trace = absorb_trace;
        trace.extend(rejection_trace);
        tb.extend_evals(trace);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built
            .as_ref()
            .expect("ExpandA built")
            .prover_components()
    }
}

/// Verifier module for private `ExpandA`.
///
/// All layout data is fixed. The `rho` value remains private.
pub struct ExpandAVerifier {
    profile: MlDsaProfile,
    claim: ExpandAClaim,
    namespace: String,
    stream_base: u32,
    range_handle: SharedRangeRelation,
    keccak_handle: SharedKeccakRelations,
    bindings: ExpandABindings,
    relations: Option<ExpandARelations>,
    built: Option<Built>,
}

impl ExpandAVerifier {
    /// Create the verifier module from the public claim.
    pub fn new(
        profile: MlDsaProfile,
        claim: ExpandAClaim,
        namespace: impl Into<String>,
        stream_base: u32,
        range_handle: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
        bindings: ExpandABindings,
    ) -> Result<Self, ExpandAError> {
        validate_stream_base(stream_base)?;
        Ok(Self {
            profile,
            claim,
            namespace: namespace.into(),
            stream_base,
            range_handle,
            keccak_handle,
            bindings,
            relations: None,
            built: None,
        })
    }

    fn relations(&self) -> &ExpandARelations {
        self.relations.as_ref().expect("ExpandA relations drawn")
    }
}

impl Air for ExpandAVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        mix_public(channel, self.profile, &self.namespace, self.stream_base);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relations = Some(draw_relations(
            channel,
            &self.range_handle,
            &self.keccak_handle,
            &self.bindings,
        ));
    }

    fn layout(&self) -> TreeLayout {
        layout(self.profile)
    }

    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![
            self.claim.absorb_claimed_sum,
            self.claim.rejection_claimed_sum,
        ]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        expand_a_preprocessed_ids(&self.namespace)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, VerificationError> {
        Ok(gen_expand_a_preprocessed(self.profile, &self.namespace))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
            self.profile,
            &self.namespace,
            self.stream_base,
            self.relations(),
            &self.claim,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built.as_ref().expect("ExpandA built").components()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::ML_DSA_65;

    use stwo::core::fields::m31::M31;
    use stwo::core::utils::{
        bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
    };
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::Multiplicity;

    #[test]
    fn fixed_shape_and_stream_order_are_exact() {
        assert_eq!(MATRIX_POLYS, 30);
        assert_eq!(MAX_CANDIDATES, 336);
        assert_eq!(ABSORB_ACTIVE_ROWS, 1_020);
        assert_eq!(REJECTION_ACTIVE_ROWS, 10_080);
        assert_eq!(ABSORB_LOG_SIZE, 10);
        assert_eq!(REJECTION_LOG_SIZE, 14);
        assert_eq!(ABSORB_PRE_NAMES.len(), 6);
        assert_eq!(REJECTION_PRE_NAMES.len(), 5);
        let preprocessed_ids = expand_a_preprocessed_ids("shape-test");
        assert_eq!(preprocessed_ids.len(), 11);
        assert_eq!(gen_expand_a_preprocessed(ML_DSA_65, "shape-test").len(), 11);
        assert!(preprocessed_ids
            .iter()
            .all(|id| !id.id.ends_with("_absorb_poly")));
        assert!(preprocessed_ids
            .iter()
            .all(|id| !id.id.ends_with("_absorb_active")));
        assert!(preprocessed_ids
            .iter()
            .all(|id| !id.id.ends_with("_rejection_candidate")));
        assert!(preprocessed_ids
            .iter()
            .all(|id| !id.id.ends_with("_rejection_not_first")));
        assert!(preprocessed_ids
            .iter()
            .all(|id| !id.id.ends_with("_rejection_poly")));
        assert_eq!(ABSORB_BASE_COLS, 1);
        assert_eq!(REJECTION_BASE_COLS, 13);
        assert_eq!(ABSORB_INTERACTION_COLS, 4);
        assert_eq!(REJECTION_INTERACTION_COLS, 12);
        let rho = [17u8; 32];
        let streams = shake128_absorb_streams(ML_DSA_65, &rho);
        let shapes = shake128_job_shapes(ML_DSA_65, 256).unwrap();
        assert_eq!(streams.len(), MATRIX_POLYS);
        assert_eq!(shapes.len(), MATRIX_POLYS);
        for poly in 0..MATRIX_POLYS {
            assert_eq!(&streams[poly][..32], &rho);
            assert_eq!(streams[poly][32], (poly % L) as u8);
            assert_eq!(streams[poly][33], (poly / L) as u8);
            assert_eq!(shapes[poly].message_len, 34);
            assert_eq!(shapes[poly].n_squeeze, 6);
            assert_eq!(
                shapes[poly].absorb_stream_id,
                absorb_stream_id(ML_DSA_65, 256, poly).unwrap()
            );
            assert_eq!(
                shapes[poly].squeeze_stream_id,
                squeeze_stream_id(ML_DSA_65, 256, poly).unwrap()
            );
        }
    }

    #[test]
    fn canonical_witness_validates_and_matches_reference() {
        let rho = core::array::from_fn(|i| (17 * i + 3) as u8);
        let witness = derive_expand_a_witness(ML_DSA_65, rho).unwrap();
        let counts = validate_stream(&witness).unwrap();
        let reference = crate::reference::expand_a::expand_a(ML_DSA_65, &rho);
        let rows = build_rejection_rows(&witness);
        for poly in 0..MATRIX_POLYS {
            assert!((N..=MAX_CANDIDATES).contains(&counts[poly]));
            let accepted: Vec<u32> = rows[poly * MAX_CANDIDATES..(poly + 1) * MAX_CANDIDATES]
                .iter()
                .filter(|row| row.accept)
                .map(|row| row.bytes[0] | row.bytes[1] << 8 | row.low7 << 16)
                .collect();
            assert_eq!(accepted.len(), N);
            assert_eq!(
                accepted.as_slice(),
                reference.matrix[poly / L][poly % L].as_slice()
            );
        }
    }

    #[test]
    fn comparison_boundaries_are_exact() {
        let bytes = [(Q - 1) as u8, ((Q - 1) >> 8) as u8, ((Q - 1) >> 16) as u8];
        assert_eq!(candidate(&bytes), Q - 1);
        assert!(candidate(&bytes) < Q);
        let bytes = [Q as u8, (Q >> 8) as u8, (Q >> 16) as u8];
        assert_eq!(candidate(&bytes), Q);
        assert!(candidate(&bytes) >= Q);
        let mut high_bit = bytes;
        high_bit[2] |= 0x80;
        assert_eq!(candidate(&high_bit), Q);
    }

    struct RecordingEvaluator<'a> {
        trace: &'a [Vec<Vec<M31>>],
        col_index: [usize; 3],
        row: usize,
        log_size: u32,
        failures: usize,
    }

    impl<'a> RecordingEvaluator<'a> {
        fn new(trace: &'a [Vec<Vec<M31>>], row: usize, log_size: u32) -> Self {
            Self {
                trace,
                col_index: [0; 3],
                row,
                log_size,
                failures: 0,
            }
        }
    }

    impl EvalAtRow for RecordingEvaluator<'_> {
        type F = M31;
        type EF = SecureField;

        fn next_interaction_mask<const N_MASKS: usize>(
            &mut self,
            interaction: usize,
            offsets: [isize; N_MASKS],
        ) -> [Self::F; N_MASKS] {
            let column = self.col_index[interaction];
            self.col_index[interaction] += 1;
            offsets.map(|offset| {
                if offset == 0 {
                    return self.trace[interaction][column][self.row];
                }
                let domain_size = 1usize << self.log_size;
                let coset = circle_domain_index_to_coset_index(
                    bit_reverse_index(self.row, self.log_size),
                    self.log_size,
                );
                let offset_coset = (coset as isize + offset).rem_euclid(domain_size as isize);
                let row = bit_reverse_index(
                    coset_index_to_circle_domain_index(offset_coset as usize, self.log_size),
                    self.log_size,
                );
                self.trace[interaction][column][row]
            })
        }

        fn add_constraint<C>(&mut self, constraint: C)
        where
            Self::EF: std::ops::Mul<C, Output = Self::EF> + From<C>,
        {
            self.failures += usize::from(SecureField::from(constraint) != SecureField::zero());
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            SecureField::from_m31_array(values)
        }

        fn add_to_relation<R: Relation<Self::F, Self::EF>>(
            &mut self,
            _entry: RelationEntry<'_, Self::F, Self::EF, R>,
        ) {
        }

        fn write_logup_frac_typed(
            &mut self,
            _numerator: Multiplicity<Self::F, Self::EF>,
            _denominator: Self::EF,
        ) {
        }

        fn finalize_logup_batched(&mut self, _batch_size: usize) {}

        fn finalize_logup(&mut self) {}

        fn finalize_logup_in_pairs(&mut self) {}
    }

    fn cpu_columns(columns: Vec<ColEval>) -> Vec<Vec<M31>> {
        columns
            .into_iter()
            .map(|column| column.values.to_cpu())
            .collect()
    }

    fn absorb_constraint_failures(
        witness: &ExpandAWitness,
        attack: Option<ExpandATraceAttack>,
    ) -> usize {
        const TEST_NS: &str = "expand-a-absorb-eval";
        let profile = witness.profile;
        let relations = ExpandARelations::dummy();
        let trace = vec![
            cpu_columns(gen_absorb_preprocessed(profile, TEST_NS, attack)),
            cpu_columns(gen_absorb_base_trace(witness, attack)),
            Vec::new(),
        ];
        let log_size = absorb_log_size(profile);
        (0..1usize << log_size)
            .map(|row| {
                AbsorbEval {
                    profile,
                    ns: TEST_NS.to_owned(),
                    stream_base: 0,
                    relations: relations.clone(),
                }
                .evaluate(RecordingEvaluator::new(&trace, row, log_size))
                .failures
            })
            .sum()
    }

    fn rejection_constraint_failures(
        rows: &[RejectionRow],
        attack: Option<ExpandATraceAttack>,
    ) -> usize {
        const TEST_NS: &str = "expand-a-rejection-eval";
        let profile = ML_DSA_65;
        let relations = ExpandARelations::dummy();
        let trace = vec![
            cpu_columns(gen_rejection_preprocessed(profile, TEST_NS, attack)),
            cpu_columns(gen_rejection_base_trace(profile, rows, attack)),
            Vec::new(),
        ];
        let log_size = rejection_log_size(profile);
        (0..1usize << log_size)
            .map(|row| {
                RejectionEval {
                    profile,
                    ns: TEST_NS.to_owned(),
                    stream_base: 0,
                    relations: relations.clone(),
                }
                .evaluate(RecordingEvaluator::new(&trace, row, log_size))
                .failures
            })
            .sum()
    }

    fn set_boundary_candidate(row: &mut RejectionRow, value: u32, accept: bool) {
        row.bytes = split_u23(value);
        row.low7 = row.bytes[2] & 0x7f;
        row.lo4 = row.bytes[1] & 0xf;
        row.hi4 = row.bytes[1] >> 4;
        row.accept = accept;
        row.accept_slack = if accept {
            split_u23(Q - 1 - value)
        } else {
            [0; 3]
        };
        row.reject_delta = if row.sample && !accept { value - Q } else { 0 };
    }

    #[test]
    fn rejection_air_accepts_q_minus_one_and_rejects_q() {
        let witness = derive_expand_a_witness(ML_DSA_65, [42u8; 32]).unwrap();
        let mut rows = build_rejection_rows(&witness);
        let accept_rows: Vec<_> = rows
            .iter()
            .enumerate()
            .filter_map(|(index, row)| row.accept.then_some(index))
            .take(3)
            .collect();
        let reject_rows: Vec<_> = rows
            .iter()
            .enumerate()
            .filter_map(|(index, row)| (row.sample && !row.accept).then_some(index))
            .take(2)
            .collect();
        let done_row = rows.iter().position(|row| !row.sample).unwrap();
        assert_eq!(accept_rows.len(), 3);
        assert_eq!(reject_rows.len(), 2);

        set_boundary_candidate(&mut rows[accept_rows[0]], Q - 1, true);
        set_boundary_candidate(&mut rows[accept_rows[1]], 1, true);
        set_boundary_candidate(&mut rows[accept_rows[2]], 0, true);
        set_boundary_candidate(&mut rows[reject_rows[0]], Q, false);
        set_boundary_candidate(&mut rows[reject_rows[1]], (1 << 23) - 1, false);
        rows[done_row].bytes = [0, 0, 128];
        rows[done_row].low7 = 0;

        assert_eq!(rows[accept_rows[0]].accept_slack, [0, 0, 0]);
        assert_eq!(rows[accept_rows[1]].accept_slack[0], 255);
        assert_eq!(rows[accept_rows[2]].accept_slack[2], 127);
        assert_eq!(rows[reject_rows[0]].reject_delta, 0);
        assert_eq!(rows[reject_rows[1]].reject_delta, (1 << 13) - 2);
        assert_eq!(rejection_constraint_failures(&rows, None), 0);
    }

    #[test]
    fn rejection_air_rejects_q_marked_accepted() {
        let witness = derive_expand_a_witness(ML_DSA_65, [42u8; 32]).unwrap();
        let mut rows = build_rejection_rows(&witness);
        let row = rows.iter().position(|row| row.accept).unwrap();
        rows[row].bytes = split_u23(Q);
        rows[row].low7 = rows[row].bytes[2] & 0x7f;
        rows[row].lo4 = rows[row].bytes[1] & 0xf;
        rows[row].hi4 = rows[row].bytes[1] >> 4;
        rows[row].accept = true;
        rows[row].accept_slack = [0; 3];

        assert_eq!(
            rejection_constraint_failures(&rows, None),
            1,
            "q must not satisfy the accepted-candidate comparison"
        );
    }

    #[test]
    fn rejection_air_rejects_q_minus_one_marked_rejected() {
        let witness = derive_expand_a_witness(ML_DSA_65, [42u8; 32]).unwrap();
        let mut rows = build_rejection_rows(&witness);
        let row = rows
            .iter()
            .position(|row| row.sample && !row.accept)
            .unwrap();
        rows[row].bytes = split_u23(Q - 1);
        rows[row].low7 = rows[row].bytes[2] & 0x7f;
        rows[row].accept = false;
        rows[row].reject_delta = 0;

        assert_eq!(
            rejection_constraint_failures(&rows, None),
            1,
            "q - 1 must not satisfy the rejected-candidate comparison"
        );
    }

    /// C7b(N7a): `lo4`/`hi4` must satisfy `b1 = lo4 + 16·hi4` exactly on an
    /// accepted row -- bumping `hi4` by one (leaving `lo4` and `b1`
    /// untouched) breaks the split constraint and must be rejected.
    #[test]
    fn rejection_air_rejects_mismatched_lo4_hi4_split() {
        let witness = derive_expand_a_witness(ML_DSA_65, [42u8; 32]).unwrap();
        let mut rows = build_rejection_rows(&witness);
        let row = rows.iter().position(|row| row.accept).unwrap();
        rows[row].hi4 += 1;

        assert!(
            rejection_constraint_failures(&rows, None) > 0,
            "a mismatched (lo4, hi4) split must be rejected"
        );
    }

    /// C7b(N7b): `hi4` is still range-checked via Rc4 after the re-limb.
    /// Rc4's domain is exactly `[0, 16)`; the first excluded value (16)
    /// cannot even be recorded in the witness-side multiplicity
    /// bookkeeping, mirroring the same structural argument as the ntt.rs
    /// C7a/C7b boundary tests.
    #[test]
    #[should_panic]
    fn hi4_at_table_boundary_cannot_be_recorded() {
        let mut uses = RcUses::new();
        uses.record(RcKind::Rc4, 16);
    }

    #[test]
    fn fast_air_adversarial_matrix_rejects() {
        let witness = derive_expand_a_witness(ML_DSA_65, [42u8; 32]).unwrap();
        let rows = build_rejection_rows(&witness);
        let accept_row = rows.iter().position(|row| row.accept).unwrap();
        let reject_row = rows
            .iter()
            .position(|row| row.sample && !row.accept)
            .unwrap();
        let done_row = rows
            .iter()
            .position(|row| !row.sample)
            .expect("fixture completes before cap");

        let absorb_attacks = [
            ExpandATraceAttack::Absorb { row: 0, value: 43 },
            ExpandATraceAttack::Absorb { row: 1, value: 43 },
            ExpandATraceAttack::Absorb {
                row: 32 * MATRIX_POLYS,
                value: 1,
            },
            ExpandATraceAttack::Absorb {
                row: 33 * MATRIX_POLYS,
                value: 1,
            },
            ExpandATraceAttack::Absorb {
                row: ABSORB_ACTIVE_ROWS,
                value: 1,
            },
        ];
        for attack in absorb_attacks {
            assert_ne!(
                absorb_constraint_failures(&witness, Some(attack)),
                0,
                "absorb attack unexpectedly satisfied the AIR: {attack:?}"
            );
        }

        let rejection_attacks = [
            ExpandATraceAttack::Rejection {
                row: accept_row,
                column: COL_B0,
                value: rows[accept_row].bytes[0] ^ 1,
            },
            ExpandATraceAttack::Rejection {
                row: accept_row,
                column: COL_B1,
                value: rows[accept_row].bytes[1] ^ 1,
            },
            ExpandATraceAttack::Rejection {
                row: accept_row,
                column: COL_B2,
                value: rows[accept_row].bytes[2] ^ 1,
            },
            ExpandATraceAttack::Rejection {
                row: accept_row,
                column: COL_LOW7,
                value: rows[accept_row].low7 ^ 1,
            },
            ExpandATraceAttack::Rejection {
                row: 0,
                column: COL_SAMPLE,
                value: 2,
            },
            ExpandATraceAttack::Rejection {
                row: accept_row,
                column: COL_ACCEPT,
                value: 2,
            },
            ExpandATraceAttack::Rejection {
                row: reject_row,
                column: COL_ACCEPT,
                value: 1,
            },
            ExpandATraceAttack::Rejection {
                row: accept_row,
                column: COL_ACCEPT,
                value: 0,
            },
            ExpandATraceAttack::Rejection {
                row: 0,
                column: COL_INDEX,
                value: 1,
            },
            ExpandATraceAttack::Rejection {
                row: 1,
                column: COL_INDEX,
                value: rows[1].index + 1,
            },
            ExpandATraceAttack::Rejection {
                row: MAX_CANDIDATES,
                column: COL_INDEX,
                value: 1,
            },
            ExpandATraceAttack::Rejection {
                row: MAX_CANDIDATES - 1,
                column: COL_INDEX,
                value: 255,
            },
            ExpandATraceAttack::Rejection {
                row: done_row,
                column: COL_SAMPLE,
                value: 1,
            },
            ExpandATraceAttack::Rejection {
                row: done_row,
                column: COL_ACCEPT,
                value: 1,
            },
            ExpandATraceAttack::Rejection {
                row: done_row,
                column: COL_INDEX,
                value: 255,
            },
            ExpandATraceAttack::Rejection {
                row: reject_row,
                column: COL_ACCEPT_SLACK0,
                value: 1,
            },
            ExpandATraceAttack::Rejection {
                row: reject_row,
                column: COL_REJECT_DELTA,
                value: rows[reject_row].reject_delta + 1,
            },
            ExpandATraceAttack::Rejection {
                row: REJECTION_ACTIVE_ROWS,
                column: COL_B0,
                value: 1,
            },
        ];
        for attack in rejection_attacks {
            assert_ne!(
                rejection_constraint_failures(&rows, Some(attack)),
                0,
                "rejection attack unexpectedly satisfied the AIR: {attack:?}"
            );
        }
    }

    #[test]
    fn validator_is_typed_and_fail_closed() {
        let witness = derive_expand_a_witness(ML_DSA_65, [9u8; 32]).unwrap();

        let mut bad = witness.clone();
        bad.squeeze_streams.pop();
        assert!(matches!(
            validate_stream(&bad),
            Err(ExpandAError::StreamCount { actual: 29, .. })
        ));

        let mut bad = witness.clone();
        bad.squeeze_streams.push(bad.squeeze_streams[0].clone());
        assert!(matches!(
            validate_stream(&bad),
            Err(ExpandAError::StreamCount { actual: 31, .. })
        ));

        let mut bad = witness.clone();
        bad.squeeze_streams[0].clear();
        assert_eq!(
            validate_stream(&bad),
            Err(ExpandAError::EmptyStream { poly: 0 })
        );

        let mut bad = witness.clone();
        bad.squeeze_streams[0].push(0);
        assert!(matches!(
            validate_stream(&bad),
            Err(ExpandAError::StreamNotBlockAligned { poly: 0, .. })
        ));

        let mut bad = witness.clone();
        let short_len = bad.squeeze_streams[0].len() - SHAKE128_RATE;
        bad.squeeze_streams[0].truncate(short_len);
        assert!(matches!(
            validate_stream(&bad),
            Err(ExpandAError::NonCanonicalLength { poly: 0, .. })
        ));

        let mut bad = witness.clone();
        bad.squeeze_streams[0] = vec![0; MAX_EXPAND_A_SQUEEZE_BYTES + SHAKE128_RATE];
        assert!(matches!(
            validate_stream(&bad),
            Err(ExpandAError::StreamExceedsCap { poly: 0, .. })
        ));

        let mut bad = witness.clone();
        let extra_poly = bad
            .squeeze_streams
            .iter()
            .position(|stream| stream.len() < MAX_EXPAND_A_SQUEEZE_BYTES)
            .expect("fixture has a canonical prefix below the cap");
        let old_len = bad.squeeze_streams[extra_poly].len();
        let full = fixed_squeeze_stream(bad.profile, &bad.rho, extra_poly);
        bad.squeeze_streams[extra_poly].extend_from_slice(&full[old_len..old_len + SHAKE128_RATE]);
        assert!(matches!(
            validate_stream(&bad),
            Err(ExpandAError::NonCanonicalLength { poly, .. }) if poly == extra_poly
        ));

        let mut bad = witness;
        bad.squeeze_streams[0][0] ^= 1;
        assert_eq!(
            validate_stream(&bad),
            Err(ExpandAError::StreamMismatch { poly: 0 })
        );
    }

    #[test]
    fn injected_six_block_overflow_is_typed_and_fail_closed() {
        let witness = derive_expand_a_witness(ML_DSA_65, [31u8; 32]).unwrap();
        let rejected = [0xff, 0xff, 0x7f];
        let stream: Vec<u8> = rejected
            .into_iter()
            .cycle()
            .take(MAX_EXPAND_A_SQUEEZE_BYTES)
            .collect();
        assert_eq!(consumed_candidates(&stream), None);
        assert_eq!(
            require_consumed_candidates(&stream, 7),
            Err(ExpandAError::SqueezeCapExceeded { poly: 7 })
        );
        assert_eq!(
            validate_stream_with(&witness, |profile, rho, poly| {
                if poly == 7 {
                    stream.clone()
                } else {
                    fixed_squeeze_stream(profile, rho, poly)
                }
            }),
            Err(ExpandAError::SqueezeCapExceeded { poly: 7 })
        );
    }

    #[test]
    fn stream_base_and_polynomial_ids_are_typed_and_field_safe() {
        assert_eq!(
            squeeze_stream_id(ML_DSA_65, MAX_EXPAND_STREAM_BASE, MATRIX_POLYS - 1).unwrap(),
            M31_MODULUS - 1
        );
        for stream_base in [MAX_EXPAND_STREAM_BASE + 1, u32::MAX] {
            assert_eq!(
                validate_stream_base(stream_base),
                Err(ExpandAError::InvalidStreamBase {
                    stream_base,
                    max: MAX_EXPAND_STREAM_BASE,
                })
            );
            assert!(matches!(
                shake128_job_shapes(ML_DSA_65, stream_base),
                Err(ExpandAError::InvalidStreamBase { .. })
            ));
        }
        assert_eq!(
            absorb_stream_id(ML_DSA_65, 0, MATRIX_POLYS),
            Err(ExpandAError::PolynomialOutOfRange { poly: MATRIX_POLYS })
        );

        let invalid_base = MAX_EXPAND_STREAM_BASE + 1;
        let prover = ExpandAProver::new(
            ML_DSA_65,
            derive_expand_a_witness(ML_DSA_65, [7u8; 32]).unwrap(),
            "invalid-base",
            invalid_base,
            SharedRangeRelation::new(),
            SharedKeccakRelations::new(),
            ExpandABindings::new(),
        );
        assert!(matches!(
            prover,
            Err(ExpandAError::InvalidStreamBase {
                stream_base,
                max: MAX_EXPAND_STREAM_BASE,
            }) if stream_base == invalid_base
        ));
        let verifier = ExpandAVerifier::new(
            ML_DSA_65,
            ExpandAClaim::default(),
            "invalid-base",
            invalid_base,
            SharedRangeRelation::new(),
            SharedKeccakRelations::new(),
            ExpandABindings::new(),
        );
        assert!(matches!(
            verifier,
            Err(ExpandAError::InvalidStreamBase {
                stream_base,
                max: MAX_EXPAND_STREAM_BASE,
            }) if stream_base == invalid_base
        ));
    }

    #[test]
    fn public_claim_round_trips_exactly() {
        let claim = ExpandAClaim {
            absorb_claimed_sum: SecureField::from(m31(17)),
            rejection_claimed_sum: SecureField::from(m31(29)),
        };
        let encoded = bincode::serialize(&claim).expect("serialize ExpandA claim");
        let decoded: ExpandAClaim =
            bincode::deserialize(&encoded).expect("deserialize ExpandA claim");
        assert_eq!(decoded, claim);
        assert_eq!(
            encoded.len() as u64,
            2 * bincode::serialized_size(&SecureField::zero()).unwrap(),
            "claim serialization must contain exactly two SecureFields"
        );
    }
}
