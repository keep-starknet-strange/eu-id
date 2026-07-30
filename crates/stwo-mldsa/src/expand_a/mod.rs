//! Fixed-shape AIR for FIPS 204 `ExpandA(rho)` rejection sampling.
//!
//! Thirty SHAKE-128 jobs absorb `rho || j || i`, consume a fixed six-block
//! squeeze budget, and yield exactly 256 accepted stage-zero NTT cells each.
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

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::binding::{
    HashIoRelation, NttCellRelation, RhoCellRelation, SharedNttCellRelation, SharedRhoCellRelation,
};
use crate::coeffs::relations::{RangeRelation, SharedRangeRelation};
use crate::coeffs::tables::RcKind;
use crate::coeffs::RcUses;
use crate::constants::{K, L, N, Q};
use crate::sponge_link::ns_prefix;
use stwo_keccak::relations::SharedKeccakRelations;
use stwo_keccak::sponge::Shape;

pub const MATRIX_POLYS: usize = K * L;
pub const SHAKE128_RATE: usize = 168;
pub const CANDIDATES_PER_BLOCK: usize = SHAKE128_RATE / 3;
/// Fixed fail-closed resource cap.
///
/// Five blocks overflow across 30 streams with probability at most
/// `2^-127.485`, just above the proof-wide `2^-128` rail. Six blocks reduce
/// that union bound to `2^-542.030`.
pub const MAX_EXPAND_A_SQUEEZE_BLOCKS: usize = 6;
pub const MAX_EXPAND_A_SQUEEZE_BYTES: usize = SHAKE128_RATE * MAX_EXPAND_A_SQUEEZE_BLOCKS;
pub const MAX_CANDIDATES: usize = CANDIDATES_PER_BLOCK * MAX_EXPAND_A_SQUEEZE_BLOCKS;

pub const EXPAND_STREAM_OFFSET: u32 = 16;
pub const EXPAND_STREAM_STRIDE: u32 = 2;
pub const REQUIRED_STREAM_STRIDE: u32 = 128;
const LAST_EXPAND_STREAM_OFFSET: u32 =
    EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * (MATRIX_POLYS as u32 - 1) + 1;
pub const MAX_EXPAND_STREAM_BASE: u32 = M31_MODULUS - 1 - LAST_EXPAND_STREAM_OFFSET;

pub const ABSORB_ACTIVE_ROWS: usize = MATRIX_POLYS * 34;
pub const ABSORB_LOG_SIZE: u32 = 10;
pub const REJECTION_ACTIVE_ROWS: usize = MATRIX_POLYS * MAX_CANDIDATES;
pub const REJECTION_LOG_SIZE: u32 = 14;

const LOGUP_BATCH: usize = 4;
const EXPAND_A_MIX_TAG: u64 = 0x4d4c_4453_4145_5850;

const ABSORB_PRE_NAMES: [&str; 8] = [
    "active",
    "byte_pos",
    "poly",
    "absorb_stream",
    "rho_first",
    "rho_copy",
    "domain_gate",
    "domain_byte",
];

const REJECTION_PRE_NAMES: [&str; 8] = [
    "active",
    "first",
    "last",
    "not_first",
    "poly",
    "candidate",
    "byte_pos",
    "squeeze_stream",
];

const COL_B0: usize = 0;
const COL_B1: usize = 1;
const COL_B2: usize = 2;
const COL_LOW7: usize = 3;
const COL_TOP: usize = 4;
const COL_SAMPLE: usize = 5;
const COL_ACCEPT: usize = 6;
const COL_INDEX: usize = 7;
const COL_ACCEPT_SLACK0: usize = 8;
const COL_ACCEPT_SLACK1: usize = 9;
const COL_ACCEPT_SLACK2: usize = 10;
const COL_REJECT_DELTA: usize = 11;

pub const ABSORB_BASE_COLS: usize = 1;
pub const REJECTION_BASE_COLS: usize = 12;
pub const ABSORB_LOGUP_ENTRIES: usize = 2;
pub const REJECTION_LOGUP_ENTRIES: usize = 10;
pub const ABSORB_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;
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
pub const TRACE_COL_TOP: usize = COL_TOP;
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
    pub rho: [u8; 32],
    pub squeeze_streams: Vec<Vec<u8>>,
}

/// Fail-closed witness and fixed-resource validation errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpandAError {
    StreamCount {
        expected: usize,
        actual: usize,
    },
    EmptyStream {
        poly: usize,
    },
    StreamNotBlockAligned {
        poly: usize,
        len: usize,
    },
    StreamExceedsCap {
        poly: usize,
        len: usize,
    },
    SqueezeCapExceeded {
        poly: usize,
    },
    NonCanonicalLength {
        poly: usize,
        expected: usize,
        actual: usize,
    },
    StreamMismatch {
        poly: usize,
    },
    InvalidStreamBase {
        stream_base: u32,
        max: u32,
    },
    PolynomialOutOfRange {
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
    pub rho: SharedRhoCellRelation,
    pub ntt: SharedNttCellRelation,
}

impl ExpandABindings {
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

/// The only U5-specific public proof claim. Both log sizes are fixed constants.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpandAClaim {
    pub absorb_claimed_sum: SecureField,
    pub rejection_claimed_sum: SecureField,
}

/// Fixed preprocessing stack containing the attacked cell.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandAPreprocessedComponent {
    Absorb,
    Rejection,
}

/// Test-only mutation of one logical base-trace or preprocessing cell.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandATraceAttack {
    Absorb {
        row: usize,
        value: u32,
    },
    Rejection {
        row: usize,
        column: usize,
        value: u32,
    },
    Preprocessed {
        component: ExpandAPreprocessedComponent,
        row: usize,
        column: usize,
        value: u32,
    },
}

#[derive(Clone)]
pub struct ExpandARelations {
    pub hash_io: HashIoRelation,
    pub range: RangeRelation,
    pub rho: RhoCellRelation,
    pub ntt: NttCellRelation,
}

impl ExpandARelations {
    pub fn dummy() -> Self {
        Self {
            hash_io: HashIoRelation::dummy(),
            range: RangeRelation::dummy(),
            rho: RhoCellRelation::dummy(),
            ntt: NttCellRelation::dummy(),
        }
    }
}

pub fn validate_stream_base(stream_base: u32) -> Result<(), ExpandAError> {
    if stream_base > MAX_EXPAND_STREAM_BASE {
        return Err(ExpandAError::InvalidStreamBase {
            stream_base,
            max: MAX_EXPAND_STREAM_BASE,
        });
    }
    Ok(())
}

fn validate_poly(poly: usize) -> Result<u32, ExpandAError> {
    if poly >= MATRIX_POLYS {
        return Err(ExpandAError::PolynomialOutOfRange { poly });
    }
    Ok(poly as u32)
}

pub fn absorb_stream_id(stream_base: u32, poly: usize) -> Result<u32, ExpandAError> {
    validate_stream_base(stream_base)?;
    let poly = validate_poly(poly)?;
    Ok(stream_base + EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly)
}

pub fn squeeze_stream_id(stream_base: u32, poly: usize) -> Result<u32, ExpandAError> {
    Ok(absorb_stream_id(stream_base, poly)? + 1)
}

fn validated_absorb_stream_id(stream_base: u32, poly: usize) -> u32 {
    stream_base + EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32
}

fn validated_squeeze_stream_id(stream_base: u32, poly: usize) -> u32 {
    validated_absorb_stream_id(stream_base, poly) + 1
}

fn absorb_input(rho: &[u8; 32], poly: usize) -> [u8; 34] {
    let mut input = [0u8; 34];
    input[..32].copy_from_slice(rho);
    input[32] = (poly % L) as u8;
    input[33] = (poly / L) as u8;
    input
}

fn fixed_squeeze_stream(rho: &[u8; 32], poly: usize) -> Vec<u8> {
    let input = absorb_input(rho, poly);
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

fn canonical_stream(rho: &[u8; 32], poly: usize) -> Result<(Vec<u8>, usize), ExpandAError> {
    canonical_stream_from_full(fixed_squeeze_stream(rho, poly), poly)
}

/// Construct the canonical, block-aligned witness for all 30 streams.
pub fn derive_expand_a_witness(rho: [u8; 32]) -> Result<ExpandAWitness, ExpandAError> {
    let mut squeeze_streams = Vec::with_capacity(MATRIX_POLYS);
    for poly in 0..MATRIX_POLYS {
        squeeze_streams.push(canonical_stream(&rho, poly)?.0);
    }
    Ok(ExpandAWitness {
        rho,
        squeeze_streams,
    })
}

/// Validate all stored on-demand prefixes and return their consumed-candidate counts.
fn validate_stream_with(
    witness: &ExpandAWitness,
    mut full_stream: impl FnMut(&[u8; 32], usize) -> Vec<u8>,
) -> Result<[usize; MATRIX_POLYS], ExpandAError> {
    if witness.squeeze_streams.len() != MATRIX_POLYS {
        return Err(ExpandAError::StreamCount {
            expected: MATRIX_POLYS,
            actual: witness.squeeze_streams.len(),
        });
    }
    let mut counts = [0usize; MATRIX_POLYS];
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
            canonical_stream_from_full(full_stream(&witness.rho, poly), poly)?;
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

pub fn validate_stream(witness: &ExpandAWitness) -> Result<[usize; MATRIX_POLYS], ExpandAError> {
    validate_stream_with(witness, fixed_squeeze_stream)
}

/// Public fixed service shapes in exact row-major matrix order.
pub fn shake128_job_shapes(stream_base: u32) -> Result<Vec<Shape>, ExpandAError> {
    validate_stream_base(stream_base)?;
    (0..MATRIX_POLYS)
        .map(|poly| {
            Ok(Shape::shake128(
                34,
                MAX_EXPAND_A_SQUEEZE_BLOCKS,
                absorb_stream_id(stream_base, poly)?,
                squeeze_stream_id(stream_base, poly)?,
            ))
        })
        .collect()
}

/// Witness absorb messages paired positionally with [`shake128_job_shapes`].
pub fn shake128_absorb_streams(rho: &[u8; 32]) -> Vec<Vec<u8>> {
    (0..MATRIX_POLYS)
        .map(|poly| absorb_input(rho, poly).to_vec())
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

pub fn expand_a_preprocessed_ids(ns: &str) -> Vec<PreProcessedColumnId> {
    let mut ids = absorb_preprocessed_ids(ns);
    ids.extend(rejection_preprocessed_ids(ns));
    ids
}

fn gen_absorb_preprocessed(ns: &str, attack: Option<ExpandATraceAttack>) -> Vec<ColEval> {
    let rows = 1usize << ABSORB_LOG_SIZE;
    let mut columns = vec![vec![m31(0); rows]; ABSORB_PRE_NAMES.len()];
    for pos in 0..34 {
        for poly in 0..MATRIX_POLYS {
            let row = pos * MATRIX_POLYS + poly;
            columns[0][row] = m31(1);
            columns[1][row] = m31(pos as u32);
            columns[2][row] = m31(poly as u32);
            columns[3][row] = m31(EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32);
            columns[4][row] = m31((pos < 32 && poly == 0) as u32);
            columns[5][row] = m31((pos < 32 && poly > 0) as u32);
            columns[6][row] = m31((pos >= 32) as u32);
            columns[7][row] = m31(match pos {
                32 => (poly % L) as u32,
                33 => (poly / L) as u32,
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
        .map(|column| col_eval(ABSORB_LOG_SIZE, column))
        .collect()
}

fn gen_rejection_preprocessed(ns: &str, attack: Option<ExpandATraceAttack>) -> Vec<ColEval> {
    let rows = 1usize << REJECTION_LOG_SIZE;
    let mut columns = vec![vec![m31(0); rows]; REJECTION_PRE_NAMES.len()];
    for poly in 0..MATRIX_POLYS {
        for candidate in 0..MAX_CANDIDATES {
            let row = poly * MAX_CANDIDATES + candidate;
            columns[0][row] = m31(1);
            columns[1][row] = m31((candidate == 0) as u32);
            columns[2][row] = m31((candidate + 1 == MAX_CANDIDATES) as u32);
            columns[3][row] = m31((candidate > 0) as u32);
            columns[4][row] = m31(poly as u32);
            columns[5][row] = m31(candidate as u32);
            columns[6][row] = m31((3 * candidate) as u32);
            columns[7][row] = m31(EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32 + 1);
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
        .map(|column| col_eval(REJECTION_LOG_SIZE, column))
        .collect()
}

pub fn gen_expand_a_preprocessed(ns: &str) -> Vec<ColEval> {
    gen_expand_a_preprocessed_with_attack(ns, None)
}

fn gen_expand_a_preprocessed_with_attack(
    ns: &str,
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let mut columns = gen_absorb_preprocessed(ns, attack);
    columns.extend(gen_rejection_preprocessed(ns, attack));
    columns
}

#[derive(Clone, Copy)]
struct RejectionRow {
    bytes: [u32; 3],
    low7: u32,
    top: u32,
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
    let mut rows = Vec::with_capacity(REJECTION_ACTIVE_ROWS);
    for poly in 0..MATRIX_POLYS {
        let stream = fixed_squeeze_stream(&witness.rho, poly);
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
                top: bytes[2] >> 7,
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
    let mut byte = vec![m31(0); 1usize << ABSORB_LOG_SIZE];
    for pos in 0..34 {
        for poly in 0..MATRIX_POLYS {
            byte[pos * MATRIX_POLYS + poly] = m31(absorb_input(&witness.rho, poly)[pos] as u32);
        }
    }
    if let Some(ExpandATraceAttack::Absorb { row, value }) = attack {
        byte[row] = m31(value);
    }
    vec![col_eval(ABSORB_LOG_SIZE, byte)]
}

fn gen_rejection_base_trace(
    rows: &[RejectionRow],
    attack: Option<ExpandATraceAttack>,
) -> Vec<ColEval> {
    let n_rows = 1usize << REJECTION_LOG_SIZE;
    let mut columns = vec![vec![m31(0); n_rows]; REJECTION_BASE_COLS];
    for (row, value) in rows.iter().enumerate() {
        columns[COL_B0][row] = m31(value.bytes[0]);
        columns[COL_B1][row] = m31(value.bytes[1]);
        columns[COL_B2][row] = m31(value.bytes[2]);
        columns[COL_LOW7][row] = m31(value.low7);
        columns[COL_TOP][row] = m31(value.top);
        columns[COL_SAMPLE][row] = m31(value.sample as u32);
        columns[COL_ACCEPT][row] = m31(value.accept as u32);
        columns[COL_INDEX][row] = m31(value.index);
        columns[COL_ACCEPT_SLACK0][row] = m31(value.accept_slack[0]);
        columns[COL_ACCEPT_SLACK1][row] = m31(value.accept_slack[1]);
        columns[COL_ACCEPT_SLACK2][row] = m31(value.accept_slack[2]);
        columns[COL_REJECT_DELTA][row] = m31(value.reject_delta);
    }
    if let Some(ExpandATraceAttack::Rejection { row, column, value }) = attack {
        columns[column][row] = m31(value);
    }
    columns
        .into_iter()
        .map(|column| col_eval(REJECTION_LOG_SIZE, column))
        .collect()
}

fn range_tuple<E: EvalAtRow>(value: E::F, kind: RcKind) -> [E::F; 2] {
    [value, E::F::from(m31(kind.bound_id()))]
}

#[derive(Clone)]
struct AbsorbEval {
    ns: String,
    stream_base: u32,
    relations: ExpandARelations,
}

impl FrameworkEval for AbsorbEval {
    fn log_size(&self) -> u32 {
        ABSORB_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        ABSORB_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = |name: &str| pre_id(&self.ns, "absorb", name);
        let active = eval.get_preprocessed_column(id("active"));
        let byte_pos = eval.get_preprocessed_column(id("byte_pos"));
        let poly = eval.get_preprocessed_column(id("poly"));
        let absorb_stream = eval.get_preprocessed_column(id("absorb_stream"));
        let rho_first = eval.get_preprocessed_column(id("rho_first"));
        let rho_copy = eval.get_preprocessed_column(id("rho_copy"));
        let domain_gate = eval.get_preprocessed_column(id("domain_gate"));
        let domain_byte = eval.get_preprocessed_column(id("domain_byte"));

        let byte_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [-1, 0]);
        let byte_prev = byte_mask[0].clone();
        let byte = byte_mask[1].clone();
        let one = E::F::one();
        let expected_absorb_stream =
            E::F::from(m31(EXPAND_STREAM_OFFSET)) + E::F::from(m31(EXPAND_STREAM_STRIDE)) * poly;

        eval.add_constraint(active.clone() * (absorb_stream.clone() - expected_absorb_stream));
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
    ns: String,
    stream_base: u32,
    relations: ExpandARelations,
}

impl FrameworkEval for RejectionEval {
    fn log_size(&self) -> u32 {
        REJECTION_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        REJECTION_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = |name: &str| pre_id(&self.ns, "rejection", name);
        let active = eval.get_preprocessed_column(id("active"));
        let first = eval.get_preprocessed_column(id("first"));
        let last = eval.get_preprocessed_column(id("last"));
        let not_first = eval.get_preprocessed_column(id("not_first"));
        let poly = eval.get_preprocessed_column(id("poly"));
        let candidate = eval.get_preprocessed_column(id("candidate"));
        let byte_pos = eval.get_preprocessed_column(id("byte_pos"));
        let squeeze_stream = eval.get_preprocessed_column(id("squeeze_stream"));

        let b0 = eval.next_trace_mask();
        let b1 = eval.next_trace_mask();
        let b2 = eval.next_trace_mask();
        let low7 = eval.next_trace_mask();
        let top = eval.next_trace_mask();
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

        let one = E::F::one();
        let c128 = E::F::from(m31(128));
        let c255 = E::F::from(m31(255));
        let c256 = E::F::from(m31(256));
        let c65536 = E::F::from(m31(1 << 16));
        let q = E::F::from(m31(Q));
        let expected_squeeze_stream = E::F::from(m31(EXPAND_STREAM_OFFSET + 1))
            + E::F::from(m31(EXPAND_STREAM_STRIDE)) * poly.clone();
        let value = b0.clone() + c256.clone() * b1.clone() + c65536.clone() * low7.clone();
        let slack_value =
            slack[0].clone() + c256.clone() * slack[1].clone() + c65536 * slack[2].clone();
        let skip = sample.clone() - accept.clone();

        eval.add_constraint(top.clone() * (one.clone() - top.clone()));
        eval.add_constraint(sample.clone() * (one.clone() - sample.clone()));
        eval.add_constraint(accept.clone() * (one.clone() - accept.clone()));
        eval.add_constraint(accept.clone() * (one.clone() - sample.clone()));
        eval.add_constraint(active.clone() * (byte_pos.clone() - E::F::from(m31(3)) * candidate));
        eval.add_constraint(active.clone() * (squeeze_stream.clone() - expected_squeeze_stream));
        eval.add_constraint(active.clone() * (b2.clone() - low7.clone() - c128 * top.clone()));
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
        let padding = one.clone() - active.clone();
        for cell in [
            b0.clone(),
            b1.clone(),
            b2.clone(),
            low7.clone(),
            top,
            sample.clone(),
            accept.clone(),
            index.clone(),
            slack[0].clone(),
            slack[1].clone(),
            slack[2].clone(),
            reject_delta.clone(),
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
            &self.relations.ntt,
            accept,
            &[poly, E::F::zero(), index, b0, b1, low7],
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
    let mut rows = vec![vec![(zero, one); ABSORB_LOGUP_ENTRIES]; 1usize << ABSORB_LOG_SIZE];
    for pos in 0..34 {
        for poly in 0..MATRIX_POLYS {
            let row = pos * MATRIX_POLYS + poly;
            let byte = absorb_input(&witness.rho, poly)[pos] as u32;
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
    gen_batched_logup(ABSORB_LOG_SIZE, &rows, ABSORB_LOGUP_ENTRIES)
}

fn gen_rejection_interaction(
    rows_data: &[RejectionRow],
    stream_base: u32,
    relations: &ExpandARelations,
) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut rows = vec![vec![(zero, one); REJECTION_LOGUP_ENTRIES]; 1usize << REJECTION_LOG_SIZE];
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
        entries.push(if data.accept {
            (
                one,
                relations.ntt.combine(&[
                    m31(poly as u32),
                    m31(0),
                    m31(data.index),
                    m31(data.bytes[0]),
                    m31(data.bytes[1]),
                    m31(data.low7),
                ]),
            )
        } else {
            (zero, one)
        });
        debug_assert_eq!(entries.len(), REJECTION_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    gen_batched_logup(REJECTION_LOG_SIZE, &rows, REJECTION_LOGUP_ENTRIES)
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
    namespace: &str,
    stream_base: u32,
    relations: &ExpandARelations,
    claim: &ExpandAClaim,
) -> Built {
    Built {
        absorb: FrameworkComponent::new(
            allocator,
            AbsorbEval {
                ns: namespace.to_owned(),
                stream_base,
                relations: relations.clone(),
            },
            claim.absorb_claimed_sum,
        ),
        rejection: FrameworkComponent::new(
            allocator,
            RejectionEval {
                ns: namespace.to_owned(),
                stream_base,
                relations: relations.clone(),
            },
            claim.rejection_claimed_sum,
        ),
    }
}

fn layout() -> TreeLayout {
    let mut preprocessed = vec![ABSORB_LOG_SIZE; ABSORB_PRE_NAMES.len()];
    preprocessed.extend(vec![REJECTION_LOG_SIZE; REJECTION_PRE_NAMES.len()]);
    let mut trace = vec![ABSORB_LOG_SIZE; ABSORB_BASE_COLS];
    trace.extend(vec![REJECTION_LOG_SIZE; REJECTION_BASE_COLS]);
    let mut interaction = vec![ABSORB_LOG_SIZE; ABSORB_INTERACTION_COLS];
    interaction.extend(vec![REJECTION_LOG_SIZE; REJECTION_INTERACTION_COLS]);
    TreeLayout {
        preprocessed,
        trace,
        interaction,
    }
}

fn mix_public(channel: &mut Blake2sChannel, namespace: &str, stream_base: u32) {
    channel.mix_u64(EXPAND_A_MIX_TAG);
    channel.mix_u64(namespace.len() as u64);
    for &byte in namespace.as_bytes() {
        channel.mix_u64(byte as u64);
    }
    channel.mix_u64(stream_base as u64);
    channel.mix_u64(MAX_EXPAND_A_SQUEEZE_BLOCKS as u64);
    channel.mix_u64(MATRIX_POLYS as u64);
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

/// Prover-side U5 module. The caller places the shared range table and Keccak
/// service before it in module order.
pub struct ExpandAProver {
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
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        witness: ExpandAWitness,
        namespace: impl Into<String>,
        stream_base: u32,
        range_handle: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
        bindings: ExpandABindings,
    ) -> Result<Self, ExpandAError> {
        validate_stream_base(stream_base)?;
        validate_stream(&witness)?;
        let rows = build_rejection_rows(&witness);
        let range_uses = rejection_range_uses(&rows);
        Ok(Self {
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

    pub fn claim(&self) -> ExpandAClaim {
        self.claim.clone()
    }

    pub fn range_uses(&self) -> &RcUses {
        &self.range_uses
    }

    pub fn keccak_jobs(&self) -> Result<(Vec<Shape>, Vec<Vec<u8>>), ExpandAError> {
        Ok((
            shake128_job_shapes(self.stream_base)?,
            shake128_absorb_streams(&self.witness.rho),
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
        mix_public(channel, &self.namespace, self.stream_base);
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
        layout()
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
        Ok(gen_expand_a_preprocessed(&self.namespace))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
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
        REJECTION_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        REJECTION_LOG_SIZE + 2
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(gen_expand_a_preprocessed_with_attack(
            &self.namespace,
            self.trace_attack,
        ));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let columns = gen_expand_a_preprocessed_with_attack(&self.namespace, self.trace_attack);
        fingerprint_preprocessed_columns(
            "mldsa_expand_a",
            &expand_a_preprocessed_ids(&self.namespace),
            &columns,
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut trace = gen_absorb_base_trace(&self.witness, self.trace_attack);
        trace.extend(gen_rejection_base_trace(&self.rows, self.trace_attack));
        tb.extend_evals(trace);
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let relations = self.relations().clone();
        let (absorb_trace, absorb_claimed_sum) =
            gen_absorb_interaction(&self.witness, self.stream_base, &relations);
        let (rejection_trace, rejection_claimed_sum) =
            gen_rejection_interaction(&self.rows, self.stream_base, &relations);
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

/// Verifier-side U5 module; all layout data is fixed and `rho` remains private.
pub struct ExpandAVerifier {
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
    pub fn new(
        claim: ExpandAClaim,
        namespace: impl Into<String>,
        stream_base: u32,
        range_handle: SharedRangeRelation,
        keccak_handle: SharedKeccakRelations,
        bindings: ExpandABindings,
    ) -> Result<Self, ExpandAError> {
        validate_stream_base(stream_base)?;
        Ok(Self {
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
        mix_public(channel, &self.namespace, self.stream_base);
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
        layout()
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
        Ok(gen_expand_a_preprocessed(&self.namespace))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.built = Some(build_components(
            allocator,
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
        assert_eq!(ABSORB_PRE_NAMES.len(), 8);
        assert_eq!(REJECTION_PRE_NAMES.len(), 8);
        assert_eq!(ABSORB_BASE_COLS, 1);
        assert_eq!(REJECTION_BASE_COLS, 12);
        assert_eq!(ABSORB_INTERACTION_COLS, 4);
        assert_eq!(REJECTION_INTERACTION_COLS, 12);
        let rho = [17u8; 32];
        let streams = shake128_absorb_streams(&rho);
        let shapes = shake128_job_shapes(256).unwrap();
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
                absorb_stream_id(256, poly).unwrap()
            );
            assert_eq!(
                shapes[poly].squeeze_stream_id,
                squeeze_stream_id(256, poly).unwrap()
            );
        }
    }

    #[test]
    fn canonical_witness_validates_and_matches_reference() {
        let rho = core::array::from_fn(|i| (17 * i + 3) as u8);
        let witness = derive_expand_a_witness(rho).unwrap();
        let counts = validate_stream(&witness).unwrap();
        let reference = crate::reference::expand_a::expand_a(&rho);
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
        let relations = ExpandARelations::dummy();
        let trace = vec![
            cpu_columns(gen_absorb_preprocessed(TEST_NS, attack)),
            cpu_columns(gen_absorb_base_trace(witness, attack)),
            Vec::new(),
        ];
        (0..1usize << ABSORB_LOG_SIZE)
            .map(|row| {
                AbsorbEval {
                    ns: TEST_NS.to_owned(),
                    stream_base: 0,
                    relations: relations.clone(),
                }
                .evaluate(RecordingEvaluator::new(&trace, row, ABSORB_LOG_SIZE))
                .failures
            })
            .sum()
    }

    fn rejection_constraint_failures(
        rows: &[RejectionRow],
        attack: Option<ExpandATraceAttack>,
    ) -> usize {
        const TEST_NS: &str = "expand-a-rejection-eval";
        let relations = ExpandARelations::dummy();
        let trace = vec![
            cpu_columns(gen_rejection_preprocessed(TEST_NS, attack)),
            cpu_columns(gen_rejection_base_trace(rows, attack)),
            Vec::new(),
        ];
        (0..1usize << REJECTION_LOG_SIZE)
            .map(|row| {
                RejectionEval {
                    ns: TEST_NS.to_owned(),
                    stream_base: 0,
                    relations: relations.clone(),
                }
                .evaluate(RecordingEvaluator::new(&trace, row, REJECTION_LOG_SIZE))
                .failures
            })
            .sum()
    }

    fn set_boundary_candidate(row: &mut RejectionRow, value: u32, accept: bool) {
        row.bytes = split_u23(value);
        row.low7 = row.bytes[2] & 0x7f;
        row.top = row.bytes[2] >> 7;
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
        let witness = derive_expand_a_witness([42u8; 32]).unwrap();
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
        rows[done_row].top = 1;

        assert_eq!(rows[accept_rows[0]].accept_slack, [0, 0, 0]);
        assert_eq!(rows[accept_rows[1]].accept_slack[0], 255);
        assert_eq!(rows[accept_rows[2]].accept_slack[2], 127);
        assert_eq!(rows[reject_rows[0]].reject_delta, 0);
        assert_eq!(rows[reject_rows[1]].reject_delta, (1 << 13) - 2);
        assert_eq!(rejection_constraint_failures(&rows, None), 0);
    }

    #[test]
    fn fast_air_adversarial_matrix_rejects() {
        let witness = derive_expand_a_witness([42u8; 32]).unwrap();
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
            ExpandATraceAttack::Preprocessed {
                component: ExpandAPreprocessedComponent::Absorb,
                row: 0,
                column: 2,
                value: 1,
            },
            ExpandATraceAttack::Preprocessed {
                component: ExpandAPreprocessedComponent::Absorb,
                row: 0,
                column: 3,
                value: EXPAND_STREAM_OFFSET + 1,
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
                row: accept_row,
                column: COL_TOP,
                value: 2,
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
            ExpandATraceAttack::Preprocessed {
                component: ExpandAPreprocessedComponent::Rejection,
                row: accept_row,
                column: 4,
                value: 1,
            },
            ExpandATraceAttack::Preprocessed {
                component: ExpandAPreprocessedComponent::Rejection,
                row: accept_row,
                column: 5,
                value: 1,
            },
            ExpandATraceAttack::Preprocessed {
                component: ExpandAPreprocessedComponent::Rejection,
                row: accept_row,
                column: 6,
                value: 1,
            },
            ExpandATraceAttack::Preprocessed {
                component: ExpandAPreprocessedComponent::Rejection,
                row: accept_row,
                column: 7,
                value: EXPAND_STREAM_OFFSET,
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
        let witness = derive_expand_a_witness([9u8; 32]).unwrap();

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
        let full = fixed_squeeze_stream(&bad.rho, extra_poly);
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
        let witness = derive_expand_a_witness([31u8; 32]).unwrap();
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
            validate_stream_with(&witness, |rho, poly| {
                if poly == 7 {
                    stream.clone()
                } else {
                    fixed_squeeze_stream(rho, poly)
                }
            }),
            Err(ExpandAError::SqueezeCapExceeded { poly: 7 })
        );
    }

    #[test]
    fn stream_base_and_polynomial_ids_are_typed_and_field_safe() {
        assert_eq!(
            squeeze_stream_id(MAX_EXPAND_STREAM_BASE, MATRIX_POLYS - 1).unwrap(),
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
                shake128_job_shapes(stream_base),
                Err(ExpandAError::InvalidStreamBase { .. })
            ));
        }
        assert_eq!(
            absorb_stream_id(0, MATRIX_POLYS),
            Err(ExpandAError::PolynomialOutOfRange { poly: MATRIX_POLYS })
        );

        let invalid_base = MAX_EXPAND_STREAM_BASE + 1;
        let prover = ExpandAProver::new(
            derive_expand_a_witness([7u8; 32]).unwrap(),
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
