//! AIR for the complete FIPS 204 `ExpandA(rho)` path.
//!
//! The component pair proves SHAKE128 rejection sampling and the inverse NTT
//! that maps each sampled `A-hat` polynomial to the integer coefficients used
//! by the existing ML-DSA folded identity. Nothing in this module is accepted
//! by a native post-proof verifier.

#![allow(clippy::needless_range_loop)]

use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, INTERACTION_TRACE_IDX, ORIGINAL_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::coeffs::relations::RangeRelation;
use crate::coeffs::tables::RcKind;
use crate::constants::{K, L, N, Q, ZETA};
use crate::reference::ntt::ntt_inverse;
use crate::reference::sponge::shake128;
use crate::sponge_link::ns_prefix;
use crate::witness::B;
use stwo_keccak::relations::HashIoRelation;
use stwo_keccak::sponge::Shape;

pub const MATRIX_POLYS: usize = K * L;
pub const SHAKE128_RATE: usize = 168;
const CANDIDATES_PER_BLOCK: usize = SHAKE128_RATE / 3;
pub const MIN_CANDIDATES: usize = N;
pub const MAX_CANDIDATES: usize = 8 * CANDIDATES_PER_BLOCK;
pub const EXPAND_STREAM_OFFSET: u32 = 16;
pub const EXPAND_STREAM_STRIDE: u32 = 2;
pub const REQUIRED_STREAM_STRIDE: u32 = 128;
const CARRY_OFFSET: i64 = 1 << 12;
const N_INV: u32 = 8_347_681;

relation!(NttCellRelation, 6);
relation!(AEvalRelation, 5);

#[derive(Clone)]
pub struct ExpandARelations {
    pub hash_io: HashIoRelation,
    pub range: RangeRelation,
    pub cell: NttCellRelation,
    pub eval: AEvalRelation,
}

impl ExpandARelations {
    pub fn draw_with(
        channel: &mut impl stwo::core::channel::Channel,
        hash_io: HashIoRelation,
        range: RangeRelation,
    ) -> Self {
        Self {
            hash_io,
            range,
            cell: NttCellRelation::draw(channel),
            eval: AEvalRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            hash_io: HashIoRelation::dummy(),
            range: RangeRelation::dummy(),
            cell: NttCellRelation::dummy(),
            eval: AEvalRelation::dummy(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpandAWitness {
    pub rho: [u8; 32],
    pub candidate_counts: [u16; MATRIX_POLYS],
    pub squeeze_outputs: Vec<Vec<u8>>,
    pub a_hat: Vec<[u32; N]>,
    pub a: Vec<[u32; N]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpandAError {
    CandidateCount,
    Shape,
}

pub fn absorb_stream_id(stream_base: u32, poly: usize) -> u32 {
    stream_base + EXPAND_STREAM_OFFSET + EXPAND_STREAM_STRIDE * poly as u32
}

pub fn squeeze_stream_id(stream_base: u32, poly: usize) -> u32 {
    absorb_stream_id(stream_base, poly) + 1
}

pub fn validate_candidate_counts(counts: &[u16]) -> Result<(), ExpandAError> {
    if counts.len() != MATRIX_POLYS
        || counts
            .iter()
            .any(|&count| !(MIN_CANDIDATES..=MAX_CANDIDATES).contains(&(count as usize)))
    {
        return Err(ExpandAError::CandidateCount);
    }
    Ok(())
}

pub fn shake128_job_shapes(counts: &[u16], stream_base: u32) -> Result<Vec<Shape>, ExpandAError> {
    validate_candidate_counts(counts)?;
    Ok(counts
        .iter()
        .enumerate()
        .map(|(poly, &count)| {
            let blocks = (3 * count as usize).div_ceil(SHAKE128_RATE);
            Shape::shake128(
                34,
                blocks,
                absorb_stream_id(stream_base, poly),
                squeeze_stream_id(stream_base, poly),
            )
        })
        .collect())
}

pub fn shake128_absorb_streams(rho: &[u8; 32]) -> Vec<Vec<u8>> {
    (0..MATRIX_POLYS)
        .map(|poly| {
            let row = poly / L;
            let col = poly % L;
            let mut input = rho.to_vec();
            input.extend([col as u8, row as u8]);
            input
        })
        .collect()
}

pub fn derive_expand_a_witness(rho: [u8; 32]) -> Result<ExpandAWitness, ExpandAError> {
    let expanded = crate::reference::expand_a::expand_a(&rho);
    let mut candidate_counts = [0u16; MATRIX_POLYS];
    let mut squeeze_outputs = Vec::with_capacity(MATRIX_POLYS);
    let mut a_hat = Vec::with_capacity(MATRIX_POLYS);
    let mut a = Vec::with_capacity(MATRIX_POLYS);
    for row in 0..K {
        for col in 0..L {
            let poly = row * L + col;
            let consumed = expanded.transcripts[row][col].squeezed.len();
            if !consumed.is_multiple_of(3) {
                return Err(ExpandAError::Shape);
            }
            let count = consumed / 3;
            if !(MIN_CANDIDATES..=MAX_CANDIDATES).contains(&count) {
                return Err(ExpandAError::CandidateCount);
            }
            candidate_counts[poly] = count as u16;
            let blocks = consumed.div_ceil(SHAKE128_RATE);
            let input = [rho.as_slice(), &[col as u8], &[row as u8]].concat();
            squeeze_outputs.push(shake128(&[&input], blocks * SHAKE128_RATE).0);
            a_hat.push(expanded.matrix[row][col]);
            a.push(ntt_inverse(&expanded.matrix[row][col]));
        }
    }
    Ok(ExpandAWitness {
        rho,
        candidate_counts,
        squeeze_outputs,
        a_hat,
        a,
    })
}

fn zeta_table() -> [u32; N] {
    let mut pow = [0u64; N];
    let mut curr = 1u64;
    for entry in &mut pow {
        *entry = curr;
        curr = curr * ZETA as u64 % Q as u64;
    }
    let mut zetas = [0u32; N];
    for (i, value) in zetas.iter_mut().enumerate() {
        *value = pow[(i as u8).reverse_bits() as usize] as u32;
    }
    zetas
}

#[derive(Clone, Copy)]
struct RejRow {
    poly: usize,
    candidate: usize,
    sample: bool,
    first: bool,
    last: bool,
}

fn rejection_schedule(counts: &[u16]) -> Vec<RejRow> {
    validate_candidate_counts(counts).expect("validated ExpandA candidate counts");
    let mut rows = Vec::new();
    for (poly, &count) in counts.iter().enumerate() {
        let count = count as usize;
        let full = count.div_ceil(CANDIDATES_PER_BLOCK) * CANDIDATES_PER_BLOCK;
        for candidate in 0..full {
            rows.push(RejRow {
                poly,
                candidate,
                sample: candidate < count,
                first: candidate == 0,
                last: candidate + 1 == count,
            });
        }
    }
    rows
}

pub const NTT_STAGES: usize = 8;
pub const NTT_BUTTERFLY_LOG_SIZE: u32 = 15;
pub const NTT_SCALING_LOG_SIZE: u32 = 13;

#[derive(Clone, Copy)]
struct ButterflyRow {
    poly: usize,
    stage: usize,
    index0: usize,
    index1: usize,
    twiddle: u32,
}

#[derive(Clone, Copy)]
struct ScalingRow {
    poly: usize,
    index: usize,
    eval_start: bool,
    eval_end: bool,
}

fn butterfly_schedule() -> Vec<ButterflyRow> {
    let zetas = zeta_table();
    let mut rows = Vec::with_capacity(MATRIX_POLYS * NTT_STAGES * N / 2);
    for poly in 0..MATRIX_POLYS {
        let mut m = N;
        let mut len = 1usize;
        for stage in 0..NTT_STAGES {
            let mut start = 0usize;
            while start < N {
                m -= 1;
                let twiddle = Q - zetas[m];
                for index0 in start..start + len {
                    rows.push(ButterflyRow {
                        poly,
                        stage,
                        index0,
                        index1: index0 + len,
                        twiddle,
                    });
                }
                start += 2 * len;
            }
            len <<= 1;
        }
    }
    rows
}

fn scaling_schedule() -> Vec<ScalingRow> {
    let mut rows = Vec::with_capacity(MATRIX_POLYS * N);
    for poly in 0..MATRIX_POLYS {
        for position in 0..N {
            rows.push(ScalingRow {
                poly,
                index: N - 1 - position,
                eval_start: position == 0,
                eval_end: position + 1 == N,
            });
        }
    }
    rows
}

pub fn rejection_log_size(counts: &[u16]) -> u32 {
    (rejection_schedule(counts).len() as u32)
        .next_power_of_two()
        .ilog2()
        .max(LOG_N_LANES)
}

fn pre_id(ns: &str, component: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{}mldsa_expand_a_{component}_{name}", ns_prefix(ns)),
    }
}

fn ntt_butterfly_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_expand_a_ntt_butterfly_{name}"),
    }
}

fn ntt_scaling_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_expand_a_ntt_scaling_{name}"),
    }
}

const REJ_PRE_NAMES: [&str; 12] = [
    "active",
    "sample",
    "first",
    "last",
    "poly",
    "candidate",
    "byte_pos",
    "absorb_stream",
    "squeeze_stream",
    "not_last",
    "matrix_col",
    "matrix_row",
];

pub fn rejection_preprocessed_ids(ns: &str) -> Vec<PreProcessedColumnId> {
    REJ_PRE_NAMES
        .iter()
        .map(|name| pre_id(ns, "rej", name))
        .collect()
}

pub fn gen_rejection_preprocessed(ns: &str, counts: &[u16]) -> Vec<ColEval> {
    let log_size = rejection_log_size(counts);
    let n_rows = 1usize << log_size;
    let schedule = rejection_schedule(counts);
    let mut columns = vec![vec![m31(0); n_rows]; REJ_PRE_NAMES.len()];
    for (row, item) in schedule.iter().enumerate() {
        columns[0][row] = m31(1);
        columns[1][row] = m31(item.sample as u32);
        columns[2][row] = m31(item.first as u32);
        columns[3][row] = m31(item.last as u32);
        columns[4][row] = m31(item.poly as u32);
        columns[5][row] = m31(item.candidate as u32);
        columns[6][row] = m31((3 * item.candidate) as u32);
        columns[7][row] = m31(absorb_stream_id(0, item.poly));
        columns[8][row] = m31(squeeze_stream_id(0, item.poly));
        columns[9][row] = m31((item.sample && !item.last) as u32);
        columns[10][row] = m31((item.poly % L) as u32);
        columns[11][row] = m31((item.poly / L) as u32);
    }
    let _ = ns;
    columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect()
}

const NTT_BUTTERFLY_PRE_NAMES: [&str; 8] = [
    "active", "poly", "stage", "index0", "index1", "twiddle0", "twiddle1", "twiddle2",
];

const NTT_SCALING_PRE_NAMES: [&str; 5] = ["active", "eval_start", "eval_end", "poly", "index"];

pub fn ntt_preprocessed_ids(_ns: &str) -> Vec<PreProcessedColumnId> {
    let mut ids = Vec::with_capacity(NTT_BUTTERFLY_PRE_NAMES.len() + NTT_SCALING_PRE_NAMES.len());
    ids.extend(
        NTT_BUTTERFLY_PRE_NAMES
            .iter()
            .map(|name| ntt_butterfly_pre_id(name)),
    );
    ids.extend(
        NTT_SCALING_PRE_NAMES
            .iter()
            .map(|name| ntt_scaling_pre_id(name)),
    );
    ids
}

pub fn ntt_preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = vec![NTT_BUTTERFLY_LOG_SIZE; NTT_BUTTERFLY_PRE_NAMES.len()];
    sizes.extend(vec![NTT_SCALING_LOG_SIZE; NTT_SCALING_PRE_NAMES.len()]);
    sizes
}

pub fn gen_ntt_preprocessed(_ns: &str) -> Vec<ColEval> {
    let mut evals = Vec::new();
    let mut columns =
        vec![vec![m31(0); 1usize << NTT_BUTTERFLY_LOG_SIZE]; NTT_BUTTERFLY_PRE_NAMES.len()];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        columns[0][row] = m31(1);
        columns[1][row] = m31(item.poly as u32);
        columns[2][row] = m31(item.stage as u32);
        columns[3][row] = m31(item.index0 as u32);
        columns[4][row] = m31(item.index1 as u32);
        columns[5][row] = m31(item.twiddle & 0xff);
        columns[6][row] = m31((item.twiddle >> 8) & 0xff);
        columns[7][row] = m31(item.twiddle >> 16);
    }
    evals.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_BUTTERFLY_LOG_SIZE, column)),
    );
    let mut columns =
        vec![vec![m31(0); 1usize << NTT_SCALING_LOG_SIZE]; NTT_SCALING_PRE_NAMES.len()];
    for (row, item) in scaling_schedule().iter().enumerate() {
        columns[0][row] = m31(1);
        columns[1][row] = m31(item.eval_start as u32);
        columns[2][row] = m31(item.eval_end as u32);
        columns[3][row] = m31(item.poly as u32);
        columns[4][row] = m31(item.index as u32);
    }
    evals.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_SCALING_LOG_SIZE, column)),
    );
    evals
}

pub fn expand_a_preprocessed_ids(ns: &str) -> Vec<PreProcessedColumnId> {
    let mut ids = rejection_preprocessed_ids(ns);
    ids.extend(ntt_preprocessed_ids(ns));
    ids
}

pub fn gen_expand_a_preprocessed(ns: &str, counts: &[u16]) -> Vec<ColEval> {
    let mut columns = gen_rejection_preprocessed(ns, counts);
    columns.extend(gen_ntt_preprocessed(ns));
    columns
}

const R_B0: usize = 0;
const R_B1: usize = 1;
const R_B2: usize = 2;
const R_LOW7: usize = 3;
const R_TOP: usize = 4;
const R_ACCEPT: usize = 5;
const R_INDEX: usize = 6;
const R_ACCEPT_SLACK0: usize = 7;
const R_ACCEPT_SLACK1: usize = 8;
const R_ACCEPT_SLACK2: usize = 9;
const R_REJECT_DELTA: usize = 10;
pub const REJECTION_BASE_COLS: usize = 11;

fn split_u23(value: u32) -> [u32; 3] {
    [value & 0xff, (value >> 8) & 0xff, value >> 16]
}

fn signed_m31(value: i64) -> M31 {
    const P: i64 = (1 << 31) - 1;
    m31(value.rem_euclid(P) as u32)
}

thread_local! {
    static RANGE_BOUNDARY_ATTACK: core::cell::RefCell<Option<RcKind>> =
        const { core::cell::RefCell::new(None) };
    static NTT_TRACE_ATTACK: core::cell::RefCell<Option<NttTraceAttack>> =
        const { core::cell::RefCell::new(None) };
}

/// Test-only attack that substitutes the first excluded value at every ExpandA
/// use of one fixed range kind. Both AIR and interaction generation take this
/// path, so all arithmetic constraints remain honest and only the range lookup
/// can reject.
#[doc(hidden)]
pub struct ExpandARangeBoundaryGuard;

impl Drop for ExpandARangeBoundaryGuard {
    fn drop(&mut self) {
        RANGE_BOUNDARY_ATTACK.with(|attack| *attack.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_range_boundary_attack(kind: RcKind) -> ExpandARangeBoundaryGuard {
    RANGE_BOUNDARY_ATTACK.with(|attack| *attack.borrow_mut() = Some(kind));
    ExpandARangeBoundaryGuard
}

fn attacked_range_value(kind: RcKind, value: u32) -> u32 {
    RANGE_BOUNDARY_ATTACK.with(|attack| {
        attack
            .borrow()
            .filter(|&attacked| attacked == kind)
            .map_or(value, |_| kind.n_values() as u32)
    })
}

fn range_tuple<E: EvalAtRow>(value: E::F, kind: RcKind) -> [E::F; 2] {
    let value = RANGE_BOUNDARY_ATTACK.with(|attack| {
        attack
            .borrow()
            .filter(|&attacked| attacked == kind)
            .map_or(value, |_| E::F::from(m31(kind.n_values() as u32)))
    });
    [value, E::F::from(m31(kind.bound_id()))]
}

fn range_denominator(relation: &RangeRelation, value: u32, kind: RcKind) -> SecureField {
    relation.combine(&[m31(attacked_range_value(kind, value)), m31(kind.bound_id())])
}

/// Test-only corruption of a production NTT witness column.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NttTraceAttack {
    Quotient,
    FinalCoefficient,
}

#[doc(hidden)]
pub struct NttTraceAttackGuard;

impl Drop for NttTraceAttackGuard {
    fn drop(&mut self) {
        NTT_TRACE_ATTACK.with(|attack| *attack.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_ntt_trace_attack(attack: NttTraceAttack) -> NttTraceAttackGuard {
    NTT_TRACE_ATTACK.with(|installed| *installed.borrow_mut() = Some(attack));
    NttTraceAttackGuard
}

fn ntt_trace_attack() -> Option<NttTraceAttack> {
    NTT_TRACE_ATTACK.with(|attack| *attack.borrow())
}

pub fn gen_rejection_base_trace(witness: &ExpandAWitness) -> (Vec<ColEval>, ExpandARcUses) {
    validate_candidate_counts(&witness.candidate_counts).expect("candidate count shape");
    let schedule = rejection_schedule(&witness.candidate_counts);
    let log_size = rejection_log_size(&witness.candidate_counts);
    let n_rows = 1usize << log_size;
    let mut columns = vec![vec![m31(0); n_rows]; REJECTION_BASE_COLS];
    let mut accepted_index = [0u32; MATRIX_POLYS];
    let mut rc_uses = ExpandARcUses::new();
    for (row, item) in schedule.iter().enumerate() {
        let output = &witness.squeeze_outputs[item.poly];
        let offset = 3 * item.candidate;
        let b0 = output[offset] as u32;
        let b1 = output[offset + 1] as u32;
        let b2 = output[offset + 2] as u32;
        columns[R_B0][row] = m31(b0);
        columns[R_B1][row] = m31(b1);
        columns[R_B2][row] = m31(b2);
        if item.sample {
            let low7 = b2 & 0x7f;
            let value = b0 | (b1 << 8) | (low7 << 16);
            let accept = value < Q;
            columns[R_LOW7][row] = m31(low7);
            push_use(&mut rc_uses.rc7, low7);
            columns[R_TOP][row] = m31(b2 >> 7);
            columns[R_ACCEPT][row] = m31(accept as u32);
            columns[R_INDEX][row] = m31(accepted_index[item.poly]);
            if accept {
                let slack = split_u23(Q - 1 - value);
                columns[R_ACCEPT_SLACK0][row] = m31(slack[0]);
                columns[R_ACCEPT_SLACK1][row] = m31(slack[1]);
                columns[R_ACCEPT_SLACK2][row] = m31(slack[2]);
                push_use(&mut rc_uses.rc8, slack[0]);
                push_use(&mut rc_uses.rc8, slack[1]);
                push_use(&mut rc_uses.rc7, slack[2]);
                accepted_index[item.poly] += 1;
            } else {
                columns[R_REJECT_DELTA][row] = m31(value - Q);
                push_use(&mut rc_uses.rc13, value - Q);
            }
            if !item.last {
                let remaining = 255 - accepted_index[item.poly];
                push_use(&mut rc_uses.rc8, remaining);
            }
        }
    }
    assert!(accepted_index.iter().all(|&value| value == N as u32));
    let trace = columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect();
    (trace, rc_uses)
}

const B_IN0: usize = 0;
const B_IN1: usize = 3;
const B_OUT0: usize = 6;
const B_OUT0_SLACK: usize = 9;
const B_DIFF: usize = 12;
const B_DIFF_SLACK: usize = 15;
const B_OUT1: usize = 18;
const B_OUT1_SLACK: usize = 21;
const B_QUOT: usize = 24;
const B_QUOT_SLACK: usize = 27;
const B_REDUCE: usize = 30;
const B_BORROW: usize = 31;
const B_CARRY: usize = 32;
pub const NTT_BUTTERFLY_BASE_COLS: usize = 36;

const S_IN0: usize = 0;
const S_OUT1: usize = 3;
const S_OUT1_SLACK: usize = 6;
const S_QUOT: usize = 9;
const S_QUOT_SLACK: usize = 12;
const S_CARRY: usize = 15;
const S_DIGIT: usize = 19;
pub const NTT_SCALING_BASE_COLS: usize = 22;

fn write_canonical(
    columns: &mut [Vec<M31>],
    base: usize,
    slack_base: usize,
    row: usize,
    value: u32,
) {
    let value_bytes = split_u23(value);
    let slack_bytes = split_u23(Q - 1 - value);
    for limb in 0..3 {
        columns[base + limb][row] = m31(value_bytes[limb]);
        columns[slack_base + limb][row] = m31(slack_bytes[limb]);
    }
}

fn mul_witness(constant: u32, value: u32) -> (u32, u32, [i64; 4]) {
    let product = constant as u64 * value as u64;
    let output = (product % Q as u64) as u32;
    let quotient = (product / Q as u64) as u32;
    let z = split_u23(constant);
    let x = split_u23(value);
    let q = split_u23(Q);
    let k = split_u23(quotient);
    let out = split_u23(output);
    let e0 = z[0] as i64 * x[0] as i64 - q[0] as i64 * k[0] as i64 - out[0] as i64;
    let c1 = e0 / 256;
    let e1 = z[0] as i64 * x[1] as i64 + z[1] as i64 * x[0] as i64
        - q[0] as i64 * k[1] as i64
        - q[1] as i64 * k[0] as i64
        - out[1] as i64
        + c1;
    let c2 = e1 / 256;
    let e2 = z[0] as i64 * x[2] as i64 + z[1] as i64 * x[1] as i64 + z[2] as i64 * x[0] as i64
        - q[0] as i64 * k[2] as i64
        - q[1] as i64 * k[1] as i64
        - q[2] as i64 * k[0] as i64
        - out[2] as i64
        + c2;
    let c3 = e2 / 256;
    let e3 = z[1] as i64 * x[2] as i64 + z[2] as i64 * x[1] as i64
        - q[1] as i64 * k[2] as i64
        - q[2] as i64 * k[1] as i64
        + c3;
    let c4 = e3 / 256;
    debug_assert_eq!(e0, 256 * c1);
    debug_assert_eq!(e1, 256 * c2);
    debug_assert_eq!(e2, 256 * c3);
    debug_assert_eq!(e3, 256 * c4);
    debug_assert_eq!(
        z[2] as i64 * x[2] as i64 - q[2] as i64 * k[2] as i64 + c4,
        0
    );
    (output, quotient, [c1, c2, c3, c4])
}

fn balanced3(mut value: i64) -> [i64; 3] {
    let mut digits = [0i64; 3];
    for digit in &mut digits {
        let mut rem = value.rem_euclid(B as i64);
        if rem >= B as i64 / 2 {
            rem -= B as i64;
        }
        *digit = rem;
        value = (value - rem) / B as i64;
    }
    assert_eq!(value, 0);
    digits
}

pub struct NttBaseTraces {
    pub butterfly: Vec<ColEval>,
    pub scaling: Vec<ColEval>,
    pub rc_uses: ExpandARcUses,
}

pub fn gen_ntt_base_traces(witness: &ExpandAWitness) -> NttBaseTraces {
    let mut states = witness.a_hat.clone();
    let mut rc_uses = ExpandARcUses::new();
    let mut columns = vec![vec![m31(0); 1usize << NTT_BUTTERFLY_LOG_SIZE]; NTT_BUTTERFLY_BASE_COLS];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        let input0 = states[item.poly][item.index0];
        let input1 = states[item.poly][item.index1];
        let in0 = split_u23(input0);
        let in1 = split_u23(input1);
        for limb in 0..3 {
            columns[B_IN0 + limb][row] = m31(in0[limb]);
            columns[B_IN1 + limb][row] = m31(in1[limb]);
        }
        let sum = input0 + input1;
        let reduce = sum >= Q;
        let output0 = if reduce { sum - Q } else { sum };
        let borrow = input0 < input1;
        let diff = if borrow {
            input0 + Q - input1
        } else {
            input0 - input1
        };
        write_canonical(&mut columns, B_OUT0, B_OUT0_SLACK, row, output0);
        write_canonical(&mut columns, B_DIFF, B_DIFF_SLACK, row, diff);
        record_canonical_uses(&mut rc_uses, output0);
        record_canonical_uses(&mut rc_uses, diff);
        columns[B_REDUCE][row] = m31(reduce as u32);
        columns[B_BORROW][row] = m31(borrow as u32);
        states[item.poly][item.index0] = output0;
        let (output1, quotient, carries) = mul_witness(item.twiddle, diff);
        write_canonical(&mut columns, B_OUT1, B_OUT1_SLACK, row, output1);
        write_canonical(&mut columns, B_QUOT, B_QUOT_SLACK, row, quotient);
        record_canonical_uses(&mut rc_uses, output1);
        record_canonical_uses(&mut rc_uses, quotient);
        for limb in 0..4 {
            columns[B_CARRY + limb][row] = signed_m31(carries[limb]);
            push_use(&mut rc_uses.rc13, (carries[limb] + CARRY_OFFSET) as u32);
        }
        states[item.poly][item.index1] = output1;
    }
    if ntt_trace_attack() == Some(NttTraceAttack::Quotient) {
        columns[B_QUOT][0] += m31(1);
    }
    let butterfly = columns
        .into_iter()
        .map(|column| col_eval(NTT_BUTTERFLY_LOG_SIZE, column))
        .collect();

    let mut columns = vec![vec![m31(0); 1usize << NTT_SCALING_LOG_SIZE]; NTT_SCALING_BASE_COLS];
    for (row, item) in scaling_schedule().iter().enumerate() {
        let input = states[item.poly][item.index];
        let input_limbs = split_u23(input);
        for limb in 0..3 {
            columns[S_IN0 + limb][row] = m31(input_limbs[limb]);
        }
        let (output, quotient, carries) = mul_witness(N_INV, input);
        write_canonical(&mut columns, S_OUT1, S_OUT1_SLACK, row, output);
        write_canonical(&mut columns, S_QUOT, S_QUOT_SLACK, row, quotient);
        record_canonical_uses(&mut rc_uses, output);
        record_canonical_uses(&mut rc_uses, quotient);
        for limb in 0..4 {
            columns[S_CARRY + limb][row] = signed_m31(carries[limb]);
            push_use(&mut rc_uses.rc13, (carries[limb] + CARRY_OFFSET) as u32);
        }
        let digits = balanced3(output as i64);
        for limb in 0..3 {
            columns[S_DIGIT + limb][row] = signed_m31(digits[limb]);
            push_use(&mut rc_uses.rc9, (digits[limb] + 256) as u32);
        }
        debug_assert_eq!(output, witness.a[item.poly][item.index]);
    }
    if ntt_trace_attack() == Some(NttTraceAttack::FinalCoefficient) {
        columns[S_OUT1][0] += m31(1);
    }
    let scaling = columns
        .into_iter()
        .map(|column| col_eval(NTT_SCALING_LOG_SIZE, column))
        .collect();
    NttBaseTraces {
        butterfly,
        scaling,
        rc_uses,
    }
}

pub const REJECTION_LOGUP_ENTRIES: usize = 44;
pub const LOGUP_BATCH: usize = 4;
pub const NTT_BUTTERFLY_LOGUP_ENTRIES: usize = 32;
pub const NTT_SCALING_LOGUP_ENTRIES: usize = 21;
pub const REJECTION_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * REJECTION_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
pub const NTT_BUTTERFLY_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * NTT_BUTTERFLY_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
pub const NTT_SCALING_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE
    + SECURE_EXTENSION_DEGREE * NTT_SCALING_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

#[derive(Clone)]
pub struct RejectionEval {
    pub ns: String,
    pub log_size: u32,
    pub stream_base: u32,
    pub rho: [u8; 32],
    pub relations: ExpandARelations,
}

impl FrameworkEval for RejectionEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = |name: &str| pre_id(&self.ns, "rej", name);
        let active = eval.get_preprocessed_column(id("active"));
        let sample = eval.get_preprocessed_column(id("sample"));
        let first = eval.get_preprocessed_column(id("first"));
        let last = eval.get_preprocessed_column(id("last"));
        let poly = eval.get_preprocessed_column(id("poly"));
        let byte_pos = eval.get_preprocessed_column(id("byte_pos"));
        let absorb_stream = eval.get_preprocessed_column(id("absorb_stream"));
        let squeeze_stream = eval.get_preprocessed_column(id("squeeze_stream"));
        let not_last = eval.get_preprocessed_column(id("not_last"));
        let matrix_col = eval.get_preprocessed_column(id("matrix_col"));
        let matrix_row = eval.get_preprocessed_column(id("matrix_row"));

        let b0 = eval.next_trace_mask();
        let b1 = eval.next_trace_mask();
        let b2 = eval.next_trace_mask();
        let low7 = eval.next_trace_mask();
        let top = eval.next_trace_mask();
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
        let q = E::F::from(m31(Q));
        let q_minus_one = E::F::from(m31(Q - 1));
        let two56 = E::F::from(m31(256));
        let two16 = E::F::from(m31(1 << 16));
        let value = b0.clone() + two56.clone() * b1.clone() + two16 * low7.clone();
        let slack_value = slack[0].clone()
            + two56.clone() * slack[1].clone()
            + E::F::from(m31(1 << 16)) * slack[2].clone();

        eval.add_constraint(top.clone() * (one.clone() - top.clone()));
        eval.add_constraint(accept.clone() * (one.clone() - accept.clone()));
        eval.add_constraint(
            sample.clone() * (b2.clone() - low7.clone() - E::F::from(m31(128)) * top.clone()),
        );
        eval.add_constraint(accept.clone() * (value.clone() + slack_value - q_minus_one));
        let reject = sample.clone() - accept.clone();
        eval.add_constraint(reject.clone() * (value.clone() - q - reject_delta.clone()));
        eval.add_constraint(first.clone() * index.clone());
        eval.add_constraint(
            (sample.clone() - first.clone()) * (index.clone() - index_prev - accept_prev),
        );
        eval.add_constraint(
            last.clone() * (index.clone() + accept.clone() - E::F::from(m31(N as u32))),
        );

        let off = one.clone() - sample.clone();
        for value in [
            low7.clone(),
            top,
            accept.clone(),
            index.clone(),
            slack[0].clone(),
            slack[1].clone(),
            slack[2].clone(),
            reject_delta.clone(),
        ] {
            eval.add_constraint(off.clone() * value);
        }

        let stream_base = E::F::from(m31(self.stream_base));
        for position in 0..34 {
            let byte = if position < 32 {
                E::F::from(m31(self.rho[position] as u32))
            } else if position == 32 {
                matrix_col.clone()
            } else {
                matrix_row.clone()
            };
            eval.add_to_relation(RelationEntry::base(
                &self.relations.hash_io,
                first.clone(),
                &[
                    stream_base.clone() + absorb_stream.clone(),
                    E::F::from(m31(position as u32)),
                    byte,
                ],
            ));
        }
        for limb in 0..3 {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.hash_io,
                -active.clone(),
                &[
                    stream_base.clone() + squeeze_stream.clone(),
                    byte_pos.clone() + E::F::from(m31(limb as u32)),
                    [b0.clone(), b1.clone(), b2.clone()][limb].clone(),
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            sample.clone(),
            &range_tuple::<E>(low7.clone(), RcKind::Rc7),
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
            reject,
            &range_tuple::<E>(reject_delta, RcKind::Rc13),
        ));
        let remaining = E::F::from(m31(255)) - index.clone() - accept.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            not_last,
            &range_tuple::<E>(remaining, RcKind::Rc8),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            accept,
            &[poly, E::F::zero(), index, b0, b1, low7],
        ));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

fn recompose3<F: Clone + core::ops::Add<Output = F> + core::ops::Mul<Output = F>>(
    bytes: &[F; 3],
    c256: F,
    c65536: F,
) -> F {
    bytes[0].clone() + c256 * bytes[1].clone() + c65536 * bytes[2].clone()
}

fn add_mul_constraints<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    twiddle: &[E::F; 3],
    input: &[E::F; 3],
    quotient: &[E::F; 3],
    output: &[E::F; 3],
    carries: &[E::F; 4],
) {
    let q = [m31(Q & 0xff), m31((Q >> 8) & 0xff), m31(Q >> 16)];
    let e0 = twiddle[0].clone() * input[0].clone()
        - E::F::from(q[0]) * quotient[0].clone()
        - output[0].clone();
    eval.add_constraint(gate.clone() * (e0 - E::F::from(m31(256)) * carries[0].clone()));
    let e1 = twiddle[0].clone() * input[1].clone() + twiddle[1].clone() * input[0].clone()
        - E::F::from(q[0]) * quotient[1].clone()
        - E::F::from(q[1]) * quotient[0].clone()
        - output[1].clone()
        + carries[0].clone();
    eval.add_constraint(gate.clone() * (e1 - E::F::from(m31(256)) * carries[1].clone()));
    let e2 = twiddle[0].clone() * input[2].clone()
        + twiddle[1].clone() * input[1].clone()
        + twiddle[2].clone() * input[0].clone()
        - E::F::from(q[0]) * quotient[2].clone()
        - E::F::from(q[1]) * quotient[1].clone()
        - E::F::from(q[2]) * quotient[0].clone()
        - output[2].clone()
        + carries[1].clone();
    eval.add_constraint(gate.clone() * (e2 - E::F::from(m31(256)) * carries[2].clone()));
    let e3 = twiddle[1].clone() * input[2].clone() + twiddle[2].clone() * input[1].clone()
        - E::F::from(q[1]) * quotient[2].clone()
        - E::F::from(q[2]) * quotient[1].clone()
        + carries[2].clone();
    eval.add_constraint(gate.clone() * (e3 - E::F::from(m31(256)) * carries[3].clone()));
    let e4 = twiddle[2].clone() * input[2].clone() - E::F::from(q[2]) * quotient[2].clone()
        + carries[3].clone();
    eval.add_constraint(gate * e4);
}

fn add_canonical_constraint<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    bytes: &[E::F; 3],
    slack: &[E::F; 3],
) {
    let c256 = E::F::from(m31(256));
    let c65536 = E::F::from(m31(1 << 16));
    eval.add_constraint(
        gate * (recompose3(bytes, c256.clone(), c65536.clone()) + recompose3(slack, c256, c65536)
            - E::F::from(m31(Q - 1))),
    );
}

fn add_canonical_range_lookups<E: EvalAtRow>(
    eval: &mut E,
    relation: &RangeRelation,
    gate: E::F,
    bytes: &[E::F; 3],
    slack: &[E::F; 3],
) {
    for limb in 0..2 {
        eval.add_to_relation(RelationEntry::base(
            relation,
            gate.clone(),
            &range_tuple::<E>(bytes[limb].clone(), RcKind::Rc8),
        ));
        eval.add_to_relation(RelationEntry::base(
            relation,
            gate.clone(),
            &range_tuple::<E>(slack[limb].clone(), RcKind::Rc8),
        ));
    }
    eval.add_to_relation(RelationEntry::base(
        relation,
        gate.clone(),
        &range_tuple::<E>(bytes[2].clone(), RcKind::Rc7),
    ));
    eval.add_to_relation(RelationEntry::base(
        relation,
        gate,
        &range_tuple::<E>(slack[2].clone(), RcKind::Rc7),
    ));
}

#[derive(Clone)]
pub struct NttButterflyEval {
    pub relations: ExpandARelations,
}

impl FrameworkEval for NttButterflyEval {
    fn log_size(&self) -> u32 {
        NTT_BUTTERFLY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = ntt_butterfly_pre_id;
        let active = eval.get_preprocessed_column(id("active"));
        let poly = eval.get_preprocessed_column(id("poly"));
        let stage = eval.get_preprocessed_column(id("stage"));
        let index0 = eval.get_preprocessed_column(id("index0"));
        let index1 = eval.get_preprocessed_column(id("index1"));
        let twiddle = [
            eval.get_preprocessed_column(id("twiddle0")),
            eval.get_preprocessed_column(id("twiddle1")),
            eval.get_preprocessed_column(id("twiddle2")),
        ];

        let input0 = core::array::from_fn(|_| eval.next_trace_mask());
        let input1 = core::array::from_fn(|_| eval.next_trace_mask());
        let output0 = core::array::from_fn(|_| eval.next_trace_mask());
        let output0_slack = core::array::from_fn(|_| eval.next_trace_mask());
        let diff = core::array::from_fn(|_| eval.next_trace_mask());
        let diff_slack = core::array::from_fn(|_| eval.next_trace_mask());
        let output1 = core::array::from_fn(|_| eval.next_trace_mask());
        let output1_slack = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient_slack = core::array::from_fn(|_| eval.next_trace_mask());
        let reduce = eval.next_trace_mask();
        let borrow = eval.next_trace_mask();
        let carries = [
            eval.next_trace_mask(),
            eval.next_trace_mask(),
            eval.next_trace_mask(),
            eval.next_trace_mask(),
        ];

        let one = E::F::one();
        let c256 = E::F::from(m31(256));
        let c65536 = E::F::from(m31(1 << 16));
        let q = E::F::from(m31(Q));
        let input0_value = recompose3(&input0, c256.clone(), c65536.clone());
        let input1_value = recompose3(&input1, c256.clone(), c65536.clone());
        let output0_value = recompose3(&output0, c256.clone(), c65536.clone());
        let diff_value = recompose3(&diff, c256.clone(), c65536.clone());

        eval.add_constraint(reduce.clone() * (one.clone() - reduce.clone()));
        eval.add_constraint(borrow.clone() * (one.clone() - borrow.clone()));
        eval.add_constraint(
            active.clone()
                * (input0_value.clone() + input1_value.clone()
                    - output0_value.clone()
                    - q.clone() * reduce.clone()),
        );
        eval.add_constraint(
            active.clone()
                * (input0_value.clone() + q.clone() * borrow.clone()
                    - input1_value.clone()
                    - diff_value.clone()),
        );
        for (bytes, slack) in [
            (&output0, &output0_slack),
            (&diff, &diff_slack),
            (&output1, &output1_slack),
            (&quotient, &quotient_slack),
        ] {
            add_canonical_constraint(&mut eval, active.clone(), bytes, slack);
        }
        add_mul_constraints(
            &mut eval,
            active.clone(),
            &twiddle,
            &diff,
            &quotient,
            &output1,
            &carries,
        );

        let next_stage = stage.clone() + one;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            -active.clone(),
            &[
                poly.clone(),
                stage.clone(),
                index0.clone(),
                input0[0].clone(),
                input0[1].clone(),
                input0[2].clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            -active.clone(),
            &[
                poly.clone(),
                stage.clone(),
                index1.clone(),
                input1[0].clone(),
                input1[1].clone(),
                input1[2].clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            active.clone(),
            &[
                poly.clone(),
                next_stage.clone(),
                index0,
                output0[0].clone(),
                output0[1].clone(),
                output0[2].clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            active.clone(),
            &[
                poly.clone(),
                next_stage,
                index1,
                output1[0].clone(),
                output1[1].clone(),
                output1[2].clone(),
            ],
        ));

        for (bytes, slack) in [
            (&output0, &output0_slack),
            (&diff, &diff_slack),
            (&output1, &output1_slack),
            (&quotient, &quotient_slack),
        ] {
            add_canonical_range_lookups(
                &mut eval,
                &self.relations.range,
                active.clone(),
                bytes,
                slack,
            );
        }
        for carry in &carries {
            let shifted = carry.clone() + E::F::from(m31(CARRY_OFFSET as u32));
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(shifted, RcKind::Rc13),
            ));
        }
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

#[derive(Clone)]
pub struct NttScalingEval {
    pub r: SecureField,
    pub s: SecureField,
    pub relations: ExpandARelations,
}

impl FrameworkEval for NttScalingEval {
    fn log_size(&self) -> u32 {
        NTT_SCALING_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(ntt_scaling_pre_id("active"));
        let eval_start = eval.get_preprocessed_column(ntt_scaling_pre_id("eval_start"));
        let eval_end = eval.get_preprocessed_column(ntt_scaling_pre_id("eval_end"));
        let poly = eval.get_preprocessed_column(ntt_scaling_pre_id("poly"));
        let index = eval.get_preprocessed_column(ntt_scaling_pre_id("index"));

        let input: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let output: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let output_slack: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient_slack: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let carries: [E::F; 4] = core::array::from_fn(|_| eval.next_trace_mask());
        let digits: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let acc_masks: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(acc_masks.each_ref().map(|mask| mask[0].clone()));
        let acc_cur = E::combine_ef(acc_masks.each_ref().map(|mask| mask[1].clone()));

        add_canonical_constraint(&mut eval, active.clone(), &output, &output_slack);
        add_canonical_constraint(&mut eval, active.clone(), &quotient, &quotient_slack);
        let twiddle = split_u23(N_INV).map(|value| E::F::from(m31(value)));
        add_mul_constraints(
            &mut eval,
            active.clone(),
            &twiddle,
            &input,
            &quotient,
            &output,
            &carries,
        );

        let output_value = recompose3(&output, E::F::from(m31(256)), E::F::from(m31(1 << 16)));
        let digit_value = digits[0].clone()
            + E::F::from(m31(B as u32)) * digits[1].clone()
            + E::F::from(m31((B * B) as u32)) * digits[2].clone();
        eval.add_constraint(active.clone() * (output_value - digit_value));

        let mut s_power = SecureField::one();
        let mut digit_row = E::EF::zero();
        for digit in &digits {
            digit_row += E::EF::from(digit.clone()) * E::EF::from(s_power);
            s_power *= self.s;
        }
        let expected_acc = E::EF::from(active.clone())
            * (E::EF::from(E::F::one() - eval_start) * acc_prev * E::EF::from(self.r) + digit_row);
        eval.add_constraint(acc_cur - expected_acc);

        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            -active.clone(),
            &[
                poly.clone(),
                E::F::from(m31(NTT_STAGES as u32)),
                index,
                input[0].clone(),
                input[1].clone(),
                input[2].clone(),
            ],
        ));
        add_canonical_range_lookups(
            &mut eval,
            &self.relations.range,
            active.clone(),
            &output,
            &output_slack,
        );
        add_canonical_range_lookups(
            &mut eval,
            &self.relations.range,
            active.clone(),
            &quotient,
            &quotient_slack,
        );
        for carry in &carries {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(
                    carry.clone() + E::F::from(m31(CARRY_OFFSET as u32)),
                    RcKind::Rc13,
                ),
            ));
        }
        for digit in &digits {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(digit.clone() + E::F::from(m31(256)), RcKind::Rc9),
            ));
        }
        let mut tuple = vec![poly];
        tuple.extend(acc_masks.iter().map(|mask| mask[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.relations.eval, -eval_end, &tuple));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

pub type RejectionComponent = FrameworkComponent<RejectionEval>;
pub type NttButterflyComponent = FrameworkComponent<NttButterflyEval>;
pub type NttScalingComponent = FrameworkComponent<NttScalingEval>;

#[derive(Clone, Debug)]
pub struct ExpandARcUses {
    pub rc9: Vec<u32>,
    pub rc13: Vec<u32>,
    pub rc8: Vec<u32>,
    pub rc7: Vec<u32>,
}

impl ExpandARcUses {
    pub fn new() -> Self {
        Self {
            rc9: vec![0; RcKind::Rc9.n_values()],
            rc13: vec![0; RcKind::Rc13.n_values()],
            rc8: vec![0; RcKind::Rc8.n_values()],
            rc7: vec![0; RcKind::Rc7.n_values()],
        }
    }

    pub fn add_assign(&mut self, other: &Self) {
        for (dst, src) in self.rc9.iter_mut().zip(&other.rc9) {
            *dst += src;
        }
        for (dst, src) in self.rc13.iter_mut().zip(&other.rc13) {
            *dst += src;
        }
        for (dst, src) in self.rc8.iter_mut().zip(&other.rc8) {
            *dst += src;
        }
        for (dst, src) in self.rc7.iter_mut().zip(&other.rc7) {
            *dst += src;
        }
    }

    pub fn for_kind(&self, kind: RcKind) -> &[u32] {
        match kind {
            RcKind::Rc9 => &self.rc9,
            RcKind::Rc13 => &self.rc13,
            RcKind::Rc8 => &self.rc8,
            RcKind::Rc7 => &self.rc7,
            RcKind::Ternary => &[],
        }
    }
}

impl Default for ExpandARcUses {
    fn default() -> Self {
        Self::new()
    }
}

fn push_use(uses: &mut [u32], value: u32) {
    uses[value as usize] += 1;
}

fn record_canonical_uses(uses: &mut ExpandARcUses, value: u32) {
    let bytes = split_u23(value);
    let slack = split_u23(Q - 1 - value);
    for limb in 0..2 {
        push_use(&mut uses.rc8, bytes[limb]);
        push_use(&mut uses.rc8, slack[limb]);
    }
    push_use(&mut uses.rc7, bytes[2]);
    push_use(&mut uses.rc7, slack[2]);
}

fn combine_batch(entries: &[(SecureField, SecureField)]) -> (SecureField, SecureField) {
    let mut num = entries[0].0;
    let mut den = entries[0].1;
    for &(next_num, next_den) in &entries[1..] {
        num = next_den * num + next_num * den;
        den *= next_den;
    }
    (num, den)
}

fn gen_batched_logup(
    log_size: u32,
    rows: &[Vec<(SecureField, SecureField)>],
) -> (Vec<ColEval>, SecureField) {
    let entry_count = rows.first().map_or(0, Vec::len);
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
                let (num, den) = combine_batch(&rows[coset][start..end]);
                numerators[lane] = num;
                denominators[lane] = den;
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

pub struct RejectionInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    pub rc_uses: ExpandARcUses,
}

pub fn gen_rejection_interaction(
    witness: &ExpandAWitness,
    stream_base: u32,
    relations: &ExpandARelations,
) -> RejectionInteraction {
    let schedule = rejection_schedule(&witness.candidate_counts);
    let log_size = rejection_log_size(&witness.candidate_counts);
    let n_rows = 1usize << log_size;
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut rows = vec![vec![(zero, one); REJECTION_LOGUP_ENTRIES]; n_rows];
    let mut rc_uses = ExpandARcUses::new();
    let mut accepted_index = [0u32; MATRIX_POLYS];

    for (row, item) in schedule.iter().enumerate() {
        let output = &witness.squeeze_outputs[item.poly];
        let offset = 3 * item.candidate;
        let bytes = [output[offset], output[offset + 1], output[offset + 2]];
        let mut entries = Vec::with_capacity(REJECTION_LOGUP_ENTRIES);
        let absorb = absorb_stream_id(stream_base, item.poly);
        let squeeze = squeeze_stream_id(stream_base, item.poly);
        let absorb_bytes = {
            let mut value = witness.rho.to_vec();
            value.extend([(item.poly % L) as u8, (item.poly / L) as u8]);
            value
        };
        for position in 0..34 {
            if item.first {
                let den = relations.hash_io.combine(&[
                    m31(absorb),
                    m31(position as u32),
                    m31(absorb_bytes[position] as u32),
                ]);
                entries.push((one, den));
            } else {
                entries.push((zero, one));
            }
        }
        for (limb, &byte) in bytes.iter().enumerate() {
            let den = relations.hash_io.combine(&[
                m31(squeeze),
                m31((offset + limb) as u32),
                m31(byte as u32),
            ]);
            entries.push((-one, den));
        }

        if item.sample {
            let low7 = (bytes[2] & 0x7f) as u32;
            let value = bytes[0] as u32 | (bytes[1] as u32) << 8 | low7 << 16;
            entries.push((one, range_denominator(&relations.range, low7, RcKind::Rc7)));
            push_use(&mut rc_uses.rc7, low7);
            let accept = value < Q;
            if accept {
                let slack = split_u23(Q - 1 - value);
                entries.push((
                    one,
                    range_denominator(&relations.range, slack[0], RcKind::Rc8),
                ));
                entries.push((
                    one,
                    range_denominator(&relations.range, slack[1], RcKind::Rc8),
                ));
                entries.push((
                    one,
                    range_denominator(&relations.range, slack[2], RcKind::Rc7),
                ));
                push_use(&mut rc_uses.rc8, slack[0]);
                push_use(&mut rc_uses.rc8, slack[1]);
                push_use(&mut rc_uses.rc7, slack[2]);
            } else {
                entries.extend([(zero, one); 3]);
            }
            if accept {
                entries.push((zero, one));
            } else {
                let delta = value - Q;
                entries.push((
                    one,
                    range_denominator(&relations.range, delta, RcKind::Rc13),
                ));
                push_use(&mut rc_uses.rc13, delta);
            }
            if item.last {
                entries.push((zero, one));
            } else {
                let remaining = 255 - accepted_index[item.poly] - u32::from(accept);
                entries.push((
                    one,
                    range_denominator(&relations.range, remaining, RcKind::Rc8),
                ));
                push_use(&mut rc_uses.rc8, remaining);
            }
            if accept {
                let den = relations.cell.combine(&[
                    m31(item.poly as u32),
                    m31(0),
                    m31(accepted_index[item.poly]),
                    m31(bytes[0] as u32),
                    m31(bytes[1] as u32),
                    m31(low7),
                ]);
                entries.push((one, den));
                accepted_index[item.poly] += 1;
            } else {
                entries.push((zero, one));
            }
        } else {
            entries.extend([(zero, one); 7]);
        }
        assert_eq!(entries.len(), REJECTION_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    assert!(accepted_index.iter().all(|&value| value == N as u32));
    let (trace, claimed_sum) = gen_batched_logup(log_size, &rows);
    RejectionInteraction {
        trace,
        claimed_sum,
        rc_uses,
    }
}

pub struct NttComponentInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
}

pub struct NttInteractions {
    pub butterfly: NttComponentInteraction,
    pub scaling: NttComponentInteraction,
    pub rc_uses: ExpandARcUses,
    pub a_evals: Vec<SecureField>,
}

fn range_entries(
    entries: &mut Vec<(SecureField, SecureField)>,
    uses: &mut ExpandARcUses,
    relations: &ExpandARelations,
    value: u32,
) {
    let bytes = split_u23(value);
    let slack = split_u23(Q - 1 - value);
    for limb in 0..2 {
        entries.push((
            SecureField::one(),
            range_denominator(&relations.range, bytes[limb], RcKind::Rc8),
        ));
        entries.push((
            SecureField::one(),
            range_denominator(&relations.range, slack[limb], RcKind::Rc8),
        ));
        push_use(&mut uses.rc8, bytes[limb]);
        push_use(&mut uses.rc8, slack[limb]);
    }
    entries.push((
        SecureField::one(),
        range_denominator(&relations.range, bytes[2], RcKind::Rc7),
    ));
    entries.push((
        SecureField::one(),
        range_denominator(&relations.range, slack[2], RcKind::Rc7),
    ));
    push_use(&mut uses.rc7, bytes[2]);
    push_use(&mut uses.rc7, slack[2]);
}

pub fn gen_ntt_interactions(
    witness: &ExpandAWitness,
    r: SecureField,
    s: SecureField,
    relations: &ExpandARelations,
) -> NttInteractions {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut rc_uses = ExpandARcUses::new();
    let mut states = witness.a_hat.clone();
    let mut rows =
        vec![vec![(zero, one); NTT_BUTTERFLY_LOGUP_ENTRIES]; 1usize << NTT_BUTTERFLY_LOG_SIZE];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        let input0 = states[item.poly][item.index0];
        let input1 = states[item.poly][item.index1];
        let input0_bytes = split_u23(input0);
        let input1_bytes = split_u23(input1);
        let mut entries = Vec::with_capacity(NTT_BUTTERFLY_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.cell.combine(&[
                m31(item.poly as u32),
                m31(item.stage as u32),
                m31(item.index0 as u32),
                m31(input0_bytes[0]),
                m31(input0_bytes[1]),
                m31(input0_bytes[2]),
            ]),
        ));
        entries.push((
            -one,
            relations.cell.combine(&[
                m31(item.poly as u32),
                m31(item.stage as u32),
                m31(item.index1 as u32),
                m31(input1_bytes[0]),
                m31(input1_bytes[1]),
                m31(input1_bytes[2]),
            ]),
        ));
        let sum = input0 + input1;
        let output0 = if sum >= Q { sum - Q } else { sum };
        let diff = if input0 < input1 {
            input0 + Q - input1
        } else {
            input0 - input1
        };
        let (output1, quotient, carries) = mul_witness(item.twiddle, diff);
        let output0_bytes = split_u23(output0);
        let output1_bytes = split_u23(output1);
        entries.push((
            one,
            relations.cell.combine(&[
                m31(item.poly as u32),
                m31((item.stage + 1) as u32),
                m31(item.index0 as u32),
                m31(output0_bytes[0]),
                m31(output0_bytes[1]),
                m31(output0_bytes[2]),
            ]),
        ));
        entries.push((
            one,
            relations.cell.combine(&[
                m31(item.poly as u32),
                m31((item.stage + 1) as u32),
                m31(item.index1 as u32),
                m31(output1_bytes[0]),
                m31(output1_bytes[1]),
                m31(output1_bytes[2]),
            ]),
        ));
        states[item.poly][item.index0] = output0;
        states[item.poly][item.index1] = output1;
        for value in [output0, diff, output1, quotient] {
            range_entries(&mut entries, &mut rc_uses, relations, value);
        }
        for carry in carries {
            let shifted = (carry + CARRY_OFFSET) as u32;
            entries.push((
                one,
                range_denominator(&relations.range, shifted, RcKind::Rc13),
            ));
            push_use(&mut rc_uses.rc13, shifted);
        }
        assert_eq!(entries.len(), NTT_BUTTERFLY_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    let (trace, claimed_sum) = gen_batched_logup(NTT_BUTTERFLY_LOG_SIZE, &rows);
    let butterfly = NttComponentInteraction { trace, claimed_sum };

    let mut rows =
        vec![vec![(zero, one); NTT_SCALING_LOGUP_ENTRIES]; 1usize << NTT_SCALING_LOG_SIZE];
    let mut acc = vec![zero; 1usize << NTT_SCALING_LOG_SIZE];
    let mut a_evals = vec![zero; MATRIX_POLYS];
    let mut running = zero;
    for (row, item) in scaling_schedule().iter().enumerate() {
        let input = states[item.poly][item.index];
        let input_bytes = split_u23(input);
        let mut entries = Vec::with_capacity(NTT_SCALING_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.cell.combine(&[
                m31(item.poly as u32),
                m31(NTT_STAGES as u32),
                m31(item.index as u32),
                m31(input_bytes[0]),
                m31(input_bytes[1]),
                m31(input_bytes[2]),
            ]),
        ));
        let (output, quotient, carries) = mul_witness(N_INV, input);
        for value in [output, quotient] {
            range_entries(&mut entries, &mut rc_uses, relations, value);
        }
        for carry in carries {
            let shifted = (carry + CARRY_OFFSET) as u32;
            entries.push((
                one,
                range_denominator(&relations.range, shifted, RcKind::Rc13),
            ));
            push_use(&mut rc_uses.rc13, shifted);
        }
        let digits = balanced3(output as i64);
        let digit_row = SecureField::from(signed_m31(digits[0]))
            + s * SecureField::from(signed_m31(digits[1]))
            + s * s * SecureField::from(signed_m31(digits[2]));
        running = if item.eval_start {
            digit_row
        } else {
            running * r + digit_row
        };
        acc[row] = running;
        for digit in digits {
            let shifted = (digit + 256) as u32;
            entries.push((
                one,
                range_denominator(&relations.range, shifted, RcKind::Rc9),
            ));
            push_use(&mut rc_uses.rc9, shifted);
        }
        if item.eval_end {
            a_evals[item.poly] = running;
            let coords = running.to_m31_array();
            entries.push((
                -one,
                relations.eval.combine(&[
                    m31(item.poly as u32),
                    coords[0],
                    coords[1],
                    coords[2],
                    coords[3],
                ]),
            ));
        } else {
            entries.push((zero, one));
        }
        assert_eq!(entries.len(), NTT_SCALING_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    let mut scaling_trace: Vec<ColEval> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coordinate| {
            col_eval(
                NTT_SCALING_LOG_SIZE,
                acc.iter()
                    .map(|value| value.to_m31_array()[coordinate])
                    .collect(),
            )
        })
        .collect();
    let (logup_trace, scaling_claimed_sum) = gen_batched_logup(NTT_SCALING_LOG_SIZE, &rows);
    scaling_trace.extend(logup_trace);

    NttInteractions {
        butterfly,
        scaling: NttComponentInteraction {
            trace: scaling_trace,
            claimed_sum: scaling_claimed_sum,
        },
        rc_uses,
        a_evals,
    }
}

pub fn native_eval_use_sum(a_evals: &[SecureField], relation: &AEvalRelation) -> SecureField {
    assert_eq!(a_evals.len(), MATRIX_POLYS);
    a_evals
        .iter()
        .enumerate()
        .map(|(poly, value)| -> SecureField {
            let coords = value.to_m31_array();
            let denominator: SecureField =
                relation.combine(&[m31(poly as u32), coords[0], coords[1], coords[2], coords[3]]);
            SecureField::one() / denominator
        })
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derived_witness_matches_reference_expand_a_and_inverse_ntt() {
        let rho = core::array::from_fn(|i| (17 * i + 3) as u8);
        let witness = derive_expand_a_witness(rho).unwrap();
        let reference = crate::reference::expand_a::expand_a(&rho);
        for row in 0..K {
            for col in 0..L {
                let poly = row * L + col;
                assert_eq!(witness.a_hat[poly], reference.matrix[row][col]);
                assert_eq!(witness.a[poly], ntt_inverse(&reference.matrix[row][col]));
                assert_eq!(
                    &witness.squeeze_outputs[poly]
                        [..reference.transcripts[row][col].squeezed.len()],
                    reference.transcripts[row][col].squeezed.as_slice(),
                );
            }
        }
    }

    #[test]
    fn stacked_butterfly_schedule_covers_every_stage_cell_once() {
        let schedule = butterfly_schedule();
        assert_eq!(schedule.len(), MATRIX_POLYS * NTT_STAGES * N / 2);
        let mut seen = vec![vec![vec![false; N]; NTT_STAGES]; MATRIX_POLYS];
        for item in schedule {
            assert!(!seen[item.poly][item.stage][item.index0]);
            assert!(!seen[item.poly][item.stage][item.index1]);
            seen[item.poly][item.stage][item.index0] = true;
            seen[item.poly][item.stage][item.index1] = true;
        }
        assert!(seen.into_iter().flatten().flatten().all(|present| present));
    }

    #[test]
    fn base_trace_range_multiplicities_match_interaction_consumers() {
        let witness = derive_expand_a_witness([42; 32]).unwrap();
        let (_, rejection_base_uses) = gen_rejection_base_trace(&witness);
        let ntt_base = gen_ntt_base_traces(&witness);
        let rejection_interaction =
            gen_rejection_interaction(&witness, 0, &ExpandARelations::dummy());
        let ntt_interaction = gen_ntt_interactions(
            &witness,
            SecureField::from(m31(7)),
            SecureField::from(m31(11)),
            &ExpandARelations::dummy(),
        );
        for kind in RcKind::RANGE {
            assert_eq!(
                rejection_base_uses.for_kind(kind),
                rejection_interaction.rc_uses.for_kind(kind),
            );
            assert_eq!(
                ntt_base.rc_uses.for_kind(kind),
                ntt_interaction.rc_uses.for_kind(kind),
            );
        }
    }

    #[test]
    fn ntt_evaluations_match_native_balanced_horner() {
        let witness = derive_expand_a_witness([9; 32]).unwrap();
        let r = SecureField::from(m31(13));
        let s = SecureField::from(m31(29));
        let interaction = gen_ntt_interactions(&witness, r, s, &ExpandARelations::dummy());
        for (poly, coefficients) in witness.a.iter().enumerate() {
            let mut expected = SecureField::zero();
            for &coefficient in coefficients.iter().rev() {
                let digits = balanced3(coefficient as i64);
                let row = SecureField::from(signed_m31(digits[0]))
                    + s * SecureField::from(signed_m31(digits[1]))
                    + s * s * SecureField::from(signed_m31(digits[2]));
                expected = expected * r + row;
            }
            assert_eq!(interaction.a_evals[poly], expected);
        }
    }

    #[test]
    fn limb_multiplication_witness_is_exact_at_boundaries() {
        let zetas = zeta_table();
        for constant in [1, N_INV, Q - 1, zetas[1], Q - zetas[255]] {
            for value in [0, 1, 255, 256, Q / 2, Q - 2, Q - 1] {
                let (output, quotient, carries) = mul_witness(constant, value);
                assert_eq!(
                    constant as u64 * value as u64,
                    output as u64 + Q as u64 * quotient as u64,
                );
                assert!(output < Q && quotient < Q);
                assert!(carries
                    .iter()
                    .all(|&carry| (-CARRY_OFFSET..CARRY_OFFSET).contains(&carry)));
            }
        }
    }
}
