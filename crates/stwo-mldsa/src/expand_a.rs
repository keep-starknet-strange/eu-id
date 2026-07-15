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
use crate::coeffs::relations::RcRelation;
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
    pub rc9: RcRelation,
    pub rc13: RcRelation,
    pub rc8: RcRelation,
    pub rc7: RcRelation,
    pub cell: NttCellRelation,
    pub eval: AEvalRelation,
}

impl ExpandARelations {
    pub fn draw_with(
        channel: &mut impl stwo::core::channel::Channel,
        hash_io: HashIoRelation,
        rc9: RcRelation,
        rc13: RcRelation,
        rc8: RcRelation,
        rc7: RcRelation,
    ) -> Self {
        Self {
            hash_io,
            rc9,
            rc13,
            rc8,
            rc7,
            cell: NttCellRelation::draw(channel),
            eval: AEvalRelation::draw(channel),
        }
    }

    pub fn dummy() -> Self {
        Self {
            hash_io: HashIoRelation::dummy(),
            rc9: RcRelation::dummy(),
            rc13: RcRelation::dummy(),
            rc8: RcRelation::dummy(),
            rc7: RcRelation::dummy(),
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

#[derive(Clone, Copy)]
struct NttRow {
    poly: usize,
    stage: u32,
    index0: usize,
    index1: usize,
    twiddle: u32,
    final_scale: bool,
    eval_start: bool,
    eval_end: bool,
}

fn ntt_schedule() -> Vec<NttRow> {
    let zetas = zeta_table();
    let mut rows = Vec::with_capacity(MATRIX_POLYS * (8 * N / 2 + N));
    for poly in 0..MATRIX_POLYS {
        let mut m = N;
        let mut len = 1usize;
        let mut stage = 0u32;
        while len < N {
            let mut start = 0usize;
            while start < N {
                m -= 1;
                let twiddle = Q - zetas[m];
                for index0 in start..start + len {
                    rows.push(NttRow {
                        poly,
                        stage,
                        index0,
                        index1: index0 + len,
                        twiddle,
                        final_scale: false,
                        eval_start: false,
                        eval_end: false,
                    });
                }
                start += 2 * len;
            }
            len <<= 1;
            stage += 1;
        }
        for position in 0..N {
            let index = N - 1 - position;
            rows.push(NttRow {
                poly,
                stage: 8,
                index0: index,
                index1: 0,
                twiddle: N_INV,
                final_scale: true,
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

pub fn ntt_log_size() -> u32 {
    (ntt_schedule().len() as u32)
        .next_power_of_two()
        .ilog2()
        .max(LOG_N_LANES)
}

fn pre_id(ns: &str, component: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{}mldsa_expand_a_{component}_{name}", ns_prefix(ns)),
    }
}

fn ntt_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_expand_a_ntt_{name}"),
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

const NTT_PRE_NAMES: [&str; 13] = [
    "active",
    "final",
    "eval_start",
    "eval_end",
    "poly",
    "stage",
    "index0",
    "index1",
    "twiddle0",
    "twiddle1",
    "twiddle2",
    "next_stage",
    "butterfly",
];

pub fn ntt_preprocessed_ids(_ns: &str) -> Vec<PreProcessedColumnId> {
    NTT_PRE_NAMES.iter().map(|name| ntt_pre_id(name)).collect()
}

pub fn gen_ntt_preprocessed(_ns: &str) -> Vec<ColEval> {
    let log_size = ntt_log_size();
    let n_rows = 1usize << log_size;
    let schedule = ntt_schedule();
    let mut columns = vec![vec![m31(0); n_rows]; NTT_PRE_NAMES.len()];
    for (row, item) in schedule.iter().enumerate() {
        let butterfly = !item.final_scale;
        columns[0][row] = m31(1);
        columns[1][row] = m31(item.final_scale as u32);
        columns[2][row] = m31(item.eval_start as u32);
        columns[3][row] = m31(item.eval_end as u32);
        columns[4][row] = m31(item.poly as u32);
        columns[5][row] = m31(item.stage);
        columns[6][row] = m31(item.index0 as u32);
        columns[7][row] = m31(item.index1 as u32);
        columns[8][row] = m31(item.twiddle & 0xff);
        columns[9][row] = m31((item.twiddle >> 8) & 0xff);
        columns[10][row] = m31(item.twiddle >> 16);
        columns[11][row] = m31(item.stage + u32::from(butterfly));
        columns[12][row] = m31(butterfly as u32);
    }
    columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect()
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

const X_IN0: usize = 0;
const X_IN1: usize = 3;
const X_OUT0: usize = 6;
const X_OUT0_SLACK: usize = 9;
const X_DIFF: usize = 12;
const X_DIFF_SLACK: usize = 15;
const X_OUT1: usize = 18;
const X_OUT1_SLACK: usize = 21;
const X_QUOT: usize = 24;
const X_QUOT_SLACK: usize = 27;
const X_REDUCE: usize = 30;
const X_BORROW: usize = 31;
const X_CARRY: usize = 32;
const X_DIGIT: usize = 36;
pub const NTT_BASE_COLS: usize = 39;

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

pub fn gen_ntt_base_trace(witness: &ExpandAWitness) -> (Vec<ColEval>, ExpandARcUses) {
    let schedule = ntt_schedule();
    let log_size = ntt_log_size();
    let n_rows = 1usize << log_size;
    let mut columns = vec![vec![m31(0); n_rows]; NTT_BASE_COLS];
    let mut states = witness.a_hat.clone();
    let mut rc_uses = ExpandARcUses::new();
    for (row, item) in schedule.iter().enumerate() {
        let input0 = states[item.poly][item.index0];
        let input1 = if item.final_scale {
            0
        } else {
            states[item.poly][item.index1]
        };
        let in0 = split_u23(input0);
        let in1 = split_u23(input1);
        for limb in 0..3 {
            columns[X_IN0 + limb][row] = m31(in0[limb]);
            columns[X_IN1 + limb][row] = m31(in1[limb]);
        }
        let mul_input;
        if item.final_scale {
            mul_input = input0;
        } else {
            let sum = input0 + input1;
            let reduce = sum >= Q;
            let output0 = if reduce { sum - Q } else { sum };
            let borrow = input0 < input1;
            let diff = if borrow {
                input0 + Q - input1
            } else {
                input0 - input1
            };
            write_canonical(&mut columns, X_OUT0, X_OUT0_SLACK, row, output0);
            write_canonical(&mut columns, X_DIFF, X_DIFF_SLACK, row, diff);
            record_canonical_uses(&mut rc_uses, output0);
            record_canonical_uses(&mut rc_uses, diff);
            columns[X_REDUCE][row] = m31(reduce as u32);
            columns[X_BORROW][row] = m31(borrow as u32);
            states[item.poly][item.index0] = output0;
            mul_input = diff;
        }
        let (output1, quotient, carries) = mul_witness(item.twiddle, mul_input);
        write_canonical(&mut columns, X_OUT1, X_OUT1_SLACK, row, output1);
        write_canonical(&mut columns, X_QUOT, X_QUOT_SLACK, row, quotient);
        record_canonical_uses(&mut rc_uses, output1);
        record_canonical_uses(&mut rc_uses, quotient);
        for limb in 0..4 {
            columns[X_CARRY + limb][row] = signed_m31(carries[limb]);
            push_use(&mut rc_uses.rc13, (carries[limb] + CARRY_OFFSET) as u32);
        }
        if item.final_scale {
            let digits = balanced3(output1 as i64);
            for limb in 0..3 {
                columns[X_DIGIT + limb][row] = signed_m31(digits[limb]);
                push_use(&mut rc_uses.rc9, (digits[limb] + 256) as u32);
            }
            debug_assert_eq!(output1, witness.a[item.poly][item.index0]);
        } else {
            states[item.poly][item.index1] = output1;
        }
    }
    let trace = columns
        .into_iter()
        .map(|column| col_eval(log_size, column))
        .collect();
    (trace, rc_uses)
}

pub const REJECTION_LOGUP_ENTRIES: usize = 44;
pub const NTT_LOGUP_ENTRIES: usize = 36;
pub const LOGUP_BATCH: usize = 4;
pub const REJECTION_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * REJECTION_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
pub const NTT_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE + SECURE_EXTENSION_DEGREE * NTT_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

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
            &self.relations.rc7,
            sample.clone(),
            core::slice::from_ref(&low7),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            accept.clone(),
            core::slice::from_ref(&slack[0]),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            accept.clone(),
            core::slice::from_ref(&slack[1]),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc7,
            accept.clone(),
            core::slice::from_ref(&slack[2]),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc13,
            reject,
            core::slice::from_ref(&reject_delta),
        ));
        let remaining = E::F::from(m31(255)) - index.clone() - accept.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            not_last,
            core::slice::from_ref(&remaining),
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

#[derive(Clone)]
pub struct NttEval {
    pub log_size: u32,
    pub r: SecureField,
    pub s: SecureField,
    pub relations: ExpandARelations,
}

fn recompose3<F: Clone + core::ops::Add<Output = F> + core::ops::Mul<Output = F>>(
    bytes: &[F; 3],
    c256: F,
    c65536: F,
) -> F {
    bytes[0].clone() + c256 * bytes[1].clone() + c65536 * bytes[2].clone()
}

impl FrameworkEval for NttEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let id = ntt_pre_id;
        let active = eval.get_preprocessed_column(id("active"));
        let final_scale = eval.get_preprocessed_column(id("final"));
        let eval_start = eval.get_preprocessed_column(id("eval_start"));
        let eval_end = eval.get_preprocessed_column(id("eval_end"));
        let poly = eval.get_preprocessed_column(id("poly"));
        let stage = eval.get_preprocessed_column(id("stage"));
        let index0 = eval.get_preprocessed_column(id("index0"));
        let index1 = eval.get_preprocessed_column(id("index1"));
        let twiddle = [
            eval.get_preprocessed_column(id("twiddle0")),
            eval.get_preprocessed_column(id("twiddle1")),
            eval.get_preprocessed_column(id("twiddle2")),
        ];
        let next_stage = eval.get_preprocessed_column(id("next_stage"));
        let butterfly = eval.get_preprocessed_column(id("butterfly"));

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
        let digits: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());

        let acc_masks: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(acc_masks.each_ref().map(|mask| mask[0].clone()));
        let acc_cur = E::combine_ef(acc_masks.each_ref().map(|mask| mask[1].clone()));

        let one = E::F::one();
        let c256 = E::F::from(m31(256));
        let c65536 = E::F::from(m31(1 << 16));
        let q = E::F::from(m31(Q));
        let q_minus_one = E::F::from(m31(Q - 1));
        let input0_value = recompose3(&input0, c256.clone(), c65536.clone());
        let input1_value = recompose3(&input1, c256.clone(), c65536.clone());
        let output0_value = recompose3(&output0, c256.clone(), c65536.clone());
        let diff_value = recompose3(&diff, c256.clone(), c65536.clone());
        let output1_value = recompose3(&output1, c256.clone(), c65536.clone());

        eval.add_constraint(reduce.clone() * (one.clone() - reduce.clone()));
        eval.add_constraint(borrow.clone() * (one.clone() - borrow.clone()));
        eval.add_constraint(
            butterfly.clone()
                * (input0_value.clone() + input1_value.clone()
                    - output0_value.clone()
                    - q.clone() * reduce.clone()),
        );
        eval.add_constraint(
            butterfly.clone()
                * (input0_value.clone() + q.clone() * borrow.clone()
                    - input1_value.clone()
                    - diff_value.clone()),
        );
        eval.add_constraint(final_scale.clone() * reduce.clone());
        eval.add_constraint(final_scale.clone() * borrow.clone());
        for value in input1
            .iter()
            .chain(output0.iter())
            .chain(output0_slack.iter())
            .chain(diff.iter())
            .chain(diff_slack.iter())
        {
            eval.add_constraint(final_scale.clone() * value.clone());
        }

        for (gate, bytes, slack) in [
            (butterfly.clone(), &output0, &output0_slack),
            (butterfly.clone(), &diff, &diff_slack),
            (active.clone(), &output1, &output1_slack),
            (active.clone(), &quotient, &quotient_slack),
        ] {
            let value = recompose3(bytes, c256.clone(), c65536.clone());
            let slack_value = recompose3(slack, c256.clone(), c65536.clone());
            eval.add_constraint(gate * (value + slack_value - q_minus_one.clone()));
        }

        let mul_input: [E::F; 3] = core::array::from_fn(|limb| {
            final_scale.clone() * input0[limb].clone() + butterfly.clone() * diff[limb].clone()
        });
        let q_bytes = [m31(Q & 0xff), m31((Q >> 8) & 0xff), m31(Q >> 16)];
        let e0 = twiddle[0].clone() * mul_input[0].clone()
            - E::F::from(q_bytes[0]) * quotient[0].clone()
            - output1[0].clone();
        eval.add_constraint(active.clone() * (e0 - E::F::from(m31(256)) * carries[0].clone()));
        let e1 = twiddle[0].clone() * mul_input[1].clone()
            + twiddle[1].clone() * mul_input[0].clone()
            - E::F::from(q_bytes[0]) * quotient[1].clone()
            - E::F::from(q_bytes[1]) * quotient[0].clone()
            - output1[1].clone()
            + carries[0].clone();
        eval.add_constraint(active.clone() * (e1 - E::F::from(m31(256)) * carries[1].clone()));
        let e2 = twiddle[0].clone() * mul_input[2].clone()
            + twiddle[1].clone() * mul_input[1].clone()
            + twiddle[2].clone() * mul_input[0].clone()
            - E::F::from(q_bytes[0]) * quotient[2].clone()
            - E::F::from(q_bytes[1]) * quotient[1].clone()
            - E::F::from(q_bytes[2]) * quotient[0].clone()
            - output1[2].clone()
            + carries[1].clone();
        eval.add_constraint(active.clone() * (e2 - E::F::from(m31(256)) * carries[2].clone()));
        let e3 = twiddle[1].clone() * mul_input[2].clone()
            + twiddle[2].clone() * mul_input[1].clone()
            - E::F::from(q_bytes[1]) * quotient[2].clone()
            - E::F::from(q_bytes[2]) * quotient[1].clone()
            + carries[2].clone();
        eval.add_constraint(active.clone() * (e3 - E::F::from(m31(256)) * carries[3].clone()));
        let e4 = twiddle[2].clone() * mul_input[2].clone()
            - E::F::from(q_bytes[2]) * quotient[2].clone()
            + carries[3].clone();
        eval.add_constraint(active.clone() * e4);

        let digit_value = digits[0].clone()
            + E::F::from(m31(B as u32)) * digits[1].clone()
            + E::F::from(m31((B * B) as u32)) * digits[2].clone();
        eval.add_constraint(final_scale.clone() * (output1_value - digit_value));
        for digit in &digits {
            eval.add_constraint(butterfly.clone() * digit.clone());
        }

        let mut s_power = SecureField::one();
        let mut digit_row = E::EF::zero();
        for digit in &digits {
            digit_row += E::EF::from(digit.clone()) * E::EF::from(s_power);
            s_power *= self.s;
        }
        let expected_acc = E::EF::from(final_scale.clone())
            * (E::EF::from(one.clone() - eval_start.clone()) * acc_prev * E::EF::from(self.r)
                + digit_row);
        eval.add_constraint(acc_cur - expected_acc);

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
            -butterfly.clone(),
            &[
                poly.clone(),
                stage,
                index1.clone(),
                input1[0].clone(),
                input1[1].clone(),
                input1[2].clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.cell,
            butterfly.clone(),
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
            butterfly.clone(),
            &[
                poly.clone(),
                next_stage,
                index1,
                output1[0].clone(),
                output1[1].clone(),
                output1[2].clone(),
            ],
        ));

        for (gate, bytes, slack) in [
            (butterfly.clone(), &output0, &output0_slack),
            (butterfly.clone(), &diff, &diff_slack),
            (active.clone(), &output1, &output1_slack),
            (active.clone(), &quotient, &quotient_slack),
        ] {
            for limb in 0..2 {
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.rc8,
                    gate.clone(),
                    core::slice::from_ref(&bytes[limb]),
                ));
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.rc8,
                    gate.clone(),
                    core::slice::from_ref(&slack[limb]),
                ));
            }
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc7,
                gate.clone(),
                core::slice::from_ref(&bytes[2]),
            ));
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc7,
                gate,
                core::slice::from_ref(&slack[2]),
            ));
        }
        for carry in &carries {
            let shifted = carry.clone() + E::F::from(m31(CARRY_OFFSET as u32));
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc13,
                active.clone(),
                core::slice::from_ref(&shifted),
            ));
        }
        for digit in &digits {
            let shifted = digit.clone() + E::F::from(m31(256));
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc9,
                final_scale.clone(),
                core::slice::from_ref(&shifted),
            ));
        }
        let acc_coords: Vec<E::F> = acc_masks.iter().map(|mask| mask[1].clone()).collect();
        let mut eval_tuple = vec![poly];
        eval_tuple.extend(acc_coords);
        eval.add_to_relation(RelationEntry::base(
            &self.relations.eval,
            -eval_end,
            &eval_tuple,
        ));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

pub type RejectionComponent = FrameworkComponent<RejectionEval>;
pub type NttComponent = FrameworkComponent<NttEval>;

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
            entries.push((one, relations.rc7.combine(&[m31(low7)])));
            push_use(&mut rc_uses.rc7, low7);
            let accept = value < Q;
            if accept {
                let slack = split_u23(Q - 1 - value);
                entries.push((one, relations.rc8.combine(&[m31(slack[0])])));
                entries.push((one, relations.rc8.combine(&[m31(slack[1])])));
                entries.push((one, relations.rc7.combine(&[m31(slack[2])])));
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
                entries.push((one, relations.rc13.combine(&[m31(delta)])));
                push_use(&mut rc_uses.rc13, delta);
            }
            if item.last {
                entries.push((zero, one));
            } else {
                let remaining = 255 - accepted_index[item.poly] - u32::from(accept);
                entries.push((one, relations.rc8.combine(&[m31(remaining)])));
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

pub struct NttInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    pub rc_uses: ExpandARcUses,
    pub a_evals: Vec<SecureField>,
}

fn range_entries(
    entries: &mut Vec<(SecureField, SecureField)>,
    uses: &mut ExpandARcUses,
    relations: &ExpandARelations,
    value: u32,
    enabled: bool,
) {
    if !enabled {
        entries.extend([(SecureField::zero(), SecureField::one()); 6]);
        return;
    }
    let bytes = split_u23(value);
    let slack = split_u23(Q - 1 - value);
    for limb in 0..2 {
        entries.push((
            SecureField::one(),
            relations.rc8.combine(&[m31(bytes[limb])]),
        ));
        entries.push((
            SecureField::one(),
            relations.rc8.combine(&[m31(slack[limb])]),
        ));
        push_use(&mut uses.rc8, bytes[limb]);
        push_use(&mut uses.rc8, slack[limb]);
    }
    entries.push((SecureField::one(), relations.rc7.combine(&[m31(bytes[2])])));
    entries.push((SecureField::one(), relations.rc7.combine(&[m31(slack[2])])));
    push_use(&mut uses.rc7, bytes[2]);
    push_use(&mut uses.rc7, slack[2]);
}

pub fn gen_ntt_interaction(
    witness: &ExpandAWitness,
    r: SecureField,
    s: SecureField,
    relations: &ExpandARelations,
) -> NttInteraction {
    let schedule = ntt_schedule();
    let log_size = ntt_log_size();
    let n_rows = 1usize << log_size;
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut rows = vec![vec![(zero, one); NTT_LOGUP_ENTRIES]; n_rows];
    let mut acc = vec![zero; n_rows];
    let mut a_evals = vec![zero; MATRIX_POLYS];
    let mut rc_uses = ExpandARcUses::new();
    let mut states = witness.a_hat.clone();
    let mut running = zero;

    for (row, item) in schedule.iter().enumerate() {
        let input0 = states[item.poly][item.index0];
        let input1 = if item.final_scale {
            0
        } else {
            states[item.poly][item.index1]
        };
        let input0_bytes = split_u23(input0);
        let input1_bytes = split_u23(input1);
        let mut entries = Vec::with_capacity(NTT_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.cell.combine(&[
                m31(item.poly as u32),
                m31(item.stage),
                m31(item.index0 as u32),
                m31(input0_bytes[0]),
                m31(input0_bytes[1]),
                m31(input0_bytes[2]),
            ]),
        ));
        if item.final_scale {
            entries.extend([(zero, one); 3]);
        } else {
            entries.push((
                -one,
                relations.cell.combine(&[
                    m31(item.poly as u32),
                    m31(item.stage),
                    m31(item.index1 as u32),
                    m31(input1_bytes[0]),
                    m31(input1_bytes[1]),
                    m31(input1_bytes[2]),
                ]),
            ));
        }

        let mul_input;
        let output0;
        let diff;
        if item.final_scale {
            output0 = 0;
            diff = 0;
            mul_input = input0;
        } else {
            let sum = input0 + input1;
            output0 = if sum >= Q { sum - Q } else { sum };
            diff = if input0 < input1 {
                input0 + Q - input1
            } else {
                input0 - input1
            };
            mul_input = diff;
        }
        let (output1, quotient, carries) = mul_witness(item.twiddle, mul_input);
        if !item.final_scale {
            let output0_bytes = split_u23(output0);
            let output1_bytes = split_u23(output1);
            entries.push((
                one,
                relations.cell.combine(&[
                    m31(item.poly as u32),
                    m31(item.stage + 1),
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
                    m31(item.stage + 1),
                    m31(item.index1 as u32),
                    m31(output1_bytes[0]),
                    m31(output1_bytes[1]),
                    m31(output1_bytes[2]),
                ]),
            ));
            states[item.poly][item.index0] = output0;
            states[item.poly][item.index1] = output1;
        }

        range_entries(
            &mut entries,
            &mut rc_uses,
            relations,
            output0,
            !item.final_scale,
        );
        range_entries(
            &mut entries,
            &mut rc_uses,
            relations,
            diff,
            !item.final_scale,
        );
        range_entries(&mut entries, &mut rc_uses, relations, output1, true);
        range_entries(&mut entries, &mut rc_uses, relations, quotient, true);
        for carry in carries {
            let shifted = (carry + CARRY_OFFSET) as u32;
            entries.push((one, relations.rc13.combine(&[m31(shifted)])));
            push_use(&mut rc_uses.rc13, shifted);
        }
        if item.final_scale {
            let digits = balanced3(output1 as i64);
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
                entries.push((one, relations.rc9.combine(&[m31(shifted)])));
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
        } else {
            entries.extend([(zero, one); 4]);
        }
        assert_eq!(entries.len(), NTT_LOGUP_ENTRIES);
        rows[row] = entries;
    }

    let mut trace: Vec<ColEval> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coordinate| {
            col_eval(
                log_size,
                acc.iter()
                    .map(|value| value.to_m31_array()[coordinate])
                    .collect(),
            )
        })
        .collect();
    let (logup_trace, claimed_sum) = gen_batched_logup(log_size, &rows);
    trace.extend(logup_trace);
    NttInteraction {
        trace,
        claimed_sum,
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
    fn base_trace_range_multiplicities_match_interaction_consumers() {
        let witness = derive_expand_a_witness([42; 32]).unwrap();
        let (_, rejection_base_uses) = gen_rejection_base_trace(&witness);
        let (_, ntt_base_uses) = gen_ntt_base_trace(&witness);
        let rejection_interaction =
            gen_rejection_interaction(&witness, 0, &ExpandARelations::dummy());
        let ntt_interaction = gen_ntt_interaction(
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
                ntt_base_uses.for_kind(kind),
                ntt_interaction.rc_uses.for_kind(kind),
            );
        }
    }

    #[test]
    fn ntt_evaluations_match_native_balanced_horner() {
        let witness = derive_expand_a_witness([9; 32]).unwrap();
        let r = SecureField::from(m31(13));
        let s = SecureField::from(m31(29));
        let interaction = gen_ntt_interaction(&witness, r, s, &ExpandARelations::dummy());
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
