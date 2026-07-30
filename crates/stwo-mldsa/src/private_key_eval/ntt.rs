use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, Relation, RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::air_util::{col_eval, enc_signed, m31, ColEval};
use crate::coeffs::tables::RcKind;
use crate::coeffs::RcUses;
use crate::constants::{K, L, N, Q, ZETA};
use crate::reference::ntt::NttPoly;
use crate::witness::B;

use super::{
    gen_batched_logup, range_denominator, range_tuple, PrivateKeyEvalRelations, A_EVAL_BASE,
};

pub const MATRIX_POLYS: usize = K * L;
pub const NTT_STAGES: usize = 8;
pub const NTT_BUTTERFLY_LOG_SIZE: u32 = 15;
pub const NTT_SCALING_LOG_SIZE: u32 = 13;

const CARRY_OFFSET: i64 = 1 << 12;
const N_INV: u32 = 8_347_681;
const LOGUP_BATCH: usize = 4;

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

fn zeta_table() -> [u32; N] {
    let mut powers = [0u64; N];
    let mut current = 1u64;
    for value in &mut powers {
        *value = current;
        current = current * ZETA as u64 % Q as u64;
    }
    let mut zetas = [0u32; N];
    for (index, value) in zetas.iter_mut().enumerate() {
        *value = powers[(index as u8).reverse_bits() as usize] as u32;
    }
    zetas
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

const BUTTERFLY_PRE_NAMES: [&str; 8] = [
    "active", "poly", "stage", "index0", "index1", "twiddle0", "twiddle1", "twiddle2",
];
const SCALING_PRE_NAMES: [&str; 5] = ["active", "eval_start", "eval_end", "poly", "index"];

fn butterfly_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_ntt_butterfly_{name}"),
    }
}

fn scaling_pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_ntt_scaling_{name}"),
    }
}

pub fn ntt_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    BUTTERFLY_PRE_NAMES
        .iter()
        .map(|name| butterfly_pre_id(name))
        .chain(SCALING_PRE_NAMES.iter().map(|name| scaling_pre_id(name)))
        .collect()
}

pub fn ntt_preprocessed_log_sizes() -> Vec<u32> {
    let mut sizes = vec![NTT_BUTTERFLY_LOG_SIZE; BUTTERFLY_PRE_NAMES.len()];
    sizes.extend(vec![NTT_SCALING_LOG_SIZE; SCALING_PRE_NAMES.len()]);
    sizes
}

pub fn gen_ntt_preprocessed() -> Vec<ColEval> {
    let mut result = Vec::with_capacity(BUTTERFLY_PRE_NAMES.len() + SCALING_PRE_NAMES.len());
    let mut columns =
        vec![vec![m31(0); 1usize << NTT_BUTTERFLY_LOG_SIZE]; BUTTERFLY_PRE_NAMES.len()];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        columns[0][row] = m31(1);
        columns[1][row] = m31(item.poly as u32);
        columns[2][row] = m31(item.stage as u32);
        columns[3][row] = m31(item.index0 as u32);
        columns[4][row] = m31(item.index1 as u32);
        let twiddle = split_u23(item.twiddle);
        for limb in 0..3 {
            columns[5 + limb][row] = m31(twiddle[limb]);
        }
    }
    result.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_BUTTERFLY_LOG_SIZE, column)),
    );

    let mut columns = vec![vec![m31(0); 1usize << NTT_SCALING_LOG_SIZE]; SCALING_PRE_NAMES.len()];
    for (row, item) in scaling_schedule().iter().enumerate() {
        columns[0][row] = m31(1);
        columns[1][row] = m31(item.eval_start as u32);
        columns[2][row] = m31(item.eval_end as u32);
        columns[3][row] = m31(item.poly as u32);
        columns[4][row] = m31(item.index as u32);
    }
    result.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_SCALING_LOG_SIZE, column)),
    );
    result
}

const B_IN0: usize = 0;
const B_IN1: usize = 3;
const B_OUT0: usize = 6;
const B_OUT0_SLACK: usize = 9;
const B_DIFF: usize = 12;
const B_DIFF_SLACK: usize = 15;
const B_OUT1: usize = 18;
const B_OUT1_SLACK: usize = 21;
const B_QUOTIENT: usize = 24;
const B_QUOTIENT_SLACK: usize = 27;
const B_REDUCE: usize = 30;
const B_BORROW: usize = 31;
const B_CARRY: usize = 32;
pub const NTT_BUTTERFLY_BASE_COLS: usize = 36;

const S_INPUT: usize = 0;
const S_OUTPUT: usize = 3;
const S_OUTPUT_SLACK: usize = 6;
const S_QUOTIENT: usize = 9;
const S_QUOTIENT_SLACK: usize = 12;
const S_CARRY: usize = 15;
const S_DIGIT: usize = 19;
pub const NTT_SCALING_BASE_COLS: usize = 22;

pub const NTT_BUTTERFLY_LOGUP_ENTRIES: usize = 32;
pub const NTT_SCALING_LOGUP_ENTRIES: usize = 21;
pub const NTT_BUTTERFLY_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE * NTT_BUTTERFLY_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
pub const NTT_SCALING_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE
    + SECURE_EXTENSION_DEGREE * NTT_SCALING_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);

pub fn ntt_trace_layout() -> Vec<u32> {
    let mut layout = vec![NTT_BUTTERFLY_LOG_SIZE; NTT_BUTTERFLY_BASE_COLS];
    layout.extend(vec![NTT_SCALING_LOG_SIZE; NTT_SCALING_BASE_COLS]);
    layout
}

pub fn ntt_interaction_layout() -> Vec<u32> {
    let mut layout = vec![NTT_BUTTERFLY_LOG_SIZE; NTT_BUTTERFLY_INTERACTION_COLS];
    layout.extend(vec![NTT_SCALING_LOG_SIZE; NTT_SCALING_INTERACTION_COLS]);
    layout
}

fn split_u23(value: u32) -> [u32; 3] {
    [value & 0xff, (value >> 8) & 0xff, value >> 16]
}

fn write_canonical(
    columns: &mut [Vec<M31>],
    value_base: usize,
    slack_base: usize,
    row: usize,
    value: u32,
) {
    let value_limbs = split_u23(value);
    let slack_limbs = split_u23(Q - 1 - value);
    for limb in 0..3 {
        columns[value_base + limb][row] = m31(value_limbs[limb]);
        columns[slack_base + limb][row] = m31(slack_limbs[limb]);
    }
}

fn mul_carries(constant: u32, value: u32, output: u32, quotient: u32) -> [i64; 4] {
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
    [c1, c2, c3, c4]
}

fn mul_witness(constant: u32, value: u32) -> (u32, u32, [i64; 4]) {
    let product = constant as u64 * value as u64;
    let output = (product % Q as u64) as u32;
    let quotient = (product / Q as u64) as u32;
    (
        output,
        quotient,
        mul_carries(constant, value, output, quotient),
    )
}

fn balanced3(value: u32) -> [i64; 3] {
    crate::witness::balanced_digits::<3>(value as i128).map(|digit| digit as i64)
}

fn record_canonical_uses(uses: &mut RcUses, value: u32) {
    let limbs = split_u23(value);
    let slack = split_u23(Q - 1 - value);
    for limb in 0..2 {
        uses.record(RcKind::Rc8, limbs[limb]);
        uses.record(RcKind::Rc8, slack[limb]);
    }
    uses.record(RcKind::Rc7, limbs[2]);
    uses.record(RcKind::Rc7, slack[2]);
}

pub struct NttBase {
    pub trace: Vec<ColEval>,
    pub range_uses: RcUses,
}

pub fn gen_ntt_base(a_hat: &[NttPoly]) -> NttBase {
    assert_eq!(a_hat.len(), MATRIX_POLYS);
    let mut states = a_hat.to_vec();
    let mut range_uses = RcUses::new();
    let mut columns = vec![vec![m31(0); 1usize << NTT_BUTTERFLY_LOG_SIZE]; NTT_BUTTERFLY_BASE_COLS];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        let input0 = states[item.poly][item.index0];
        let input1 = states[item.poly][item.index1];
        for (limb, value) in split_u23(input0).into_iter().enumerate() {
            columns[B_IN0 + limb][row] = m31(value);
        }
        for (limb, value) in split_u23(input1).into_iter().enumerate() {
            columns[B_IN1 + limb][row] = m31(value);
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
        record_canonical_uses(&mut range_uses, output0);
        record_canonical_uses(&mut range_uses, diff);
        columns[B_REDUCE][row] = m31(reduce as u32);
        columns[B_BORROW][row] = m31(borrow as u32);
        states[item.poly][item.index0] = output0;

        let (output1, quotient, carries) = mul_witness(item.twiddle, diff);
        write_canonical(&mut columns, B_OUT1, B_OUT1_SLACK, row, output1);
        write_canonical(&mut columns, B_QUOTIENT, B_QUOTIENT_SLACK, row, quotient);
        record_canonical_uses(&mut range_uses, output1);
        record_canonical_uses(&mut range_uses, quotient);
        for (limb, carry) in carries.into_iter().enumerate() {
            columns[B_CARRY + limb][row] = enc_signed(carry);
            range_uses.record(RcKind::Rc13, (carry + CARRY_OFFSET) as u32);
        }
        states[item.poly][item.index1] = output1;
    }
    let mut trace: Vec<_> = columns
        .into_iter()
        .map(|column| col_eval(NTT_BUTTERFLY_LOG_SIZE, column))
        .collect();

    let mut columns = vec![vec![m31(0); 1usize << NTT_SCALING_LOG_SIZE]; NTT_SCALING_BASE_COLS];
    for (row, item) in scaling_schedule().iter().enumerate() {
        let input = states[item.poly][item.index];
        for (limb, value) in split_u23(input).into_iter().enumerate() {
            columns[S_INPUT + limb][row] = m31(value);
        }
        let (output, quotient, carries) = mul_witness(N_INV, input);
        write_canonical(&mut columns, S_OUTPUT, S_OUTPUT_SLACK, row, output);
        write_canonical(&mut columns, S_QUOTIENT, S_QUOTIENT_SLACK, row, quotient);
        record_canonical_uses(&mut range_uses, output);
        record_canonical_uses(&mut range_uses, quotient);
        for (limb, carry) in carries.into_iter().enumerate() {
            columns[S_CARRY + limb][row] = enc_signed(carry);
            range_uses.record(RcKind::Rc13, (carry + CARRY_OFFSET) as u32);
        }
        for (limb, digit) in balanced3(output).into_iter().enumerate() {
            columns[S_DIGIT + limb][row] = enc_signed(digit);
            range_uses.record(RcKind::Rc9, (digit + 256) as u32);
        }
    }
    trace.extend(
        columns
            .into_iter()
            .map(|column| col_eval(NTT_SCALING_LOG_SIZE, column)),
    );
    NttBase { trace, range_uses }
}

fn recompose3<F>(limbs: &[F; 3], c256: F, c65536: F) -> F
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Mul<Output = F>,
{
    limbs[0].clone() + c256 * limbs[1].clone() + c65536 * limbs[2].clone()
}

fn add_mul_constraints<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    constant: &[E::F; 3],
    input: &[E::F; 3],
    quotient: &[E::F; 3],
    output: &[E::F; 3],
    carries: &[E::F; 4],
) {
    let q = [m31(Q & 0xff), m31((Q >> 8) & 0xff), m31(Q >> 16)];
    let c256 = E::F::from(m31(256));
    let e0 = constant[0].clone() * input[0].clone()
        - E::F::from(q[0]) * quotient[0].clone()
        - output[0].clone();
    eval.add_constraint(gate.clone() * (e0 - c256.clone() * carries[0].clone()));
    let e1 = constant[0].clone() * input[1].clone() + constant[1].clone() * input[0].clone()
        - E::F::from(q[0]) * quotient[1].clone()
        - E::F::from(q[1]) * quotient[0].clone()
        - output[1].clone()
        + carries[0].clone();
    eval.add_constraint(gate.clone() * (e1 - c256.clone() * carries[1].clone()));
    let e2 = constant[0].clone() * input[2].clone()
        + constant[1].clone() * input[1].clone()
        + constant[2].clone() * input[0].clone()
        - E::F::from(q[0]) * quotient[2].clone()
        - E::F::from(q[1]) * quotient[1].clone()
        - E::F::from(q[2]) * quotient[0].clone()
        - output[2].clone()
        + carries[1].clone();
    eval.add_constraint(gate.clone() * (e2 - c256.clone() * carries[2].clone()));
    let e3 = constant[1].clone() * input[2].clone() + constant[2].clone() * input[1].clone()
        - E::F::from(q[1]) * quotient[2].clone()
        - E::F::from(q[2]) * quotient[1].clone()
        + carries[2].clone();
    eval.add_constraint(gate.clone() * (e3 - c256 * carries[3].clone()));
    let e4 = constant[2].clone() * input[2].clone() - E::F::from(q[2]) * quotient[2].clone()
        + carries[3].clone();
    eval.add_constraint(gate * e4);
}

fn add_canonical_constraint<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    value: &[E::F; 3],
    slack: &[E::F; 3],
) {
    add_canonical_constraint_with_bound(eval, gate, value, slack, Q - 1);
}

fn add_canonical_constraint_with_bound<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    value: &[E::F; 3],
    slack: &[E::F; 3],
    bound: u32,
) {
    let c256 = E::F::from(m31(256));
    let c65536 = E::F::from(m31(1 << 16));
    eval.add_constraint(
        gate * (recompose3(value, c256.clone(), c65536.clone()) + recompose3(slack, c256, c65536)
            - E::F::from(m31(bound))),
    );
}

struct ButterflyTransition<F> {
    active: F,
    input0: F,
    input1: F,
    output0: F,
    diff: F,
    reduce: F,
    borrow: F,
    output_adjustment: i64,
}

fn add_butterfly_transition_constraints<E: EvalAtRow>(
    eval: &mut E,
    transition: ButterflyTransition<E::F>,
) {
    let ButterflyTransition {
        active,
        input0,
        input1,
        output0,
        diff,
        reduce,
        borrow,
        output_adjustment,
    } = transition;
    let one = E::F::one();
    let q = E::F::from(m31(Q));
    eval.add_constraint(reduce.clone() * (one.clone() - reduce.clone()));
    eval.add_constraint(borrow.clone() * (one - borrow.clone()));
    eval.add_constraint(
        active.clone()
            * (input0.clone() + input1.clone() - output0 - q.clone() * reduce
                + E::F::from(enc_signed(output_adjustment))),
    );
    eval.add_constraint(active * (input0 + q * borrow - input1 - diff));
}

fn add_canonical_range_lookups<E: EvalAtRow>(
    eval: &mut E,
    relations: &PrivateKeyEvalRelations,
    gate: E::F,
    value: &[E::F; 3],
    slack: &[E::F; 3],
) {
    for limb in 0..2 {
        eval.add_to_relation(RelationEntry::base(
            &relations.range,
            gate.clone(),
            &range_tuple::<E>(value[limb].clone(), RcKind::Rc8),
        ));
        eval.add_to_relation(RelationEntry::base(
            &relations.range,
            gate.clone(),
            &range_tuple::<E>(slack[limb].clone(), RcKind::Rc8),
        ));
    }
    eval.add_to_relation(RelationEntry::base(
        &relations.range,
        gate.clone(),
        &range_tuple::<E>(value[2].clone(), RcKind::Rc7),
    ));
    eval.add_to_relation(RelationEntry::base(
        &relations.range,
        gate,
        &range_tuple::<E>(slack[2].clone(), RcKind::Rc7),
    ));
}

#[derive(Clone)]
pub struct NttButterflyEval {
    pub relations: PrivateKeyEvalRelations,
}

impl FrameworkEval for NttButterflyEval {
    fn log_size(&self) -> u32 {
        NTT_BUTTERFLY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(butterfly_pre_id("active"));
        let poly = eval.get_preprocessed_column(butterfly_pre_id("poly"));
        let stage = eval.get_preprocessed_column(butterfly_pre_id("stage"));
        let index0 = eval.get_preprocessed_column(butterfly_pre_id("index0"));
        let index1 = eval.get_preprocessed_column(butterfly_pre_id("index1"));
        let twiddle = [
            eval.get_preprocessed_column(butterfly_pre_id("twiddle0")),
            eval.get_preprocessed_column(butterfly_pre_id("twiddle1")),
            eval.get_preprocessed_column(butterfly_pre_id("twiddle2")),
        ];
        let input0: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let input1: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let output0: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let output0_slack: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let diff: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let diff_slack: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let output1: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let output1_slack: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let quotient_slack: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let reduce = eval.next_trace_mask();
        let borrow = eval.next_trace_mask();
        let carries: [E::F; 4] = core::array::from_fn(|_| eval.next_trace_mask());

        let one = E::F::one();
        let c256 = E::F::from(m31(256));
        let c65536 = E::F::from(m31(1 << 16));
        let input0_value = recompose3(&input0, c256.clone(), c65536.clone());
        let input1_value = recompose3(&input1, c256.clone(), c65536.clone());
        let output0_value = recompose3(&output0, c256.clone(), c65536.clone());
        let diff_value = recompose3(&diff, c256, c65536);

        add_butterfly_transition_constraints(
            &mut eval,
            ButterflyTransition {
                active: active.clone(),
                input0: input0_value,
                input1: input1_value,
                output0: output0_value,
                diff: diff_value,
                reduce,
                borrow,
                output_adjustment: 0,
            },
        );
        for (value, slack) in [
            (&output0, &output0_slack),
            (&diff, &diff_slack),
            (&output1, &output1_slack),
            (&quotient, &quotient_slack),
        ] {
            add_canonical_constraint(&mut eval, active.clone(), value, slack);
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
        for (numerator, row_stage, index, value) in [
            (-active.clone(), stage.clone(), index0.clone(), &input0),
            (-active.clone(), stage.clone(), index1.clone(), &input1),
            (active.clone(), next_stage.clone(), index0, &output0),
            (active.clone(), next_stage, index1, &output1),
        ] {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.ntt,
                numerator,
                &[
                    poly.clone(),
                    row_stage,
                    index,
                    value[0].clone(),
                    value[1].clone(),
                    value[2].clone(),
                ],
            ));
        }
        for (value, slack) in [
            (&output0, &output0_slack),
            (&diff, &diff_slack),
            (&output1, &output1_slack),
            (&quotient, &quotient_slack),
        ] {
            add_canonical_range_lookups(&mut eval, &self.relations, active.clone(), value, slack);
        }
        for carry in carries {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(carry + E::F::from(m31(CARRY_OFFSET as u32)), RcKind::Rc13),
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
    pub relations: PrivateKeyEvalRelations,
}

impl FrameworkEval for NttScalingEval {
    fn log_size(&self) -> u32 {
        NTT_SCALING_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(scaling_pre_id("active"));
        let eval_start = eval.get_preprocessed_column(scaling_pre_id("eval_start"));
        let eval_end = eval.get_preprocessed_column(scaling_pre_id("eval_end"));
        let poly = eval.get_preprocessed_column(scaling_pre_id("poly"));
        let index = eval.get_preprocessed_column(scaling_pre_id("index"));
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
        let constant = split_u23(N_INV).map(|value| E::F::from(m31(value)));
        add_mul_constraints(
            &mut eval,
            active.clone(),
            &constant,
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
            &self.relations.ntt,
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
            &self.relations,
            active.clone(),
            &output,
            &output_slack,
        );
        add_canonical_range_lookups(
            &mut eval,
            &self.relations,
            active.clone(),
            &quotient,
            &quotient_slack,
        );
        for carry in carries {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(carry + E::F::from(m31(CARRY_OFFSET as u32)), RcKind::Rc13),
            ));
        }
        for digit in digits {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(digit + E::F::from(m31(256)), RcKind::Rc9),
            ));
        }
        let mut tuple = vec![poly + E::F::from(m31(A_EVAL_BASE as u32))];
        tuple.extend(acc_masks.iter().map(|mask| mask[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.relations.eval, -eval_end, &tuple));
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NttClaims {
    pub butterfly: SecureField,
    pub scaling: SecureField,
}

pub struct NttInteraction {
    pub trace: Vec<ColEval>,
    pub a_evals: Vec<SecureField>,
    pub claims: NttClaims,
}

fn push_range_entries(
    entries: &mut Vec<(SecureField, SecureField)>,
    relations: &PrivateKeyEvalRelations,
    value: u32,
) {
    let limbs = split_u23(value);
    let slack = split_u23(Q - 1 - value);
    for limb in 0..2 {
        entries.push((
            SecureField::one(),
            range_denominator(&relations.range, limbs[limb], RcKind::Rc8),
        ));
        entries.push((
            SecureField::one(),
            range_denominator(&relations.range, slack[limb], RcKind::Rc8),
        ));
    }
    entries.push((
        SecureField::one(),
        range_denominator(&relations.range, limbs[2], RcKind::Rc7),
    ));
    entries.push((
        SecureField::one(),
        range_denominator(&relations.range, slack[2], RcKind::Rc7),
    ));
}

pub fn gen_ntt_interaction(
    a_hat: &[NttPoly],
    r: SecureField,
    s: SecureField,
    relations: &PrivateKeyEvalRelations,
) -> NttInteraction {
    assert_eq!(a_hat.len(), MATRIX_POLYS);
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut states = a_hat.to_vec();
    let mut rows =
        vec![vec![(zero, one); NTT_BUTTERFLY_LOGUP_ENTRIES]; 1usize << NTT_BUTTERFLY_LOG_SIZE];
    for (row, item) in butterfly_schedule().iter().enumerate() {
        let input0 = states[item.poly][item.index0];
        let input1 = states[item.poly][item.index1];
        let input0_limbs = split_u23(input0);
        let input1_limbs = split_u23(input1);
        let mut entries = Vec::with_capacity(NTT_BUTTERFLY_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31(item.stage as u32),
                m31(item.index0 as u32),
                m31(input0_limbs[0]),
                m31(input0_limbs[1]),
                m31(input0_limbs[2]),
            ]),
        ));
        entries.push((
            -one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31(item.stage as u32),
                m31(item.index1 as u32),
                m31(input1_limbs[0]),
                m31(input1_limbs[1]),
                m31(input1_limbs[2]),
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
        let output0_limbs = split_u23(output0);
        let output1_limbs = split_u23(output1);
        entries.push((
            one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31((item.stage + 1) as u32),
                m31(item.index0 as u32),
                m31(output0_limbs[0]),
                m31(output0_limbs[1]),
                m31(output0_limbs[2]),
            ]),
        ));
        entries.push((
            one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31((item.stage + 1) as u32),
                m31(item.index1 as u32),
                m31(output1_limbs[0]),
                m31(output1_limbs[1]),
                m31(output1_limbs[2]),
            ]),
        ));
        states[item.poly][item.index0] = output0;
        states[item.poly][item.index1] = output1;
        for value in [output0, diff, output1, quotient] {
            push_range_entries(&mut entries, relations, value);
        }
        for carry in carries {
            entries.push((
                one,
                range_denominator(
                    &relations.range,
                    (carry + CARRY_OFFSET) as u32,
                    RcKind::Rc13,
                ),
            ));
        }
        assert_eq!(entries.len(), NTT_BUTTERFLY_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    let (butterfly_trace, butterfly_claim) =
        gen_batched_logup(NTT_BUTTERFLY_LOG_SIZE, &rows, NTT_BUTTERFLY_LOGUP_ENTRIES);

    let mut rows =
        vec![vec![(zero, one); NTT_SCALING_LOGUP_ENTRIES]; 1usize << NTT_SCALING_LOG_SIZE];
    let mut acc = vec![zero; 1usize << NTT_SCALING_LOG_SIZE];
    let mut a_evals = vec![zero; MATRIX_POLYS];
    let mut running = zero;
    for (row, item) in scaling_schedule().iter().enumerate() {
        let input = states[item.poly][item.index];
        let input_limbs = split_u23(input);
        let mut entries = Vec::with_capacity(NTT_SCALING_LOGUP_ENTRIES);
        entries.push((
            -one,
            relations.ntt.combine(&[
                m31(item.poly as u32),
                m31(NTT_STAGES as u32),
                m31(item.index as u32),
                m31(input_limbs[0]),
                m31(input_limbs[1]),
                m31(input_limbs[2]),
            ]),
        ));
        let (output, quotient, carries) = mul_witness(N_INV, input);
        for value in [output, quotient] {
            push_range_entries(&mut entries, relations, value);
        }
        for carry in carries {
            entries.push((
                one,
                range_denominator(
                    &relations.range,
                    (carry + CARRY_OFFSET) as u32,
                    RcKind::Rc13,
                ),
            ));
        }
        let digits = balanced3(output);
        let digit_row = SecureField::from(enc_signed(digits[0]))
            + s * SecureField::from(enc_signed(digits[1]))
            + s * s * SecureField::from(enc_signed(digits[2]));
        running = if item.eval_start {
            digit_row
        } else {
            running * r + digit_row
        };
        acc[row] = running;
        for digit in digits {
            entries.push((
                one,
                range_denominator(&relations.range, (digit + 256) as u32, RcKind::Rc9),
            ));
        }
        if item.eval_end {
            a_evals[item.poly] = running;
            let coords = running.to_m31_array();
            entries.push((
                -one,
                relations.eval.combine(&[
                    m31((A_EVAL_BASE + item.poly) as u32),
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
    let mut scaling_trace: Vec<_> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coordinate| {
            col_eval(
                NTT_SCALING_LOG_SIZE,
                acc.iter()
                    .map(|value| value.to_m31_array()[coordinate])
                    .collect(),
            )
        })
        .collect();
    let (scaling_logup, scaling_claim) =
        gen_batched_logup(NTT_SCALING_LOG_SIZE, &rows, NTT_SCALING_LOGUP_ENTRIES);
    scaling_trace.extend(scaling_logup);
    let mut trace = butterfly_trace;
    trace.extend(scaling_trace);
    NttInteraction {
        trace,
        a_evals,
        claims: NttClaims {
            butterfly: butterfly_claim,
            scaling: scaling_claim,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_key_eval::proof_test::{active_id as test_active_id, OneRowAir};
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;

    #[derive(Clone, Copy)]
    enum Formula {
        Butterfly { output_adjustment: i64 },
        Normalizer { constant: u32 },
        Canonical { bound: u32 },
    }

    #[derive(Clone)]
    struct FormulaEval {
        formula: Formula,
    }

    impl FrameworkEval for FormulaEval {
        fn log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let fixed_active = eval.get_preprocessed_column(test_active_id());
            let active = eval.next_trace_mask();
            eval.add_constraint(active.clone() - fixed_active);
            match self.formula {
                Formula::Butterfly { output_adjustment } => {
                    let input0 = eval.next_trace_mask();
                    let input1 = eval.next_trace_mask();
                    let output0 = eval.next_trace_mask();
                    let diff = eval.next_trace_mask();
                    let reduce = eval.next_trace_mask();
                    let borrow = eval.next_trace_mask();
                    add_butterfly_transition_constraints(
                        &mut eval,
                        ButterflyTransition {
                            active,
                            input0,
                            input1,
                            output0,
                            diff,
                            reduce,
                            borrow,
                            output_adjustment,
                        },
                    );
                }
                Formula::Normalizer { constant } => {
                    let input = core::array::from_fn(|_| eval.next_trace_mask());
                    let quotient = core::array::from_fn(|_| eval.next_trace_mask());
                    let output = core::array::from_fn(|_| eval.next_trace_mask());
                    let carries = core::array::from_fn(|_| eval.next_trace_mask());
                    add_mul_constraints(
                        &mut eval,
                        active,
                        &split_u23(constant).map(|value| E::F::from(m31(value))),
                        &input,
                        &quotient,
                        &output,
                        &carries,
                    );
                }
                Formula::Canonical { bound } => {
                    let value = core::array::from_fn(|_| eval.next_trace_mask());
                    let slack = core::array::from_fn(|_| eval.next_trace_mask());
                    add_canonical_constraint_with_bound(&mut eval, active, &value, &slack, bound);
                }
            }
            let dummy = eval.next_interaction_mask(INTERACTION_TRACE_IDX, [0]);
            eval.add_constraint(dummy[0].clone());
            eval
        }
    }

    fn assert_forged_formula_rejected(label: &str, trace: &[M31], forged: Formula, exact: Formula) {
        let mut prover = OneRowAir::new(FormulaEval { formula: forged }, trace);
        let proof = air_core::prove(&mut [&mut prover], PcsConfig::default())
            .unwrap_or_else(|error| panic!("{label}: forged proving failed: {error:?}"));
        let mut forged_verifier = OneRowAir::new(FormulaEval { formula: forged }, trace);
        air_core::verify(&mut [&mut forged_verifier], &proof)
            .unwrap_or_else(|error| panic!("{label}: forged control failed: {error:?}"));
        let mut exact_verifier = OneRowAir::new(FormulaEval { formula: exact }, trace);
        assert!(
            air_core::verify(&mut [&mut exact_verifier], &proof).is_err(),
            "{label}: production formula must reject"
        );
    }

    #[test]
    fn malformed_inverse_ntt_rows_prove_only_under_forged_formulas() {
        assert_forged_formula_rejected(
            "inverse-butterfly transition",
            &[m31(1), m31(10), m31(3), m31(14), m31(7), m31(0), m31(0)],
            Formula::Butterfly {
                output_adjustment: 1,
            },
            Formula::Butterfly {
                output_adjustment: 0,
            },
        );

        let input = 123_456;
        let (output, quotient, carries) = mul_witness(N_INV - 1, input);
        let mut normalization_trace = vec![m31(1)];
        normalization_trace.extend(split_u23(input).map(m31));
        normalization_trace.extend(split_u23(quotient).map(m31));
        normalization_trace.extend(split_u23(output).map(m31));
        normalization_trace.extend(carries.map(enc_signed));
        assert_forged_formula_rejected(
            "inverse normalization",
            &normalization_trace,
            Formula::Normalizer {
                constant: N_INV - 1,
            },
            Formula::Normalizer { constant: N_INV },
        );

        let alias = Q + 5;
        let slack = Q - 1 - 5;
        let mut alias_trace = vec![m31(1)];
        alias_trace.extend(split_u23(alias).map(m31));
        alias_trace.extend(split_u23(slack).map(m31));
        assert_forged_formula_rejected(
            "inverse-NTT modular alias",
            &alias_trace,
            Formula::Canonical { bound: 2 * Q - 1 },
            Formula::Canonical { bound: Q - 1 },
        );
    }

    #[test]
    fn schedules_cover_every_required_cell_once() {
        let schedule = butterfly_schedule();
        assert_eq!(schedule.len(), MATRIX_POLYS * NTT_STAGES * N / 2);
        let mut seen = vec![vec![vec![false; N]; NTT_STAGES]; MATRIX_POLYS];
        for item in schedule {
            assert!(!seen[item.poly][item.stage][item.index0]);
            assert!(!seen[item.poly][item.stage][item.index1]);
            seen[item.poly][item.stage][item.index0] = true;
            seen[item.poly][item.stage][item.index1] = true;
        }
        assert!(seen.into_iter().flatten().flatten().all(|value| value));
        assert_eq!(scaling_schedule().len(), MATRIX_POLYS * N);
    }

    #[test]
    fn inverse_ntt_and_horner_match_independent_reference() {
        let expanded = crate::reference::expand_a::expand_a(&[9; 32]);
        let mut a_hat = Vec::new();
        for i in 0..K {
            for j in 0..L {
                a_hat.push(expanded.matrix[i][j]);
            }
        }
        let r = SecureField::from(m31(13));
        let s = SecureField::from(m31(29));
        let interaction = gen_ntt_interaction(&a_hat, r, s, &PrivateKeyEvalRelations::dummy());
        for (poly, source) in a_hat.iter().enumerate() {
            let coefficients = crate::reference::ntt::ntt_inverse(source);
            let mut expected = SecureField::zero();
            for &coefficient in coefficients.iter().rev() {
                let digits = balanced3(coefficient);
                let row = SecureField::from(enc_signed(digits[0]))
                    + s * SecureField::from(enc_signed(digits[1]))
                    + s * s * SecureField::from(enc_signed(digits[2]));
                expected = expected * r + row;
            }
            assert_eq!(interaction.a_evals[poly], expected);
        }
    }

    #[test]
    fn multiplication_witness_is_exact_at_boundaries() {
        let zetas = zeta_table();
        for constant in [1, N_INV, Q - 1, zetas[1], Q - zetas[255]] {
            for value in [0, 1, 255, 256, Q / 2, Q - 2, Q - 1] {
                let (output, quotient, carries) = mul_witness(constant, value);
                assert_eq!(
                    constant as u64 * value as u64,
                    output as u64 + Q as u64 * quotient as u64
                );
                assert!(output < Q && quotient < Q);
                assert!(carries
                    .iter()
                    .all(|carry| (-CARRY_OFFSET..CARRY_OFFSET).contains(carry)));
            }
        }
    }

    #[test]
    fn base_range_census_and_interaction_shape_are_exact() {
        let expanded = crate::reference::expand_a::expand_a(&[42; 32]);
        let a_hat: Vec<_> = expanded.matrix.into_iter().flatten().collect();
        let base = gen_ntt_base(&a_hat);
        let interaction = gen_ntt_interaction(
            &a_hat,
            SecureField::from(m31(7)),
            SecureField::from(m31(11)),
            &PrivateKeyEvalRelations::dummy(),
        );
        assert_eq!(interaction.a_evals.len(), MATRIX_POLYS);
        assert_eq!(
            interaction.trace.len(),
            NTT_BUTTERFLY_INTERACTION_COLS + NTT_SCALING_INTERACTION_COLS
        );
        let butterfly_rows = (MATRIX_POLYS * NTT_STAGES * N / 2) as u32;
        let scaling_rows = (MATRIX_POLYS * N) as u32;
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc8).iter().sum::<u32>(),
            16 * butterfly_rows + 8 * scaling_rows
        );
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc7).iter().sum::<u32>(),
            8 * butterfly_rows + 4 * scaling_rows
        );
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc13).iter().sum::<u32>(),
            4 * butterfly_rows + 4 * scaling_rows
        );
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc9).iter().sum::<u32>(),
            3 * scaling_rows
        );
        assert_eq!(
            base.range_uses
                .for_kind(RcKind::Ternary)
                .iter()
                .sum::<u32>(),
            0
        );
    }
}
