//! WO-Q10.4b phase-1 spike: the fixed virtual-intermediate NTT protocol.
//!
//! This is deliberately an integration-test-only harness. It commits no
//! production code and models the three eventual MLE tie-backs by checking the
//! same evaluations directly against the dense endpoint/aux oracles.

use num_traits::{One, Zero};
use serde::Serialize;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fields::FieldExpOps;
use stwo_mldsa::constants::{K, L, N, Q, ZETA};
use stwo_mldsa::expand_a::derive_expand_a_witness;
use stwo_mldsa::reference::ntt::ntt_inverse;

type SF = SecureField;

const REAL_POLYS: usize = K * L;
const PADDED_POLYS: usize = 32;
const STAGES: usize = 8;
const HALF_N: usize = N / 2;
const STATE_VARS: usize = 13;
const AUX_VARS: usize = 15;
const AUX_COLS: usize = 28;
const LAYER_ROUNDS: usize = STATE_VARS;
const ROUND_COEFFS: usize = 4;
const STATE_LINE_COEFFS: usize = STATE_VARS + 1;
const AUX_LINE_COEFFS: usize = AUX_VARS + 1;
const N_INV: u32 = 8_347_681;

// Exactly the WO-4a non-state witnesses (24), followed by A-406-FU's four
// limb-explicit witnesses. Output limbs remain virtual state, never aux.
const A_OUT0_SLACK: usize = 0; // 3
const A_DIFF: usize = 3; // 3
const A_DIFF_SLACK: usize = 6; // 3
const A_OUT1_SLACK: usize = 9; // 3
const A_QUOT: usize = 12; // 3
const A_QUOT_SLACK: usize = 15; // 3
const A_REDUCE: usize = 18;
const A_BORROW: usize = 19;
const A_MUL_CARRY: usize = 20; // 4
const A_ADD_CARRY: usize = 24; // 2
const A_SUB_BORROW: usize = 26; // 2

const O_IN0: usize = 0; // 3
const O_IN1: usize = 3; // 3
const O_AUX: usize = 6; // 28
const O_TWIDDLE: usize = O_AUX + AUX_COLS; // 3
const O_BRANCH: usize = O_TWIDDLE + 3;
const O_EQ_RHO: usize = O_BRANCH + 1;
const O_EQ_Z: usize = O_EQ_RHO + 1;
const ORACLE_COLS: usize = O_EQ_Z + 1;

type LayerVerifyOutput = (Vec<SF>, [SF; 3], Vec<SF>);

#[inline]
fn sf(value: u32) -> SF {
    SF::from(BaseField::from(value))
}

#[inline]
fn sf_i(value: i64) -> SF {
    const P: i64 = (1 << 31) - 1;
    sf(value.rem_euclid(P) as u32)
}

#[inline]
fn split3(value: u32) -> [u32; 3] {
    [value & 0xff, (value >> 8) & 0xff, value >> 16]
}

#[inline]
fn rlc(values: &[SF], challenge: SF) -> SF {
    let mut power = SF::one();
    let mut out = SF::zero();
    for value in values {
        out += power * *value;
        power *= challenge;
    }
    out
}

fn poly_eval<const M: usize>(coeffs: &[SF; M], x: SF) -> SF {
    coeffs
        .iter()
        .rev()
        .fold(SF::zero(), |acc, coefficient| acc * x + *coefficient)
}

fn interpolate<const M: usize>(ys: [SF; M]) -> [SF; M] {
    let mut out = [SF::zero(); M];
    for (i, yi) in ys.into_iter().enumerate() {
        let xi = sf(i as u32);
        let mut basis = vec![SF::one()];
        let mut denominator = SF::one();
        for j in 0..M {
            if i == j {
                continue;
            }
            let xj = sf(j as u32);
            denominator *= xi - xj;
            let mut next = vec![SF::zero(); basis.len() + 1];
            for (degree, coefficient) in basis.iter().enumerate() {
                next[degree] -= *coefficient * xj;
                next[degree + 1] += *coefficient;
            }
            basis = next;
        }
        let scale = yi * denominator.inverse();
        for (degree, coefficient) in basis.into_iter().enumerate() {
            out[degree] += scale * coefficient;
        }
    }
    out
}

/// Dense multilinear evaluation in the pinned MSB-first convention.
fn ml_eval(evals: &[SF], point: &[SF]) -> SF {
    assert_eq!(evals.len(), 1usize << point.len());
    let mut layer = evals.to_vec();
    for coordinate in point {
        let half = layer.len() / 2;
        for row in 0..half {
            let left = layer[row];
            let right = layer[half + row];
            layer[row] = left + *coordinate * (right - left);
        }
        layer.truncate(half);
    }
    layer[0]
}

fn eq_table(point: &[SF]) -> Vec<SF> {
    (0..1usize << point.len())
        .map(|index| {
            point
                .iter()
                .enumerate()
                .fold(SF::one(), |acc, (coordinate, value)| {
                    let bit = (index >> (point.len() - 1 - coordinate)) & 1;
                    acc * if bit == 0 { SF::one() - *value } else { *value }
                })
        })
        .collect()
}

fn eq_eval(left: &[SF], right: &[SF]) -> SF {
    left.iter().zip(right).fold(SF::one(), |acc, (a, b)| {
        acc * (*a * *b + (SF::one() - *a) * (SF::one() - *b))
    })
}

fn zeta_table() -> [u32; N] {
    let mut powers = [0u64; N];
    let mut current = 1u64;
    for value in &mut powers {
        *value = current;
        current = current * ZETA as u64 % Q as u64;
    }
    core::array::from_fn(|index| powers[(index as u8).reverse_bits() as usize] as u32)
}

fn stage_twiddles() -> [Vec<u32>; STAGES] {
    let zetas = zeta_table();
    let mut m = N;
    let mut len = 1usize;
    core::array::from_fn(|_| {
        let mut out = Vec::with_capacity(HALF_N);
        let mut start = 0;
        while start < N {
            m -= 1;
            let twiddle = Q - zetas[m];
            out.extend(core::iter::repeat_n(twiddle, len));
            start += 2 * len;
        }
        len <<= 1;
        out
    })
}

#[inline]
fn pair_indices(stage: usize, butterfly: usize) -> (usize, usize) {
    let low_mask = (1usize << stage) - 1;
    let low = butterfly & low_mask;
    let high = butterfly >> stage;
    let index0 = (high << (stage + 1)) | low;
    (index0, index0 | (1 << stage))
}

#[inline]
fn butterfly_index(stage: usize, index: usize) -> usize {
    let low_mask = (1usize << stage) - 1;
    ((index >> (stage + 1)) << stage) | (index & low_mask)
}

#[inline]
fn state_bit_position(stage: usize) -> usize {
    5 + (7 - stage)
}

#[inline]
fn aux_row(poly: usize, stage: usize, butterfly: usize) -> usize {
    (poly << 10) | (stage << 7) | butterfly
}

fn mul_witness(constant: u32, value: u32) -> (u32, u32, [i64; 4]) {
    let product = constant as u64 * value as u64;
    let output = (product % Q as u64) as u32;
    let quotient = (product / Q as u64) as u32;
    let z = split3(constant).map(i64::from);
    let x = split3(value).map(i64::from);
    let q = split3(Q).map(i64::from);
    let k = split3(quotient).map(i64::from);
    let out = split3(output).map(i64::from);
    let e0 = z[0] * x[0] - q[0] * k[0] - out[0];
    let c0 = e0 / 256;
    let e1 = z[0] * x[1] + z[1] * x[0] - q[0] * k[1] - q[1] * k[0] - out[1] + c0;
    let c1 = e1 / 256;
    let e2 =
        z[0] * x[2] + z[1] * x[1] + z[2] * x[0] - q[0] * k[2] - q[1] * k[1] - q[2] * k[0] - out[2]
            + c1;
    let c2 = e2 / 256;
    let e3 = z[1] * x[2] + z[2] * x[1] - q[1] * k[2] - q[2] * k[1] + c2;
    let c3 = e3 / 256;
    assert_eq!(z[2] * x[2] - q[2] * k[2] + c3, 0);
    (output, quotient, [c0, c1, c2, c3])
}

fn canonical_slack(value: u32) -> [u32; 3] {
    split3(Q - 1 - value)
}

fn write3(aux: &mut [Vec<SF>; AUX_COLS], base: usize, row: usize, value: u32) {
    for (limb, byte) in split3(value).into_iter().enumerate() {
        aux[base + limb][row] = sf(byte);
    }
}

#[derive(Clone)]
struct SpikeWitness {
    /// stages[0] is the committed input and stages[8] the committed output.
    stages: Vec<[Vec<SF>; 3]>,
    raw_stages: Vec<Vec<[u32; N]>>,
    aux: [Vec<SF>; AUX_COLS],
    twiddles: [Vec<u32>; STAGES],
}

fn sample_inputs() -> Vec<[u32; N]> {
    let mut inputs = derive_expand_a_witness([0x42; 32])
        .expect("fixed rho expands")
        .a_hat;
    assert_eq!(inputs.len(), REAL_POLYS);
    inputs.resize(PADDED_POLYS, [0u32; N]);
    inputs
}

fn build_witness() -> SpikeWitness {
    let twiddles = stage_twiddles();
    let mut raw_stages = vec![sample_inputs()];
    let mut aux: [Vec<SF>; AUX_COLS] =
        core::array::from_fn(|_| vec![SF::zero(); 1usize << AUX_VARS]);
    let q = split3(Q).map(i64::from);

    for stage in 0..STAGES {
        let mut next = raw_stages[stage].clone();
        for poly in 0..PADDED_POLYS {
            for (butterfly, &twiddle) in twiddles[stage].iter().enumerate() {
                let row = aux_row(poly, stage, butterfly);
                let (index0, index1) = pair_indices(stage, butterfly);
                let input0 = raw_stages[stage][poly][index0];
                let input1 = raw_stages[stage][poly][index1];
                let in0 = split3(input0).map(i64::from);
                let in1 = split3(input1).map(i64::from);

                let sum = input0 + input1;
                let reduce = sum >= Q;
                let output0 = if reduce { sum - Q } else { sum };
                let out0 = split3(output0).map(i64::from);
                let add0 = (in0[0] + in1[0] - i64::from(reduce) * q[0] - out0[0]) / 256;
                let add1 = (in0[1] + in1[1] + add0 - i64::from(reduce) * q[1] - out0[1]) / 256;
                assert!(
                    (-1..=1).contains(&add0),
                    "stage={stage} poly={poly} butterfly={butterfly} input0={input0} input1={input1} reduce={reduce} q={q:?} add0={add0} add1={add1}"
                );
                assert!(
                    (-1..=1).contains(&add1),
                    "stage={stage} poly={poly} butterfly={butterfly} input0={input0} input1={input1} reduce={reduce} q={q:?} add0={add0} add1={add1}"
                );
                assert_eq!(in0[2] + in1[2] + add1 - i64::from(reduce) * q[2], out0[2]);

                let borrow = input0 < input1;
                let diff = if borrow {
                    input0 + Q - input1
                } else {
                    input0 - input1
                };
                let diff_bytes = split3(diff).map(i64::from);
                let sub0 = -(in0[0] + i64::from(borrow) * q[0] - in1[0] - diff_bytes[0]) / 256;
                let sub1 =
                    -(in0[1] + i64::from(borrow) * q[1] - in1[1] - sub0 - diff_bytes[1]) / 256;
                assert!(
                    (-1..=1).contains(&sub0),
                    "stage={stage} poly={poly} butterfly={butterfly} input0={input0} input1={input1} borrow={borrow} q={q:?} sub0={sub0} sub1={sub1}"
                );
                assert!(
                    (-1..=1).contains(&sub1),
                    "stage={stage} poly={poly} butterfly={butterfly} input0={input0} input1={input1} borrow={borrow} q={q:?} sub0={sub0} sub1={sub1}"
                );
                assert_eq!(
                    in0[2] + i64::from(borrow) * q[2] - in1[2] - sub1,
                    diff_bytes[2]
                );

                let (output1, quotient, carries) = mul_witness(twiddle, diff);
                next[poly][index0] = output0;
                next[poly][index1] = output1;

                write3(&mut aux, A_OUT0_SLACK, row, Q - 1 - output0);
                write3(&mut aux, A_DIFF, row, diff);
                write3(&mut aux, A_DIFF_SLACK, row, Q - 1 - diff);
                write3(&mut aux, A_OUT1_SLACK, row, Q - 1 - output1);
                write3(&mut aux, A_QUOT, row, quotient);
                write3(&mut aux, A_QUOT_SLACK, row, Q - 1 - quotient);
                aux[A_REDUCE][row] = sf(u32::from(reduce));
                aux[A_BORROW][row] = sf(u32::from(borrow));
                for limb in 0..4 {
                    aux[A_MUL_CARRY + limb][row] = sf_i(carries[limb]);
                }
                aux[A_ADD_CARRY][row] = sf_i(add0);
                aux[A_ADD_CARRY + 1][row] = sf_i(add1);
                aux[A_SUB_BORROW][row] = sf_i(sub0);
                aux[A_SUB_BORROW + 1][row] = sf_i(sub1);
            }
        }
        raw_stages.push(next);
    }

    let stages = raw_stages
        .iter()
        .map(|stage| {
            core::array::from_fn(|limb| {
                stage
                    .iter()
                    .flat_map(|poly| poly.iter().map(move |value| sf(split3(*value)[limb])))
                    .collect()
            })
        })
        .collect();
    SpikeWitness {
        stages,
        raw_stages,
        aux,
        twiddles,
    }
}

fn state_pair_points(point: &[SF], stage: usize) -> (Vec<SF>, Vec<SF>) {
    let bit = state_bit_position(stage);
    let mut point0 = point.to_vec();
    let mut point1 = point.to_vec();
    point0[bit] = SF::zero();
    point1[bit] = SF::one();
    (point0, point1)
}

fn aux_point(point: &[SF], stage: usize) -> Vec<SF> {
    let bit = state_bit_position(stage);
    let mut out = Vec::with_capacity(AUX_VARS);
    out.extend_from_slice(&point[..5]);
    for shift in (0..3).rev() {
        out.push(sf(((stage >> shift) & 1) as u32));
    }
    out.extend_from_slice(&point[5..bit]);
    out.extend_from_slice(&point[bit + 1..]);
    assert_eq!(out.len(), AUX_VARS);
    out
}

fn twiddle_claims(witness: &SpikeWitness, stage: usize, point: &[SF]) -> [SF; 3] {
    let mut columns: [Vec<SF>; 3] =
        core::array::from_fn(|_| vec![SF::zero(); PADDED_POLYS * HALF_N]);
    for poly in 0..PADDED_POLYS {
        for butterfly in 0..HALF_N {
            let bytes = split3(witness.twiddles[stage][butterfly]);
            for limb in 0..3 {
                columns[limb][poly * HALF_N + butterfly] = sf(bytes[limb]);
            }
        }
    }
    core::array::from_fn(|limb| ml_eval(&columns[limb], point))
}

fn project_twiddle_point(state_point: &[SF], stage: usize) -> Vec<SF> {
    let bit = state_bit_position(stage);
    let mut point = Vec::with_capacity(12);
    point.extend_from_slice(&state_point[..bit]);
    point.extend_from_slice(&state_point[bit + 1..]);
    point
}

fn recompose(bytes: &[SF]) -> SF {
    bytes[0] + sf(256) * bytes[1] + sf(1 << 16) * bytes[2]
}

/// The fixed layer summand. Residual order is frozen as: three diff limb ties,
/// two high multiplication limbs, four canonical slacks, then the two boolean
/// witnesses (reduce and borrow). All four new inter-limb carries are signed
/// ternary and use the A-501 shifted lookup in production (A-406-FU2/FU3),
/// never a cubic polynomial in this degree-3 sumcheck.
fn layer_summand(values: &[SF; ORACLE_COLS], beta: SF, gamma: SF) -> SF {
    let in0: [SF; 3] = core::array::from_fn(|i| values[O_IN0 + i]);
    let in1: [SF; 3] = core::array::from_fn(|i| values[O_IN1 + i]);
    let aux = &values[O_AUX..O_AUX + AUX_COLS];
    let tw: [SF; 3] = core::array::from_fn(|i| values[O_TWIDDLE + i]);
    let branch = values[O_BRANCH];
    let q = split3(Q).map(sf);
    let c256 = sf(256);
    let reduce = aux[A_REDUCE];
    let borrow = aux[A_BORROW];
    let add = [aux[A_ADD_CARRY], aux[A_ADD_CARRY + 1]];
    let sub = [aux[A_SUB_BORROW], aux[A_SUB_BORROW + 1]];

    let out0 = [
        in0[0] + in1[0] - reduce * q[0] - c256 * add[0],
        in0[1] + in1[1] + add[0] - reduce * q[1] - c256 * add[1],
        in0[2] + in1[2] + add[1] - reduce * q[2],
    ];
    let diff_expr = [
        in0[0] + borrow * q[0] - in1[0] + c256 * sub[0],
        in0[1] + borrow * q[1] - in1[1] - sub[0] + c256 * sub[1],
        in0[2] + borrow * q[2] - in1[2] - sub[1],
    ];
    let diff: [SF; 3] = core::array::from_fn(|i| aux[A_DIFF + i]);
    let quotient: [SF; 3] = core::array::from_fn(|i| aux[A_QUOT + i]);
    let carry: [SF; 4] = core::array::from_fn(|i| aux[A_MUL_CARRY + i]);
    let out1 = [
        tw[0] * diff[0] - q[0] * quotient[0] - c256 * carry[0],
        tw[0] * diff[1] + tw[1] * diff[0] - q[0] * quotient[1] - q[1] * quotient[0] + carry[0]
            - c256 * carry[1],
        tw[0] * diff[2] + tw[1] * diff[1] + tw[2] * diff[0]
            - q[0] * quotient[2]
            - q[1] * quotient[1]
            - q[2] * quotient[0]
            + carry[1]
            - c256 * carry[2],
    ];
    let output: [SF; 3] =
        core::array::from_fn(|i| (SF::one() - branch) * out0[i] + branch * out1[i]);

    let high3 = tw[1] * diff[2] + tw[2] * diff[1] - q[1] * quotient[2] - q[2] * quotient[1]
        + carry[2]
        - c256 * carry[3];
    let high4 = tw[2] * diff[2] - q[2] * quotient[2] + carry[3];
    let q_minus_one = sf(Q - 1);
    let canonical = |value: &[SF], slack_base: usize| {
        recompose(value) + recompose(&aux[slack_base..slack_base + 3]) - q_minus_one
    };
    let bit = |value: SF| value * (SF::one() - value);
    let residuals = [
        diff[0] - diff_expr[0],
        diff[1] - diff_expr[1],
        diff[2] - diff_expr[2],
        high3,
        high4,
        canonical(&out0, A_OUT0_SLACK),
        canonical(&diff, A_DIFF_SLACK),
        canonical(&out1, A_OUT1_SLACK),
        canonical(&quotient, A_QUOT_SLACK),
        bit(reduce),
        bit(borrow),
    ];
    values[O_EQ_RHO] * rlc(&output, beta) + gamma * values[O_EQ_Z] * rlc(&residuals, gamma)
}

struct LayerOracle {
    columns: [Vec<SF>; ORACLE_COLS],
    beta: SF,
    gamma: SF,
}

impl LayerOracle {
    fn new(
        witness: &SpikeWitness,
        stage: usize,
        rho: &[SF],
        z: &[SF],
        beta: SF,
        gamma: SF,
    ) -> Self {
        let mut columns: [Vec<SF>; ORACLE_COLS] =
            core::array::from_fn(|_| vec![SF::zero(); 1usize << STATE_VARS]);
        let eq_rho = eq_table(rho);
        let eq_z = eq_table(z);
        for flat in 0..1usize << STATE_VARS {
            let poly = flat >> 8;
            let index = flat & 0xff;
            let butterfly = butterfly_index(stage, index);
            let (index0, index1) = pair_indices(stage, butterfly);
            for limb in 0..3 {
                columns[O_IN0 + limb][flat] = witness.stages[stage][limb][poly * N + index0];
                columns[O_IN1 + limb][flat] = witness.stages[stage][limb][poly * N + index1];
            }
            let row = aux_row(poly, stage, butterfly);
            for aux in 0..AUX_COLS {
                columns[O_AUX + aux][flat] = witness.aux[aux][row];
            }
            let twiddle = split3(witness.twiddles[stage][butterfly]);
            for limb in 0..3 {
                columns[O_TWIDDLE + limb][flat] = sf(twiddle[limb]);
            }
            columns[O_BRANCH][flat] = sf(((index >> stage) & 1) as u32);
            columns[O_EQ_RHO][flat] = eq_rho[flat];
            columns[O_EQ_Z][flat] = eq_z[flat];
        }
        Self {
            columns,
            beta,
            gamma,
        }
    }

    fn round_poly(&self) -> [SF; ROUND_COEFFS] {
        let half = self.columns[0].len() / 2;
        let mut ys = [SF::zero(); ROUND_COEFFS];
        let mut values = [SF::zero(); ORACLE_COLS];
        for (sample, y) in ys.iter_mut().enumerate() {
            let t = sf(sample as u32);
            for row in 0..half {
                for (column, values_column) in self.columns.iter().zip(values.iter_mut()) {
                    *values_column = column[row] + t * (column[half + row] - column[row]);
                }
                *y += layer_summand(&values, self.beta, self.gamma);
            }
        }
        interpolate(ys)
    }

    fn fix_first(&mut self, challenge: SF) {
        let half = self.columns[0].len() / 2;
        for column in &mut self.columns {
            for row in 0..half {
                let left = column[row];
                let right = column[half + row];
                column[row] = left + challenge * (right - left);
            }
            column.truncate(half);
        }
    }
}

fn line_poly<const M: usize>(oracle: &[SF], point0: &[SF], point1: &[SF]) -> [SF; M] {
    let ys = core::array::from_fn(|sample| {
        let t = sf(sample as u32);
        let point: Vec<SF> = point0
            .iter()
            .zip(point1)
            .map(|(a, b)| *a + t * (*b - *a))
            .collect();
        ml_eval(oracle, &point)
    });
    interpolate(ys)
}

#[derive(Clone, Serialize)]
struct LayerProof {
    round_polys: [[SF; ROUND_COEFFS]; LAYER_ROUNDS],
    state_claims: [[SF; 2]; 3],
    aux_claims: [SF; AUX_COLS],
    state_lines: [[SF; STATE_LINE_COEFFS]; 3],
}

#[derive(Clone, Serialize)]
struct SpikeProof {
    state8_claims: [SF; 3],
    layers: [LayerProof; STAGES],
    aux_lines: [[SF; AUX_LINE_COEFFS]; STAGES - 1],
}

#[derive(Debug, PartialEq, Eq)]
enum VerifyError {
    SumcheckRound { stage: usize, round: usize },
    LayerFinal { stage: usize },
    StateLineEndpoint { stage: usize, limb: usize },
    AuxLineEndpoint { reduction: usize },
    AuxTieBack,
    InputTieBack,
    OutputTieBack,
}

fn mix_claims(channel: &mut Blake2sChannel, state: &[[SF; 2]; 3], aux: &[SF; AUX_COLS]) {
    let mut claims = Vec::with_capacity(6 + AUX_COLS);
    for limb in state {
        claims.extend_from_slice(limb);
    }
    claims.extend_from_slice(aux);
    channel.mix_felts(&claims);
}

fn prove_layer(
    witness: &SpikeWitness,
    stage: usize,
    rho: &[SF],
    seed_claims: [SF; 3],
    channel: &mut Blake2sChannel,
) -> (LayerProof, Vec<SF>, [SF; 3], Vec<SF>) {
    channel.mix_felts(&seed_claims);
    let beta = channel.draw_secure_felt();
    let gamma = channel.draw_secure_felt();
    let z = channel.draw_secure_felts(STATE_VARS);
    let mut oracle = LayerOracle::new(witness, stage, rho, &z, beta, gamma);
    let mut claim = rlc(&seed_claims, beta);
    let mut assignment = Vec::with_capacity(STATE_VARS);
    let mut round_polys = [[SF::zero(); ROUND_COEFFS]; LAYER_ROUNDS];
    for (round, polynomial) in round_polys.iter_mut().enumerate() {
        *polynomial = oracle.round_poly();
        // An invalid witness must still produce a proof that the verifier can
        // reject without a prover panic. Round zero therefore starts from the
        // witness's actual sum; all later rounds must chain internally.
        if round != 0 {
            assert_eq!(
                poly_eval(polynomial, SF::zero()) + poly_eval(polynomial, SF::one()),
                claim
            );
        }
        channel.mix_felts(polynomial);
        let challenge = channel.draw_secure_felt();
        assignment.push(challenge);
        claim = poly_eval(polynomial, challenge);
        oracle.fix_first(challenge);
        assert_eq!(oracle.columns[0].len(), 1usize << (STATE_VARS - 1 - round));
    }

    let (point0, point1) = state_pair_points(&assignment, stage);
    let state_claims = core::array::from_fn(|limb| {
        [
            ml_eval(&witness.stages[stage][limb], &point0),
            ml_eval(&witness.stages[stage][limb], &point1),
        ]
    });
    let aux_point = aux_point(&assignment, stage);
    let aux_claims = core::array::from_fn(|column| ml_eval(&witness.aux[column], &aux_point));
    mix_claims(channel, &state_claims, &aux_claims);

    let twiddle_point = project_twiddle_point(&assignment, stage);
    let twiddle = twiddle_claims(witness, stage, &twiddle_point);
    let mut final_values = [SF::zero(); ORACLE_COLS];
    for limb in 0..3 {
        final_values[O_IN0 + limb] = state_claims[limb][0];
        final_values[O_IN1 + limb] = state_claims[limb][1];
        final_values[O_TWIDDLE + limb] = twiddle[limb];
    }
    final_values[O_AUX..O_AUX + AUX_COLS].copy_from_slice(&aux_claims);
    final_values[O_BRANCH] = assignment[state_bit_position(stage)];
    final_values[O_EQ_RHO] = eq_eval(rho, &assignment);
    final_values[O_EQ_Z] = eq_eval(&z, &assignment);
    assert_eq!(layer_summand(&final_values, beta, gamma), claim);

    let state_lines = core::array::from_fn(|limb| {
        line_poly::<STATE_LINE_COEFFS>(&witness.stages[stage][limb], &point0, &point1)
    });
    for line in &state_lines {
        channel.mix_felts(line);
    }
    let line_challenge = channel.draw_secure_felt();
    let next_point = point0
        .iter()
        .zip(&point1)
        .map(|(a, b)| *a + line_challenge * (*b - *a))
        .collect();
    let next_claims = core::array::from_fn(|limb| poly_eval(&state_lines[limb], line_challenge));
    (
        LayerProof {
            round_polys,
            state_claims,
            aux_claims,
            state_lines,
        },
        next_point,
        next_claims,
        aux_point,
    )
}

fn folded_aux_oracle(witness: &SpikeWitness, delta: SF) -> Vec<SF> {
    let mut out = vec![SF::zero(); 1usize << AUX_VARS];
    let mut power = SF::one();
    for column in &witness.aux {
        for (value, cell) in out.iter_mut().zip(column) {
            *value += power * *cell;
        }
        power *= delta;
    }
    out
}

fn prove(witness: &SpikeWitness) -> SpikeProof {
    let mut channel = Blake2sChannel::default();
    let rho8 = channel.draw_secure_felts(STATE_VARS);
    let state8_claims = core::array::from_fn(|limb| ml_eval(&witness.stages[STAGES][limb], &rho8));
    let mut point = rho8.clone();
    let mut claims = state8_claims;
    let mut aux_points: [Vec<SF>; STAGES] = core::array::from_fn(|_| Vec::new());
    let mut layers = Vec::with_capacity(STAGES);
    for (slot, stage) in (0..STAGES).rev().enumerate() {
        let (proof, next_point, next_claims, aux_point) =
            prove_layer(witness, stage, &point, claims, &mut channel);
        layers.push(proof);
        aux_points[slot] = aux_point;
        point = next_point;
        claims = next_claims;
    }
    let layers: [LayerProof; STAGES] = layers.try_into().ok().expect("eight layers");

    let delta_aux = channel.draw_secure_felt();
    let aux_oracle = folded_aux_oracle(witness, delta_aux);
    let aux_claims: [SF; STAGES] =
        core::array::from_fn(|slot| rlc(&layers[slot].aux_claims, delta_aux));
    let mut frontier: Vec<(Vec<SF>, SF)> = aux_points.into_iter().zip(aux_claims).collect();
    let mut aux_lines = [[SF::zero(); AUX_LINE_COEFFS]; STAGES - 1];
    let mut line_index = 0;
    while frontier.len() > 1 {
        let mut next_frontier = Vec::with_capacity(frontier.len() / 2);
        for pair in frontier.chunks_exact(2) {
            let (point0, claim0) = &pair[0];
            let (point1, claim1) = &pair[1];
            let line = line_poly::<AUX_LINE_COEFFS>(&aux_oracle, point0, point1);
            assert_eq!(poly_eval(&line, SF::zero()), *claim0);
            assert_eq!(poly_eval(&line, SF::one()), *claim1);
            channel.mix_felts(&line);
            let challenge = channel.draw_secure_felt();
            let point = point0
                .iter()
                .zip(point1)
                .map(|(a, b)| *a + challenge * (*b - *a))
                .collect();
            next_frontier.push((point, poly_eval(&line, challenge)));
            aux_lines[line_index] = line;
            line_index += 1;
        }
        frontier = next_frontier;
    }
    let (current_point, current_claim) = frontier.pop().expect("nonempty aux frontier");
    assert_eq!(line_index, STAGES - 1);
    assert_eq!(ml_eval(&aux_oracle, &current_point), current_claim);

    channel.mix_felts(&claims);
    let delta_input = channel.draw_secure_felt();
    let folded_input = rlc(&claims, delta_input);
    let input_oracle: Vec<SF> = (0..1usize << STATE_VARS)
        .map(|row| {
            rlc(
                &[
                    witness.stages[0][0][row],
                    witness.stages[0][1][row],
                    witness.stages[0][2][row],
                ],
                delta_input,
            )
        })
        .collect();
    assert_eq!(ml_eval(&input_oracle, &point), folded_input);
    channel.mix_felts(&state8_claims);
    let delta_output = channel.draw_secure_felt();
    let folded_output = rlc(&state8_claims, delta_output);
    let output_oracle: Vec<SF> = (0..1usize << STATE_VARS)
        .map(|row| {
            rlc(
                &[
                    witness.stages[STAGES][0][row],
                    witness.stages[STAGES][1][row],
                    witness.stages[STAGES][2][row],
                ],
                delta_output,
            )
        })
        .collect();
    assert_eq!(ml_eval(&output_oracle, &rho8), folded_output);
    SpikeProof {
        state8_claims,
        layers,
        aux_lines,
    }
}

fn verify_layer(
    witness: &SpikeWitness,
    layer: &LayerProof,
    stage: usize,
    rho: &[SF],
    seed_claims: [SF; 3],
    channel: &mut Blake2sChannel,
) -> Result<LayerVerifyOutput, VerifyError> {
    channel.mix_felts(&seed_claims);
    let beta = channel.draw_secure_felt();
    let gamma = channel.draw_secure_felt();
    let z = channel.draw_secure_felts(STATE_VARS);
    let mut claim = rlc(&seed_claims, beta);
    let mut assignment = Vec::with_capacity(STATE_VARS);
    for (round, polynomial) in layer.round_polys.iter().enumerate() {
        if poly_eval(polynomial, SF::zero()) + poly_eval(polynomial, SF::one()) != claim {
            return Err(VerifyError::SumcheckRound { stage, round });
        }
        channel.mix_felts(polynomial);
        let challenge = channel.draw_secure_felt();
        assignment.push(challenge);
        claim = poly_eval(polynomial, challenge);
    }
    mix_claims(channel, &layer.state_claims, &layer.aux_claims);
    let twiddle_point = project_twiddle_point(&assignment, stage);
    let twiddle = twiddle_claims(witness, stage, &twiddle_point);
    let mut final_values = [SF::zero(); ORACLE_COLS];
    for limb in 0..3 {
        final_values[O_IN0 + limb] = layer.state_claims[limb][0];
        final_values[O_IN1 + limb] = layer.state_claims[limb][1];
        final_values[O_TWIDDLE + limb] = twiddle[limb];
    }
    final_values[O_AUX..O_AUX + AUX_COLS].copy_from_slice(&layer.aux_claims);
    final_values[O_BRANCH] = assignment[state_bit_position(stage)];
    final_values[O_EQ_RHO] = eq_eval(rho, &assignment);
    final_values[O_EQ_Z] = eq_eval(&z, &assignment);
    if layer_summand(&final_values, beta, gamma) != claim {
        return Err(VerifyError::LayerFinal { stage });
    }

    let (point0, point1) = state_pair_points(&assignment, stage);
    for (limb, line) in layer.state_lines.iter().enumerate() {
        if poly_eval(line, SF::zero()) != layer.state_claims[limb][0]
            || poly_eval(line, SF::one()) != layer.state_claims[limb][1]
        {
            return Err(VerifyError::StateLineEndpoint { stage, limb });
        }
        channel.mix_felts(line);
    }
    let challenge = channel.draw_secure_felt();
    let next_point = point0
        .iter()
        .zip(&point1)
        .map(|(a, b)| *a + challenge * (*b - *a))
        .collect();
    let next_claims = core::array::from_fn(|limb| poly_eval(&layer.state_lines[limb], challenge));
    Ok((next_point, next_claims, aux_point(&assignment, stage)))
}

fn verify(proof: &SpikeProof, witness: &SpikeWitness) -> Result<(), VerifyError> {
    let mut channel = Blake2sChannel::default();
    let rho8 = channel.draw_secure_felts(STATE_VARS);
    let mut point = rho8.clone();
    let mut claims = proof.state8_claims;
    let mut aux_points: [Vec<SF>; STAGES] = core::array::from_fn(|_| Vec::new());
    for (slot, stage) in (0..STAGES).rev().enumerate() {
        let (next_point, next_claims, aux_point) = verify_layer(
            witness,
            &proof.layers[slot],
            stage,
            &point,
            claims,
            &mut channel,
        )?;
        aux_points[slot] = aux_point;
        point = next_point;
        claims = next_claims;
    }

    let delta_aux = channel.draw_secure_felt();
    let aux_claims: [SF; STAGES] =
        core::array::from_fn(|slot| rlc(&proof.layers[slot].aux_claims, delta_aux));
    let mut frontier: Vec<(Vec<SF>, SF)> = aux_points.into_iter().zip(aux_claims).collect();
    let mut line_index = 0;
    while frontier.len() > 1 {
        let mut next_frontier = Vec::with_capacity(frontier.len() / 2);
        for pair in frontier.chunks_exact(2) {
            let line = &proof.aux_lines[line_index];
            if poly_eval(line, SF::zero()) != pair[0].1 || poly_eval(line, SF::one()) != pair[1].1 {
                return Err(VerifyError::AuxLineEndpoint {
                    reduction: line_index,
                });
            }
            channel.mix_felts(line);
            let challenge = channel.draw_secure_felt();
            let point = pair[0]
                .0
                .iter()
                .zip(&pair[1].0)
                .map(|(a, b)| *a + challenge * (*b - *a))
                .collect();
            next_frontier.push((point, poly_eval(line, challenge)));
            line_index += 1;
        }
        frontier = next_frontier;
    }
    let (current_point, current_claim) = frontier.pop().expect("nonempty aux frontier");
    let aux_oracle = folded_aux_oracle(witness, delta_aux);
    if ml_eval(&aux_oracle, &current_point) != current_claim {
        return Err(VerifyError::AuxTieBack);
    }

    channel.mix_felts(&claims);
    let delta_input = channel.draw_secure_felt();
    let input_claim = rlc(&claims, delta_input);
    let input_oracle: Vec<SF> = (0..1usize << STATE_VARS)
        .map(|row| {
            rlc(
                &[
                    witness.stages[0][0][row],
                    witness.stages[0][1][row],
                    witness.stages[0][2][row],
                ],
                delta_input,
            )
        })
        .collect();
    if ml_eval(&input_oracle, &point) != input_claim {
        return Err(VerifyError::InputTieBack);
    }
    channel.mix_felts(&proof.state8_claims);
    let delta_output = channel.draw_secure_felt();
    let output_claim = rlc(&proof.state8_claims, delta_output);
    let output_oracle: Vec<SF> = (0..1usize << STATE_VARS)
        .map(|row| {
            rlc(
                &[
                    witness.stages[STAGES][0][row],
                    witness.stages[STAGES][1][row],
                    witness.stages[STAGES][2][row],
                ],
                delta_output,
            )
        })
        .collect();
    if ml_eval(&output_oracle, &rho8) != output_claim {
        return Err(VerifyError::OutputTieBack);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::OnceLock;

    fn witness() -> &'static SpikeWitness {
        static WITNESS: OnceLock<SpikeWitness> = OnceLock::new();
        WITNESS.get_or_init(build_witness)
    }

    fn honest_proof() -> &'static SpikeProof {
        static PROOF: OnceLock<SpikeProof> = OnceLock::new();
        PROOF.get_or_init(|| prove(witness()))
    }

    #[test]
    fn full_virtual_chain_proves_and_verifies() {
        assert_eq!(verify(honest_proof(), witness()), Ok(()));
    }

    #[test]
    fn forged_aux_limb_rejects_with_error() {
        let mut forged = witness().clone();
        forged.aux[A_QUOT][aux_row(3, 4, 17)] += SF::one();
        let proof = prove(&forged);
        assert!(verify(&proof, &forged).is_err());
    }

    #[test]
    fn tampered_add_carry_rejects_with_error() {
        let mut forged = witness().clone();
        forged.aux[A_ADD_CARRY][aux_row(5, 2, 31)] += SF::one();
        let proof = prove(&forged);
        assert!(verify(&proof, &forged).is_err());
    }

    #[test]
    fn wrong_sign_additive_carry_rejects_with_error() {
        let mut forged = witness().clone();
        // A-406-FU3 fixture: real ExpandA row stage 0 / poly 0 / bf 5.
        let row = aux_row(0, 0, 5);
        let column = [A_ADD_CARRY, A_ADD_CARRY + 1]
            .into_iter()
            .find(|column| forged.aux[*column][row] == sf_i(-1))
            .expect("FU3 additive fixture has a -1 carry");
        forged.aux[column][row] = sf(1);
        let proof = prove(&forged);
        assert!(verify(&proof, &forged).is_err());
    }

    #[test]
    fn wrong_sign_subtraction_carry_rejects_with_error() {
        let mut forged = witness().clone();
        // First -1 subtraction carry in the real ExpandA witness: stage 0 /
        // poly 0 / bf 2. FU2's earlier bf-0 example predated A-407's switch
        // from synthetic inputs to derive_expand_a_witness.
        let row = aux_row(0, 0, 2);
        let column = [A_SUB_BORROW, A_SUB_BORROW + 1]
            .into_iter()
            .find(|column| forged.aux[*column][row] == sf_i(-1))
            .expect("real subtraction fixture has a -1 carry");
        forged.aux[column][row] = sf(1);
        let proof = prove(&forged);
        assert!(verify(&proof, &forged).is_err());
    }

    #[test]
    fn tampered_round_polynomial_rejects_with_error() {
        let mut proof = honest_proof().clone();
        proof.layers[2].round_polys[4][1] += SF::one();
        assert!(matches!(
            verify(&proof, witness()),
            Err(VerifyError::SumcheckRound { .. })
        ));
    }

    #[test]
    fn tampered_state_line_endpoint_rejects_with_error() {
        let mut proof = honest_proof().clone();
        proof.layers[1].state_lines[2][0] += SF::one();
        assert!(matches!(
            verify(&proof, witness()),
            Err(VerifyError::StateLineEndpoint { .. })
        ));
    }

    #[test]
    fn limb_explicit_generator_matches_reference_intt() {
        let witness = witness();
        for poly in 0..REAL_POLYS {
            let expected = ntt_inverse(&witness.raw_stages[0][poly]);
            let actual = core::array::from_fn(|index| {
                (witness.raw_stages[STAGES][poly][index] as u64 * N_INV as u64 % Q as u64) as u32
            });
            assert_eq!(actual, expected, "poly {poly}");
        }
        // Padding is relation-consistent: zero values carry nonzero Q-1 slacks.
        let padding_row = aux_row(REAL_POLYS, 0, 0);
        assert_eq!(
            [
                witness.aux[A_OUT0_SLACK][padding_row],
                witness.aux[A_OUT0_SLACK + 1][padding_row],
                witness.aux[A_OUT0_SLACK + 2][padding_row],
            ],
            canonical_slack(0).map(sf)
        );
    }

    #[test]
    fn eq_table_and_coordinate_projection_match_convention() {
        let mut channel = Blake2sChannel::default();
        for variables in [STATE_VARS, AUX_VARS] {
            let point = channel.draw_secure_felts(variables);
            let table = eq_table(&point);
            for index in [
                0,
                1,
                5,
                (1usize << variables) / 2 + 7,
                (1usize << variables) - 1,
            ] {
                let mut unit = vec![SF::zero(); 1usize << variables];
                unit[index] = SF::one();
                assert_eq!(ml_eval(&unit, &point), table[index]);
            }
        }
        for stage in 0..STAGES {
            for butterfly in [0, 1, 63, 127] {
                let (index0, index1) = pair_indices(stage, butterfly);
                assert_eq!(butterfly_index(stage, index0), butterfly);
                assert_eq!(butterfly_index(stage, index1), butterfly);
                let row = aux_row(17, stage, butterfly);
                assert_eq!(row, (17 << 10) | (stage << 7) | butterfly);
            }
        }
    }

    // Run with:
    // RAYON_NUM_THREADS=1 cargo test -p stwo-mldsa --release \
    //   --test ntt_gkr_spike measure_phase1_gate -- --ignored --nocapture
    #[test]
    #[ignore = "explicit WO-4b phase-1 measurement"]
    fn measure_phase1_gate() {
        use std::time::Instant;

        let witness = witness();
        assert_eq!(verify(honest_proof(), witness), Ok(()));
        let mut times = [0.0f64; 3];
        let mut last = None;
        for time in &mut times {
            let started = Instant::now();
            let proof = prove(witness);
            *time = started.elapsed().as_secs_f64() * 1_000.0;
            assert_eq!(verify(&proof, witness), Ok(()));
            last = Some(proof);
        }
        times.sort_by(f64::total_cmp);
        let proof = last.expect("three proof runs");
        let payload = bincode::serialize(&proof).expect("spike proof serializes");
        println!("WO4b_PHASE1_PROVE_RUNS_MS={times:?}");
        println!("WO4b_PHASE1_PROVE_MIN_MS={:.3}", times[0]);
        println!("WO4b_PHASE1_PROVE_MEDIAN_MS={:.3}", times[1]);
        println!("WO4b_PHASE1_PAYLOAD_BYTES={}", payload.len());
        println!("WO4b_PHASE1_AUX_COLUMNS={AUX_COLS}");
        println!("WO4b_PHASE1_GATE_TIME={}", times[0] <= 700.0);
        println!("WO4b_PHASE1_GATE_PAYLOAD={}", payload.len() <= 25 * 1024);
    }
}
