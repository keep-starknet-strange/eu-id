use crate::{Circuit, CircuitError, CoprocessorChannel, Fp, Layer, Mle};
use serde::{Deserialize, Serialize};
use std::sync::OnceLock;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct InputClaims {
    pub points: [Vec<Fp>; 2],
    pub values: [Fp; 2],
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct CircuitSumcheckProof {
    pub layers: Vec<CircuitLayerProof>,
    pub input_claims: InputClaims,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct CircuitLayerProof {
    pub rounds: Vec<[Fp; 2]>,
    pub round_pads: Vec<[Fp; 2]>,
    pub claim_pads: [Fp; 3],
    pub next_claims: [Fp; 2],
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SumcheckProof {
    pub rounds: Vec<[Fp; 2]>,
    pub final_value: Fp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SumcheckError {
    EmptyTable,
    NonPowerOfTwoTable,
    RoundCountMismatch { expected: usize, actual: usize },
    Circuit(CircuitError),
    UnsatisfiedCircuit,
    LayerCountMismatch { expected: usize, actual: usize },
    Rejected,
}

pub fn prove_sum(
    values: Vec<Fp>,
    claimed_sum: Fp,
    channel: &mut CoprocessorChannel,
) -> Result<SumcheckProof, SumcheckError> {
    validate_table(&values)?;
    let mut claim = claimed_sum;
    let mut table = values;
    let mut rounds = Vec::new();

    while table.len() > 1 {
        let (p0, p1) = round_sums(&table);
        debug_assert_eq!(p0 + p1, claim);
        rounds.push([p0, p1]);
        channel.mix_fp(p0);
        channel.mix_fp(p1);
        let challenge = channel.draw_fp();
        table = fold_adjacent(&table, challenge);
        claim = p0 + challenge * (p1 - p0);
    }

    Ok(SumcheckProof {
        rounds,
        final_value: table[0],
    })
}

pub fn verify_sum(
    proof: &SumcheckProof,
    claimed_sum: Fp,
    values: &[Fp],
    channel: &mut CoprocessorChannel,
) -> Result<bool, SumcheckError> {
    validate_table(values)?;
    let expected_rounds = values.len().ilog2() as usize;
    if proof.rounds.len() != expected_rounds {
        return Err(SumcheckError::RoundCountMismatch {
            expected: expected_rounds,
            actual: proof.rounds.len(),
        });
    }

    let mut claim = claimed_sum;
    let mut point = Vec::with_capacity(expected_rounds);
    for [p0, p1] in proof.rounds.iter().copied() {
        if p0 + p1 != claim {
            return Ok(false);
        }
        channel.mix_fp(p0);
        channel.mix_fp(p1);
        let challenge = channel.draw_fp();
        point.push(challenge);
        claim = p0 + challenge * (p1 - p0);
    }

    if claim != proof.final_value {
        return Ok(false);
    }

    let mle = Mle::new(values.to_vec());
    Ok(mle
        .eval_at(&point)
        .map(|value| value == proof.final_value)
        .unwrap_or(false))
}

pub fn prove_circuit(
    circuit: &Circuit,
    witness: &[Vec<Fp>],
    commitment_root: [u8; 32],
    channel: &mut CoprocessorChannel,
) -> Result<CircuitSumcheckProof, SumcheckError> {
    if !circuit
        .is_satisfied(witness)
        .map_err(SumcheckError::Circuit)?
    {
        return Err(SumcheckError::UnsatisfiedCircuit);
    }

    prove_circuit_inner(circuit, witness, commitment_root, channel)
}

pub(crate) fn prove_evaluated_circuit(
    circuit: &Circuit,
    witness: &[Vec<Fp>],
    commitment_root: [u8; 32],
    channel: &mut CoprocessorChannel,
) -> Result<CircuitSumcheckProof, SumcheckError> {
    validate_evaluated_witness(circuit, witness)?;
    prove_circuit_inner(circuit, witness, commitment_root, channel)
}

fn prove_circuit_inner(
    circuit: &Circuit,
    witness: &[Vec<Fp>],
    commitment_root: [u8; 32],
    channel: &mut CoprocessorChannel,
) -> Result<CircuitSumcheckProof, SumcheckError> {
    mix_circuit_domain(circuit, commitment_root, channel);
    let output_log_size = circuit.layers()[0].out_log_size();
    let initial_point = draw_point(channel, output_log_size);
    let mut points = [initial_point.clone(), initial_point];
    let mut claims = [Fp::ZERO, Fp::ZERO];
    let mut layer_proofs = Vec::with_capacity(circuit.layers().len());

    for (layer_index, (layer, next_values)) in
        circuit.layers().iter().zip(&witness[1..]).enumerate()
    {
        let alpha = channel.draw_fp();
        let next_mle = Mle::new(next_values.clone());
        let mut round_state = LayerRoundState::new(layer, &next_mle, &points, alpha);
        let mut claim = alpha * claims[0] + (Fp::ONE - alpha) * claims[1];
        let mut sumcheck_point = Vec::with_capacity(2 * layer.next_log_size());
        let mut rounds = Vec::with_capacity(2 * layer.next_log_size());
        let mut round_pads = Vec::with_capacity(2 * layer.next_log_size());
        let two_inverse = fp_two_inverse();

        for round_index in 0..2 * layer.next_log_size() {
            let [p0, p2] = round_state.round_evals_0_2(round_index);
            let evals = [p0, claim - p0, p2];
            debug_assert_eq!(evals[0] + evals[1], claim);
            let pad_pair = otp_pad_pair(layer_index, b"P", round_index);
            let transmitted = [evals[0] - pad_pair[0], evals[2] - pad_pair[1]];
            for eval in transmitted {
                channel.mix_fp(eval);
            }
            let challenge = channel.draw_fp();
            claim = lagrange_eval_0_1_2([evals[0], evals[1], evals[2]], challenge, two_inverse);
            round_state.absorb_challenge(round_index, challenge);
            sumcheck_point.push(challenge);
            rounds.push(transmitted);
            round_pads.push(pad_pair);
        }

        let (left, right) = split_sumcheck_point(&sumcheck_point, layer.next_log_size());
        let next_claims = round_state.final_claims();
        debug_assert_eq!(
            next_claims[0],
            next_mle
                .eval_at(left)
                .expect("left point matches next layer")
        );
        debug_assert_eq!(
            next_claims[1],
            next_mle
                .eval_at(right)
                .expect("right point matches next layer")
        );
        let claim_pair = otp_pad_pair(layer_index, b"W", 0);
        let claim_pads = [claim_pair[0], claim_pair[1], Fp::ZERO];
        let claim_pads = [claim_pads[0], claim_pads[1], claim_pads[0] * claim_pads[1]];
        let masked_next_claims = [
            next_claims[0] - claim_pads[0],
            next_claims[1] - claim_pads[1],
        ];
        channel.mix_fp(masked_next_claims[0]);
        channel.mix_fp(masked_next_claims[1]);
        layer_proofs.push(CircuitLayerProof {
            rounds,
            round_pads,
            claim_pads,
            next_claims: masked_next_claims,
        });
        points = [left.to_vec(), right.to_vec()];
        claims = next_claims;
    }

    Ok(CircuitSumcheckProof {
        layers: layer_proofs,
        input_claims: InputClaims {
            points,
            values: claims,
        },
    })
}

fn validate_evaluated_witness(circuit: &Circuit, witness: &[Vec<Fp>]) -> Result<(), SumcheckError> {
    let expected_depth = circuit.layers().len() + 1;
    if witness.len() != expected_depth {
        return Err(SumcheckError::Circuit(CircuitError::WrongWitnessDepth {
            expected: expected_depth,
            actual: witness.len(),
        }));
    }
    for (layer_index, layer) in circuit.layers().iter().enumerate() {
        let expected_out = 1usize << layer.out_log_size();
        if witness[layer_index].len() != expected_out {
            return Err(SumcheckError::Circuit(CircuitError::WrongWitnessWidth {
                layer: layer_index,
                expected: expected_out,
                actual: witness[layer_index].len(),
            }));
        }
    }
    let input_log = circuit.layers().last().expect("non-empty").next_log_size();
    let expected_input = 1usize << input_log;
    if witness[circuit.layers().len()].len() != expected_input {
        return Err(SumcheckError::Circuit(CircuitError::WrongWitnessWidth {
            layer: circuit.layers().len(),
            expected: expected_input,
            actual: witness[circuit.layers().len()].len(),
        }));
    }
    if witness[0].iter().any(|value| *value != Fp::ZERO) {
        return Err(SumcheckError::UnsatisfiedCircuit);
    }
    Ok(())
}

pub fn verify_circuit(
    circuit: &Circuit,
    proof: &CircuitSumcheckProof,
    commitment_root: [u8; 32],
    channel: &mut CoprocessorChannel,
) -> Result<InputClaims, SumcheckError> {
    if proof.layers.len() != circuit.layers().len() {
        return Err(SumcheckError::LayerCountMismatch {
            expected: circuit.layers().len(),
            actual: proof.layers.len(),
        });
    }
    if proof_otp_pad_values(proof) != circuit_otp_pad_values(circuit) {
        return Err(SumcheckError::Rejected);
    }

    mix_circuit_domain(circuit, commitment_root, channel);
    let output_log_size = circuit.layers()[0].out_log_size();
    let initial_point = draw_point(channel, output_log_size);
    let mut points = [initial_point.clone(), initial_point];
    let mut claims = [Fp::ZERO, Fp::ZERO];

    for (layer, layer_proof) in circuit.layers().iter().zip(&proof.layers) {
        let expected_rounds = 2 * layer.next_log_size();
        if layer_proof.rounds.len() != expected_rounds {
            return Err(SumcheckError::RoundCountMismatch {
                expected: expected_rounds,
                actual: layer_proof.rounds.len(),
            });
        }
        if layer_proof.round_pads.len() != expected_rounds {
            return Err(SumcheckError::RoundCountMismatch {
                expected: expected_rounds,
                actual: layer_proof.round_pads.len(),
            });
        }
        if layer_proof.claim_pads[0] * layer_proof.claim_pads[1] != layer_proof.claim_pads[2] {
            return Err(SumcheckError::Rejected);
        }

        let alpha = channel.draw_fp();
        let mut claim = alpha * claims[0] + (Fp::ONE - alpha) * claims[1];
        let mut sumcheck_point = Vec::with_capacity(expected_rounds);
        let two_inverse = fp_two_inverse();
        for ([p0_hat, p2_hat], [d_p0, d_p2]) in layer_proof
            .rounds
            .iter()
            .copied()
            .zip(layer_proof.round_pads.iter().copied())
        {
            let p0 = p0_hat + d_p0;
            let p2 = p2_hat + d_p2;
            let p1 = claim - p0;
            let evals = [p0, p1, p2];
            if evals[0] + evals[1] != claim {
                return Err(SumcheckError::Rejected);
            }
            for eval in [p0_hat, p2_hat] {
                channel.mix_fp(eval);
            }
            let challenge = channel.draw_fp();
            claim = lagrange_eval_0_1_2(evals, challenge, two_inverse);
            sumcheck_point.push(challenge);
        }

        let (left, right) = split_sumcheck_point(&sumcheck_point, layer.next_log_size());
        let [q0, q1] =
            q_tilde_eval_pair(layer, &points, left, right).map_err(SumcheckError::Circuit)?;
        let next_claims = [
            layer_proof.next_claims[0] + layer_proof.claim_pads[0],
            layer_proof.next_claims[1] + layer_proof.claim_pads[1],
        ];
        let expected = (alpha * q0 + (Fp::ONE - alpha) * q1) * next_claims[0] * next_claims[1];
        if claim != expected {
            return Err(SumcheckError::Rejected);
        }

        channel.mix_fp(layer_proof.next_claims[0]);
        channel.mix_fp(layer_proof.next_claims[1]);
        points = [left.to_vec(), right.to_vec()];
        claims = next_claims;
    }

    let input_claims = InputClaims {
        points,
        values: claims,
    };
    if proof.input_claims != input_claims {
        return Err(SumcheckError::Rejected);
    }
    Ok(input_claims)
}

pub fn circuit_otp_pad_values(circuit: &Circuit) -> Vec<Fp> {
    let mut values = Vec::new();
    for (layer_index, layer) in circuit.layers().iter().enumerate() {
        for round_index in 0..2 * layer.next_log_size() {
            values.extend_from_slice(&otp_pad_pair(layer_index, b"P", round_index));
        }
        let [d_w_l, d_w_r] = otp_pad_pair(layer_index, b"W", 0);
        values.push(d_w_l);
        values.push(d_w_r);
        values.push(d_w_l * d_w_r);
    }
    values
}

pub fn proof_otp_pad_values(proof: &CircuitSumcheckProof) -> Vec<Fp> {
    let mut values = Vec::new();
    for layer in &proof.layers {
        for pad_pair in &layer.round_pads {
            values.extend_from_slice(pad_pair);
        }
        values.extend_from_slice(&layer.claim_pads);
    }
    values
}

fn validate_table(values: &[Fp]) -> Result<(), SumcheckError> {
    if values.is_empty() {
        return Err(SumcheckError::EmptyTable);
    }
    if !values.len().is_power_of_two() {
        return Err(SumcheckError::NonPowerOfTwoTable);
    }
    Ok(())
}

fn mix_circuit_domain(
    circuit: &Circuit,
    commitment_root: [u8; 32],
    channel: &mut CoprocessorChannel,
) {
    channel.mix_bytes(b"eu-id-ec-coproc-sumcheck-v1");
    channel.mix_bytes(&commitment_root);
    channel.mix_bytes(&(circuit.layers().len() as u64).to_be_bytes());
    for layer in circuit.layers() {
        channel.mix_bytes(&(layer.out_log_size() as u64).to_be_bytes());
        channel.mix_bytes(&(layer.next_log_size() as u64).to_be_bytes());
    }
}

fn draw_point(channel: &mut CoprocessorChannel, len: usize) -> Vec<Fp> {
    (0..len).map(|_| channel.draw_fp()).collect()
}

fn otp_pad_pair(layer_index: usize, kind: &[u8], item_index: usize) -> [Fp; 2] {
    let mut channel = CoprocessorChannel::from_seed([0u8; 32], b"eu-id-ec-coproc-otp-pad-pair-v1");
    channel.mix_bytes(b"eu-id-ec-coproc-otp-pad-pair-v1");
    channel.mix_bytes(&(layer_index as u64).to_be_bytes());
    channel.mix_bytes(kind);
    channel.mix_bytes(&(item_index as u64).to_be_bytes());
    [channel.draw_fp(), channel.draw_fp()]
}

fn split_sumcheck_point(point: &[Fp], next_log_size: usize) -> (&[Fp], &[Fp]) {
    point.split_at(next_log_size)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RoundTerm {
    l: u32,
    r: u32,
    q: Fp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RightPhaseTerm {
    r: u32,
    q: Fp,
    eq: Fp,
}

struct LayerRoundState {
    next_log_size: usize,
    terms: Vec<RoundTerm>,
    left_eq: Vec<Fp>,
    right_phase_terms: Vec<RightPhaseTerm>,
    left_folded: Vec<Fp>,
    right_folded: Vec<Fp>,
}

impl LayerRoundState {
    fn new(layer: &Layer, next_mle: &Mle, output_points: &[Vec<Fp>; 2], alpha: Fp) -> Self {
        let output_lookup = output_lookup(layer, output_points, alpha);
        let terms = compressed_round_terms(layer, &output_lookup);
        let term_count = terms.len();
        Self {
            next_log_size: layer.next_log_size(),
            terms,
            left_eq: vec![Fp::ONE; term_count],
            right_phase_terms: Vec::new(),
            left_folded: next_mle.values().to_vec(),
            right_folded: next_mle.values().to_vec(),
        }
    }

    fn round_evals_0_2(&self, round_index: usize) -> [Fp; 2] {
        if round_index < self.next_log_size {
            self.left_round_evals_0_2(round_index)
        } else {
            self.right_round_evals_0_2(round_index - self.next_log_size)
        }
    }

    fn absorb_challenge(&mut self, round_index: usize, challenge: Fp) {
        if round_index < self.next_log_size {
            for (eq, term) in self.left_eq.iter_mut().zip(&self.terms) {
                *eq = *eq * bit_eq(term.l, round_index, challenge);
            }
            fold_one_in_place(&mut self.left_folded, challenge);
            if round_index + 1 == self.next_log_size {
                let left_scalar = self.left_folded[0];
                self.bind_right_phase_terms(left_scalar);
            }
        } else {
            let right_round = round_index - self.next_log_size;
            for term in &mut self.right_phase_terms {
                term.eq = term.eq * bit_eq(term.r, right_round, challenge);
            }
            fold_one_in_place(&mut self.right_folded, challenge);
        }
    }

    fn left_round_evals_0_2(&self, round_index: usize) -> [Fp; 2] {
        let left_at_two = fold_at_two(&self.left_folded);
        let mut evals = [Fp::ZERO; 2];
        for (term_index, term) in self.terms.iter().enumerate() {
            let q_right = term.q * self.right_folded[term.r as usize] * self.left_eq[term_index];
            let left_index = (term.l as usize) >> (round_index + 1);
            let left_bit = (term.l >> round_index) & 1;

            if left_bit == 0 {
                evals[0] = evals[0] + q_right * self.left_folded[left_index * 2];
            }

            let mut left = left_at_two[left_index];
            left = if left_bit == 1 { left + left } else { -left };
            evals[1] = evals[1] + q_right * left;
        }
        evals
    }

    fn right_round_evals_0_2(&self, round_index: usize) -> [Fp; 2] {
        let right_at_two = fold_at_two(&self.right_folded);
        let mut evals = [Fp::ZERO; 2];
        for term in &self.right_phase_terms {
            let q_left = term.q * term.eq;
            let right_index = (term.r as usize) >> (round_index + 1);
            let right_bit = (term.r >> round_index) & 1;

            if right_bit == 0 {
                evals[0] = evals[0] + q_left * self.right_folded[right_index * 2];
            }

            let mut right = right_at_two[right_index];
            right = if right_bit == 1 {
                right + right
            } else {
                -right
            };
            evals[1] = evals[1] + q_left * right;
        }
        evals
    }

    fn bind_right_phase_terms(&mut self, left_scalar: Fp) {
        let mut by_r = vec![Fp::ZERO; self.right_folded.len()];
        let mut active = Vec::new();
        for (term_index, term) in self.terms.iter().enumerate() {
            let r = term.r as usize;
            if by_r[r] == Fp::ZERO {
                active.push(term.r);
            }
            by_r[r] = by_r[r] + term.q * self.left_eq[term_index] * left_scalar;
        }
        self.right_phase_terms.clear();
        self.right_phase_terms.reserve(active.len());
        for r in active {
            let q = by_r[r as usize];
            if q != Fp::ZERO {
                self.right_phase_terms.push(RightPhaseTerm { r, q, eq: Fp::ONE });
            }
        }
    }

    fn final_claims(&self) -> [Fp; 2] {
        debug_assert_eq!(self.left_folded.len(), 1);
        debug_assert_eq!(self.right_folded.len(), 1);
        [self.left_folded[0], self.right_folded[0]]
    }
}

fn compressed_round_terms(layer: &Layer, output_lookup: &[Fp]) -> Vec<RoundTerm> {
    let mut terms = Vec::with_capacity(layer.terms().len());
    let mut zero_zero_q = Fp::ZERO;
    for term in layer.terms() {
        let q = term.coeff * output_lookup[term.out as usize];
        if term.l == 0 && term.r == 0 {
            zero_zero_q = zero_zero_q + q;
        } else {
            terms.push(RoundTerm {
                l: term.l,
                r: term.r,
                q,
            });
        }
    }
    if zero_zero_q != Fp::ZERO {
        terms.push(RoundTerm {
            l: 0,
            r: 0,
            q: zero_zero_q,
        });
    }
    terms
}

fn output_lookup(layer: &Layer, output_points: &[Vec<Fp>; 2], alpha: Fp) -> Vec<Fp> {
    (0..1u32 << layer.out_log_size())
        .map(|index| {
            alpha * index_eq(index, &output_points[0])
                + (Fp::ONE - alpha) * index_eq(index, &output_points[1])
        })
        .collect()
}

fn q_tilde_eval_pair(
    layer: &Layer,
    output_points: &[Vec<Fp>; 2],
    left: &[Fp],
    right: &[Fp],
) -> Result<[Fp; 2], CircuitError> {
    if output_points[0].len() != layer.out_log_size() {
        return Err(CircuitError::WrongPointLength {
            expected: layer.out_log_size(),
            actual: output_points[0].len(),
        });
    }
    if output_points[1].len() != layer.out_log_size() {
        return Err(CircuitError::WrongPointLength {
            expected: layer.out_log_size(),
            actual: output_points[1].len(),
        });
    }
    if left.len() != layer.next_log_size() {
        return Err(CircuitError::WrongPointLength {
            expected: layer.next_log_size(),
            actual: left.len(),
        });
    }
    if right.len() != layer.next_log_size() {
        return Err(CircuitError::WrongPointLength {
            expected: layer.next_log_size(),
            actual: right.len(),
        });
    }

    let mut out = [Fp::ZERO; 2];
    for term in layer.terms() {
        let lr = term.coeff * prefix_eq(term.l, left) * prefix_eq(term.r, right);
        out[0] = out[0] + lr * prefix_eq(term.out, &output_points[0]);
        out[1] = out[1] + lr * prefix_eq(term.out, &output_points[1]);
    }
    Ok(out)
}

fn fold_one_in_place(values: &mut Vec<Fp>, challenge: Fp) {
    let half = values.len() / 2;
    for index in 0..half {
        let left = values[index * 2];
        let right = values[index * 2 + 1];
        values[index] = left + challenge * (right - left);
    }
    values.truncate(half);
}

fn fold_at_two(values: &[Fp]) -> Vec<Fp> {
    let mut at_two = Vec::with_capacity(values.len() / 2);
    for pair in values.chunks_exact(2) {
        at_two.push(pair[1] + pair[1] - pair[0]);
    }
    at_two
}

fn index_eq(index: u32, point: &[Fp]) -> Fp {
    prefix_eq(index, point)
}

fn bit_eq(index: u32, bit: usize, point: Fp) -> Fp {
    if ((index >> bit) & 1) == 1 {
        point
    } else {
        Fp::ONE - point
    }
}

fn prefix_eq(index: u32, point: &[Fp]) -> Fp {
    point
        .iter()
        .enumerate()
        .fold(Fp::ONE, |acc, (bit, &value)| {
            if ((index >> bit) & 1) == 1 {
                acc * value
            } else {
                acc * (Fp::ONE - value)
            }
        })
}

fn lagrange_eval_0_1_2(values: [Fp; 3], point: Fp, half: Fp) -> Fp {
    let first_delta = values[1] - values[0];
    let second_delta = values[2] - values[1] - values[1] + values[0];
    let quadratic = point * (point - Fp::ONE) * half;
    values[0] + point * first_delta + quadratic * second_delta
}

fn fp_two_inverse() -> Fp {
    static TWO_INVERSE: OnceLock<Fp> = OnceLock::new();
    *TWO_INVERSE.get_or_init(|| Fp::from_u64(2).inverse().expect("2 is non-zero in Fp"))
}

fn round_sums(values: &[Fp]) -> (Fp, Fp) {
    values
        .chunks_exact(2)
        .fold((Fp::ZERO, Fp::ZERO), |(p0, p1), pair| {
            (p0 + pair[0], p1 + pair[1])
        })
}

fn fold_adjacent(values: &[Fp], challenge: Fp) -> Vec<Fp> {
    values
        .chunks_exact(2)
        .map(|pair| pair[0] + challenge * (pair[1] - pair[0]))
        .collect()
}
