use eu_id_ec_coprocessor::sumcheck::{
    circuit_otp_pad_values, proof_otp_pad_values, prove_circuit, prove_sum, verify_circuit,
    verify_sum,
};
use eu_id_ec_coprocessor::{Circuit, CoprocessorChannel, Fp, Layer, Mle, QuadTerm};

fn table() -> Vec<Fp> {
    (1u64..=8).map(Fp::from_u64).collect()
}

fn term(out: u32, l: u32, r: u32, coeff: u64) -> QuadTerm {
    QuadTerm {
        out,
        l,
        r,
        coeff: Fp::from_u64(coeff),
    }
}

fn small_satisfied_circuit() -> (Circuit, Vec<Vec<Fp>>) {
    let layer = Layer::new(1, 1, vec![term(0, 0, 1, 1), term(1, 1, 0, 1)]).unwrap();
    let circuit = Circuit::new(vec![layer]).unwrap();
    let witness = circuit
        .evaluate_input(vec![Fp::ZERO, Fp::from_u64(7)])
        .unwrap();
    (circuit, witness)
}

fn two_layer_satisfied_circuit() -> (Circuit, Vec<Vec<Fp>>) {
    let output = Layer::new(1, 1, vec![term(0, 0, 1, 1)]).unwrap();
    let middle = Layer::new(1, 1, vec![term(0, 0, 1, 1), term(1, 1, 1, 1)]).unwrap();
    let circuit = Circuit::new(vec![output, middle]).unwrap();
    let witness = circuit
        .evaluate_input(vec![Fp::ZERO, Fp::from_u64(7)])
        .unwrap();
    (circuit, witness)
}

#[test]
fn honest_multilinear_sumcheck_accepts() {
    let values = table();
    let claimed_sum = values
        .iter()
        .copied()
        .fold(Fp::ZERO, |acc, value| acc + value);
    let mut prover_channel = CoprocessorChannel::default();
    prover_channel.mix_bytes(b"sumcheck-test");

    let proof = prove_sum(values.clone(), claimed_sum, &mut prover_channel).unwrap();

    let mut verifier_channel = CoprocessorChannel::default();
    verifier_channel.mix_bytes(b"sumcheck-test");
    assert!(verify_sum(&proof, claimed_sum, &values, &mut verifier_channel).unwrap());
}

#[test]
fn tampered_round_polynomial_rejects() {
    let values = table();
    let claimed_sum = values
        .iter()
        .copied()
        .fold(Fp::ZERO, |acc, value| acc + value);
    let mut prover_channel = CoprocessorChannel::default();
    prover_channel.mix_bytes(b"sumcheck-test");
    let mut proof = prove_sum(values.clone(), claimed_sum, &mut prover_channel).unwrap();
    proof.rounds[0][0] = proof.rounds[0][0] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::default();
    verifier_channel.mix_bytes(b"sumcheck-test");
    assert!(!verify_sum(&proof, claimed_sum, &values, &mut verifier_channel).unwrap());
}

#[test]
fn same_seed_produces_identical_proof() {
    let values = table();
    let claimed_sum = values
        .iter()
        .copied()
        .fold(Fp::ZERO, |acc, value| acc + value);

    let mut a = CoprocessorChannel::default();
    a.mix_bytes(b"same-seed");
    let proof_a = prove_sum(values.clone(), claimed_sum, &mut a).unwrap();

    let mut b = CoprocessorChannel::default();
    b.mix_bytes(b"same-seed");
    let proof_b = prove_sum(values, claimed_sum, &mut b).unwrap();

    assert_eq!(proof_a, proof_b);
}

#[test]
fn circuit_sumcheck_exports_input_claims_for_bl3() {
    let (circuit, witness) = small_satisfied_circuit();
    let commitment_root = [9u8; 32];
    let mut prover_channel = CoprocessorChannel::default();

    let proof = prove_circuit(&circuit, &witness, commitment_root, &mut prover_channel).unwrap();

    assert_eq!(
        proof.layers[0].rounds[0].len(),
        2,
        "Q-018 circuit sumcheck rounds transmit only p(0) and p(2)"
    );
    assert_eq!(
        proof.layers[0].round_pads.len(),
        proof.layers[0].rounds.len(),
        "Q-018 commits one [dP(0), dP(2)] pair per half-round"
    );
    let claim_pads = proof.layers[0].claim_pads;
    assert_eq!(
        claim_pads[0] * claim_pads[1],
        claim_pads[2],
        "Q-018 claim pad triple commits dW_L*dW_R=dW_LR"
    );
    assert_eq!(
        proof_otp_pad_values(&proof),
        circuit_otp_pad_values(&circuit),
        "proof pads must match the circuit-shaped committed pad layout"
    );

    let mut verifier_channel = CoprocessorChannel::default();
    let input_claims =
        verify_circuit(&circuit, &proof, commitment_root, &mut verifier_channel).unwrap();
    let input_mle = Mle::new(witness.last().unwrap().clone());

    assert_eq!(proof.input_claims, input_claims);
    for (point, value) in input_claims.points.iter().zip(input_claims.values) {
        assert_eq!(input_mle.eval_at(point).unwrap(), value);
    }
}

#[test]
fn circuit_sumcheck_recurses_to_input_claims_across_layers() {
    let (circuit, witness) = two_layer_satisfied_circuit();
    let commitment_root = [7u8; 32];
    let mut prover_channel = CoprocessorChannel::default();

    let proof = prove_circuit(&circuit, &witness, commitment_root, &mut prover_channel).unwrap();

    let mut verifier_channel = CoprocessorChannel::default();
    let input_claims =
        verify_circuit(&circuit, &proof, commitment_root, &mut verifier_channel).unwrap();
    let input_mle = Mle::new(witness.last().unwrap().clone());

    assert_eq!(proof.layers.len(), 2);
    for (point, value) in input_claims.points.iter().zip(input_claims.values) {
        assert_eq!(input_mle.eval_at(point).unwrap(), value);
    }
}

#[test]
fn circuit_sumcheck_rejects_wrong_final_input_claim() {
    let (circuit, witness) = small_satisfied_circuit();
    let commitment_root = [9u8; 32];
    let mut prover_channel = CoprocessorChannel::default();
    let mut proof =
        prove_circuit(&circuit, &witness, commitment_root, &mut prover_channel).unwrap();
    proof.input_claims.values[0] = proof.input_claims.values[0] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::default();

    assert!(verify_circuit(&circuit, &proof, commitment_root, &mut verifier_channel).is_err());
}

#[test]
fn circuit_sumcheck_rejects_wrong_commitment_root() {
    let (circuit, witness) = small_satisfied_circuit();
    let mut prover_channel = CoprocessorChannel::default();
    let proof = prove_circuit(&circuit, &witness, [9u8; 32], &mut prover_channel).unwrap();

    let mut verifier_channel = CoprocessorChannel::default();

    assert!(verify_circuit(&circuit, &proof, [8u8; 32], &mut verifier_channel).is_err());
}

#[test]
fn circuit_sumcheck_rejects_tampered_round_polynomial() {
    let (circuit, witness) = small_satisfied_circuit();
    let commitment_root = [9u8; 32];
    let mut prover_channel = CoprocessorChannel::default();
    let mut proof =
        prove_circuit(&circuit, &witness, commitment_root, &mut prover_channel).unwrap();
    proof.layers[0].rounds[0][1] = proof.layers[0].rounds[0][1] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::default();

    assert!(verify_circuit(&circuit, &proof, commitment_root, &mut verifier_channel).is_err());
}

#[test]
fn circuit_sumcheck_rejects_tampered_otp_round_pad() {
    let (circuit, witness) = small_satisfied_circuit();
    let commitment_root = [9u8; 32];
    let mut prover_channel = CoprocessorChannel::default();
    let mut proof =
        prove_circuit(&circuit, &witness, commitment_root, &mut prover_channel).unwrap();
    proof.layers[0].round_pads[0][0] = proof.layers[0].round_pads[0][0] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::default();

    assert!(verify_circuit(&circuit, &proof, commitment_root, &mut verifier_channel).is_err());
}

#[test]
fn circuit_sumcheck_rejects_tampered_otp_claim_pad_product() {
    let (circuit, witness) = small_satisfied_circuit();
    let commitment_root = [9u8; 32];
    let mut prover_channel = CoprocessorChannel::default();
    let mut proof =
        prove_circuit(&circuit, &witness, commitment_root, &mut prover_channel).unwrap();
    proof.layers[0].claim_pads[2] = proof.layers[0].claim_pads[2] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::default();

    assert!(verify_circuit(&circuit, &proof, commitment_root, &mut verifier_channel).is_err());
}
