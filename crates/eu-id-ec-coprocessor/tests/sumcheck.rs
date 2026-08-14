use eu_id_ec_coprocessor::sumcheck::{
    prove_circuit, prove_sum, verify_circuit, verify_sum, CircuitPads, CircuitVerification,
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
    let mut prover_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    prover_channel.mix_bytes(b"sumcheck-test");

    let proof = prove_sum(values.clone(), claimed_sum, &mut prover_channel).unwrap();

    let mut verifier_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
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
    let mut prover_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    prover_channel.mix_bytes(b"sumcheck-test");
    let mut proof = prove_sum(values.clone(), claimed_sum, &mut prover_channel).unwrap();
    proof.rounds[0][0] = proof.rounds[0][0] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
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

    let mut a = CoprocessorChannel::from_seed([0u8; 32], b"test");
    a.mix_bytes(b"same-seed");
    let proof_a = prove_sum(values.clone(), claimed_sum, &mut a).unwrap();

    let mut b = CoprocessorChannel::from_seed([0u8; 32], b"test");
    b.mix_bytes(b"same-seed");
    let proof_b = prove_sum(values, claimed_sum, &mut b).unwrap();

    assert_eq!(proof_a, proof_b);
}

fn committed_constraints_hold(
    verification: &CircuitVerification,
    pads: &CircuitPads,
    input: &[Fp],
) -> bool {
    if verification.layer_constraints.iter().any(|constraint| {
        let got = constraint.terms.iter().fold(Fp::ZERO, |acc, term| {
            acc + term.coefficient * pads.values()[term.pad_offset]
        });
        got != constraint.value
    }) {
        return false;
    }
    let mle = Mle::new(input.to_vec());
    let [point_0, point_1] = &verification.input_claims.points;
    let beta = verification.input_challenge;
    let got = mle.eval_at(point_0).unwrap() + beta * mle.eval_at(point_1).unwrap()
        - pads.values()[verification.input_pad_offsets[0]]
        - beta * pads.values()[verification.input_pad_offsets[1]];
    let want = verification.input_claims.values[0] + beta * verification.input_claims.values[1];
    got == want
}

fn prove_and_reconstruct(
    circuit: &Circuit,
    witness: &[Vec<Fp>],
    pads: &CircuitPads,
    root: [u8; 32],
) -> (
    eu_id_ec_coprocessor::sumcheck::CircuitSumcheckProof,
    CircuitVerification,
) {
    let mut prover_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let proof = prove_circuit(circuit, witness, pads, root, &mut prover_channel).unwrap();
    let mut verifier_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let verification = verify_circuit(circuit, &proof, root, &mut verifier_channel).unwrap();
    (proof, verification)
}

#[test]
fn circuit_sumcheck_masks_every_private_transcript_value() {
    let (circuit, witness) = small_satisfied_circuit();
    let pads = CircuitPads::fresh(&circuit);
    let (proof, verification) = prove_and_reconstruct(&circuit, &witness, &pads, [9u8; 32]);

    assert_eq!(proof.layers[0].rounds[0].len(), 2);
    assert!(committed_constraints_hold(
        &verification,
        &pads,
        witness.last().unwrap()
    ));

    let encoded = bincode::serialize(&proof).unwrap();
    for pad in pads.values() {
        assert!(
            !encoded
                .windows(32)
                .any(|window| window == pad.to_bytes_be().as_slice()),
            "a secret pad was serialized in the sumcheck proof"
        );
    }
}

#[test]
fn circuit_sumcheck_recurses_across_layers_under_committed_masks() {
    let (circuit, witness) = two_layer_satisfied_circuit();
    let pads = CircuitPads::fresh(&circuit);
    let (proof, verification) = prove_and_reconstruct(&circuit, &witness, &pads, [7u8; 32]);

    assert_eq!(proof.layers.len(), 2);
    assert_eq!(verification.layer_constraints.len(), 2);
    assert!(committed_constraints_hold(
        &verification,
        &pads,
        witness.last().unwrap()
    ));
}

#[test]
fn fresh_masks_randomize_the_same_witness_transcript() {
    let (circuit, witness) = small_satisfied_circuit();
    let pads_a = CircuitPads::fresh(&circuit);
    let pads_b = CircuitPads::fresh(&circuit);
    let (proof_a, _) = prove_and_reconstruct(&circuit, &witness, &pads_a, [9u8; 32]);
    let (proof_b, _) = prove_and_reconstruct(&circuit, &witness, &pads_b, [9u8; 32]);
    assert_ne!(proof_a, proof_b);
}

#[test]
fn tampered_masked_round_fails_the_committed_constraints() {
    let (circuit, witness) = small_satisfied_circuit();
    let pads = CircuitPads::fresh(&circuit);
    let (mut proof, _) = prove_and_reconstruct(&circuit, &witness, &pads, [9u8; 32]);
    proof.layers[0].rounds[0][1] = proof.layers[0].rounds[0][1] + Fp::ONE;

    let mut verifier_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let verification = verify_circuit(&circuit, &proof, [9u8; 32], &mut verifier_channel).unwrap();
    assert!(!committed_constraints_hold(
        &verification,
        &pads,
        witness.last().unwrap()
    ));
}

#[test]
fn wrong_commitment_root_fails_the_committed_constraints() {
    let (circuit, witness) = small_satisfied_circuit();
    let pads = CircuitPads::fresh(&circuit);
    let (proof, _) = prove_and_reconstruct(&circuit, &witness, &pads, [9u8; 32]);
    let mut verifier_channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    let verification = verify_circuit(&circuit, &proof, [8u8; 32], &mut verifier_channel).unwrap();
    assert!(!committed_constraints_hold(
        &verification,
        &pads,
        witness.last().unwrap()
    ));
}
