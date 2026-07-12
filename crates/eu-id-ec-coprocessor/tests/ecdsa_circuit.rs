use ecdsa::signature::Signer;
use eu_id_ec_coprocessor::ecdsa::{
    build_c11_final_add_circuit, build_c12_on_curve_circuit, build_c14_c15_final_check_circuit,
    build_c1_input_limbs_circuit, build_c2_canonicality_circuit, build_c3_c5_scalar_setup_circuit,
    c11_final_add_input, c12_on_curve_input, c12_witness_on_curve_input, c14_c15_final_check_input,
    c1_input_limbs_input, c2_canonicality_input, c3_c5_scalar_setup_input, generate_witness,
    implemented_circuit_family_labels, implemented_circuit_gate_count, layout_range,
    prove_implemented_circuit_bundle, prove_implemented_circuit_bundle_batch_with_projection,
    prove_implemented_circuit_bundle_profiled, prove_implemented_circuit_proofs,
    prove_mdoc_p4b_circuit_bundle, verify_implemented_circuit_bundle,
    verify_implemented_circuit_bundle_batch_with_projection, verify_implemented_circuit_proofs,
    verify_implemented_circuits, verify_mdoc_p4b_circuit_bundle, verify_witness, EcdsaInput,
    EcdsaPublicProjection, ImplementedCircuitBundleEntry, LayoutSlot, MdocP4bMacKeyShares,
    WitnessError, MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS,
};
use eu_id_ec_coprocessor::ligero::{
    commit_witness, v2_ligero_params, v4_circle_params, LigeroCode, LigeroParams,
};
use eu_id_ec_coprocessor::sumcheck::{circuit_otp_pad_values, prove_circuit};
use eu_id_ec_coprocessor::CoprocessorChannel;
use eu_id_ec_coprocessor::Fp;
use p256::ecdsa::{Signature, SigningKey};
use p256::elliptic_curve::sec1::ToEncodedPoint;
use p256::AffinePoint;
use sha2::{Digest as _, Sha256};

const TEST_SEED: [u8; 32] = [9u8; 32];

fn fp_from_coord(coord: &[u8]) -> Fp {
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(coord);
    Fp::from_bytes_be(bytes).unwrap()
}

fn signed_input() -> EcdsaInput {
    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).unwrap();
    let message = b"eu-id s4 final check circuit";
    let digest: [u8; 32] = Sha256::digest(message).into();
    let signature: Signature = signing_key.sign(message);
    let public_key = signing_key.verifying_key().to_encoded_point(false);
    let mut qx = [0u8; 32];
    let mut qy = [0u8; 32];
    qx.copy_from_slice(public_key.x().unwrap());
    qy.copy_from_slice(public_key.y().unwrap());

    EcdsaInput {
        z: digest,
        r: signature.r().to_bytes().into(),
        s: signature.s().to_bytes().into(),
        qx,
        qy,
    }
}

fn alternate_signed_input() -> EcdsaInput {
    let signing_key = SigningKey::from_bytes((&[9u8; 32]).into()).unwrap();
    let message = b"eu-id s4 alternate final check circuit";
    let digest: [u8; 32] = Sha256::digest(message).into();
    let signature: Signature = signing_key.sign(message);
    let public_key = signing_key.verifying_key().to_encoded_point(false);
    let mut qx = [0u8; 32];
    let mut qy = [0u8; 32];
    qx.copy_from_slice(public_key.x().unwrap());
    qy.copy_from_slice(public_key.y().unwrap());

    EcdsaInput {
        z: digest,
        r: signature.r().to_bytes().into(),
        s: signature.s().to_bytes().into(),
        qx,
        qy,
    }
}

fn revocation_signed_input() -> EcdsaInput {
    let signing_key = SigningKey::from_bytes((&[11u8; 32]).into()).unwrap();
    let message = b"eu-id s4 revocation final check circuit";
    let digest: [u8; 32] = Sha256::digest(message).into();
    let signature: Signature = signing_key.sign(message);
    let public_key = signing_key.verifying_key().to_encoded_point(false);
    let mut qx = [0u8; 32];
    let mut qy = [0u8; 32];
    qx.copy_from_slice(public_key.x().unwrap());
    qy.copy_from_slice(public_key.y().unwrap());

    EcdsaInput {
        z: digest,
        r: signature.r().to_bytes().into(),
        s: signature.s().to_bytes().into(),
        qx,
        qy,
    }
}

#[test]
fn implemented_circuit_gate_count_stays_under_s4_budget() {
    let gates = implemented_circuit_gate_count().unwrap();
    eprintln!("implemented S4-lite ECDSA BL2 gate count: {gates}");

    assert!(gates > 0);
    assert!(gates <= 35_000, "implemented gate count exceeds S4 budget");
}

#[test]
fn c2_canonicality_circuit_accepts_honest_input() {
    let input = signed_input();
    let circuit = build_c2_canonicality_circuit().unwrap();
    let layers = circuit
        .evaluate_input(c2_canonicality_input(&input).unwrap())
        .unwrap();

    assert!(circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn c2_canonicality_circuit_rejects_zero_scalars_and_bad_public_key() {
    let circuit = build_c2_canonicality_circuit().unwrap();

    let mut input = signed_input();
    input.r = [0u8; 32];
    assert_eq!(
        c2_canonicality_input(&input).unwrap_err(),
        WitnessError::ZeroScalar
    );

    let mut input = signed_input();
    input.s = [0u8; 32];
    assert_eq!(
        c2_canonicality_input(&input).unwrap_err(),
        WitnessError::ZeroScalar
    );

    let mut input = signed_input();
    input.qy[31] ^= 1;
    let layers = circuit
        .evaluate_input(c2_canonicality_input(&input).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "off-curve key must reject"
    );
}

#[test]
fn c1_input_limb_circuit_accepts_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let circuit = build_c1_input_limbs_circuit().unwrap();
    let layers = circuit
        .evaluate_input(c1_input_limbs_input(&input, &witness).unwrap())
        .unwrap();

    assert!(circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn c1_input_limb_circuit_rejects_limb_and_value_mutations() {
    let input = signed_input();
    let circuit = build_c1_input_limbs_circuit().unwrap();

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::InputLimbs).start] =
        witness.values[layout_range(LayoutSlot::InputLimbs).start] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c1_input_limbs_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad z limb must reject"
    );

    let witness = generate_witness(&input).unwrap();
    let mut changed_input = input;
    changed_input.r[31] ^= 1;
    let layers = circuit
        .evaluate_input(c1_input_limbs_input(&changed_input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad r value must reject"
    );
}

#[test]
fn c3_c5_scalar_setup_circuit_accepts_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let circuit = build_c3_c5_scalar_setup_circuit().unwrap();
    let layers = circuit
        .evaluate_input(c3_c5_scalar_setup_input(&input, &witness).unwrap())
        .unwrap();

    assert!(circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn c3_c5_scalar_setup_circuit_rejects_mutations() {
    let input = signed_input();
    let circuit = build_c3_c5_scalar_setup_circuit().unwrap();

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::ScalarInverses).start] =
        witness.values[layout_range(LayoutSlot::ScalarInverses).start] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c3_c5_scalar_setup_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad sinv must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::UScalars).start] =
        witness.values[layout_range(LayoutSlot::UScalars).start] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c3_c5_scalar_setup_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad u1 must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::ModNQuotients).start + 2] =
        witness.values[layout_range(LayoutSlot::ModNQuotients).start + 2] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c3_c5_scalar_setup_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad q2 must reject"
    );
}

#[test]
fn c11_final_add_circuit_accepts_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let circuit = build_c11_final_add_circuit().unwrap();
    let layers = circuit
        .evaluate_input(c11_final_add_input(&witness).unwrap())
        .unwrap();

    assert!(circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn c11_final_add_circuit_rejects_accumulator_and_final_point_mutations() {
    let input = signed_input();
    let circuit = build_c11_final_add_circuit().unwrap();

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start] =
        witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c11_final_add_input(&witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad corrected S1 endpoint must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalPoint).start] =
        witness.values[layout_range(LayoutSlot::FinalPoint).start] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c11_final_add_input(&witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad final R must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] =
        witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c11_final_add_input(&witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad witnessed final-add inverse must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    witness.values[corrected.start + 2] = witness.values[corrected.start];
    witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] = Fp::ZERO;
    let layers = circuit
        .evaluate_input(c11_final_add_input(&witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "zero final-add denominator must reject in C11 without C13"
    );
}

#[test]
fn c14_c15_final_check_circuit_accepts_real_signature_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let circuit = build_c14_c15_final_check_circuit().unwrap();
    let layers = circuit
        .evaluate_input(c14_c15_final_check_input(&input, &witness).unwrap())
        .unwrap();

    assert!(circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn c14_c15_final_check_circuit_rejects_final_and_flag_mutations() {
    let input = signed_input();
    let circuit = build_c14_c15_final_check_circuit().unwrap();

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalReduction).start + 1] = Fp::from_u64(9);
    let layers = circuit
        .evaluate_input(c14_c15_final_check_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad r' must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalReduction).start] = Fp::from_u64(2);
    let layers = circuit
        .evaluate_input(c14_c15_final_check_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "non-boolean k must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::InfinityFlags).start + 1] = Fp::ONE;
    let layers = circuit
        .evaluate_input(c14_c15_final_check_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "infinity flag must reject"
    );
}

#[test]
fn c12_on_curve_circuit_accepts_public_key_and_final_point() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let circuit = build_c12_on_curve_circuit().unwrap();

    let layers = circuit
        .evaluate_input(c12_on_curve_input(
            Fp::from_bytes_be(input.qx).unwrap(),
            Fp::from_bytes_be(input.qy).unwrap(),
        ))
        .unwrap();
    assert!(
        circuit.is_satisfied(&layers).unwrap(),
        "public key must be on curve"
    );

    let final_point = layout_range(LayoutSlot::FinalPoint);
    let layers = circuit
        .evaluate_input(c12_on_curve_input(
            witness.values[final_point.start],
            witness.values[final_point.start + 1],
        ))
        .unwrap();
    assert!(
        circuit.is_satisfied(&layers).unwrap(),
        "final R must be on curve"
    );
}

#[test]
fn c12_on_curve_circuit_rejects_mutated_point() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let final_point = layout_range(LayoutSlot::FinalPoint);
    let circuit = build_c12_on_curve_circuit().unwrap();

    let layers = circuit
        .evaluate_input(c12_on_curve_input(
            witness.values[final_point.start],
            witness.values[final_point.start + 1] + Fp::ONE,
        ))
        .unwrap();

    assert!(!circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn c12_witness_on_curve_circuit_rejects_mutated_corrected_endpoint() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start + 1] =
        witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start + 1] + Fp::ONE;
    let circuit = build_c12_on_curve_circuit().unwrap();
    let layers = circuit
        .evaluate_input(c12_witness_on_curve_input(&witness).unwrap())
        .unwrap();

    assert!(!circuit.is_satisfied(&layers).unwrap());
}

#[test]
fn implemented_circuit_verifier_accepts_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();

    verify_implemented_circuits(&input, &witness).unwrap();
}

#[test]
fn implemented_circuit_verifier_rejects_covered_mutations() {
    let input = signed_input();

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::InputLimbs).start] =
        witness.values[layout_range(LayoutSlot::InputLimbs).start] + Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::ScalarInverses).start] =
        witness.values[layout_range(LayoutSlot::ScalarInverses).start] + Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::U1GAccumulators).start + 3] =
        witness.values[layout_range(LayoutSlot::U1GAccumulators).start + 3] + Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalPoint).start + 1] =
        witness.values[layout_range(LayoutSlot::FinalPoint).start + 1] + Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::InfinityFlags).start] = Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] =
        witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] + Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());
}

#[test]
fn implemented_circuit_proofs_accept_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let commitment_root = [3u8; 32];

    let proofs =
        prove_implemented_circuit_proofs(&input, &witness, commitment_root, TEST_SEED).unwrap();

    let labels = implemented_circuit_family_labels().unwrap();
    assert_eq!(
        labels,
        vec![
            b"s4-ecdsa-c1-input-limbs".as_slice(),
            b"s4-ecdsa-c2-canonicality".as_slice(),
            b"s4-ecdsa-c3-c5-scalar-setup".as_slice(),
            b"s4-ecdsa-c11-final-add".as_slice(),
            b"s4-ecdsa-c12-final-on-curve".as_slice(),
            b"s4-ecdsa-c14-c15-final-check".as_slice(),
        ],
        "C13 is intentionally absent: its unbound interior pairs constrained no shared witness, and its sole bound final pair duplicated C11"
    );
    assert_eq!(proofs.proofs.len(), labels.len());
    let claims = verify_implemented_circuit_proofs(&proofs, commitment_root, TEST_SEED).unwrap();
    assert_eq!(claims.len(), labels.len());
    assert_eq!(labels[0], b"s4-ecdsa-c1-input-limbs");
    assert_eq!(labels[5], b"s4-ecdsa-c14-c15-final-check");
}

#[test]
fn implemented_circuit_proofs_reject_wrong_commitment_root() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let proofs = prove_implemented_circuit_proofs(&input, &witness, [3u8; 32], TEST_SEED).unwrap();

    assert!(verify_implemented_circuit_proofs(&proofs, [4u8; 32], TEST_SEED).is_err());
}

#[test]
fn implemented_circuit_provers_reject_mismatched_input_and_witness() {
    let input = signed_input();
    let alternate = alternate_signed_input();
    let alternate_witness = generate_witness(&alternate).unwrap();

    assert!(
        prove_implemented_circuit_proofs(&input, &alternate_witness, [3u8; 32], TEST_SEED).is_err(),
        "standalone BL2 proof prover must reject a witness from another statement"
    );
    assert!(
        prove_implemented_circuit_bundle(&input, &alternate_witness, TEST_SEED).is_err(),
        "BL2+BL3 bundle prover must reject a witness from another statement"
    );
}

#[test]
fn implemented_circuit_provers_reject_unsatisfied_witness_mutation() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::InputLimbs).start] =
        witness.values[layout_range(LayoutSlot::InputLimbs).start] + Fp::ONE;

    assert!(
        prove_implemented_circuit_proofs(&input, &witness, [3u8; 32], TEST_SEED).is_err(),
        "standalone BL2 proof prover must reject unsatisfied circuit witnesses"
    );
    assert!(
        prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).is_err(),
        "BL2+BL3 bundle prover must reject unsatisfied circuit witnesses"
    );
}

#[test]
fn implemented_circuit_provers_reject_native_witness_mismatch_even_if_covered_circuits_pass() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();
    mutate_interior_u1_accumulator(&mut witness);

    assert!(
        verify_witness(&input, &witness).is_err(),
        "native checker must reject the mutated accumulator transcript"
    );
    verify_implemented_circuits(&input, &witness)
        .expect("current implemented families do not yet cover C9 transition algebra");

    assert!(
        prove_implemented_circuit_proofs(&input, &witness, [3u8; 32], TEST_SEED).is_err(),
        "standalone BL2 proof prover must reject witnesses that fail the native checker"
    );
    assert!(
        prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).is_err(),
        "BL2+BL3 bundle prover must reject witnesses that fail the native checker"
    );
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_carries_ligero_proximity_openings() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();

    assert_eq!(bundle.proximity_openings.len(), bundle.params.openings);
    assert!(bundle.params.openings > 0);
}

#[test]
#[ignore = "full P4a masked Ligero bundle is a release gate"]
fn implemented_circuit_bundle_rejects_corrupt_ligero_opening() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.proximity_openings[0].column[0] = bundle.proximity_openings[0].column[0] + Fp::ONE;

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_corrupt_ligero_proximity_claim() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.proximity_claim.combined_row[0] = bundle.proximity_claim.combined_row[0] + Fp::ONE;

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_corrupt_ligero_claim_batch_coefficient() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.claim_batch.coefficients[0] = bundle.claim_batch.coefficients[0] + Fp::ONE;

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_corrupt_ligero_blind_claim() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.claim_batch.blind_claim = bundle.claim_batch.blind_claim + Fp::ONE;

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_corrupt_ligero_blind_row_opening() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let last = bundle.proximity_openings[0].column.len() - 1;
    bundle.proximity_openings[0].column[last] = bundle.proximity_openings[0].column[last] + Fp::ONE;

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_corrupt_ligero_consistency_claim_value() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.consistency_claim_values[0] = bundle.consistency_claim_values[0] + Fp::ONE;

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_prover_selected_ligero_proximity_columns() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.proximity_openings.reverse();

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_prover_selected_ligero_params() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    bundle.params = LigeroParams {
        row_len: 32,
        degree_bound: 36,
        codeword_len: 128,
        openings: 4,
        proximity_radius: 0,
        code: LigeroCode::Rs,
    };

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full P4a masked Ligero bundle is a release gate"]
fn implemented_circuit_bundle_rejects_wrong_caller_input_binding() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();

    let mut wrong_input = input;
    wrong_input.r[31] ^= 1;

    assert!(verify_implemented_circuit_bundle(&wrong_input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_spliced_c14_entry() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let alternate = alternate_signed_input();
    let alternate_witness = generate_witness(&alternate).unwrap();

    bundle.entries[5] = c14_bundle_entry(&alternate, &alternate_witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_spliced_c2_entry() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let alternate = alternate_signed_input();

    bundle.entries[1] = c2_bundle_entry(&alternate);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_spliced_c3_entry() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let alternate = alternate_signed_input();
    let alternate_witness = generate_witness(&alternate).unwrap();

    bundle.entries[2] = c3_bundle_entry(&alternate, &alternate_witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_spliced_c11_entry() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let alternate = alternate_signed_input();
    let alternate_witness = generate_witness(&alternate).unwrap();

    bundle.entries[3] = c11_bundle_entry(&alternate_witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_spliced_c12_entry() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let alternate = alternate_signed_input();
    let alternate_witness = generate_witness(&alternate).unwrap();

    bundle.entries[4] = c12_bundle_entry(&alternate_witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_legacy_entry_without_statement_absorb() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();

    bundle.entries[5] = c14_legacy_transcript_bundle_entry(&input, &witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full P4a masked Ligero bundle is a release gate"]
fn implemented_circuit_bundle_accepts_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let (bundle, profile) =
        prove_implemented_circuit_bundle_profiled(&input, &witness, TEST_SEED).unwrap();

    assert_eq!(bundle.entries.len(), 6);
    assert_eq!(bundle.params, v4_circle_params());
    assert_eq!(bundle.proximity_openings.len(), bundle.params.openings);
    assert!(bundle
        .proximity_openings
        .iter()
        .all(|opening| opening.index < bundle.params.codeword_len));
    assert_eq!(
        bundle
            .proximity_openings
            .iter()
            .map(|opening| opening.index)
            .collect::<std::collections::HashSet<_>>()
            .len(),
        bundle.params.openings,
        "proximity columns must be distinct"
    );
    assert!(
        bundle
            .proximity_openings
            .iter()
            .any(|opening| opening.index < bundle.params.row_len),
        "circle proximity sampling must cover its full non-systematic domain"
    );
    assert!(profile.committed_values <= 10_000, "{profile:?}");
    assert!(profile.ligero_rows <= 156, "{profile:?}");
    assert_eq!(
        bundle.proximity_claim.combined_row.len(),
        bundle.params.degree_bound
    );
    assert_eq!(
        bundle.claim_batch.coefficients.len(),
        bundle.params.claim_degree_bound()
    );
    verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).unwrap();

    let mut missing_entry = bundle.clone();
    missing_entry.entries.pop();
    assert!(verify_implemented_circuit_bundle(&input, &missing_entry, TEST_SEED).is_err());

    let mut extra_entry = bundle.clone();
    extra_entry.entries.push(bundle.entries[0].clone());
    assert!(verify_implemented_circuit_bundle(&input, &extra_entry, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_wrong_caller_input() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let mut wrong_input = input;
    wrong_input.r[31] ^= 1;

    assert!(verify_implemented_circuit_bundle(&wrong_input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "release gate: full P4b public projection bundle proof"]
fn implemented_circuit_bundle_accepts_p4b_public_projection() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let witnesses = [
        generate_witness(&issuer).unwrap(),
        generate_witness(&device).unwrap(),
    ];
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let projections = [issuer_public, device_public];
    let bundle = prove_implemented_circuit_bundle_batch_with_projection(
        &[issuer, device],
        &projections,
        &witnesses,
        TEST_SEED,
    )
    .unwrap();

    verify_implemented_circuit_bundle_batch_with_projection(&projections, &bundle, TEST_SEED)
        .unwrap();
}

#[test]
#[ignore = "release gate: full P4b public projection bundle proof"]
fn implemented_circuit_bundle_rejects_wrong_p4b_public_projection() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let witnesses = [
        generate_witness(&issuer).unwrap(),
        generate_witness(&device).unwrap(),
    ];
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let bundle = prove_implemented_circuit_bundle_batch_with_projection(
        &[issuer, device],
        &[issuer_public, device_public],
        &witnesses,
        TEST_SEED,
    )
    .unwrap();

    let mut wrong_issuer_q = issuer_public;
    wrong_issuer_q.qx.as_mut().unwrap()[31] ^= 1;
    assert!(verify_implemented_circuit_bundle_batch_with_projection(
        &[wrong_issuer_q, device_public],
        &bundle,
        TEST_SEED,
    )
    .is_err());

    let mut wrong_device_z = device_public;
    wrong_device_z.z.as_mut().unwrap()[31] ^= 1;
    assert!(verify_implemented_circuit_bundle_batch_with_projection(
        &[issuer_public, wrong_device_z],
        &bundle,
        TEST_SEED,
    )
    .is_err());
}

#[test]
#[ignore = "release gate: full P4b mdoc MAC-bound bundle proof"]
fn mdoc_p4b_bundle_accepts_honest_mac_tags_and_rejects_tag_tamper() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let mac_key_shares = test_mac_key_shares();

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        None,
        &mac_key_shares,
        TEST_SEED,
    )
    .unwrap();

    assert_eq!(bundle.mac_tags.len(), 6);
    assert_eq!(
        MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS, 8448,
        "Q-021 requires six halves of x, a_p, u, and q parity-witness bits"
    );
    verify_mdoc_p4b_circuit_bundle(&issuer_public, &device_public, None, &bundle, TEST_SEED)
        .unwrap();

    let mut tampered = bundle.clone();
    tampered.mac_tags[0][0] ^= 1;
    assert!(verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        None,
        &tampered,
        TEST_SEED
    )
    .is_err());

    let mut tampered_root_b = bundle.clone();
    tampered_root_b.root_b.as_mut().unwrap()[0] ^= 1;
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            None,
            &tampered_root_b,
            TEST_SEED
        )
        .is_err(),
        "Q022 root_B is part of the full transcript root and must be binding"
    );

    let mut missing_root_b = bundle.clone();
    missing_root_b.root_b = None;
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            None,
            &missing_root_b,
            TEST_SEED
        )
        .is_err(),
        "Q022 verifier must require the second MAC witness commitment"
    );

    let mut tampered_b_opening = bundle;
    tampered_b_opening.proximity_openings_b[0].column[0] =
        tampered_b_opening.proximity_openings_b[0].column[0] + Fp::ONE;
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            None,
            &tampered_b_opening,
            TEST_SEED
        )
        .is_err(),
        "Q022 Group B openings must be verified against root_B"
    );
}

#[test]
#[ignore = "release gate: full P4b mdoc MAC-bound bundle proof"]
fn mdoc_p4b_bundle_rejects_spliced_mac_batch_entry() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        None,
        &test_mac_key_shares(),
        TEST_SEED,
    )
    .unwrap();
    let alternate_bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        None,
        &alternate_mac_key_shares(),
        TEST_SEED,
    )
    .unwrap();

    assert_eq!(bundle.entries.len(), 13);
    verify_mdoc_p4b_circuit_bundle(&issuer_public, &device_public, None, &bundle, TEST_SEED)
        .unwrap();

    let mut spliced = bundle;
    let mac_batch_index = spliced.entries.len() - 1;
    spliced.entries[mac_batch_index] = alternate_bundle.entries[mac_batch_index].clone();
    assert!(
        verify_mdoc_p4b_circuit_bundle(&issuer_public, &device_public, None, &spliced, TEST_SEED)
            .is_err(),
        "MAC batch sumcheck entry from a different root/key-share transcript unexpectedly verified"
    );
}

#[test]
#[ignore = "release gate: full P4b mdoc MAC-bound bundle proof with revocation set"]
fn mdoc_p4b_bundle_with_revocation_set_verifies_and_fails_closed() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let revocation = revocation_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let revocation_witness = generate_witness(&revocation).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let revocation_public = EcdsaPublicProjection::message_hash_only(revocation.z);
    let mac_key_shares = test_mac_key_shares();

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        Some((&revocation, &revocation_public, &revocation_witness)),
        &mac_key_shares,
        TEST_SEED,
    )
    .unwrap();

    assert_eq!(bundle.entries.len(), 19, "three ECDSA sets plus MAC batch");
    verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        Some(&revocation_public),
        &bundle,
        TEST_SEED,
    )
    .unwrap();

    assert!(
        verify_mdoc_p4b_circuit_bundle(&issuer_public, &device_public, None, &bundle, TEST_SEED)
            .is_err(),
        "three-set bundle must not verify against a two-set expectation"
    );

    let mut wrong_revocation_z = revocation_public;
    wrong_revocation_z.z.as_mut().unwrap()[31] ^= 1;
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            Some(&wrong_revocation_z),
            &bundle,
            TEST_SEED,
        )
        .is_err(),
        "tampered revocation message-hash projection must be rejected"
    );

    let two_set_bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        None,
        &mac_key_shares,
        TEST_SEED,
    )
    .unwrap();
    assert_eq!(two_set_bundle.entries.len(), 13);
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            Some(&revocation_public),
            &two_set_bundle,
            TEST_SEED,
        )
        .is_err(),
        "two-set bundle must not verify against a three-set expectation"
    );
}

fn test_mac_key_shares() -> MdocP4bMacKeyShares {
    MdocP4bMacKeyShares(std::array::from_fn(|index| {
        let mut share = [0u8; 16];
        for (byte_index, byte) in share.iter_mut().enumerate() {
            *byte = 0x41u8
                .wrapping_add(index as u8 * 19)
                .wrapping_add(byte_index as u8 * 7);
        }
        share
    }))
}

fn alternate_mac_key_shares() -> MdocP4bMacKeyShares {
    MdocP4bMacKeyShares(std::array::from_fn(|index| {
        let mut share = [0u8; 16];
        for (byte_index, byte) in share.iter_mut().enumerate() {
            *byte = 0xb3u8
                .wrapping_sub(index as u8 * 11)
                .wrapping_add(byte_index as u8 * 5);
        }
        share
    }))
}

fn c2_bundle_entry(input: &EcdsaInput) -> ImplementedCircuitBundleEntry {
    let witness = generate_witness(input).unwrap();
    prove_implemented_circuit_bundle(input, &witness, TEST_SEED)
        .unwrap()
        .entries[1]
        .clone()
}

fn c3_bundle_entry(
    input: &EcdsaInput,
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    prove_implemented_circuit_bundle(input, witness, TEST_SEED)
        .unwrap()
        .entries[2]
        .clone()
}

fn c11_bundle_entry(
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    let input = alternate_signed_input();
    prove_implemented_circuit_bundle(&input, witness, TEST_SEED)
        .unwrap()
        .entries[3]
        .clone()
}

fn c12_bundle_entry(
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    let input = alternate_signed_input();
    prove_implemented_circuit_bundle(&input, witness, TEST_SEED)
        .unwrap()
        .entries[4]
        .clone()
}

fn c14_bundle_entry(
    input: &EcdsaInput,
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    prove_implemented_circuit_bundle(input, witness, TEST_SEED)
        .unwrap()
        .entries[5]
        .clone()
}

fn mutate_interior_u1_accumulator(witness: &mut eu_id_ec_coprocessor::ecdsa::Witness) {
    let generator = AffinePoint::GENERATOR.to_encoded_point(false);
    let gx = fp_from_coord(generator.x().unwrap());
    let gy = fp_from_coord(generator.y().unwrap());
    let point_index = 20usize;
    let u1 = layout_range(LayoutSlot::U1GAccumulators);
    witness.values[u1.start + point_index * 2] = gx;
    witness.values[u1.start + point_index * 2 + 1] = gy;
}

fn c14_legacy_transcript_bundle_entry(
    input: &EcdsaInput,
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    let circuit = build_c14_c15_final_check_circuit().unwrap();
    let circuit_input = c14_c15_final_check_input(input, witness).unwrap();
    let mut committed_input = circuit_input.clone();
    committed_input.extend(circuit_otp_pad_values(&circuit));
    let params = v2_ligero_params();
    let commitment = commit_witness(&committed_input, params).unwrap();
    let root = commitment.root();
    let layers = circuit.evaluate_input(circuit_input).unwrap();
    let mut channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    channel.mix_bytes(b"s4-ecdsa-c14-c15-final-check");
    let proof = prove_circuit(&circuit, &layers, root, &mut channel).unwrap();

    ImplementedCircuitBundleEntry { proof }
}
