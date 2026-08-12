use ecdsa::signature::hazmat::PrehashSigner;
use ecdsa::signature::Signer;
use eu_id_ec_coprocessor::ecdsa::{
    build_c11_final_add_circuit, build_c12_on_curve_circuit, build_c14_c15_final_check_circuit,
    build_c1_input_limbs_circuit, build_c2_canonicality_circuit, build_c3_c5_scalar_setup_circuit,
    build_c9_c10_ladder_circuit, c11_final_add_input, c12_on_curve_input,
    c12_witness_on_curve_input, c14_c15_final_check_input, c1_input_limbs_input,
    c2_canonicality_input, c3_c5_scalar_setup_input, c9_c10_ladder_input, generate_witness,
    implemented_circuit_family_labels, implemented_circuit_gate_count, layout_range,
    prove_implemented_circuit_bundle, prove_implemented_circuit_bundle_batch_with_projection,
    prove_implemented_circuit_bundle_profiled, prove_implemented_circuit_bundle_unchecked_profiled,
    prove_implemented_circuit_proofs, prove_mdoc_p4b_circuit_bundle,
    verify_implemented_circuit_bundle, verify_implemented_circuit_bundle_batch_with_projection,
    verify_implemented_circuit_proofs, verify_implemented_circuits, verify_mdoc_p4b_circuit_bundle,
    verify_witness, EcdsaInput, EcdsaPublicProjection, ImplementedCircuitBundle,
    ImplementedCircuitBundleEntry, LayoutSlot, MdocP4bMacKeyShares, Witness, WitnessError,
    MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS, MDOC_P4B_MAC_HALF_COUNT, N_LIMBS,
};
use eu_id_ec_coprocessor::ligero::{commit_witness, product_circle_params};
use eu_id_ec_coprocessor::sumcheck::{prove_circuit, CircuitPads};
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

fn signed_input_for_digest(secret: u8, z: [u8; 32]) -> EcdsaInput {
    let signing_key = SigningKey::from_bytes((&[secret; 32]).into()).unwrap();
    let signature: Signature = signing_key.sign_prehash(&z).unwrap();
    let public_key = signing_key.verifying_key().to_encoded_point(false);
    let mut qx = [0u8; 32];
    let mut qy = [0u8; 32];
    qx.copy_from_slice(public_key.x().unwrap());
    qy.copy_from_slice(public_key.y().unwrap());
    EcdsaInput {
        z,
        r: signature.r().to_bytes().into(),
        s: signature.s().to_bytes().into(),
        qx,
        qy,
    }
}

fn p256_field_modulus_digest() -> [u8; 32] {
    [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff,
    ]
}

fn p256_order_digest() -> [u8; 32] {
    [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x51,
    ]
}

fn increment_digest(mut digest: [u8; 32]) -> [u8; 32] {
    for byte in digest.iter_mut().rev() {
        let (value, carry) = byte.overflowing_add(1);
        *byte = value;
        if !carry {
            return digest;
        }
    }
    panic!("test digest overflow")
}

#[test]
fn implemented_circuit_gate_count_stays_under_s4_budget() {
    let gates = implemented_circuit_gate_count().unwrap();
    eprintln!("implemented S4-lite ECDSA BL2 gate count: {gates}");

    assert!(gates > 0);
    assert!(
        gates <= 80_000,
        "implemented gate count exceeds repaired S4 budget"
    );
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
fn c2_canonicality_circuit_rejects_bad_public_key() {
    let circuit = build_c2_canonicality_circuit().unwrap();

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
    let r_limb = layout_range(LayoutSlot::InputLimbs).start + N_LIMBS;
    witness.values[r_limb] = witness.values[r_limb] + Fp::ONE;
    let layers = circuit
        .evaluate_input(c1_input_limbs_input(&input, &witness).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "bad r limb must reject"
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
    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::UScalars).start] =
        witness.values[layout_range(LayoutSlot::UScalars).start] + Fp::ONE;
    assert!(
        c3_c5_scalar_setup_input(&input, &witness).is_err(),
        "bad u1 must reject"
    );

    let witness = generate_witness(&input).unwrap();
    let mut zero_r = input;
    zero_r.r = [0u8; 32];
    assert!(
        c3_c5_scalar_setup_input(&zero_r, &witness).is_err(),
        "C3 owns the nonzero r constraint"
    );

    let mut zero_s = input;
    zero_s.s = [0u8; 32];
    assert!(
        c3_c5_scalar_setup_input(&zero_s, &witness).is_err(),
        "C3 owns the nonzero s constraint"
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
fn c9_c10_ladder_circuit_binds_every_transition_and_endpoint() {
    let input = signed_input();
    let circuit = build_c9_c10_ladder_circuit().unwrap();
    let witness = generate_witness(&input).unwrap();
    let layers = circuit
        .evaluate_input(c9_c10_ladder_input(&input, &witness).unwrap())
        .unwrap();
    assert!(circuit.is_satisfied(&layers).unwrap());

    let mut forged = witness.clone();
    let generator = AffinePoint::GENERATOR.to_encoded_point(false);
    let gx = fp_from_coord(generator.x().unwrap());
    let gy = fp_from_coord(generator.y().unwrap());
    for slot in [LayoutSlot::U1GAccumulators, LayoutSlot::U2QAccumulators] {
        for point in forged.values[layout_range(slot)].chunks_exact_mut(2) {
            point.copy_from_slice(&[gx, gy]);
        }
    }
    let layers = circuit
        .evaluate_input(c9_c10_ladder_input(&input, &forged).unwrap())
        .unwrap();
    assert!(
        !circuit.is_satisfied(&layers).unwrap(),
        "on-curve accumulator substitutions must fail the transition relation"
    );
}

#[test]
fn c11_final_add_circuit_rejects_accumulator_and_final_point_mutations() {
    let input = signed_input();
    let circuit = build_c11_final_add_circuit().unwrap();
    let rejects = |witness: &Witness| match c11_final_add_input(witness) {
        Ok(circuit_input) => {
            let layers = circuit.evaluate_input(circuit_input).unwrap();
            !circuit.is_satisfied(&layers).unwrap()
        }
        Err(WitnessError::ExceptionalTrace) => true,
        Err(error) => panic!("unexpected C11 input error: {error:?}"),
    };

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start] =
        witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start] + Fp::ONE;
    assert!(rejects(&witness), "bad corrected S1 endpoint must reject");

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalPoint).start] =
        witness.values[layout_range(LayoutSlot::FinalPoint).start] + Fp::ONE;
    assert!(rejects(&witness), "bad final R must reject");

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] =
        witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] + Fp::ONE;
    assert!(
        rejects(&witness),
        "bad witnessed final-add inverse must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    let corrected = layout_range(LayoutSlot::CorrectedEndpoints);
    witness.values[corrected.start + 2] = witness.values[corrected.start];
    witness.values[layout_range(LayoutSlot::FinalAddDenominatorInverse).start] = Fp::ZERO;
    assert_eq!(
        c11_final_add_input(&witness),
        Err(WitnessError::ExceptionalTrace),
        "the input builder must fail closed on a zero final-add denominator"
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
fn c14_c15_final_check_circuit_rejects_final_mutations() {
    let input = signed_input();

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalPoint).start] =
        witness.values[layout_range(LayoutSlot::FinalPoint).start] + Fp::ONE;
    assert!(
        c14_c15_final_check_input(&input, &witness).is_err(),
        "inconsistent R.x must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalReduction).start] = Fp::from_u64(2);
    assert!(
        c14_c15_final_check_input(&input, &witness).is_err(),
        "non-boolean k must reject"
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
    let r_limb = layout_range(LayoutSlot::InputLimbs).start + N_LIMBS;
    witness.values[r_limb] = witness.values[r_limb] + Fp::ONE;
    assert!(verify_implemented_circuits(&input, &witness).is_err());

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::UScalars).start] =
        witness.values[layout_range(LayoutSlot::UScalars).start] + Fp::ONE;
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
            b"s4-ecdsa-c9-c10-ladder".as_slice(),
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
    assert_eq!(labels[6], b"s4-ecdsa-c14-c15-final-check");
}

#[test]
fn unbound_circuit_proofs_derive_different_claims_under_wrong_root() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let proofs = prove_implemented_circuit_proofs(&input, &witness, [3u8; 32], TEST_SEED).unwrap();

    let honest =
        verify_implemented_circuit_proofs(&proofs, [3u8; 32], TEST_SEED).expect("honest claims");
    let wrong =
        verify_implemented_circuit_proofs(&proofs, [4u8; 32], TEST_SEED).expect("derived claims");
    assert_ne!(
        honest, wrong,
        "the low-level API is intentionally unbound, but its derived claims must bind the root; the production bundle rejects the wrong-root constraints through Ligero"
    );
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
    let r_limb = layout_range(LayoutSlot::InputLimbs).start + N_LIMBS;
    witness.values[r_limb] = witness.values[r_limb] + Fp::ONE;

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
fn implemented_circuits_reject_native_witness_ladder_mismatch() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();
    mutate_interior_u1_accumulator(&mut witness);

    assert!(
        verify_witness(&input, &witness).is_err(),
        "native checker must reject the mutated accumulator transcript"
    );
    assert!(
        verify_implemented_circuits(&input, &witness).is_err(),
        "C9-C10 must reject a mutated accumulator transition"
    );

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
fn forged_ladder_accumulators_must_reject() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();
    let generator = AffinePoint::GENERATOR.to_encoded_point(false);
    let gx = fp_from_coord(generator.x().unwrap());
    let gy = fp_from_coord(generator.y().unwrap());

    for slot in [LayoutSlot::U1GAccumulators, LayoutSlot::U2QAccumulators] {
        for point in witness.values[layout_range(slot)].chunks_exact_mut(2) {
            point.copy_from_slice(&[gx, gy]);
        }
    }

    assert!(
        verify_witness(&input, &witness).is_err(),
        "native witness checking must notice the forged ladder"
    );
    assert!(
        verify_implemented_circuits(&input, &witness).is_err(),
        "the implemented relation must enforce every ladder transition",
    );

    assert!(
        prove_implemented_circuit_bundle_unchecked_profiled(&input, &witness, TEST_SEED).is_err(),
        "even the native-check-bypassing prover must reject an unsatisfied ladder circuit"
    );
}

#[test]
fn invalid_external_ecdsa_input_bundle_must_reject() {
    let mut input = signed_input();
    input.z[0] ^= 1;
    let witness = generate_witness(&input).expect("invalid signatures still have an EC trace");
    assert!(
        verify_witness(&input, &witness).is_err(),
        "native ECDSA verification must reject the changed message hash"
    );

    assert!(
        prove_implemented_circuit_bundle_unchecked_profiled(&input, &witness, TEST_SEED).is_err(),
        "the proof relation must reject an invalid external ECDSA tuple"
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
    bundle.params.row_len = 0;

    let verdict =
        std::panic::catch_unwind(|| verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED));
    assert!(
        verdict.is_ok(),
        "malformed proof-carried params must not panic the production verifier"
    );
    assert!(verdict.unwrap().is_err());
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

    bundle.entries[6] = c14_bundle_entry(&alternate, &alternate_witness);

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
fn implemented_circuit_bundle_rejects_spliced_c9_entry() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();
    let alternate = alternate_signed_input();
    let alternate_witness = generate_witness(&alternate).unwrap();

    bundle.entries[3] = c9_bundle_entry(&alternate, &alternate_witness);

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

    bundle.entries[4] = c11_bundle_entry(&alternate_witness);

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

    bundle.entries[5] = c12_bundle_entry(&alternate_witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full S4-lite bundle proves every implemented ECDSA circuit"]
fn implemented_circuit_bundle_rejects_entry_without_statement_absorb() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let mut bundle = prove_implemented_circuit_bundle(&input, &witness, TEST_SEED).unwrap();

    bundle.entries[6] = c14_transcript_without_statement_bundle_entry(&input, &witness);

    assert!(verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).is_err());
}

#[test]
#[ignore = "full P4a masked Ligero bundle is a release gate"]
fn implemented_circuit_bundle_accepts_honest_witness() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let (bundle, profile) =
        prove_implemented_circuit_bundle_profiled(&input, &witness, TEST_SEED).unwrap();

    assert_eq!(bundle.entries.len(), 7);
    assert_eq!(bundle.params, product_circle_params());
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
    assert!(profile.committed_values <= 22_000, "{profile:?}");
    assert!(profile.ligero_rows <= 90, "{profile:?}");
    assert_eq!(
        bundle.proximity_claim.combined_row.len(),
        bundle.params.degree_bound
    );
    assert_eq!(
        bundle.claim_batch.coefficients.len(),
        bundle.params.claim_degree_bound()
    );
    assert_eq!(
        bundle.claim_blind_check.combined_row.len(),
        bundle.params.claim_degree_bound()
    );
    assert_eq!(
        bundle.quadratic_batch.quotient.len(),
        bundle.params.quadratic_degree_bound() - bundle.params.row_len,
        "the committed quadratic constraints require the exact Z_W quotient bound"
    );
    verify_implemented_circuit_bundle(&input, &bundle, TEST_SEED).unwrap();

    let mut corrupt_quadratic = bundle.clone();
    corrupt_quadratic.quadratic_batch.quotient[0] =
        corrupt_quadratic.quadratic_batch.quotient[0] + Fp::ONE;
    assert!(
        verify_implemented_circuit_bundle(&input, &corrupt_quadratic, TEST_SEED).is_err(),
        "the production path must reject a forged quadratic response"
    );

    let mut corrupt_claim_blind_check = bundle.clone();
    corrupt_claim_blind_check.claim_blind_check.combined_row[0] =
        corrupt_claim_blind_check.claim_blind_check.combined_row[0] + Fp::ONE;
    assert!(
        verify_implemented_circuit_bundle(&input, &corrupt_claim_blind_check, TEST_SEED).is_err(),
        "the production path must reject a forged claim-blind kernel response"
    );

    let mut corrupt_masked_sumcheck = bundle.clone();
    corrupt_masked_sumcheck.entries[0].proof.layers[0].rounds[0][0] =
        corrupt_masked_sumcheck.entries[0].proof.layers[0].rounds[0][0] + Fp::ONE;
    assert!(
        verify_implemented_circuit_bundle(&input, &corrupt_masked_sumcheck, TEST_SEED).is_err(),
        "the production path must reject a forged masked sumcheck response"
    );

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
#[ignore = "release gate: full projected proof over full-width public digests"]
fn implemented_circuit_bundle_accepts_full_width_public_digests() {
    let digests = [
        ("n", p256_order_digest()),
        ("p+1", increment_digest(p256_field_modulus_digest())),
    ];
    let inputs = digests.map(|(_, digest)| signed_input_for_digest(13, digest));
    let witnesses = inputs.map(|input| {
        generate_witness(&input).expect("full-width digest has a complete valid ECDSA witness")
    });
    let projections = digests.map(|(_, digest)| EcdsaPublicProjection::message_hash_only(digest));
    let bundle = prove_implemented_circuit_bundle_batch_with_projection(
        &inputs,
        &projections,
        &witnesses,
        TEST_SEED,
    )
    .expect("full-width projected proof succeeds");

    verify_implemented_circuit_bundle_batch_with_projection(&projections, &bundle, TEST_SEED)
        .expect("full-width projected proof verifies");
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
    let revocation = revocation_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let revocation_witness = generate_witness(&revocation).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let revocation_public = EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);
    let mac_key_shares = test_mac_key_shares();

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        (&revocation, &revocation_public, &revocation_witness),
        &mac_key_shares,
        TEST_SEED,
    )
    .unwrap();

    assert_eq!(bundle.mac_tags.len(), MDOC_P4B_MAC_HALF_COUNT);
    assert_eq!(
        MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS, 10_242,
        "the eight affine MAC halves include two exact-coordinate canonicality witnesses"
    );
    let serialized = bincode::serialize(&bundle).unwrap();
    let mut hidden_values = vec![
        issuer.z.to_vec(),
        issuer.r.to_vec(),
        issuer.s.to_vec(),
        device.r.to_vec(),
        device.s.to_vec(),
        device.qx.to_vec(),
        device.qy.to_vec(),
        revocation.z.to_vec(),
        revocation.r.to_vec(),
        revocation.s.to_vec(),
    ];
    for witness in [&issuer_witness, &device_witness, &revocation_witness] {
        hidden_values.extend(
            witness.values[layout_range(LayoutSlot::UScalars)]
                .iter()
                .map(|value| value.to_bytes_be().to_vec()),
        );
    }
    for hidden in hidden_values {
        assert!(
            !serialized
                .windows(hidden.len())
                .any(|window| window == hidden),
            "serialized bundle contains a private ECDSA/MAC binding operand"
        );
    }
    verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        &revocation_public,
        &bundle,
        TEST_SEED,
    )
    .unwrap();

    let mut corrupt_claim_blind_check = bundle.clone();
    corrupt_claim_blind_check.claim_blind_check.combined_row[0] =
        corrupt_claim_blind_check.claim_blind_check.combined_row[0] + Fp::ONE;
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            &revocation_public,
            &corrupt_claim_blind_check,
            TEST_SEED
        )
        .is_err(),
        "the split production path must reject a forged kernel response"
    );

    let mut malformed_params = bundle.clone();
    malformed_params.params.row_len = 0;
    let malformed_verdict = std::panic::catch_unwind(|| {
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            &revocation_public,
            &malformed_params,
            TEST_SEED,
        )
    });
    assert!(
        malformed_verdict.is_ok(),
        "malformed split proof params must not panic the production verifier"
    );
    assert!(malformed_verdict.unwrap().is_err());

    let mut tampered = bundle.clone();
    tampered.mac_tags[0][0] ^= 1;
    assert!(verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        &revocation_public,
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
            &revocation_public,
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
            &revocation_public,
            &missing_root_b,
            TEST_SEED
        )
        .is_err(),
        "Q022 verifier must require the second MAC witness commitment"
    );

    let mut tampered_b_opening = bundle;
    let batch_b = tampered_b_opening.proximity_batch_b.as_mut().unwrap();
    batch_b.columns[0] = batch_b.columns[0] + Fp::ONE;
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            &revocation_public,
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
    let revocation = revocation_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let revocation_witness = generate_witness(&revocation).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let revocation_public = EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        (&revocation, &revocation_public, &revocation_witness),
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
        (&revocation, &revocation_public, &revocation_witness),
        &alternate_mac_key_shares(),
        TEST_SEED,
    )
    .unwrap();

    assert_eq!(bundle.entries.len(), 22);
    verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        &revocation_public,
        &bundle,
        TEST_SEED,
    )
    .unwrap();

    let mut spliced = bundle;
    let mac_batch_index = spliced.entries.len() - 1;
    spliced.entries[mac_batch_index] = alternate_bundle.entries[mac_batch_index].clone();
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            &revocation_public,
            &spliced,
            TEST_SEED,
        )
        .is_err(),
        "MAC batch sumcheck entry from a different root/key-share transcript unexpectedly verified"
    );
}

#[test]
#[ignore = "release gate: full P4b mdoc MAC-bound bundle proof with revocation set"]
fn mdoc_p4b_bundle_with_mandatory_revocation_verifies_and_fails_closed() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let revocation = revocation_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let revocation_witness = generate_witness(&revocation).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let revocation_public = EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);
    assert_eq!(revocation_public.z, None);
    assert_eq!(revocation_public.r, None);
    assert_eq!(revocation_public.s, None);
    let mac_key_shares = test_mac_key_shares();

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        (&revocation, &revocation_public, &revocation_witness),
        &mac_key_shares,
        TEST_SEED,
    )
    .unwrap();

    assert_eq!(bundle.entries.len(), 22, "three ECDSA sets plus MAC batch");
    verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        &revocation_public,
        &bundle,
        TEST_SEED,
    )
    .unwrap();
    let serialized = bincode::serialize(&bundle).unwrap();
    for private_value in [revocation.z, revocation.r, revocation.s] {
        assert!(
            !serialized
                .windows(private_value.len())
                .any(|window| window == private_value),
            "serialized revocation bundle contains a private digest/signature operand"
        );
    }

    let wrong_revocation_key = EcdsaPublicProjection::public_key_only(issuer.qx, issuer.qy);
    assert!(
        verify_mdoc_p4b_circuit_bundle(
            &issuer_public,
            &device_public,
            &wrong_revocation_key,
            &bundle,
            TEST_SEED,
        )
        .is_err(),
        "a different valid revocation public key must be rejected"
    );
}

#[test]
#[ignore = "release gate: full P4b mdoc bundle covers private/public full-width digest roles"]
fn mdoc_p4b_bundle_accepts_p_p_plus_one_and_max_digests() {
    let p = p256_field_modulus_digest();
    let p_plus_one = increment_digest(p);
    let issuer = signed_input_for_digest(15, p);
    let device = signed_input_for_digest(17, p_plus_one);
    let revocation = signed_input_for_digest(19, [u8::MAX; 32]);
    let issuer_witness = generate_witness(&issuer).expect("issuer z=p witness");
    let device_witness = generate_witness(&device).expect("device z=p+1 witness");
    let revocation_witness = generate_witness(&revocation).expect("revocation z=max witness");
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let revocation_public = EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        (&revocation, &revocation_public, &revocation_witness),
        &test_mac_key_shares(),
        TEST_SEED,
    )
    .expect("full-width digest mdoc proof succeeds");

    verify_mdoc_p4b_circuit_bundle(
        &issuer_public,
        &device_public,
        &revocation_public,
        &bundle,
        TEST_SEED,
    )
    .expect("full-width digest mdoc proof verifies");
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

fn c9_bundle_entry(
    input: &EcdsaInput,
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    prove_implemented_circuit_bundle(input, witness, TEST_SEED)
        .unwrap()
        .entries[3]
        .clone()
}

fn c11_bundle_entry(
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    let input = alternate_signed_input();
    prove_implemented_circuit_bundle(&input, witness, TEST_SEED)
        .unwrap()
        .entries[4]
        .clone()
}

fn c12_bundle_entry(
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    let input = alternate_signed_input();
    prove_implemented_circuit_bundle(&input, witness, TEST_SEED)
        .unwrap()
        .entries[5]
        .clone()
}

fn c14_bundle_entry(
    input: &EcdsaInput,
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    prove_implemented_circuit_bundle(input, witness, TEST_SEED)
        .unwrap()
        .entries[6]
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

fn c14_transcript_without_statement_bundle_entry(
    input: &EcdsaInput,
    witness: &eu_id_ec_coprocessor::ecdsa::Witness,
) -> ImplementedCircuitBundleEntry {
    let circuit = build_c14_c15_final_check_circuit().unwrap();
    let circuit_input = c14_c15_final_check_input(input, witness).unwrap();
    let pads = CircuitPads::fresh(&circuit);
    let mut committed_input = circuit_input.clone();
    committed_input.extend_from_slice(pads.values());
    let params = product_circle_params();
    let commitment = commit_witness(&committed_input, params).unwrap();
    let root = commitment.root();
    let layers = circuit.evaluate_input(circuit_input).unwrap();
    let mut channel = CoprocessorChannel::from_seed([0u8; 32], b"test");
    channel.mix_bytes(b"s4-ecdsa-c14-c15-final-check");
    let proof = prove_circuit(&circuit, &layers, &pads, root, &mut channel).unwrap();

    ImplementedCircuitBundleEntry { proof }
}

/// One row of the P4b bundle byte accounting, named after the bundle field it
/// covers.
struct BundleSection {
    label: String,
    bytes: usize,
}

fn serialized_len<T: serde::Serialize>(value: &T) -> usize {
    bincode::serialized_size(value).expect("bundle field serializes") as usize
}

/// Attributes every serialized byte of an `ImplementedCircuitBundle` to the
/// struct field it comes from.
///
/// bincode concatenates struct fields with no framing of its own, so per-field
/// lengths add up to the whole serialized bundle. The residual returned
/// alongside the sections is therefore only the length prefix of each `Vec`
/// that got split into sub-field rows.
fn bundle_byte_breakdown(
    bundle: &ImplementedCircuitBundle,
    entry_labels: &[String],
) -> (Vec<BundleSection>, usize, usize) {
    let mut sections = Vec::new();
    let mut push = |label: String, bytes: usize| sections.push(BundleSection { label, bytes });

    for (index, entry) in bundle.entries.iter().enumerate() {
        let rounds = entry
            .proof
            .layers
            .iter()
            .map(|layer| layer.rounds.len())
            .sum::<usize>();
        let name = entry_labels
            .get(index)
            .map(String::as_str)
            .unwrap_or("unlabelled");
        push(
            format!(
                "entries[{index:02}].proof sumcheck transcript — {name} ({} layers, {rounds} rounds)",
                entry.proof.layers.len(),
            ),
            serialized_len(&entry.proof),
        );
    }

    for (field, openings) in [
        ("proximity_openings", &bundle.proximity_openings),
        ("proximity_openings_b", &bundle.proximity_openings_b),
    ] {
        if openings.is_empty() {
            continue;
        }
        let siblings = openings.iter().map(|o| o.path.len()).sum::<usize>();
        push(
            format!("{field}[*].column ligero openings ({})", openings.len()),
            openings.iter().map(|o| serialized_len(&o.column)).sum(),
        );
        push(
            format!("{field}[*].path merkle auth paths ({siblings} siblings)"),
            openings.iter().map(|o| serialized_len(&o.path)).sum(),
        );
        push(
            format!("{field}[*].index"),
            openings.iter().map(|o| serialized_len(&o.index)).sum(),
        );
    }
    for (field, opening) in [
        ("proximity_batch", bundle.proximity_batch.as_ref()),
        ("proximity_batch_b", bundle.proximity_batch_b.as_ref()),
    ] {
        let Some(opening) = opening else {
            continue;
        };
        push(
            format!("{field}.columns flat ligero openings"),
            serialized_len(&opening.columns),
        );
        push(
            format!(
                "{field}.frontier canonical merkle multiproof ({} hashes)",
                opening.frontier.len(),
            ),
            serialized_len(&opening.frontier),
        );
    }

    push(
        "proximity_claim.combined_row".to_string(),
        serialized_len(&bundle.proximity_claim.combined_row),
    );
    push(
        "claim_batch.coefficients".to_string(),
        serialized_len(&bundle.claim_batch.coefficients),
    );
    push(
        "claim_batch.blind_claim".to_string(),
        serialized_len(&bundle.claim_batch.blind_claim),
    );
    push(
        "claim_blind_check.combined_row".to_string(),
        serialized_len(&bundle.claim_blind_check.combined_row),
    );
    push(
        "quadratic_batch.quotient".to_string(),
        serialized_len(&bundle.quadratic_batch.quotient),
    );
    push(
        format!("mac_tags ({} gf128 tags)", bundle.mac_tags.len()),
        serialized_len(&bundle.mac_tags),
    );
    push("root".to_string(), serialized_len(&bundle.root));
    push("root_b".to_string(), serialized_len(&bundle.root_b));
    push("params".to_string(), serialized_len(&bundle.params));

    let total = serialized_len(bundle);
    let accounted = sections.iter().map(|section| section.bytes).sum::<usize>();
    let framing = total - accounted;
    sections.sort_by(|left, right| {
        right
            .bytes
            .cmp(&left.bytes)
            .then_with(|| left.label.cmp(&right.label))
    });
    (sections, total, framing)
}

fn mdoc_p4b_entry_labels(entries: usize) -> Vec<String> {
    let families = implemented_circuit_family_labels().unwrap();
    let roles = ["issuer", "device", "revocation"];
    let mut labels = roles
        .iter()
        .flat_map(|role| {
            families
                .iter()
                .map(move |family| format!("{role}/{}", String::from_utf8_lossy(family)))
        })
        .collect::<Vec<_>>();
    labels.push("mac_batch".to_string());
    assert_eq!(
        labels.len(),
        entries,
        "P4b proves the implemented circuit families once per ECDSA role plus one MAC batch",
    );
    labels
}

/// Byte accounting of the P4b coprocessor bundle the mdoc proof embeds, the
/// bundle `verify_mdoc_p4b_circuit_bundle_from_stwo` consumes.
///
/// The hard gate is sum-exactness: every serialized byte lands in a named
/// section or in the printed framing residual.
#[test]
fn mdoc_p4b_bundle_byte_breakdown_accounts_every_serialized_byte() {
    let issuer = signed_input();
    let device = alternate_signed_input();
    let revocation = revocation_signed_input();
    let issuer_witness = generate_witness(&issuer).unwrap();
    let device_witness = generate_witness(&device).unwrap();
    let revocation_witness = generate_witness(&revocation).unwrap();
    let issuer_public = EcdsaPublicProjection::issuer_key_only(issuer.qx, issuer.qy);
    let device_public = EcdsaPublicProjection::message_hash_only(device.z);
    let revocation_public = EcdsaPublicProjection::public_key_only(revocation.qx, revocation.qy);
    let mac_key_shares = test_mac_key_shares();

    let bundle = prove_mdoc_p4b_circuit_bundle(
        &issuer,
        &issuer_public,
        &issuer_witness,
        &device,
        &device_public,
        &device_witness,
        (&revocation, &revocation_public, &revocation_witness),
        &mac_key_shares,
        TEST_SEED,
    )
    .expect("demo P4b bundle proves");

    let labels = mdoc_p4b_entry_labels(bundle.entries.len());
    let (sections, total, framing) = bundle_byte_breakdown(&bundle, &labels);

    let percent = |bytes: usize| 100.0 * bytes as f64 / total as f64;
    println!("P4b coprocessor bundle byte breakdown");
    println!(
        "serialized bundle: {total} B ({:.2} KiB), {} instances, {} ligero openings per group, \
         row_len {} codeword_len {}",
        total as f64 / 1024.0,
        bundle.entries.len(),
        bundle.params.openings,
        bundle.params.row_len,
        bundle.params.codeword_len,
    );
    println!("{:>12}  {:>6}  section", "bytes", "%");
    for section in &sections {
        println!(
            "{:>12}  {:>5.2}%  {}",
            section.bytes,
            percent(section.bytes),
            section.label,
        );
    }
    println!(
        "{:>12}  {:>5.2}%  framing/other (vec length prefixes)",
        framing,
        percent(framing),
    );

    let accounted = sections.iter().map(|section| section.bytes).sum::<usize>();
    assert_eq!(
        accounted + framing,
        total,
        "named sections plus framing must account for every serialized bundle byte",
    );
    assert_eq!(
        total,
        bincode::serialize(&bundle).unwrap().len(),
        "serialized_size must agree with the bytes the proof actually carries",
    );
    // Independent completeness check on the taxonomy: the top-level
    // fields already cover the whole bundle, so no field was left out above.
    let top_level = serialized_len(&bundle.params)
        + serialized_len(&bundle.root)
        + serialized_len(&bundle.root_b)
        + serialized_len(&bundle.proximity_openings)
        + serialized_len(&bundle.proximity_openings_b)
        + serialized_len(&bundle.proximity_batch)
        + serialized_len(&bundle.proximity_batch_b)
        + serialized_len(&bundle.proximity_claim)
        + serialized_len(&bundle.claim_batch)
        + serialized_len(&bundle.claim_blind_check)
        + serialized_len(&bundle.quadratic_batch)
        + serialized_len(&bundle.mac_tags)
        + serialized_len(&bundle.entries);
    assert_eq!(
        top_level, total,
        "every bundle field must be represented in the breakdown",
    );
    // The residual is exactly the two batch presence tags plus the length
    // prefixes of entries and the two absent legacy opening vectors.
    assert_eq!(
        framing, 26,
        "framing residual must stay the two option tags and three Vec length prefixes",
    );
}
