use ecdsa::signature::Signer;
use eu_id_ec_coprocessor::ecdsa::{
    generate_witness, layout_range, verify_witness, EcdsaInput, LayoutSlot, LAYOUT_LEN,
};
use eu_id_ec_coprocessor::Fp;
use p256::ecdsa::{Signature, SigningKey};
use p256::elliptic_curve::point::Double;
use p256::elliptic_curve::sec1::ToEncodedPoint;
use p256::{AffinePoint, ProjectivePoint, Scalar};
use sha2::{Digest as _, Sha256};

const P_BE: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];

const N_BE: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
];

fn scalar(value: u64) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[24..32].copy_from_slice(&value.to_be_bytes());
    bytes
}

fn valid_input() -> EcdsaInput {
    let generator = AffinePoint::GENERATOR.to_encoded_point(false);
    let mut qx = [0u8; 32];
    let mut qy = [0u8; 32];
    qx.copy_from_slice(generator.x().unwrap());
    qy.copy_from_slice(generator.y().unwrap());

    EcdsaInput {
        z: scalar(42),
        r: scalar(77),
        s: scalar(1),
        qx,
        qy,
    }
}

fn signed_input() -> EcdsaInput {
    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).unwrap();
    let message = b"eu-id s4 witness checker";
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

fn fp_from_coord(coord: &[u8]) -> Fp {
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(coord);
    Fp::from_bytes_be(bytes).unwrap()
}

fn affine_coords(point: ProjectivePoint) -> (Fp, Fp) {
    let encoded = point.to_affine().to_encoded_point(false);
    (
        fp_from_coord(encoded.x().unwrap()),
        fp_from_coord(encoded.y().unwrap()),
    )
}

fn double_256(mut point: ProjectivePoint) -> ProjectivePoint {
    for _ in 0..256 {
        point = point.double();
    }
    point
}

#[test]
fn generated_witness_has_frozen_length() {
    let witness = generate_witness(&valid_input()).unwrap();

    assert_eq!(witness.values.len(), LAYOUT_LEN);
}

#[test]
fn input_limbs_use_existing_20_by_13_little_endian_layout() {
    let mut input = valid_input();
    input.z = scalar(42);
    input.r = scalar(1 << 13);
    input.s = scalar((1 << 13) + 7);
    let witness = generate_witness(&input).unwrap();
    let limbs = &witness.values[layout_range(LayoutSlot::InputLimbs)];

    assert_eq!(limbs[0], Fp::from_u64(42));
    assert_eq!(limbs[20], Fp::ZERO);
    assert_eq!(limbs[21], Fp::ONE);
    assert_eq!(limbs[40], Fp::from_u64(7));
    assert_eq!(limbs[41], Fp::ONE);
}

#[test]
fn invalid_scalar_and_coordinate_inputs_are_rejected() {
    let mut input = valid_input();
    input.r = scalar(0);
    assert!(generate_witness(&input).is_err(), "r=0 must reject");

    let mut input = valid_input();
    input.s = scalar(0);
    assert!(generate_witness(&input).is_err(), "s=0 must reject");

    let mut input = valid_input();
    input.z = N_BE;
    assert!(generate_witness(&input).is_err(), "z=n must reject");

    let mut input = valid_input();
    input.r = N_BE;
    assert!(generate_witness(&input).is_err(), "r=n must reject");

    let mut input = valid_input();
    input.s = N_BE;
    assert!(generate_witness(&input).is_err(), "s=n must reject");

    let mut input = valid_input();
    input.qx = P_BE;
    assert!(generate_witness(&input).is_err(), "Qx=p must reject");

    let mut input = valid_input();
    input.qy = P_BE;
    assert!(generate_witness(&input).is_err(), "Qy=p must reject");

    let mut input = valid_input();
    input.qy = scalar(5);
    assert!(generate_witness(&input).is_err(), "off-curve Q must reject");
}

#[test]
fn scalar_setup_hints_fill_frozen_slots_deterministically() {
    let first = generate_witness(&valid_input()).unwrap();
    let second = generate_witness(&valid_input()).unwrap();
    assert_eq!(
        first, second,
        "same input must produce byte-identical witness"
    );

    let sinv = &first.values[layout_range(LayoutSlot::ScalarInverses)];
    let us = &first.values[layout_range(LayoutSlot::UScalars)];
    let qs = &first.values[layout_range(LayoutSlot::ModNQuotients)];
    let bits = &first.values[layout_range(LayoutSlot::ScalarBits)];

    assert_eq!(sinv, &[Fp::ONE]);
    assert_eq!(us, &[Fp::from_u64(42), Fp::from_u64(77)]);
    assert_eq!(qs, &[Fp::ZERO, Fp::ZERO, Fp::ZERO]);

    for slot in 0..256 {
        let bit = 255 - slot;
        let expected = if bit < 64 && (42u64 >> bit) & 1 == 1 {
            Fp::ONE
        } else {
            Fp::ZERO
        };
        assert_eq!(bits[slot], expected, "u1 MSB-first slot {slot}");
    }
    for slot in 0..256 {
        let bit = 255 - slot;
        let expected = if bit < 64 && (77u64 >> bit) & 1 == 1 {
            Fp::ONE
        } else {
            Fp::ZERO
        };
        assert_eq!(bits[256 + slot], expected, "u2 MSB-first slot {slot}");
    }
}

#[test]
fn final_point_slots_match_p256_oracle() {
    let witness = generate_witness(&valid_input()).unwrap();
    let final_point = &witness.values[layout_range(LayoutSlot::FinalPoint)];
    let final_reduction = &witness.values[layout_range(LayoutSlot::FinalReduction)];

    let expected = (ProjectivePoint::GENERATOR * Scalar::from(119u64)).to_affine();
    let encoded = expected.to_encoded_point(false);
    let mut expected_x = [0u8; 32];
    let mut expected_y = [0u8; 32];
    expected_x.copy_from_slice(encoded.x().unwrap());
    expected_y.copy_from_slice(encoded.y().unwrap());

    assert_eq!(final_point[0], Fp::from_bytes_be(expected_x).unwrap());
    assert_eq!(final_point[1], Fp::from_bytes_be(expected_y).unwrap());
    assert_eq!(
        final_reduction[0],
        Fp::ZERO,
        "119G.x is below n in this KAT"
    );
    assert_eq!(final_reduction[1], Fp::from_bytes_be(expected_x).unwrap());
}

#[test]
fn ladder_accumulator_slots_end_at_scalar_mul_outputs() {
    let first = generate_witness(&valid_input()).unwrap();
    let second = generate_witness(&valid_input()).unwrap();
    assert_eq!(first, second, "ladder transcript must be deterministic");

    let expected_u1 = ProjectivePoint::GENERATOR * Scalar::from(42u64);
    let expected_u2 = ProjectivePoint::GENERATOR * Scalar::from(77u64);
    let d = double_256(ProjectivePoint::GENERATOR);
    let expected_u1_raw = d + expected_u1;
    let expected_u2_raw = d + expected_u2;
    let (expected_u1_x, expected_u1_y) = affine_coords(expected_u1);
    let (expected_u2_x, expected_u2_y) = affine_coords(expected_u2);
    let (expected_u1_raw_x, expected_u1_raw_y) = affine_coords(expected_u1_raw);
    let (expected_u2_raw_x, expected_u2_raw_y) = affine_coords(expected_u2_raw);
    let u1_acc = &first.values[layout_range(LayoutSlot::U1GAccumulators)];
    let u2_acc = &first.values[layout_range(LayoutSlot::U2QAccumulators)];
    let corrected = &first.values[layout_range(LayoutSlot::CorrectedEndpoints)];

    assert!(
        u1_acc.iter().any(|value| *value != Fp::ZERO),
        "u1G transcript is populated"
    );
    assert!(
        u2_acc.iter().any(|value| *value != Fp::ZERO),
        "u2Q transcript is populated"
    );
    assert_eq!(u1_acc[510], expected_u1_raw_x);
    assert_eq!(u1_acc[511], expected_u1_raw_y);
    assert_eq!(u2_acc[510], expected_u2_raw_x);
    assert_eq!(u2_acc[511], expected_u2_raw_y);
    assert_ne!(
        (u1_acc[510], u1_acc[511]),
        (expected_u1_x, expected_u1_y),
        "raw accumulator keeps the blinded 2^256*B offset"
    );
    assert_eq!(corrected[0], expected_u1_x, "S1.x corrected endpoint");
    assert_eq!(corrected[1], expected_u1_y, "S1.y corrected endpoint");
    assert_eq!(corrected[2], expected_u2_x, "S2.x corrected endpoint");
    assert_eq!(corrected[3], expected_u2_y, "S2.y corrected endpoint");
}

#[test]
fn witness_populates_slope_inverse_slots() {
    let input = signed_input();
    let witness = generate_witness(&input).unwrap();
    let slopes = &witness.values[layout_range(LayoutSlot::SlopeInverses)];

    assert_eq!(slopes.len(), 1027);
    assert!(
        slopes.iter().all(|value| *value != Fp::ZERO),
        "all C13 slope denominator inverses must be populated"
    );
}

#[test]
fn c13_denominator_slots_follow_q022_double_then_add_order() {
    let witness = generate_witness(&valid_input()).unwrap();
    let denoms = &witness.values[layout_range(LayoutSlot::U1GDenominatorInverses)];
    let base = ProjectivePoint::GENERATOR;
    let doubled = base.double();
    let (base_x, base_y) = affine_coords(base);
    let (doubled_x, _) = affine_coords(doubled);

    assert_eq!(denoms.len(), 513);
    assert_eq!(
        denoms[0],
        (base_y + base_y).inverse().unwrap(),
        "slot 0 is the first doubling denominator inverse"
    );
    assert_eq!(
        denoms[1],
        (base_x - doubled_x).inverse().unwrap(),
        "slot 1 is the first add-branch denominator inverse"
    );
}

#[test]
fn witness_checker_accepts_honest_witness_and_rejects_scalar_mutations() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();
    verify_witness(&input, &witness).unwrap();

    witness.values[layout_range(LayoutSlot::ScalarInverses).start] = Fp::from_u64(2);
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad sinv must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::UScalars).start] = Fp::from_u64(43);
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad u1 must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::ScalarBits).start + 1] = Fp::from_u64(2);
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad scalar bit must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::U1GAccumulators).start] =
        witness.values[layout_range(LayoutSlot::U1GAccumulators).start] + Fp::ONE;
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad u1G accumulator must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::U2QAccumulators).start] =
        witness.values[layout_range(LayoutSlot::U2QAccumulators).start] + Fp::ONE;
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad u2Q accumulator must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start] =
        witness.values[layout_range(LayoutSlot::CorrectedEndpoints).start] + Fp::ONE;
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad corrected endpoint must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::SlopeInverses).start] =
        witness.values[layout_range(LayoutSlot::SlopeInverses).start] + Fp::ONE;
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad slope inverse must reject"
    );
}

#[test]
fn witness_checker_rejects_final_check_and_infinity_mutations() {
    let input = signed_input();
    let mut witness = generate_witness(&input).unwrap();

    witness.values[layout_range(LayoutSlot::FinalPoint).start] = Fp::from_u64(9);
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad R.x must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::FinalReduction).start + 1] = Fp::from_u64(9);
    assert!(
        verify_witness(&input, &witness).is_err(),
        "bad r' must reject"
    );

    let mut witness = generate_witness(&input).unwrap();
    witness.values[layout_range(LayoutSlot::InfinityFlags).start] = Fp::ONE;
    assert!(
        verify_witness(&input, &witness).is_err(),
        "infinity flag must reject"
    );
}

#[test]
fn witness_checker_rejects_signature_r_mismatch() {
    let mut input = signed_input();
    input.r[31] ^= 1;
    let witness = generate_witness(&input).unwrap();

    assert!(
        verify_witness(&input, &witness).is_err(),
        "C14 must bind r' to signature r"
    );
}
