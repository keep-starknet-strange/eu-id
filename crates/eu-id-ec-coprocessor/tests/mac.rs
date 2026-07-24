use eu_id_ec_coprocessor::ecdsa::{
    build_mac_half_circuit, gf128_halves_from_be32, mac_half_input_with_av, recompose_gf128_halves,
    MAC_HALF_COMMITTED_PRIVATE_INPUTS, MAC_HALF_INPUT_LOG_SIZE, MAC_HALF_PARITY_Q_BITS,
    MAC_HALF_Q_BITS_START, MAC_HALF_X_BITS_START, MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS,
};
use eu_id_ec_coprocessor::mac::{bytes_to_bits, gf128_mul, gf128_tag, xor_128, Gf128};
use eu_id_ec_coprocessor::{CoprocessorChannel, Fp};

const TEST_SEED: [u8; 32] = [7u8; 32];

fn basis(bit: usize) -> [u8; 16] {
    let mut out = [0u8; 16];
    out[bit / 8] = 1 << (bit % 8);
    out
}

#[test]
fn gf128_mul_uses_longfellow_reduction_polynomial() {
    let product = gf128_mul(&basis(127), &basis(1));

    let mut expected = [0u8; 16];
    expected[0] = 0b1000_0111;
    assert_eq!(product, expected, "x^128 must reduce to x^7 + x^2 + x + 1");
}

#[test]
fn gf128_mul_identity_and_xor_distribution_hold() {
    let one = basis(0);
    let left = [
        0x51, 0x9e, 0x3c, 0x04, 0xa7, 0x02, 0x99, 0x10, 0x47, 0xee, 0x08, 0xd1, 0x2a, 0x6b, 0x77,
        0xc4,
    ];
    let right = [
        0xa4, 0x1d, 0x89, 0xf0, 0x22, 0xb7, 0x6c, 0x33, 0x18, 0x50, 0xde, 0x91, 0x6f, 0x09, 0xc2,
        0x7b,
    ];
    let third = [
        0x0f, 0xc0, 0x55, 0x12, 0x89, 0x4e, 0xa1, 0x03, 0x73, 0x2d, 0x44, 0xb8, 0x5a, 0xe6, 0x19,
        0x20,
    ];

    assert_eq!(gf128_mul(&left, &one), left);
    assert_eq!(
        gf128_mul(&xor_128(&left, &right), &third),
        xor_128(&gf128_mul(&left, &third), &gf128_mul(&right, &third)),
        "GF(2^128) multiplication must distribute over XOR"
    );
}

#[test]
fn gf128_tag_uses_ap_xor_av_key_share() {
    let ap = [
        0x11, 0x52, 0x9a, 0x4b, 0x2d, 0xf0, 0x01, 0x33, 0xbe, 0x82, 0x9f, 0x74, 0x08, 0x64, 0xd2,
        0x9c,
    ];
    let av = [
        0x7e, 0x01, 0x44, 0xa9, 0xc3, 0x6b, 0x0f, 0x22, 0x41, 0x10, 0x88, 0xfa, 0x33, 0x5d, 0x19,
        0x07,
    ];
    let x = [
        0xd0, 0x4c, 0x21, 0x81, 0xaf, 0x7d, 0x5e, 0x99, 0x03, 0x26, 0xba, 0x40, 0x67, 0x91, 0xe8,
        0x2f,
    ];

    assert_eq!(gf128_tag(&ap, &av, &x), gf128_mul(&xor_128(&ap, &av), &x));
}

#[test]
fn gf128_tag_documents_no_b_zero_x_edge() {
    let ap = sample_ap();
    let av = sample_av();
    let x = [0u8; 16];

    assert_eq!(
        gf128_tag(&ap, &av, &x),
        [0u8; 16],
        "the shipped no-+b Longfellow parity MAC maps x=0 to a zero tag"
    );
}

#[test]
fn coprocessor_channel_draws_labelled_gf128_deterministically() {
    let mut left = CoprocessorChannel::from_seed(TEST_SEED, b"mac-test");
    let mut right = CoprocessorChannel::from_seed(TEST_SEED, b"mac-test");
    let first = left.draw_gf128(b"eu-id-p4b-mac-av");

    assert_eq!(first, right.draw_gf128(b"eu-id-p4b-mac-av"));
    assert_ne!(
        first,
        right.draw_gf128(b"eu-id-p4b-mac-other"),
        "domain label must affect the drawn GF(2^128) value"
    );
    assert_ne!(
        first,
        left.draw_gf128(b"eu-id-p4b-mac-av"),
        "drawing must advance the channel counter"
    );
}

#[test]
fn gf128_halves_recompose_big_endian_p256_values() {
    let mut value = [0u8; 32];
    for (index, byte) in value.iter_mut().enumerate() {
        *byte = (index as u8).wrapping_mul(7).wrapping_add(3);
    }

    let [lo, hi] = gf128_halves_from_be32(value);

    assert_eq!(
        lo[0], value[31],
        "low half is byte-little-endian for the least significant 128 bits"
    );
    assert_eq!(
        hi[0], value[15],
        "high half is byte-little-endian for the most significant 128 bits"
    );
    assert_eq!(
        recompose_gf128_halves(&lo, &hi),
        Fp::from_bytes_be(value).expect("sample is below the P-256 field modulus")
    );
}

#[test]
fn mac_half_circuit_accepts_reference_tag_and_recomposition() {
    let ap = sample_ap();
    let av = sample_av();
    let x = sample_x();
    let tag = gf128_tag(&ap, &av, &x);
    let circuit = build_mac_half_circuit(&av, &tag).expect("MAC circuit builds");
    let input = mac_half_input_with_av(&ap, &av, &x).expect("MAC input builds");
    assert_eq!(
        MAC_HALF_COMMITTED_PRIVATE_INPUTS, 1408,
        "each half commits x bits, a_p bits, and post-a_v Q quotient bits"
    );
    assert_eq!(
        MDOC_P4B_MAC_COMMITTED_PRIVATE_INPUTS, 9_987,
        "MAC inputs include exact-byte canonicality witnesses for the three 256-bit values"
    );
    assert_eq!(
        input.len(),
        1usize << MAC_HALF_INPUT_LOG_SIZE,
        "the BL2 input table carries compact Group A and Group B without product or S-ladder slots"
    );
    let witness = circuit
        .evaluate_input(input)
        .expect("MAC witness evaluates");

    assert!(
        circuit.is_satisfied(&witness).expect("MAC witness shape"),
        "honest MAC witness must satisfy the circuit"
    );
}

#[test]
fn mac_half_q024_reduction_bound_fits_q_bits() {
    assert_eq!(
        MAC_HALF_PARITY_Q_BITS, 9,
        "Q024 quotient bits cover W_k + V_k <= 632"
    );
}

#[test]
fn av_linear_fold_matches_gf128_mul() {
    let av = sample_av();
    let x = sample_x();
    let av_times_x = gf128_mul(&av, &x);
    let av_bits = bytes_to_bits(&av);
    let x_bits = bytes_to_bits(&x);
    let product_bits = bytes_to_bits(&av_times_x);

    for bit in 0..128 {
        let mut folded = false;
        for basis_bit in 0..128 {
            if !x_bits[basis_bit] {
                continue;
            }
            let basis_product = gf128_mul(&av, &basis(basis_bit));
            folded ^= bytes_to_bits(&basis_product)[bit];
        }
        assert_eq!(
            folded, product_bits[bit],
            "public a_v fold must match gf128_mul bit {bit}; av_lsb={}",
            av_bits[0]
        );
    }
}

#[test]
fn mac_half_circuit_pins_zero_x_edge_behavior() {
    let ap = sample_ap();
    let av = sample_av();
    let x = [0u8; 16];
    let zero_tag = [0u8; 16];
    let circuit = build_mac_half_circuit(&av, &zero_tag).expect("MAC circuit builds");
    let input = mac_half_input_with_av(&ap, &av, &x).expect("MAC input builds");
    let witness = circuit
        .evaluate_input(input.clone())
        .expect("MAC witness evaluates");

    assert!(
        circuit.is_satisfied(&witness).expect("MAC witness shape"),
        "x=0 is accepted with the documented zero tag in the no-+b construction"
    );

    let nonzero_tag = basis(0);
    let rejecting_circuit = build_mac_half_circuit(&av, &nonzero_tag).expect("MAC circuit builds");
    let rejecting_witness = rejecting_circuit
        .evaluate_input(input)
        .expect("MAC witness evaluates");
    assert!(
        !rejecting_circuit
            .is_satisfied(&rejecting_witness)
            .expect("MAC witness shape"),
        "x=0 must reject any non-zero public tag"
    );
}

#[test]
fn mac_half_circuit_rejects_non_boolean_x_bit() {
    let ap = sample_ap();
    let av = sample_av();
    let x = sample_x();
    let tag = gf128_tag(&ap, &av, &x);
    let circuit = build_mac_half_circuit(&av, &tag).expect("MAC circuit builds");
    let mut input = mac_half_input_with_av(&ap, &av, &x).expect("MAC input builds");
    input[MAC_HALF_X_BITS_START] = Fp::from_u64(2);
    let witness = circuit
        .evaluate_input(input)
        .expect("MAC witness evaluates");

    assert!(
        !circuit.is_satisfied(&witness).expect("MAC witness shape"),
        "committed x inputs must be boolean"
    );
}

#[test]
fn mac_half_circuit_rejects_q_quotient_tamper() {
    let ap = sample_ap();
    let av = sample_av();
    let x = sample_x();
    let tag = gf128_tag(&ap, &av, &x);
    let circuit = build_mac_half_circuit(&av, &tag).expect("MAC circuit builds");
    let mut input = mac_half_input_with_av(&ap, &av, &x).expect("MAC input builds");
    input[MAC_HALF_Q_BITS_START] = Fp::ONE - input[MAC_HALF_Q_BITS_START];
    let witness = circuit
        .evaluate_input(input)
        .expect("MAC witness evaluates");

    assert!(
        !circuit.is_satisfied(&witness).expect("MAC witness shape"),
        "committed Q quotient bits must pin W_k + V_k to the public tag"
    );
}

#[test]
fn mac_half_circuit_rejects_internal_wire_tamper() {
    let ap = sample_ap();
    let av = sample_av();
    let x = sample_x();
    let tag = gf128_tag(&ap, &av, &x);
    let circuit = build_mac_half_circuit(&av, &tag).expect("MAC circuit builds");
    let input = mac_half_input_with_av(&ap, &av, &x).expect("MAC input builds");
    let mut witness = circuit
        .evaluate_input(input)
        .expect("MAC witness evaluates");
    witness[1][0] = witness[1][0] + Fp::ONE;

    assert!(
        circuit.is_satisfied(&witness).is_err(),
        "forged internal product/accumulator wires must be rejected by layer recurrence"
    );
}

fn sample_ap() -> Gf128 {
    [
        0x11, 0x52, 0x9a, 0x4b, 0x2d, 0xf0, 0x01, 0x33, 0xbe, 0x82, 0x9f, 0x74, 0x08, 0x64, 0xd2,
        0x9c,
    ]
}

fn sample_av() -> Gf128 {
    [
        0x7e, 0x01, 0x44, 0xa9, 0xc3, 0x6b, 0x0f, 0x22, 0x41, 0x10, 0x88, 0xfa, 0x33, 0x5d, 0x19,
        0x07,
    ]
}

fn sample_x() -> Gf128 {
    [
        0xd0, 0x4c, 0x21, 0x81, 0xaf, 0x7d, 0x5e, 0x99, 0x03, 0x26, 0xba, 0x40, 0x67, 0x91, 0xe8,
        0x2f,
    ]
}
