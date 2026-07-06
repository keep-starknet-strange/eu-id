use eu_id_ec_coprocessor::mac::{gf128_mul, gf128_tag, xor_128};
use eu_id_ec_coprocessor::CoprocessorChannel;

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
