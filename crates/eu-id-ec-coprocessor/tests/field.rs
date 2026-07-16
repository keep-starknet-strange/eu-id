use eu_id_ec_coprocessor::Fp;
use p256::elliptic_curve::ff::PrimeField;
use p256::{FieldBytes, FieldElement};

const P_BE: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];

fn dec_be(mut value: [u8; 32]) -> [u8; 32] {
    for byte in value.iter_mut().rev() {
        let (next, borrow) = byte.overflowing_sub(1);
        *byte = next;
        if !borrow {
            break;
        }
    }
    value
}

fn inc_be(mut value: [u8; 32]) -> [u8; 32] {
    for byte in value.iter_mut().rev() {
        let (next, carry) = byte.overflowing_add(1);
        *byte = next;
        if !carry {
            break;
        }
    }
    value
}

#[test]
fn canonical_decoding_accepts_exactly_values_below_p() {
    let p_minus_one = dec_be(P_BE);
    assert_eq!(
        Fp::from_bytes_be(p_minus_one).unwrap().to_bytes_be(),
        p_minus_one
    );
    assert!(Fp::from_bytes_be(P_BE).is_none(), "p is non-canonical");
    assert!(
        Fp::from_bytes_be(inc_be(P_BE)).is_none(),
        "p + 1 is non-canonical"
    );
    assert!(
        Fp::from_bytes_be([0xff; 32]).is_none(),
        "2^256 - 1 is non-canonical"
    );
}

#[test]
fn arithmetic_obeys_basic_field_laws() {
    let a = Fp::from_u64(17);
    let b = Fp::from_u64(91);
    let c = Fp::from_u64(65537);

    assert_eq!(a + Fp::ZERO, a);
    assert_eq!(a - a, Fp::ZERO);
    assert_eq!(a * Fp::ONE, a);
    assert_eq!(a.square(), a * a);
    assert_eq!((a + b) + c, a + (b + c));
    assert_eq!((a * b) * c, a * (b * c));
    assert_eq!(a * (b + c), (a * b) + (a * c));
}

#[test]
fn inverse_and_batch_inverse_match_single_inverse() {
    let values = [Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(7), Fp::ZERO];
    let inverses = Fp::batch_inverse(&values);

    assert_eq!(inverses.len(), values.len());
    assert_eq!(values[0] * inverses[0], Fp::ONE);
    assert_eq!(values[1] * inverses[1], Fp::ONE);
    assert_eq!(values[2] * inverses[2], Fp::ONE);
    assert_eq!(inverses[3], Fp::ZERO);
    assert_eq!(inverses[0], values[0].inverse().unwrap());
}

#[test]
fn challenge_reduction_is_deterministic_and_canonical() {
    let bytes = [0xff; 32];
    let reduced = Fp::random(bytes);

    assert_eq!(reduced, Fp::random(bytes));
    assert!(Fp::from_bytes_be(reduced.to_bytes_be()).is_some());
}

#[test]
fn arithmetic_matches_p256_field_oracle() {
    let samples = [
        [0u8; 32],
        scalar_bytes(1),
        scalar_bytes(2),
        scalar_bytes(17),
        scalar_bytes(65537),
        dec_be(P_BE),
    ];

    for lhs in samples {
        for rhs in samples {
            let a = Fp::from_bytes_be(lhs).unwrap();
            let b = Fp::from_bytes_be(rhs).unwrap();
            let oracle_a = oracle(lhs);
            let oracle_b = oracle(rhs);

            assert_eq!((a + b).to_bytes_be(), oracle_bytes(oracle_a + oracle_b));
            assert_eq!((a - b).to_bytes_be(), oracle_bytes(oracle_a - oracle_b));
            assert_eq!((a * b).to_bytes_be(), oracle_bytes(oracle_a * oracle_b));
        }
    }

    let a = Fp::from_u64(65537);
    let oracle_a = FieldElement::from(65537u64);
    assert_eq!(a.square().to_bytes_be(), oracle_bytes(oracle_a.square()));
    assert_eq!(
        a.inverse().unwrap().to_bytes_be(),
        oracle_bytes(oracle_a.invert().unwrap())
    );
}

fn scalar_bytes(value: u64) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[24..].copy_from_slice(&value.to_be_bytes());
    bytes
}

fn oracle(bytes: [u8; 32]) -> FieldElement {
    FieldElement::from_repr(FieldBytes::from(bytes)).unwrap()
}

fn oracle_bytes(value: FieldElement) -> [u8; 32] {
    value.to_repr().into()
}
