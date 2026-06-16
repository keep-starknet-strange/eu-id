use crate::constants::{P256_B, P256_GX, P256_GY, P256_MODULUS, P256_ORDER};

use crate::curve::{mod_inverse, point_add, point_double, scalar_mul};
use crate::field_ops::{add_mod_witness, mul_mod_witness, sub_mod_witness};
use crate::types::{AffinePoint, EcdsaVerifyInput, U256};

/// Verify an ECDSA P-256 signature natively (outside the circuit).
///
/// Algorithm:
/// 1. Check r, s are in [1, n-1]
/// 2. s_inv = s^(-1) mod n
/// 3. u1 = message_hash * s_inv mod n
/// 4. u2 = r * s_inv mod n
/// 5. R = u1*G + u2*Q
/// 6. Check R.x == r mod n
pub fn ecdsa_verify(input: &EcdsaVerifyInput) -> bool {
    let n = U256::from_le_u64s(&P256_ORDER);
    let g = AffinePoint {
        x: U256::from_le_u64s(&P256_GX),
        y: U256::from_le_u64s(&P256_GY),
    };

    if !is_scalar_nonzero_and_below_order(&input.signature.r)
        || !is_scalar_nonzero_and_below_order(&input.signature.s)
        || !is_point_on_curve(&input.public_key)
    {
        return false;
    }

    let s_inv = mod_inverse(&input.signature.s, &n);
    let u1 = mul_mod_witness(&input.message_hash, &s_inv, &n)
        .result
        .to_u256();
    let u2 = mul_mod_witness(&input.signature.r, &s_inv, &n)
        .result
        .to_u256();

    let r1 = scalar_mul(&u1, &g);
    let r2 = scalar_mul(&u2, &input.public_key);

    let Some(r_point) = add_optional_points(r1, r2) else {
        return false;
    };

    // Check R.x mod n == r
    // For P-256, x < p < 2*n, so x mod n is either x or x - n.
    let r_x_le = r_point.x.to_le_u64s();
    let r_le = input.signature.r.to_le_u64s();

    r_x_le == r_le || {
        let n_le = P256_ORDER;
        let mut diff = [0u64; 4];
        let mut borrow = 0u64;
        for i in 0..4 {
            let (s1, c1) = r_x_le[i].overflowing_sub(n_le[i]);
            let (s2, c2) = s1.overflowing_sub(borrow);
            diff[i] = s2;
            borrow = (c1 as u64) + (c2 as u64);
        }
        diff == r_le
    }
}

fn is_scalar_nonzero_and_below_order(value: &U256) -> bool {
    *value != U256::ZERO && cmp_u256(value, &U256::from_le_u64s(&P256_ORDER)).is_lt()
}

fn is_field_element(value: &U256) -> bool {
    cmp_u256(value, &U256::from_le_u64s(&P256_MODULUS)).is_lt()
}

fn is_point_on_curve(point: &AffinePoint) -> bool {
    if !is_field_element(&point.x) || !is_field_element(&point.y) {
        return false;
    }

    let p = U256::from_le_u64s(&P256_MODULUS);
    let y2 = mul_mod_witness(&point.y, &point.y, &p).result.to_u256();
    let x2 = mul_mod_witness(&point.x, &point.x, &p).result.to_u256();
    let x3 = mul_mod_witness(&x2, &point.x, &p).result.to_u256();
    let three = U256::from_le_u64s(&[3, 0, 0, 0]);
    let three_x = mul_mod_witness(&three, &point.x, &p).result.to_u256();
    let x3_minus_3x = sub_mod_witness(&x3, &three_x, &p).result.to_u256();
    let rhs = add_mod_witness(&x3_minus_3x, &U256::from_le_u64s(&P256_B), &p)
        .result
        .to_u256();

    y2 == rhs
}

fn add_optional_points(lhs: Option<AffinePoint>, rhs: Option<AffinePoint>) -> Option<AffinePoint> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(point), None) | (None, Some(point)) => Some(point),
        (Some(lhs), Some(rhs)) if lhs == rhs => Some(point_double(&lhs).output),
        (Some(lhs), Some(rhs)) if is_additive_inverse(&lhs, &rhs) => None,
        (Some(lhs), Some(rhs)) => Some(point_add(&lhs, &rhs).output),
    }
}

fn is_additive_inverse(lhs: &AffinePoint, rhs: &AffinePoint) -> bool {
    lhs.x == rhs.x
        && add_mod_witness(&lhs.y, &rhs.y, &U256::from_le_u64s(&P256_MODULUS))
            .result
            .to_u256()
            == U256::ZERO
}

fn cmp_u256(lhs: &U256, rhs: &U256) -> core::cmp::Ordering {
    let lhs = lhs.to_le_u64s();
    let rhs = rhs.to_le_u64s();
    for i in (0..4).rev() {
        match lhs[i].cmp(&rhs[i]) {
            core::cmp::Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    core::cmp::Ordering::Equal
}

/// Full witness for ECDSA verification, capturing all intermediate values
/// needed for trace generation.
#[derive(Clone, Debug)]
pub struct EcdsaVerifyWitness {
    pub input: EcdsaVerifyInput,
    pub s_inv: U256,
    pub u1: U256,
    pub u2: U256,
    pub r1: Option<AffinePoint>, // u1*G, or infinity for u1 = 0
    pub r2: Option<AffinePoint>, // u2*Q, or infinity for u2 = 0
    pub r_point: Option<AffinePoint>,
    pub valid: bool,
}

/// Compute the full ECDSA verification witness.
pub fn ecdsa_verify_witness(input: &EcdsaVerifyInput) -> EcdsaVerifyWitness {
    let n = U256::from_le_u64s(&P256_ORDER);
    let g = AffinePoint {
        x: U256::from_le_u64s(&P256_GX),
        y: U256::from_le_u64s(&P256_GY),
    };

    let s_inv = mod_inverse(&input.signature.s, &n);
    let u1 = mul_mod_witness(&input.message_hash, &s_inv, &n)
        .result
        .to_u256();
    let u2 = mul_mod_witness(&input.signature.r, &s_inv, &n)
        .result
        .to_u256();

    let r1 = scalar_mul(&u1, &g);
    let r2 = scalar_mul(&u2, &input.public_key);

    let r_point = add_optional_points(r1.clone(), r2.clone());

    let valid = ecdsa_verify(input);

    EcdsaVerifyWitness {
        input: input.clone(),
        s_inv,
        u1,
        u2,
        r1,
        r2,
        r_point,
        valid,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Signature;

    #[test]
    fn test_ecdsa_verify_with_p256_crate() {
        use ecdsa::signature::Signer;
        use p256::ecdsa::{SigningKey, VerifyingKey};
        use rand::rngs::OsRng;

        let signing_key = SigningKey::random(&mut OsRng);
        let verifying_key = VerifyingKey::from(&signing_key);

        let message = b"test message for ECDSA P-256 verification";
        let signature: p256::ecdsa::Signature = signing_key.sign(message);

        // Extract r, s from the signature
        let sig_bytes = signature.to_bytes();
        let mut r_bytes = [0u8; 32];
        let mut s_bytes = [0u8; 32];
        r_bytes.copy_from_slice(&sig_bytes[..32]);
        s_bytes.copy_from_slice(&sig_bytes[32..]);

        let r = U256(r_bytes);
        let s = U256(s_bytes);

        // Extract public key coordinates
        let pk_point = verifying_key.to_encoded_point(false);
        let mut pk_x = [0u8; 32];
        let mut pk_y = [0u8; 32];
        pk_x.copy_from_slice(pk_point.x().unwrap());
        pk_y.copy_from_slice(pk_point.y().unwrap());

        let public_key = AffinePoint {
            x: U256(pk_x),
            y: U256(pk_y),
        };

        // Compute message hash (SHA-256 is used by the p256 crate)
        use p256::ecdsa::signature::digest::Digest;
        let hash = <sha2::Sha256 as Digest>::digest(message);
        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash);
        let message_hash = U256(hash_bytes);

        let input = EcdsaVerifyInput {
            message_hash,
            signature: Signature { r, s },
            public_key,
        };

        let result = ecdsa_verify(&input);
        assert!(
            result,
            "ECDSA verification must succeed for a valid signature"
        );
    }

    #[test]
    fn ecdsa_verify_rejects_zero_r_without_panicking() {
        let input = EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: U256::ZERO,
                s: scalar(11),
            },
            public_key: generator_point(),
        };

        assert!(!ecdsa_verify(&input));
    }

    #[test]
    fn ecdsa_verify_rejects_zero_s_without_panicking() {
        let input = EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(77),
                s: U256::ZERO,
            },
            public_key: generator_point(),
        };

        assert!(!ecdsa_verify(&input));
    }

    #[test]
    fn ecdsa_verify_rejects_public_key_off_curve() {
        let mut public_key = generator_point();
        public_key.y = scalar(1);
        let input = EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(77),
                s: scalar(11),
            },
            public_key,
        };

        assert!(!ecdsa_verify(&input));
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn generator_point() -> AffinePoint {
        AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        }
    }
}
