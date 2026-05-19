use stwo_p256_utils::constants::{P256_GX, P256_GY, P256_ORDER};

use crate::curve::{mod_inverse, point_add, point_double, scalar_mul};
use crate::field_ops::mul_mod_witness;
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

    let s_inv = mod_inverse(&input.signature.s, &n);
    let u1 = mul_mod_witness(&input.message_hash, &s_inv, &n)
        .result
        .to_u256();
    let u2 = mul_mod_witness(&input.signature.r, &s_inv, &n)
        .result
        .to_u256();

    let r1 = scalar_mul(&u1, &g);
    let r2 = scalar_mul(&u2, &input.public_key);

    let r_point = if r1 == r2 {
        point_double(&r1).output
    } else {
        point_add(&r1, &r2).output
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

/// Full witness for ECDSA verification, capturing all intermediate values
/// needed for trace generation.
#[derive(Clone, Debug)]
pub struct EcdsaVerifyWitness {
    pub input: EcdsaVerifyInput,
    pub s_inv: U256,
    pub u1: U256,
    pub u2: U256,
    pub r1: AffinePoint, // u1*G
    pub r2: AffinePoint, // u2*Q
    pub r_point: AffinePoint,
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

    let r_point = if r1 == r2 {
        point_double(&r1).output
    } else {
        point_add(&r1, &r2).output
    };

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
}
