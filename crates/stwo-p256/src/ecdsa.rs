use crypto_bigint::{NonZero, U256};

use crate::ops::affine_point::AffinePoint;
use crate::ops::consts::ORDER;
use crate::ops::glv::{fake_glv_decompose, FakeGlvDecomposition};
use crate::ops::{add_mod, mod_inverse, mul_mod};
use crate::types::EcdsaVerifyInput;

/// Witness for one fake-GLV certificate: the hinted EC point and the
/// scalar decomposition used to prove it.
#[derive(Clone, Debug)]
pub struct CertWitness {
    /// Hinted point H = [u]P (None if u = 0, representing infinity).
    pub h: Option<AffinePoint>,
    pub decomp: FakeGlvDecomposition,
}

/// Full Phase-1 witness for ECDSA verification.
#[derive(Clone, Debug)]
pub struct EcdsaVerifyWitness {
    pub input: EcdsaVerifyInput,
    /// Reduced digest: z mod n.
    pub z_red: U256,
    /// u1 = z_red * s^{-1} mod n  (scalar for G).
    pub u1: U256,
    /// u2 = r * s^{-1} mod n  (scalar for public key).
    pub u2: U256,
    /// Certificate for cert 0: base point G, scalar u1.
    pub cert1: CertWitness,
    /// Certificate for cert 1: base point Pub, scalar u2.
    pub cert2: CertWitness,
    /// Final EC point R = H1 + H2 (None means infinity — invalid signature).
    pub r_point: Option<AffinePoint>,
}

/// Verify an ECDSA P-256 signature natively.
pub fn ecdsa_verify(input: &EcdsaVerifyInput) -> bool {
    let n = NonZero::new(ORDER).unwrap();

    // r, s must be in [1, n-1]
    if bool::from(input.signature.r.is_zero()) || input.signature.r >= ORDER {
        return false;
    }
    if bool::from(input.signature.s.is_zero()) || input.signature.s >= ORDER {
        return false;
    }

    let s_inv = mod_inverse(&input.signature.s, &n);
    let z_red = digest_reduce(&input.message_hash);
    let u1 = mul_mod(&z_red, &s_inv, &n);
    let u2 = mul_mod(&input.signature.r, &s_inv, &n);

    let h1 = ec_mul_opt(&AffinePoint::generator(), &u1);
    let h2 = ec_mul_opt(&input.public_key, &u2);

    match ec_add_opt(h1, h2) {
        None => false,
        Some(r) => x_mod_n(&r.x) == input.signature.r,
    }
}

/// Compute the full Phase-1 ECDSA witness.
pub fn ecdsa_verify_witness(input: &EcdsaVerifyInput) -> EcdsaVerifyWitness {
    let n = NonZero::new(ORDER).unwrap();

    let s_inv = mod_inverse(&input.signature.s, &n);
    let z_red = digest_reduce(&input.message_hash);
    let u1 = mul_mod(&z_red, &s_inv, &n);
    let u2 = mul_mod(&input.signature.r, &s_inv, &n);

    let h1 = ec_mul_opt(&AffinePoint::generator(), &u1);
    let h2 = ec_mul_opt(&input.public_key, &u2);

    let cert1 = CertWitness {
        h: h1.clone(),
        decomp: fake_glv_decompose(&u1.max(U256::ONE), &n),
    };
    let cert2 = CertWitness {
        h: h2.clone(),
        decomp: fake_glv_decompose(&u2, &n),
    };

    let r_point = ec_add_opt(h1, h2);

    EcdsaVerifyWitness { input: input.clone(), z_red, u1, u2, cert1, cert2, r_point }
}

/// Reduce a 256-bit digest modulo n.
/// Since n > 2^255, z mod n requires at most one subtraction.
fn digest_reduce(z: &U256) -> U256 {
    if *z >= ORDER { z.wrapping_sub(&ORDER) } else { *z }
}

/// Reduce a field x-coordinate modulo n.
/// Since p < 2n for P-256, at most one subtraction is needed.
fn x_mod_n(x: &U256) -> U256 {
    if *x >= ORDER { x.wrapping_sub(&ORDER) } else { *x }
}

/// Scalar multiply P by k, returning None if k = 0 (point at infinity).
fn ec_mul_opt(p: &AffinePoint, k: &U256) -> Option<AffinePoint> {
    if bool::from(k.is_zero()) { None } else { Some(p.scalar_mul(k)) }
}

/// Add two optional EC points (None = point at infinity).
/// Returns None if the result is the point at infinity (H + (-H)).
fn ec_add_opt(a: Option<AffinePoint>, b: Option<AffinePoint>) -> Option<AffinePoint> {
    match (a, b) {
        (None, r) | (r, None) => r,
        (Some(p), Some(q)) => {
            if p == q {
                Some(p.double())
            } else if p.x == q.x {
                // p = -q, result is infinity
                None
            } else {
                Some(p.add(&q))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::consts::ORDER;
    use crate::ops::{add_mod, mod_inverse, mul_mod};
    use crate::types::Signature;

    /// Build a self-consistent (z, r, s, Q) from a private key d, nonce k, hash z.
    fn make_signature(d: u32, k: u32, z: u32) -> EcdsaVerifyInput {
        let n = NonZero::new(ORDER).unwrap();
        let d = U256::from(d);
        let k = U256::from(k);
        let z = U256::from(z);

        let g = AffinePoint::generator();
        let q = g.scalar_mul(&d);
        let r_point = g.scalar_mul(&k);
        let r = x_mod_n(&r_point.x);

        let k_inv = mod_inverse(&k, &n);
        let s = mul_mod(&k_inv, &add_mod(&z, &mul_mod(&r, &d, &n), &n), &n);

        EcdsaVerifyInput { message_hash: z, signature: Signature { r, s }, public_key: q }
    }

    #[test]
    fn test_verify_valid_signature() {
        let input = make_signature(2, 3, 42);
        assert!(ecdsa_verify(&input));
    }

    #[test]
    fn test_verify_wrong_hash() {
        let mut input = make_signature(2, 3, 42);
        input.message_hash = U256::from(43u32);
        assert!(!ecdsa_verify(&input));
    }

    #[test]
    fn test_verify_wrong_r() {
        let mut input = make_signature(2, 3, 42);
        input.signature.r = input.signature.r.wrapping_add(&U256::ONE);
        assert!(!ecdsa_verify(&input));
    }

    #[test]
    fn test_verify_s_zero_rejected() {
        let mut input = make_signature(2, 3, 42);
        input.signature.s = U256::ZERO;
        assert!(!ecdsa_verify(&input));
    }

    #[test]
    fn test_verify_r_zero_rejected() {
        let mut input = make_signature(2, 3, 42);
        input.signature.r = U256::ZERO;
        assert!(!ecdsa_verify(&input));
    }

    #[test]
    fn test_witness_r_point_matches_verify() {
        let input = make_signature(5, 7, 99);
        let w = ecdsa_verify_witness(&input);
        assert!(w.r_point.is_some());
        assert_eq!(x_mod_n(&w.r_point.unwrap().x), input.signature.r);
    }

    #[test]
    fn test_witness_glv_decomp_valid() {
        let input = make_signature(2, 3, 42);
        let w = ecdsa_verify_witness(&input);
        let n = NonZero::new(ORDER).unwrap();

        for (u, cert) in [(&w.u1, &w.cert1), (&w.u2, &w.cert2)] {
            let d = &cert.decomp;
            let s2_signed = if d.s2_sign_bit {
                ORDER.wrapping_sub(&d.s2_abs)
            } else {
                d.s2_abs
            };
            let check = add_mod(&d.s1, &mul_mod(u, &s2_signed, &n), &n);
            assert!(bool::from(check.is_zero()));
        }
    }
}
