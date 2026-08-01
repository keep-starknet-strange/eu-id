//! Rounding helpers: `Decompose` (FIPS 204 Algorithm 36), `UseHint`
//! (Algorithm 39), and `w1Encode` (Algorithm 28). Verification recovers `w1`
//! from the approximate commitment through `UseHint`. The witness generator
//! also uses `Decompose` and `HighBits`.
//!
//! All arithmetic is over the centered residue system used by FIPS 204:
//! `r mod± α ∈ (−α/2, α/2]`.

#[cfg(test)]
use crate::constants::GAMMA2;
use crate::constants::{N, Q};
use crate::profile::{MlDsaProfile, ML_DSA_65};

/// `α = 2·γ2`, the decomposition modulus.
#[cfg(test)]
const ALPHA: u32 = 2 * GAMMA2;

/// Default number of possible `w1` values for ML-DSA-65, so `r1`
/// ranges over `[0, 15]`.
#[cfg(test)]
const M: u32 = (Q - 1) / ALPHA;

/// `r mod⁺ m`: the representative in `[0, m)`.
#[inline]
fn mod_plus(r: i64, m: i64) -> i64 {
    r.rem_euclid(m)
}

/// `r mod± α`: the centered representative in `(−α/2, α/2]` (FIPS 204 §2.4).
#[inline]
fn mod_pm(r: u32, alpha: u32) -> i32 {
    let a = alpha as i64;
    let mut v = mod_plus(r as i64, a);
    if v > a / 2 {
        v -= a;
    }
    v as i32
}

/// FIPS 204 Algorithm 36 `Decompose(r)` → `(r1, r0)` with
/// `r = r1·α + r0 (mod q)`, `r0 ∈ (−α/2, α/2]` except for the special
/// `(r1,r0)=(0,−α/2)` wrap point, and `r1 ∈ [0, (q−1)/α)`.
pub fn decompose(r: u32) -> (i32, i32) {
    decompose_for(ML_DSA_65, r)
}

pub fn decompose_for(profile: MlDsaProfile, r: u32) -> (i32, i32) {
    let alpha = 2 * profile.gamma2();
    let r = r % Q;
    let r0 = mod_pm(r, alpha);
    let r_minus_r0 = r as i64 - r0 as i64;
    if r_minus_r0 == (Q - 1) as i64 {
        // r1 would be (q-1)/α; wrap to 0 and pull r0 down by 1.
        (0, r0 - 1)
    } else {
        let r1 = r_minus_r0 / alpha as i64;
        (r1 as i32, r0)
    }
}

/// `HighBits(r) = r1` (FIPS 204 Algorithm 37).
pub fn high_bits(r: u32) -> i32 {
    high_bits_for(ML_DSA_65, r)
}

pub fn high_bits_for(profile: MlDsaProfile, r: u32) -> i32 {
    decompose_for(profile, r).0
}

/// FIPS 204 Algorithm 39 `UseHint(h, r)`: recover the high bits of the true
/// commitment given the one-bit hint `h ∈ {0, 1}`.
pub fn use_hint(hint: u8, r: u32) -> i32 {
    use_hint_for(ML_DSA_65, hint, r)
}

pub fn use_hint_for(profile: MlDsaProfile, hint: u8, r: u32) -> i32 {
    let (r1, r0) = decompose_for(profile, r);
    let m = profile.w1_values() as i32;
    if hint == 0 {
        return r1;
    }
    if r0 > 0 {
        (r1 + 1).rem_euclid(m)
    } else {
        (r1 - 1).rem_euclid(m)
    }
}

/// Apply `UseHint` coefficient-wise across a `w'approx` polynomial with its
/// per-coefficient hint bits, yielding `w1'` (values in `[0, M)`).
pub fn use_hint_poly(hint: &[u8; N], w_approx: &[u32; N]) -> [u32; N] {
    use_hint_poly_for(ML_DSA_65, hint, w_approx)
}

pub fn use_hint_poly_for(profile: MlDsaProfile, hint: &[u8; N], w_approx: &[u32; N]) -> [u32; N] {
    let mut w1 = [0u32; N];
    for i in 0..N {
        w1[i] = use_hint_for(profile, hint[i], w_approx[i]) as u32;
    }
    w1
}

/// FIPS 204 Algorithm 28 `w1Encode`: pack a `w1` vector (`k` polynomials, each
/// coefficient in `[0, M)`, `M = 16 ⇒ 4 bits`) into a byte string, the
/// `SHAKE-256` input for the `c̃` recomputation.
pub fn w1_encode(w1: &[[u32; N]]) -> Vec<u8> {
    w1_encode_for(ML_DSA_65, w1)
}

/// FIPS 204 `w1Encode` for a verifier-selected parameter set.
pub fn w1_encode_for(profile: MlDsaProfile, w1: &[[u32; N]]) -> Vec<u8> {
    assert!(w1.len() >= profile.k(), "missing w1 polynomials");
    let mut out = Vec::with_capacity(profile.w1_encoded_bytes());
    let mut accumulator = 0u32;
    let mut bits = 0usize;
    for poly in &w1[..profile.k()] {
        for &coefficient in poly {
            assert!(
                coefficient < profile.w1_values(),
                "w1 coefficient is outside the selected profile"
            );
            accumulator |= coefficient << bits;
            bits += profile.w1_bits();
            while bits >= 8 {
                out.push(accumulator as u8);
                accumulator >>= 8;
                bits -= 8;
            }
        }
    }
    assert_eq!(bits, 0, "w1 encoding must end on a byte boundary");
    debug_assert_eq!(out.len(), profile.w1_encoded_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decompose_reconstructs() {
        for &r in &[0u32, 1, GAMMA2, ALPHA, Q - 1, 123_456, 7_777_777] {
            let (r1, r0) = decompose(r);
            let recon = (r1 as i64 * ALPHA as i64 + r0 as i64).rem_euclid(Q as i64);
            assert_eq!(recon, (r % Q) as i64, "decompose must reconstruct r mod q");
            assert!(r1 >= 0 && (r1 as u32) < M, "r1 in range for r={r}");
        }
    }

    #[test]
    fn decompose_emits_fips_negative_gamma2_wrap_point() {
        assert_eq!(
            decompose(Q - GAMMA2),
            (0, -(GAMMA2 as i32)),
            "FIPS wrap point must use the unique (w1,w0)=(0,−γ2) encoding"
        );
    }

    #[test]
    fn use_hint_zero_is_high_bits() {
        for &r in &[0u32, 42, GAMMA2, 999_999] {
            assert_eq!(use_hint(0, r), high_bits(r));
        }
    }

    #[test]
    fn w1_encode_packs_two_coeffs_per_byte() {
        let mut w1 = [[0u32; N]; crate::constants::K];
        w1[0][0] = 0x0a;
        w1[0][1] = 0x03;
        let bytes = w1_encode(&w1);
        assert_eq!(bytes.len(), crate::profile::ML_DSA_65.w1_encoded_bytes());
        assert_eq!(bytes[0], 0x0a | (0x03 << 4));
    }

    #[test]
    fn mldsa44_w1_encode_packs_four_six_bit_coefficients_into_three_bytes() {
        use crate::profile::ML_DSA_44;

        let mut w1 = [[0u32; N]; crate::constants::K];
        w1[0][..4].copy_from_slice(&[1, 42, 35, 43]);
        let bytes = w1_encode_for(ML_DSA_44, &w1);
        assert_eq!(bytes.len(), 768);
        assert_eq!(&bytes[..3], &[129, 58, 174]);
    }
}
