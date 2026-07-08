//! Rounding helpers: `Decompose` (FIPS 204 Algorithm 36), `UseHint`
//! (Algorithm 39), and `w1Encode` (Algorithm 28). Verification never calls
//! `Decompose`/`HighBits` directly — it recovers `w1` from the approximate
//! commitment via `UseHint` — but `Decompose` is exposed because `UseHint` is
//! defined in terms of it and the witness generator needs both.
//!
//! All arithmetic is over the centered residue system used by FIPS 204:
//! `r mod± α ∈ (−α/2, α/2]`.

use crate::constants::{GAMMA2, N, Q};

/// `α = 2·γ2`, the decomposition modulus.
const ALPHA: u32 = 2 * GAMMA2;

/// Number of possible `w1` values: `(q − 1) / α = 16` for ML-DSA-65, so `r1`
/// ranges over `[0, 15]`.
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
/// `r = r1·α + r0 (mod q)`, `r0 ∈ (−α/2, α/2]`, and the special-case wrap so
/// `r1 ∈ [0, (q−1)/α)`.
pub fn decompose(r: u32) -> (i32, i32) {
    let r = r % Q;
    let r0 = mod_pm(r, ALPHA);
    let r_minus_r0 = r as i64 - r0 as i64;
    if r_minus_r0 == (Q - 1) as i64 {
        // r1 would be (q-1)/α; wrap to 0 and pull r0 down by 1.
        (0, r0 - 1)
    } else {
        let r1 = r_minus_r0 / ALPHA as i64;
        (r1 as i32, r0)
    }
}

/// `HighBits(r) = r1` (FIPS 204 Algorithm 37).
pub fn high_bits(r: u32) -> i32 {
    decompose(r).0
}

/// FIPS 204 Algorithm 39 `UseHint(h, r)`: recover the high bits of the true
/// commitment given the one-bit hint `h ∈ {0, 1}`.
pub fn use_hint(hint: u8, r: u32) -> i32 {
    let (r1, r0) = decompose(r);
    if hint == 0 {
        return r1;
    }
    if r0 > 0 {
        (r1 + 1).rem_euclid(M as i32)
    } else {
        (r1 - 1).rem_euclid(M as i32)
    }
}

/// Apply `UseHint` coefficient-wise across a `w'approx` polynomial with its
/// per-coefficient hint bits, yielding `w1'` (values in `[0, M)`).
pub fn use_hint_poly(hint: &[u8; N], w_approx: &[u32; N]) -> [u32; N] {
    let mut w1 = [0u32; N];
    for i in 0..N {
        w1[i] = use_hint(hint[i], w_approx[i]) as u32;
    }
    w1
}

/// FIPS 204 Algorithm 28 `w1Encode`: pack a `w1` vector (`k` polynomials, each
/// coefficient in `[0, M)`, `M = 16 ⇒ 4 bits`) into a byte string, the
/// `SHAKE-256` input for the `c̃` recomputation.
pub fn w1_encode(w1: &[[u32; N]]) -> Vec<u8> {
    // 4 bits per coefficient, 256 coefficients per poly ⇒ 128 bytes per poly.
    let mut out = Vec::with_capacity(w1.len() * N / 2);
    for poly in w1 {
        for pair in poly.chunks_exact(2) {
            let lo = (pair[0] & 0x0f) as u8;
            let hi = (pair[1] & 0x0f) as u8;
            out.push(lo | (hi << 4));
        }
    }
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
    fn use_hint_zero_is_high_bits() {
        for &r in &[0u32, 42, GAMMA2, 999_999] {
            assert_eq!(use_hint(0, r), high_bits(r));
        }
    }

    #[test]
    fn w1_encode_packs_two_coeffs_per_byte() {
        let mut poly = [0u32; N];
        poly[0] = 0x0a;
        poly[1] = 0x03;
        let bytes = w1_encode(&[poly]);
        assert_eq!(bytes.len(), N / 2);
        assert_eq!(bytes[0], 0x0a | (0x03 << 4));
    }
}
