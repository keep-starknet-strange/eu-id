//! Number-Theoretic Transform over `Z_q` (`q = 8_380_417`, `n = 256`).
//!
//! FIPS 204 §7.5: the NTT (Algorithm 41) maps a polynomial to its evaluations,
//! `NTT^-1` (Algorithm 42) inverts it, and `MultiplyNTTs` (Algorithm 45) is a
//! pointwise product. The verifier computes `w'approx = A·z − c·t1·2^d` most
//! cheaply in the NTT domain, so this module exposes both directions and the
//! pointwise multiply.
//!
//! The twiddle table is `zetas[i] = ζ^{brv8(i)} mod q` with `ζ = 1753`
//! (Appendix B). We derive it at load time rather than hard-coding 256 magic
//! numbers — cheaper to audit against the spec's one-line definition.

use crate::constants::{N, Q, ZETA};

/// A degree-<256 polynomial in `Z_q`, coefficients in `[0, q)`.
pub type Poly = [u32; N];

/// A polynomial already in the NTT (evaluation) domain.
pub type NttPoly = [u32; N];

/// `zetas[i] = ζ^{brv8(i)} mod q` (FIPS 204 Appendix B). `zetas[0] = 1`.
fn zeta_table() -> [u32; N] {
    // Powers of ζ in natural order.
    let mut pow = [0u64; N];
    let mut curr = 1u64;
    for entry in pow.iter_mut() {
        *entry = curr;
        curr = (curr * ZETA as u64) % Q as u64;
    }
    // Reorder by the 8-bit bit-reversal of the index.
    let mut zetas = [0u32; N];
    for (i, z) in zetas.iter_mut().enumerate() {
        *z = pow[(i as u8).reverse_bits() as usize] as u32;
    }
    zetas
}

#[inline]
fn addq(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= Q {
        s - Q
    } else {
        s
    }
}

#[inline]
fn subq(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        a + Q - b
    }
}

#[inline]
fn mulq(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) % Q as u64) as u32
}

/// Forward NTT (FIPS 204 Algorithm 41), in place, Cooley–Tukey.
pub fn ntt(f: &Poly) -> NttPoly {
    let zetas = zeta_table();
    let mut a = *f;
    let mut m = 0usize;
    let mut len = 128usize;
    while len >= 1 {
        let mut start = 0usize;
        while start < N {
            m += 1;
            let z = zetas[m];
            for j in start..start + len {
                let t = mulq(z, a[j + len]);
                a[j + len] = subq(a[j], t);
                a[j] = addq(a[j], t);
            }
            start += 2 * len;
        }
        len >>= 1;
    }
    a
}

/// Inverse NTT (FIPS 204 Algorithm 42), in place, Gentleman–Sande, final scale
/// by `256^-1 mod q = 8347681`.
pub fn ntt_inverse(f: &NttPoly) -> Poly {
    const N_INV: u32 = 8_347_681; // 256^{-1} mod q
    let zetas = zeta_table();
    let mut a = *f;
    let mut m = N; // 256
    let mut len = 1usize;
    while len < N {
        let mut start = 0usize;
        while start < N {
            m -= 1;
            let z = Q - zetas[m]; // -zetas[m] mod q
            for j in start..start + len {
                let t = a[j];
                a[j] = addq(t, a[j + len]);
                a[j + len] = mulq(z, subq(t, a[j + len]));
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    for coeff in a.iter_mut() {
        *coeff = mulq(*coeff, N_INV);
    }
    a
}

/// Pointwise product in the NTT domain (FIPS 204 Algorithm 45 `MultiplyNTTs`).
pub fn pointwise(a: &NttPoly, b: &NttPoly) -> NttPoly {
    let mut out = [0u32; N];
    for i in 0..N {
        out[i] = mulq(a[i], b[i]);
    }
    out
}

/// Coefficient-wise addition mod `q`.
pub fn poly_add(a: &Poly, b: &Poly) -> Poly {
    let mut out = [0u32; N];
    for i in 0..N {
        out[i] = addq(a[i], b[i]);
    }
    out
}

/// Coefficient-wise subtraction mod `q`.
pub fn poly_sub(a: &Poly, b: &Poly) -> Poly {
    let mut out = [0u32; N];
    for i in 0..N {
        out[i] = subq(a[i], b[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zeta_table_matches_spec_anchors() {
        let z = zeta_table();
        // FIPS 204 Appendix B: zetas[0] = 1, zetas[1] = 4808194 (ζ^128).
        assert_eq!(z[0], 1);
        assert_eq!(z[1], 4_808_194);
    }

    #[test]
    fn ntt_round_trips() {
        let mut f = [0u32; N];
        for (i, c) in f.iter_mut().enumerate() {
            *c = ((i as u32 * 7 + 3) * 101) % Q;
        }
        let back = ntt_inverse(&ntt(&f));
        assert_eq!(back, f, "NTT^-1 ∘ NTT is the identity");
    }

    #[test]
    fn multiply_via_ntt_matches_schoolbook() {
        // Two small polynomials; product in R_q = Z_q[X]/(X^256+1).
        let mut a = [0u32; N];
        let mut b = [0u32; N];
        a[0] = 5;
        a[1] = 3;
        b[0] = 2;
        b[255] = 4; // exercises the negacyclic wrap X^256 = -1
        let prod = ntt_inverse(&pointwise(&ntt(&a), &ntt(&b)));

        // Schoolbook negacyclic reference.
        let mut expect = [0u32; N];
        for (i, &ai) in a.iter().enumerate() {
            for (j, &bj) in b.iter().enumerate() {
                let prod_ij = ((ai as u64 * bj as u64) % Q as u64) as u32;
                let k = i + j;
                if k < N {
                    expect[k] = addq(expect[k], prod_ij);
                } else {
                    expect[k - N] = subq(expect[k - N], prod_ij);
                }
            }
        }
        assert_eq!(prod, expect);
    }
}
