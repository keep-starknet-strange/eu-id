//! Minimal dense degree-2 sumcheck prover (no LogUp, no ZK, no transcript).
//!
//! Per circuit layer we prove the standard degree-2 GKR-style claim
//!     C = Σ_{x∈{0,1}^m} eq(r, x) · V(x)
//! where V is the MLE of the layer's gate output values and eq(r,·) is the
//! equality selector MLE at a random point r (Fiat-Shamir stand-in: fixed
//! deterministic challenges, since transcripts are out of scope). This is a
//! product of two MLEs → the round polynomial is degree 2, exactly the
//! GrandProduct cost class from parity S3. The inner fold loop is the thing we
//! price: per round it collapses one variable of BOTH tables (2·2^k mults).
//!
//! A "term" = one entry of a layer's MLE (one hypercube point). ns/term =
//! best_ms·1e6 / Σ_layers pad2(layer_len). The final claimed sum is checked
//! against direct circuit evaluation (correctness assert).

use crate::field::{Gf128, M31};

/// The two-element field operations the sumcheck needs, abstracted so the
/// identical prover runs over M31 and GF(2^128).
pub trait Field: Copy + PartialEq + std::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(self, o: Self) -> Self;
    fn sub(self, o: Self) -> Self;
    fn mul(self, o: Self) -> Self;
    fn from_bit(b: bool) -> Self;
    /// A deterministic non-trivial challenge from a round index (transcript
    /// stand-in — out of scope to build a real Fiat-Shamir channel).
    fn challenge(seed: u64) -> Self;
}

impl Field for M31 {
    #[inline(always)]
    fn zero() -> Self {
        M31::zero()
    }
    #[inline(always)]
    fn one() -> Self {
        M31::one()
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        M31::add(self, o)
    }
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        M31::sub(self, o)
    }
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        M31::mul(self, o)
    }
    #[inline(always)]
    fn from_bit(b: bool) -> Self {
        M31(b as u32)
    }
    #[inline(always)]
    fn challenge(seed: u64) -> Self {
        // spread the seed across the field, keep it away from 0/1.
        M31(((seed.wrapping_mul(0x9E3779B1) >> 3) as u32 % ((1 << 31) - 3)) + 2)
    }
}

impl Field for Gf128 {
    #[inline(always)]
    fn zero() -> Self {
        Gf128::zero()
    }
    #[inline(always)]
    fn one() -> Self {
        Gf128(1, 0)
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Gf128::add(self, o)
    }
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        // characteristic 2: subtraction == addition.
        Gf128::add(self, o)
    }
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        Gf128::mul(self, o)
    }
    #[inline(always)]
    fn from_bit(b: bool) -> Self {
        Gf128::from_bit(b)
    }
    #[inline(always)]
    fn challenge(seed: u64) -> Self {
        let s = seed.wrapping_mul(0x9E3779B97F4A7C15);
        Gf128(s | 3, s.rotate_left(17) | 1)
    }
}

/// Build eq(r, x) table over m variables: eq[x] = Π_i (r_i x_i + (1-r_i)(1-x_i)).
fn eq_table<F: Field>(r: &[F]) -> Vec<F> {
    let m = r.len();
    let mut t = vec![F::zero(); 1 << m];
    t[0] = F::one();
    for (i, &ri) in r.iter().enumerate() {
        let half = 1 << i;
        let one_minus = F::one().sub(ri);
        for j in 0..half {
            let v = t[j];
            t[j] = v.mul(one_minus);
            t[j + half] = v.mul(ri);
        }
    }
    t
}

/// Prove Σ_x a(x)·b(x) with a dense degree-2 sumcheck. Returns the claimed sum
/// (the value the honest prover commits to at round 0). `a` and `b` are
/// consumed/folded in place. Deterministic challenges from `seed_base`.
///
/// Round poly is degree 2; we evaluate it at 3 points (0,1,2) by the standard
/// even/odd fold. This is the hot loop that gets priced.
pub fn prove_product<F: Field>(mut a: Vec<F>, mut b: Vec<F>, seed_base: u64) -> F {
    debug_assert_eq!(a.len(), b.len());
    debug_assert!(a.len().is_power_of_two());
    let m = a.len().trailing_zeros() as usize;

    // Claimed sum = Σ a·b over the cube.
    let mut claim = F::zero();
    for i in 0..a.len() {
        claim = claim.add(a[i].mul(b[i]));
    }

    let mut size = a.len();
    for round in 0..m {
        let half = size / 2;
        // Evaluate the univariate round polynomial g(t) = Σ_hi (a0+t(a1-a0))(b0+t(b1-b0))
        // at t = 0,1,2 (degree 2 needs 3 points).
        let mut e0 = F::zero();
        let mut e1 = F::zero();
        let mut e2 = F::zero();
        for j in 0..half {
            let a0 = a[j];
            let a1 = a[j + half];
            let b0 = b[j];
            let b1 = b[j + half];
            // t=0
            e0 = e0.add(a0.mul(b0));
            // t=1
            e1 = e1.add(a1.mul(b1));
            // t=2: a(2)=2a1-a0, b(2)=2b1-b0
            let a2 = a1.add(a1).sub(a0);
            let b2 = b1.add(b1).sub(b0);
            e2 = e2.add(a2.mul(b2));
        }
        // The verifier would check g(0)+g(1)==claim and draw a challenge; we
        // just fold at the deterministic challenge to advance the prover.
        let _ = (e0, e1, e2); // consumed as the round message (not transcripted)
        let c = F::challenge(seed_base ^ (round as u64 + 1));
        for j in 0..half {
            a[j] = a[j].add(c.mul(a[j + half].sub(a[j])));
            b[j] = b[j].add(c.mul(b[j + half].sub(b[j])));
        }
        size = half;
    }
    claim
}

/// Convenience: build eq(r,·) with deterministic r and prove Σ eq·V for a layer
/// MLE `v` (padded to power of two with zeros). Returns claimed sum.
pub fn prove_layer<F: Field>(v: &[F], seed_base: u64) -> F {
    let len = v.len().next_power_of_two();
    let m = len.trailing_zeros() as usize;
    let r: Vec<F> = (0..m)
        .map(|i| F::challenge(seed_base ^ (0xA000 + i as u64)))
        .collect();
    let eq = eq_table(&r);
    let mut vpad = vec![F::zero(); len];
    for (i, &x) in v.iter().enumerate() {
        vpad[i] = x;
    }
    prove_product(eq, vpad, seed_base)
}
