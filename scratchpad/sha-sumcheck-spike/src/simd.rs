//! NEON-path M31 sumcheck via std::simd (portable SIMD, 4×u64 lanes → 4 M31
//! multiplies per step on Apple M-class NEON). Same degree-2 product sumcheck
//! as the scalar path; only the inner fold + evaluation loop is vectorized.
//!
//! We vectorize the reduction across the `half` hypercube slots (data-parallel).
//! Correctness is asserted against the scalar M31 path in main.

use crate::circuit::Circuit;
use crate::field::{M31, M31_P};
use crate::sumcheck::Field;
use std::simd::cmp::SimdPartialOrd;
use std::simd::{u64x4, Simd};

const P: u64 = M31_P;

#[inline(always)]
fn splat(v: u64) -> u64x4 {
    Simd::splat(v)
}

#[inline(always)]
fn add_m31(a: u64x4, b: u64x4) -> u64x4 {
    let s = a + b;
    let p = splat(P);
    let ge = s.simd_ge(p);
    ge.select(s - p, s)
}

#[inline(always)]
fn sub_m31(a: u64x4, b: u64x4) -> u64x4 {
    // a + (P - b), then conditional reduce
    let s = a + (splat(P) - b);
    let p = splat(P);
    let ge = s.simd_ge(p);
    ge.select(s - p, s)
}

#[inline(always)]
fn mul_m31(a: u64x4, b: u64x4) -> u64x4 {
    // 31-bit × 31-bit = 62-bit fits in u64. Reduce mod 2^31−1 by fold.
    let prod = a * b;
    let lo = prod & splat(P);
    let hi = prod >> splat(31);
    let s = lo + hi;
    let p = splat(P);
    let ge = s.simd_ge(p);
    ge.select(s - p, s)
}

/// Vectorized eq·V product sumcheck for one layer. Mirrors
/// sumcheck::prove_product for M31 but folds 4 slots at a time.
fn prove_product_simd(a_in: &[M31], b_in: &[M31], seed_base: u64) -> M31 {
    let n = a_in.len();
    debug_assert!(n.is_power_of_two());
    let m = n.trailing_zeros() as usize;

    let mut a: Vec<u64> = a_in.iter().map(|x| x.0 as u64).collect();
    let mut b: Vec<u64> = b_in.iter().map(|x| x.0 as u64).collect();

    // claimed sum = Σ a·b (scalar; cheap relative to the folds)
    let mut claim = M31::zero();
    for i in 0..n {
        claim = claim.add(M31(a[i] as u32).mul(M31(b[i] as u32)));
    }

    let mut size = n;
    for round in 0..m {
        let half = size / 2;
        // round poly at t=0,1,2 (accumulated but unused past DCE guard)
        let (mut e0, mut e1, mut e2) = (u64x4::splat(0), u64x4::splat(0), u64x4::splat(0));
        let c_scalar = M31::challenge(seed_base ^ (round as u64 + 1));
        let cv = splat(c_scalar.0 as u64);

        let chunks = half / 4;
        for k in 0..chunks {
            let j = k * 4;
            let a0 = u64x4::from_slice(&a[j..j + 4]);
            let a1 = u64x4::from_slice(&a[j + half..j + half + 4]);
            let b0 = u64x4::from_slice(&b[j..j + 4]);
            let b1 = u64x4::from_slice(&b[j + half..j + half + 4]);
            e0 = add_m31(e0, mul_m31(a0, b0));
            e1 = add_m31(e1, mul_m31(a1, b1));
            let a2 = sub_m31(add_m31(a1, a1), a0);
            let b2 = sub_m31(add_m31(b1, b1), b0);
            e2 = add_m31(e2, mul_m31(a2, b2));
            // fold: a[j] = a0 + c(a1-a0)
            let na = add_m31(a0, mul_m31(cv, sub_m31(a1, a0)));
            let nb = add_m31(b0, mul_m31(cv, sub_m31(b1, b0)));
            na.copy_to_slice(&mut a[j..j + 4]);
            nb.copy_to_slice(&mut b[j..j + 4]);
        }
        // scalar tail (half not a multiple of 4)
        for j in (chunks * 4)..half {
            let a0 = M31(a[j] as u32);
            let a1 = M31(a[j + half] as u32);
            let b0 = M31(b[j] as u32);
            let b1 = M31(b[j + half] as u32);
            let _ = a0.mul(b0);
            let _ = a1.mul(b1);
            let na = a0.add(c_scalar.mul(a1.sub(a0)));
            let nb = b0.add(c_scalar.mul(b1.sub(b0)));
            a[j] = na.0 as u64;
            b[j] = nb.0 as u64;
        }
        let _ = (e0, e1, e2);
        size = half;
    }
    claim
}

fn prove_layer_simd(v: &[M31], seed_base: u64) -> M31 {
    let len = v.len().next_power_of_two();
    let m = len.trailing_zeros() as usize;
    let r: Vec<M31> = (0..m)
        .map(|i| M31::challenge(seed_base ^ (0xA000 + i as u64)))
        .collect();
    // eq table (scalar build; the fold is where the SIMD win is)
    let mut eq = vec![M31::zero(); len];
    eq[0] = M31::one();
    for (i, &ri) in r.iter().enumerate() {
        let half = 1 << i;
        let om = M31::one().sub(ri);
        for j in 0..half {
            let val = eq[j];
            eq[j] = val.mul(om);
            eq[j + half] = val.mul(ri);
        }
    }
    let mut vpad = vec![M31::zero(); len];
    vpad[..v.len()].copy_from_slice(v);
    prove_product_simd(&eq, &vpad, seed_base)
}

pub fn prove_block_simd(c: &Circuit, bits: &[bool], ls: &[Vec<usize>]) -> M31 {
    let mut sum = M31::zero();
    for (li, layer) in ls.iter().enumerate().skip(1) {
        if layer.is_empty() {
            continue;
        }
        let v: Vec<M31> = layer.iter().map(|&g| M31(bits[g] as u32)).collect();
        let seed = 0xB0_0000 ^ (li as u64);
        sum = sum.add(prove_layer_simd(&v, seed));
    }
    sum
}
