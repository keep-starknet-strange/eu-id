#![feature(portable_simd)]
//! WO-B0 spike harness: ns/term for an uncommitted-wire layered sumcheck
//! proving one SHA-256 compression block, single-thread, two encodings.
//!
//! Non-goals (per WO): no ZK, no Ligero, no transcript, no production code,
//! no multi-block. One number per encoding.

mod circuit;
mod field;
mod simd;
mod sumcheck;

use circuit::{build_compression_block, eval_bits, native_compress, Circuit, Op};
use field::{Gf128, M31};
use std::time::Instant;
use sumcheck::{prove_layer, Field};

/// Group gates by layer (depth). Returns Vec of gate-id lists per layer,
/// skipping layer 0 (inputs) since inputs are not "proved" by a layer sumcheck.
fn layers(c: &Circuit) -> Vec<Vec<usize>> {
    let mut ls: Vec<Vec<usize>> = vec![Vec::new(); c.n_layers as usize];
    for (i, &d) in c.depth.iter().enumerate() {
        ls[d as usize].push(i);
    }
    ls
}

/// Total terms = Σ over provable layers of pad2(layer_len). This is the
/// divisor for ns/term (one term = one hypercube MLE entry, mirroring S3).
fn total_terms(ls: &[Vec<usize>]) -> usize {
    ls.iter()
        .skip(1)
        .map(|l| l.len().next_power_of_two().max(1))
        .sum()
}

/// Run the layered sumcheck once over field F. Returns an accumulator of all
/// layer claims (to defeat dead-code elimination) plus a per-layer direct
/// recomputation used for the correctness assert.
fn prove_block<F: Field>(c: &Circuit, bits: &[bool], ls: &[Vec<usize>]) -> (F, F) {
    let mut sum_claims = F::zero();
    let mut sum_direct = F::zero();
    for (li, layer) in ls.iter().enumerate().skip(1) {
        if layer.is_empty() {
            continue;
        }
        // Layer MLE = the gate output bits of this layer, in gate-id order.
        let v: Vec<F> = layer.iter().map(|&g| F::from_bit(bits[g])).collect();
        let seed = 0xB0_0000 ^ (li as u64);
        let claim = prove_layer::<F>(&v, seed);
        sum_claims = sum_claims.add(claim);
        // Independent direct recomputation of Σ eq(r,x)·V(x) for the assert.
        sum_direct = sum_direct.add(direct_eq_dot::<F>(&v, seed));
    }
    (sum_claims, sum_direct)
}

/// Direct Σ_x eq(r,x)·V(x) recomputed independently of the sumcheck prover.
fn direct_eq_dot<F: Field>(v: &[F], seed_base: u64) -> F {
    let len = v.len().next_power_of_two();
    let m = len.trailing_zeros() as usize;
    let r: Vec<F> = (0..m)
        .map(|i| F::challenge(seed_base ^ (0xA000 + i as u64)))
        .collect();
    // eq table
    let mut eq = vec![F::zero(); len];
    eq[0] = F::one();
    for (i, &ri) in r.iter().enumerate() {
        let half = 1 << i;
        let om = F::one().sub(ri);
        for j in 0..half {
            let val = eq[j];
            eq[j] = val.mul(om);
            eq[j + half] = val.mul(ri);
        }
    }
    let mut acc = F::zero();
    for i in 0..v.len() {
        acc = acc.add(eq[i].mul(v[i]));
    }
    acc
}

fn best_of_3<Fn: FnMut() -> f64>(mut f: Fn) -> [f64; 3] {
    let mut runs = [0.0f64; 3];
    // one warm-up
    f();
    for r in runs.iter_mut() {
        *r = f();
    }
    runs
}

fn main() {
    // Message: a fixed non-trivial block (0,1,2,...,15) — genuine compression.
    let msg: [u32; 16] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x01010101) ^ 0xdeadbeef);

    // --- KAT: hardware PMULL gf128 mul == bit-serial reference (from mac.rs) ---
    {
        let mut ok = true;
        let mut s: u64 = 0x1234_5678_9abc_def0;
        for _ in 0..10_000 {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let x = Gf128(s, s.rotate_left(29));
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let y = Gf128(s, s.rotate_left(13));
            if x.mul(y) != x.mul_bitserial(y) {
                ok = false;
                break;
            }
        }
        assert!(ok, "hardware gf128 mul != bit-serial reference (mac.rs)");
        println!("[ok] hardware PMULL gf128 mul == bit-serial reference (10k KAT)");
    }

    let c = build_compression_block(&msg);
    let bits = eval_bits(&c);
    let ls = layers(&c);

    // --- circuit shape ---
    let n_gates = c.gates.len();
    let n_inputs = c.inputs.len();
    let n_and = c.gates.iter().filter(|g| matches!(g, Op::And(..))).count();
    let n_xor = c.gates.iter().filter(|g| matches!(g, Op::Xor(..))).count();
    let n_not = c.gates.iter().filter(|g| matches!(g, Op::Not(..))).count();
    let terms = total_terms(&ls);
    let provable_layers = ls.iter().skip(1).filter(|l| !l.is_empty()).count();

    println!("== circuit shape ==");
    println!("gates            : {n_gates}");
    println!("  inputs         : {n_inputs}");
    println!("  AND            : {n_and}");
    println!("  XOR            : {n_xor}");
    println!("  NOT            : {n_not}");
    println!("layers (total)   : {}", c.n_layers);
    println!("provable layers  : {provable_layers}");
    println!("terms/block      : {terms}   (Σ pad2(layer_len) over provable layers)");
    // Layer-size histogram (auditability of the ns/term divisor).
    let mut hist: std::collections::BTreeMap<usize, usize> = Default::default();
    let mut raw_gates_in_layers = 0usize;
    for l in ls.iter().skip(1) {
        if l.is_empty() {
            continue;
        }
        raw_gates_in_layers += l.len();
        *hist.entry(l.len().next_power_of_two()).or_default() += 1;
    }
    println!("raw gates in provable layers: {raw_gates_in_layers}");
    println!("layer pad2-size histogram (pad2 -> #layers):");
    for (sz, n) in &hist {
        println!("    {sz:>6} -> {n}");
    }

    // --- correctness: circuit output bits == native SHA compression ---
    let want = native_compress(&msg);
    let mut got = [0u32; 8];
    for w in 0..8 {
        for i in 0..32 {
            if bits[c.out_wires[w][i]] {
                got[w] |= 1 << i;
            }
        }
    }
    assert_eq!(got, want, "circuit output != native SHA-256 compression");
    println!("\n[ok] circuit output == native SHA-256 compression");

    // --- correctness: sumcheck claim == direct eq·V (per encoding) ---
    let (claim_m31, direct_m31) = prove_block::<M31>(&c, &bits, &ls);
    assert_eq!(claim_m31, direct_m31, "M31 sumcheck claim != direct");
    let (claim_gf, direct_gf) = prove_block::<Gf128>(&c, &bits, &ls);
    assert_eq!(claim_gf, direct_gf, "GF128 sumcheck claim != direct");
    println!("[ok] M31   sumcheck claim == direct eq·V");
    println!("[ok] GF128 sumcheck claim == direct eq·V");

    // --- SIMD-path correctness (M31 4-lane fold) ---
    let claim_simd = simd::prove_block_simd(&c, &bits, &ls);
    // scalar M31 reference over the same layering/seed:
    let (claim_ref, _) = prove_block::<M31>(&c, &bits, &ls);
    assert_eq!(
        claim_simd, claim_ref,
        "SIMD M31 claim != scalar M31 claim"
    );
    println!("[ok] SIMD M31 claim == scalar M31 claim");

    // --- timing: best-of-3 full-block proof, single-thread ---
    println!("\n== timing (best-of-3, single-thread) ==");

    let m31_runs = best_of_3(|| {
        let t = Instant::now();
        let (s, _) = prove_block::<M31>(&c, &bits, &ls);
        std::hint::black_box(s);
        t.elapsed().as_secs_f64() * 1e3
    });
    let gf_runs = best_of_3(|| {
        let t = Instant::now();
        let (s, _) = prove_block::<Gf128>(&c, &bits, &ls);
        std::hint::black_box(s);
        t.elapsed().as_secs_f64() * 1e3
    });
    let simd_runs = best_of_3(|| {
        let t = Instant::now();
        let s = simd::prove_block_simd(&c, &bits, &ls);
        std::hint::black_box(s);
        t.elapsed().as_secs_f64() * 1e3
    });

    let report = |name: &str, runs: [f64; 3]| {
        let best = runs.iter().cloned().fold(f64::INFINITY, f64::min);
        let ns_per_term = best * 1e6 / terms as f64;
        println!(
            "{name:<16} runs(ms)=[{:.3}, {:.3}, {:.3}]  best={:.3} ms  ns/term={:.2}",
            runs[0], runs[1], runs[2], best, ns_per_term
        );
    };
    report("M31 scalar", m31_runs);
    report("M31 SIMD(4x)", simd_runs);
    report("GF128 scalar", gf_runs);
}
