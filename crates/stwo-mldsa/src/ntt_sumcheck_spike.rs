//! WO-Q10.3 — INTT limb-exact layered-sumcheck spike (DE-RISK, NOT production).
//!
//! Question being de-risked: can the inverse-NTT AIR (`expand_a::NttEval`,
//! log_size 16, ~6.03 M cells) be replaced by a layered zero-check sumcheck that
//! only commits the per-butterfly quotient/carry witnesses, virtualizing the
//! chained coefficient values? This module is an off-protocol harness that
//! mirrors `keccak_round::gkr_offload_spike`. It is NOT wired into any
//! production component (`statement.rs`/`proof.rs`/hosts are untouched).
//!
//! Design (fixed by the WO, implemented verbatim):
//!  * Keep the EXISTING limb-exact representation (8/8/7-bit base-256 limbs, the
//!    same butterfly relations as `NttEval::evaluate`). The INTT is linear over
//!    Zq (q ≈ 2^23), not over M31, so a plain Schwartz–Zippel field identity is
//!    unsound — the mod-q integrity lives in the range-checked quotient/carry
//!    limb equations, which we carry through unchanged.
//!  * One polynomial = N=256 coeffs, 8 Gentleman–Sande stages × 128 butterflies,
//!    then a 256-row N_INV scaling layer.
//!  * Per stage: draw z from the channel, prove `Σ_x eq(z,x)·R_s(x) = 0` with
//!    stwo's generic sumcheck (`prove_batch`/`partially_verify`). `R_s` is a
//!    random-β-linear-combination of the butterfly relations; degree ≤ 2, so
//!    eq·R_s has degree ≤ 3 = `sumcheck::MAX_DEGREE`.
//!  * The 30 polynomials of the production matrix are batched into ONE sumcheck
//!    per stage via `prove_batch`.
//!
//! Layer chaining / commitment seam (the point of the exercise): stage-s inputs
//! are stage-(s−1) outputs, so intermediate coefficient VALUES are never
//! committed — only the quotient/carry witnesses would be (see the census in the
//! test module). In this spike the endpoints and inter-stage wiring are held
//! natively and the final sumcheck claim is tied back to the native witness MLEs
//! (`tie_back`); a production build would replace those native holds with an
//! `MleEval` tie-back to committed columns and a wiring predicate. That wiring
//! predicate is verifier-side (public) structure — it adds NO committed cells,
//! only verifier compute + a soundness-proof obligation, and it is the residual
//! risk this spike does not close.

// Off-protocol de-risk harness: every item is driven from `#[cfg(test)]`.
#![allow(dead_code)]

use num_traits::{One, Zero};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::prover::lookups::sumcheck::{
    partially_verify, prove_batch, MultivariatePolyOracle, SumcheckProof,
};
use stwo::prover::lookups::utils::{eq, UnivariatePoly};

use crate::constants::{K, L, N, Q, ZETA};

type SF = SecureField;

/// Production ML-DSA-65 matrix polynomial count (K·L).
const MATRIX_POLYS: usize = K * L; // 30
/// N^{-1} mod q, the inverse-NTT final scaling constant (see FIPS 204).
const N_INV: u32 = 8_347_681;
/// Butterflies per stage (N/2).
const HALF_N: usize = N / 2; // 128
/// Number of GS stages.
const STAGES: usize = 8;

// ── Butterfly-oracle component layout (27 MLEs) ──────────────────────────────
const B_IN0: usize = 0; //  input0 limbs   [3]
const B_IN1: usize = 3; //  input1 limbs   [3]
const B_OUT0: usize = 6; //  output0 limbs  [3]
const B_DIFF: usize = 9; //  diff limbs     [3]  (mul input)
const B_OUT1: usize = 12; // output1 limbs  [3]
const B_QUOT: usize = 15; // quotient limbs [3]
const B_CARRY: usize = 18; // carries       [4]
const B_REDUCE: usize = 22; // reduce bit
const B_BORROW: usize = 23; // borrow bit
const B_TW: usize = 24; // twiddle limbs  [3]
const B_COMPS: usize = 27;

// ── Scaling-oracle component layout (13 MLEs) ────────────────────────────────
const S_IN0: usize = 0; //  input limbs    [3]
const S_OUT1: usize = 3; //  output limbs   [3]
const S_QUOT: usize = 6; //  quotient limbs [3]
const S_CARRY: usize = 9; //  carries        [4]
const S_COMPS: usize = 13;

#[inline]
fn sf(v: u32) -> SF {
    SF::from(BaseField::from(v))
}

/// Map a small signed integer (carry / balanced value) into M31.
#[inline]
fn sf_i(v: i64) -> SF {
    const P: i64 = (1 << 31) - 1;
    sf(v.rem_euclid(P) as u32)
}

#[inline]
fn split3(value: u32) -> [u32; 3] {
    [value & 0xff, (value >> 8) & 0xff, value >> 16]
}

/// Exact modular multiplication witness (re-derived from `expand_a::mul_witness`
/// — that helper is module-private). Returns `(output, quotient, carries)` with
/// `output = constant·value mod Q` under the base-256 limb equations.
fn mul_witness(constant: u32, value: u32) -> (u32, u32, [i64; 4]) {
    let product = constant as u64 * value as u64;
    let output = (product % Q as u64) as u32;
    let quotient = (product / Q as u64) as u32;
    let z = split3(constant);
    let x = split3(value);
    let q = split3(Q);
    let k = split3(quotient);
    let out = split3(output);
    let e0 = z[0] as i64 * x[0] as i64 - q[0] as i64 * k[0] as i64 - out[0] as i64;
    let c1 = e0 / 256;
    let e1 = z[0] as i64 * x[1] as i64 + z[1] as i64 * x[0] as i64
        - q[0] as i64 * k[1] as i64
        - q[1] as i64 * k[0] as i64
        - out[1] as i64
        + c1;
    let c2 = e1 / 256;
    let e2 = z[0] as i64 * x[2] as i64 + z[1] as i64 * x[1] as i64 + z[2] as i64 * x[0] as i64
        - q[0] as i64 * k[2] as i64
        - q[1] as i64 * k[1] as i64
        - q[2] as i64 * k[0] as i64
        - out[2] as i64
        + c2;
    let c3 = e2 / 256;
    let e3 = z[1] as i64 * x[2] as i64 + z[2] as i64 * x[1] as i64
        - q[1] as i64 * k[2] as i64
        - q[2] as i64 * k[1] as i64
        + c3;
    let c4 = e3 / 256;
    debug_assert_eq!(e0, 256 * c1);
    debug_assert_eq!(e1, 256 * c2);
    debug_assert_eq!(e2, 256 * c3);
    debug_assert_eq!(e3, 256 * c4);
    debug_assert_eq!(z[2] as i64 * x[2] as i64 - q[2] as i64 * k[2] as i64 + c4, 0);
    (output, quotient, [c1, c2, c3, c4])
}

/// Bit-reversed zeta powers (re-derived from `expand_a::zeta_table`).
fn zeta_table() -> [u32; N] {
    let mut pow = [0u64; N];
    let mut curr = 1u64;
    for entry in &mut pow {
        *entry = curr;
        curr = curr * ZETA as u64 % Q as u64;
    }
    let mut zetas = [0u32; N];
    for (i, value) in zetas.iter_mut().enumerate() {
        *value = pow[(i as u8).reverse_bits() as usize] as u32;
    }
    zetas
}

// ── Witness ──────────────────────────────────────────────────────────────────

/// One butterfly's witness (all values as produced by the honest INTT).
#[derive(Clone)]
struct Butterfly {
    in0: u32,
    in1: u32,
    out0: u32,
    diff: u32,
    out1: u32,
    quot: u32,
    carry: [i64; 4],
    reduce: bool,
    borrow: bool,
    tw: u32,
}

/// One scaling row's witness.
#[derive(Clone)]
struct ScaleRow {
    in0: u32,
    out1: u32,
    quot: u32,
    carry: [i64; 4],
}

/// Full INTT witness for the 30-poly matrix: `stages[poly][stage] = 128
/// butterflies`, `scaling[poly] = 256 rows`.
struct InttWitness {
    stages: Vec<[Vec<Butterfly>; STAGES]>,
    scaling: Vec<Vec<ScaleRow>>,
}

/// Run the honest Gentleman–Sande inverse NTT on each `a_hat` polynomial,
/// recording every butterfly / scaling witness. Mirrors
/// `expand_a::gen_ntt_base_trace`'s state evolution exactly.
fn gen_witness(a_hat: &[[u32; N]]) -> InttWitness {
    let zetas = zeta_table();
    let mut stages = Vec::with_capacity(a_hat.len());
    let mut scaling = Vec::with_capacity(a_hat.len());

    for state0 in a_hat {
        let mut state = *state0;
        let mut per_stage: [Vec<Butterfly>; STAGES] = Default::default();
        let mut m = N;
        let mut len = 1usize;
        for stage in per_stage.iter_mut() {
            let mut start = 0usize;
            while start < N {
                m -= 1;
                let tw = Q - zetas[m];
                for index0 in start..start + len {
                    let index1 = index0 + len;
                    let in0 = state[index0];
                    let in1 = state[index1];
                    let sum = in0 + in1;
                    let reduce = sum >= Q;
                    let out0 = if reduce { sum - Q } else { sum };
                    let borrow = in0 < in1;
                    let diff = if borrow { in0 + Q - in1 } else { in0 - in1 };
                    let (out1, quot, carry) = mul_witness(tw, diff);
                    state[index0] = out0;
                    state[index1] = out1;
                    stage.push(Butterfly {
                        in0,
                        in1,
                        out0,
                        diff,
                        out1,
                        quot,
                        carry,
                        reduce,
                        borrow,
                        tw,
                    });
                }
                start += 2 * len;
            }
            len <<= 1;
        }

        let mut rows = Vec::with_capacity(N);
        for &in0 in state.iter() {
            let (out1, quot, carry) = mul_witness(N_INV, in0);
            rows.push(ScaleRow {
                in0,
                out1,
                quot,
                carry,
            });
        }
        stages.push(per_stage);
        scaling.push(rows);
    }
    InttWitness { stages, scaling }
}

// ── MLE construction ─────────────────────────────────────────────────────────

fn butterfly_comps(bfs: &[Butterfly]) -> Vec<Vec<SF>> {
    let mut comps = vec![vec![SF::zero(); bfs.len()]; B_COMPS];
    for (x, bf) in bfs.iter().enumerate() {
        let put = |comps: &mut [Vec<SF>], base: usize, v: u32| {
            let l = split3(v);
            for i in 0..3 {
                comps[base + i][x] = sf(l[i]);
            }
        };
        put(&mut comps, B_IN0, bf.in0);
        put(&mut comps, B_IN1, bf.in1);
        put(&mut comps, B_OUT0, bf.out0);
        put(&mut comps, B_DIFF, bf.diff);
        put(&mut comps, B_OUT1, bf.out1);
        put(&mut comps, B_QUOT, bf.quot);
        put(&mut comps, B_TW, bf.tw);
        for i in 0..4 {
            comps[B_CARRY + i][x] = sf_i(bf.carry[i]);
        }
        comps[B_REDUCE][x] = sf(bf.reduce as u32);
        comps[B_BORROW][x] = sf(bf.borrow as u32);
    }
    comps
}

fn scaling_comps(rows: &[ScaleRow]) -> Vec<Vec<SF>> {
    let mut comps = vec![vec![SF::zero(); rows.len()]; S_COMPS];
    for (x, row) in rows.iter().enumerate() {
        let put = |comps: &mut [Vec<SF>], base: usize, v: u32| {
            let l = split3(v);
            for i in 0..3 {
                comps[base + i][x] = sf(l[i]);
            }
        };
        put(&mut comps, S_IN0, row.in0);
        put(&mut comps, S_OUT1, row.out1);
        put(&mut comps, S_QUOT, row.quot);
        for i in 0..4 {
            comps[S_CARRY + i][x] = sf_i(row.carry[i]);
        }
    }
    comps
}

// ── The relation R (must be ≤ degree 2 per variable) ─────────────────────────

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Butterfly,
    Scaling,
}

#[inline]
fn recompose(v: &[SF], base: usize) -> SF {
    v[base] + sf(256) * v[base + 1] + sf(1 << 16) * v[base + 2]
}

/// Base-256 limb equations for `out = z·x mod Q` with quotient `k` and carries
/// `cr` (shared by butterfly-mul and scaling). `z` may be an MLE (butterfly
/// twiddle) or a constant (scaling N_INV); passed as three `SF` limbs.
#[inline]
fn mul_relations(z: [SF; 3], x: [SF; 3], k: [SF; 3], out: [SF; 3], cr: [SF; 4]) -> [SF; 5] {
    let qb = [sf(Q & 0xff), sf((Q >> 8) & 0xff), sf(Q >> 16)];
    let c256 = sf(256);
    let m0 = z[0] * x[0] - qb[0] * k[0] - out[0] - c256 * cr[0];
    let m1 = z[0] * x[1] + z[1] * x[0] - qb[0] * k[1] - qb[1] * k[0] - out[1] + cr[0] - c256 * cr[1];
    let m2 = z[0] * x[2] + z[1] * x[1] + z[2] * x[0]
        - qb[0] * k[2]
        - qb[1] * k[1]
        - qb[2] * k[0]
        - out[2]
        + cr[1]
        - c256 * cr[2];
    let m3 = z[1] * x[2] + z[2] * x[1] - qb[1] * k[2] - qb[2] * k[1] + cr[2] - c256 * cr[3];
    let m4 = z[2] * x[2] - qb[2] * k[2] + cr[3];
    [m0, m1, m2, m3, m4]
}

/// `R(point-values)` as a β-random-linear-combination of the stage's relations.
fn combine(kind: Kind, v: &[SF], beta: SF) -> SF {
    let one = SF::one();
    let q = sf(Q);
    match kind {
        Kind::Butterfly => {
            let in0 = recompose(v, B_IN0);
            let in1 = recompose(v, B_IN1);
            let out0 = recompose(v, B_OUT0);
            let diff = recompose(v, B_DIFF);
            let reduce = v[B_REDUCE];
            let borrow = v[B_BORROW];
            let add = in0 + in1 - out0 - q * reduce;
            let sub = in0 + q * borrow - in1 - diff;
            let red_bit = reduce * (one - reduce);
            let bor_bit = borrow * (one - borrow);
            let z = [v[B_TW], v[B_TW + 1], v[B_TW + 2]];
            let x = [v[B_DIFF], v[B_DIFF + 1], v[B_DIFF + 2]];
            let k = [v[B_QUOT], v[B_QUOT + 1], v[B_QUOT + 2]];
            let out = [v[B_OUT1], v[B_OUT1 + 1], v[B_OUT1 + 2]];
            let cr = [v[B_CARRY], v[B_CARRY + 1], v[B_CARRY + 2], v[B_CARRY + 3]];
            let m = mul_relations(z, x, k, out, cr);
            let terms = [add, sub, red_bit, bor_bit, m[0], m[1], m[2], m[3], m[4]];
            rlc(&terms, beta)
        }
        Kind::Scaling => {
            let z = split3(N_INV).map(sf);
            let x = [v[S_IN0], v[S_IN0 + 1], v[S_IN0 + 2]];
            let k = [v[S_QUOT], v[S_QUOT + 1], v[S_QUOT + 2]];
            let out = [v[S_OUT1], v[S_OUT1 + 1], v[S_OUT1 + 2]];
            let cr = [v[S_CARRY], v[S_CARRY + 1], v[S_CARRY + 2], v[S_CARRY + 3]];
            let m = mul_relations(z, x, k, out, cr);
            rlc(&m, beta)
        }
    }
}

#[inline]
fn rlc(terms: &[SF], beta: SF) -> SF {
    let mut acc = SF::zero();
    for t in terms.iter().rev() {
        acc = acc * beta + *t;
    }
    acc
}

// ── The zero-check oracle: g(x) = eq(z,x)·R(x), claimed sum 0 ────────────────

#[derive(Clone)]
struct ZeroCheck {
    comps: Vec<Vec<SF>>,
    eq: Vec<SF>,
    n: usize,
    kind: Kind,
    beta: SF,
}

impl ZeroCheck {
    fn new(comps: Vec<Vec<SF>>, z: &[SF], kind: Kind, beta: SF) -> Self {
        let n = z.len();
        debug_assert_eq!(comps[0].len(), 1 << n);
        ZeroCheck {
            comps,
            eq: eq_table(z),
            n,
            kind,
            beta,
        }
    }

    /// `Σ_x eq(z,x)·R(x)` over the full current hypercube (0 for honest data).
    fn full_sum(&self) -> SF {
        let len = self.eq.len();
        let mut cvals = vec![SF::zero(); self.comps.len()];
        let mut acc = SF::zero();
        for x in 0..len {
            for (c, comp) in self.comps.iter().enumerate() {
                cvals[c] = comp[x];
            }
            acc += self.eq[x] * combine(self.kind, &cvals, self.beta);
        }
        acc
    }
}

impl MultivariatePolyOracle for ZeroCheck {
    fn n_variables(&self) -> usize {
        self.n
    }

    fn sum_as_poly_in_first_variable(&self, _claim: SF) -> UnivariatePoly<SF> {
        // g has degree ≤ 3 in x_0 (eq: 1, R: ≤ 2) → 4 evaluation points suffice.
        let half = self.eq.len() / 2;
        let ts = [sf(0), sf(1), sf(2), sf(3)];
        let mut ys = [SF::zero(); 4];
        let mut cvals = vec![SF::zero(); self.comps.len()];
        for (ti, &t) in ts.iter().enumerate() {
            let mut acc = SF::zero();
            for y in 0..half {
                for (c, comp) in self.comps.iter().enumerate() {
                    cvals[c] = comp[y] + t * (comp[half + y] - comp[y]);
                }
                let eqv = self.eq[y] + t * (self.eq[half + y] - self.eq[y]);
                acc += eqv * combine(self.kind, &cvals, self.beta);
            }
            ys[ti] = acc;
        }
        UnivariatePoly::interpolate_lagrange(&ts, &ys)
    }

    fn fix_first_variable(mut self, challenge: SF) -> Self {
        let half = self.eq.len() / 2;
        for comp in &mut self.comps {
            for y in 0..half {
                comp[y] = comp[y] + challenge * (comp[half + y] - comp[y]);
            }
            comp.truncate(half);
        }
        for y in 0..half {
            self.eq[y] = self.eq[y] + challenge * (self.eq[half + y] - self.eq[y]);
        }
        self.eq.truncate(half);
        self.n -= 1;
        self
    }
}

/// `eq(z, x)` over the hypercube, index bits MSB-first (matches
/// `Mle::eval_at_point` / `fix_first_variable` splitting the first variable off
/// the high index bit).
fn eq_table(z: &[SF]) -> Vec<SF> {
    let n = z.len();
    (0..(1usize << n))
        .map(|idx| {
            let mut acc = SF::one();
            for (i, &zi) in z.iter().enumerate() {
                let bit = (idx >> (n - 1 - i)) & 1;
                acc *= if bit == 1 { zi } else { SF::one() - zi };
            }
            acc
        })
        .collect()
}

/// Multilinear eval, `point[0]` = MSB (mirrors keccak `gkr_offload_spike`).
fn ml_eval(evals: &[SF], point: &[SF]) -> SF {
    match point {
        [] => evals[0],
        [p0, rest @ ..] => {
            let (lhs, rhs) = evals.split_at(evals.len() / 2);
            let le = ml_eval(lhs, rest);
            let re = ml_eval(rhs, rest);
            *p0 * (re - le) + le
        }
    }
}

// ── Layer prove / verify ─────────────────────────────────────────────────────

/// A proved layer: the sumcheck proof + the challenges + z/β so the verifier can
/// tie the final claim back to the native witness MLEs.
struct LayerProof {
    proof: SumcheckProof,
    z: Vec<SF>,
    beta: SF,
    lambda: SF,
    kind: Kind,
}

/// Prove one layer (all 30 polys batched). `comps_per_poly` are the native MLEs
/// (kept for the tie-back). `n_vars` = 7 (butterfly) or 8 (scaling).
fn prove_layer(
    comps_per_poly: &[Vec<Vec<SF>>],
    n_vars: usize,
    kind: Kind,
    channel: &mut impl Channel,
) -> LayerProof {
    let z = channel.draw_secure_felts(n_vars);
    let beta = channel.draw_secure_felt();
    let oracles: Vec<ZeroCheck> = comps_per_poly
        .iter()
        .map(|comps| ZeroCheck::new(comps.clone(), &z, kind, beta))
        .collect();
    // Prover claims the ACTUAL per-poly sum (0 for honest data, ≠0 if forged).
    // The verifier independently expects 0, so a forged witness is rejected at
    // the top round without the prover ever panicking on an internal assert.
    let claims: Vec<SF> = oracles.iter().map(ZeroCheck::full_sum).collect();
    let lambda = channel.draw_secure_felt();
    let (proof, _assignment, _oracles, _claimed) =
        prove_batch(claims, oracles, lambda, channel);
    LayerProof {
        proof,
        z,
        beta,
        lambda,
        kind,
    }
}

#[derive(Debug)]
enum VerifyError {
    Sumcheck,
    TieBack,
}

/// Verify one layer against the honest expected sum (0) and tie the final claim
/// back to the native witness MLEs.
fn verify_layer(
    layer: &LayerProof,
    comps_per_poly: &[Vec<Vec<SF>>],
    n_vars: usize,
    channel: &mut impl Channel,
) -> Result<(), VerifyError> {
    // Re-draw the same transcript values to stay in sync with the prover.
    let z = channel.draw_secure_felts(n_vars);
    let beta = channel.draw_secure_felt();
    let lambda = channel.draw_secure_felt();
    // (In the spike these equal the prover's; assert to catch desync.)
    debug_assert_eq!(z, layer.z);
    debug_assert_eq!(beta, layer.beta);
    debug_assert_eq!(lambda, layer.lambda);

    // Honest expected combined claim = Σ_i λ^i · 0 = 0.
    let (assignment, claimed_eval) = match partially_verify(SF::zero(), &layer.proof, channel) {
        Ok(v) => v,
        Err(_) => return Err(VerifyError::Sumcheck),
    };

    // Tie-back: reconstruct h(assignment) = Σ_i λ^i eq(z,r)·R_i(r) from the
    // native MLEs and check it equals the sumcheck's final claim. In production
    // this is an MleEval tie-back to committed quotient/carry columns.
    let eq_r = eq(&z, &assignment);
    let mut recon = SF::zero();
    let mut lambda_pow = SF::one();
    for comps in comps_per_poly {
        let cvals: Vec<SF> = comps.iter().map(|c| ml_eval(c, &assignment)).collect();
        recon += lambda_pow * eq_r * combine(layer.kind, &cvals, beta);
        lambda_pow *= lambda;
    }
    if recon != claimed_eval {
        return Err(VerifyError::TieBack);
    }
    Ok(())
}

// ── Full-pipeline driver (all 9 layers, one shared transcript) ───────────────

/// One layer's native MLEs: `[poly] -> [component] -> evals over the hypercube`.
type LayerComps = Vec<Vec<Vec<SF>>>;

/// Build the per-poly MLEs for every layer from a witness.
fn build_layers(w: &InttWitness) -> (LayerComps, [LayerComps; STAGES]) {
    // stage layers: [stage] -> [poly] -> comps
    let stage_layers: [LayerComps; STAGES] = core::array::from_fn(|s| {
        w.stages
            .iter()
            .map(|poly| butterfly_comps(&poly[s]))
            .collect()
    });
    let scale_layer: Vec<Vec<Vec<SF>>> = w.scaling.iter().map(|rows| scaling_comps(rows)).collect();
    (scale_layer, stage_layers)
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::channel::Blake2sChannel;

    /// Deterministic in-range `a_hat` matrix (a real ML-DSA sample shape: 30
    /// polys × 256 coeffs, each in [0, Q)). A fixed LCG keeps the test
    /// reproducible without an RNG dependency.
    fn sample_a_hat() -> Vec<[u32; N]> {
        let mut s: u64 = 0x1234_5678_9abc_def0;
        let mut next = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((s >> 33) as u32) % Q
        };
        (0..MATRIX_POLYS).map(|_| core::array::from_fn(|_| next())).collect()
    }

    fn prove_all(
        scale: &[Vec<Vec<SF>>],
        stages: &[Vec<Vec<Vec<SF>>>; STAGES],
        channel: &mut Blake2sChannel,
    ) -> ([LayerProof; STAGES], LayerProof) {
        let stage_proofs: [LayerProof; STAGES] = core::array::from_fn(|s| {
            prove_layer(&stages[s], 7, Kind::Butterfly, channel)
        });
        let scale_proof = prove_layer(scale, 8, Kind::Scaling, channel);
        (stage_proofs, scale_proof)
    }

    #[test]
    fn positive_full_pipeline_proves_and_verifies() {
        let a_hat = sample_a_hat();
        let w = gen_witness(&a_hat);
        let (scale, stages) = build_layers(&w);

        let mut prover_ch = Blake2sChannel::default();
        let (stage_proofs, scale_proof) = prove_all(&scale, &stages, &mut prover_ch);

        let mut verifier_ch = Blake2sChannel::default();
        for (s, lp) in stage_proofs.iter().enumerate() {
            verify_layer(lp, &stages[s], 7, &mut verifier_ch)
                .unwrap_or_else(|e| panic!("stage {s} rejected honest proof: {e:?}"));
        }
        verify_layer(&scale_proof, &scale, 8, &mut verifier_ch)
            .expect("scaling layer rejected honest proof");
    }

    #[test]
    fn negative_forged_input_limb_rejected() {
        let a_hat = sample_a_hat();
        let w = gen_witness(&a_hat);
        let (_scale, stages) = build_layers(&w);

        // Tamper one limb of one A-hat cell in the stage-0 input MLE.
        let mut tampered = stages[0].clone();
        tampered[0][B_IN0][0] += SF::one();

        let mut prover_ch = Blake2sChannel::default();
        let lp = prove_layer(&tampered, 7, Kind::Butterfly, &mut prover_ch);

        let mut verifier_ch = Blake2sChannel::default();
        // Verifier uses the tampered MLEs too; rejection must come from the
        // sumcheck (top claim ≠ 0), i.e. it is not maskable by the tie-back.
        let res = verify_layer(&lp, &tampered, 7, &mut verifier_ch);
        assert!(
            matches!(res, Err(VerifyError::Sumcheck)),
            "forged input limb must be rejected by the sumcheck, got {res:?}"
        );
    }

    #[test]
    fn negative_forged_quotient_rejected() {
        let a_hat = sample_a_hat();
        let w = gen_witness(&a_hat);
        let (_scale, stages) = build_layers(&w);

        // Tamper one quotient limb of one butterfly (stage 3) — the mod-q
        // integrity core.
        let mut tampered = stages[3].clone();
        tampered[7][B_QUOT][5] += SF::one();

        let mut prover_ch = Blake2sChannel::default();
        let lp = prove_layer(&tampered, 7, Kind::Butterfly, &mut prover_ch);

        let mut verifier_ch = Blake2sChannel::default();
        let res = verify_layer(&lp, &tampered, 7, &mut verifier_ch);
        assert!(
            matches!(res, Err(VerifyError::Sumcheck)),
            "forged quotient must be rejected by the sumcheck, got {res:?}"
        );
    }

    /// eq_table matches the stwo `eq`/`ml_eval` MSB-first convention.
    #[test]
    fn eq_table_matches_convention() {
        let mut ch = Blake2sChannel::default();
        let z = ch.draw_secure_felts(7);
        let table = eq_table(&z);
        // eq(z, e_idx) picks out table[idx] under ml_eval.
        for idx in [0usize, 1, 5, 63, 100, 127] {
            let unit: Vec<SF> = (0..128)
                .map(|i| if i == idx { SF::one() } else { SF::zero() })
                .collect();
            // ml_eval(unit, z) = table[idx]  (the multilinear extension of a
            // hypercube indicator evaluated at z is eq(z, idx)).
            assert_eq!(ml_eval(&unit, &z), table[idx], "idx={idx}");
        }
    }

    // ── Measurement harness: census + prover time + payload ──────────────────
    //
    // Run with:
    //   RAYON_NUM_THREADS=1 cargo test -p stwo-mldsa --release \
    //     ntt_sumcheck_spike::tests::measure -- --nocapture --ignored
    #[test]
    #[ignore = "measurement harness, run explicitly with --nocapture"]
    fn measure() {
        use std::time::Instant;

        let a_hat = sample_a_hat();
        let w = gen_witness(&a_hat);
        let (scale, stages) = build_layers(&w);

        // Warm one honest verify so we know the pipeline is sound before timing.
        {
            let mut pc = Blake2sChannel::default();
            let (sp, scp) = prove_all(&scale, &stages, &mut pc);
            let mut vc = Blake2sChannel::default();
            for (s, lp) in sp.iter().enumerate() {
                verify_layer(lp, &stages[s], 7, &mut vc).unwrap();
            }
            verify_layer(&scp, &scale, 8, &mut vc).unwrap();
        }

        // Prover time (30 polys batched, all 9 layers), best of 5.
        let mut best = f64::INFINITY;
        let mut coeff_count = 0usize;
        for _ in 0..5 {
            let mut pc = Blake2sChannel::default();
            let t = Instant::now();
            let (sp, scp) = prove_all(&scale, &stages, &mut pc);
            let ms = t.elapsed().as_secs_f64() * 1e3;
            best = best.min(ms);
            coeff_count = sp
                .iter()
                .map(|lp| lp.proof.round_polys.iter().map(|p| p.len()).sum::<usize>())
                .sum::<usize>()
                + scp.proof.round_polys.iter().map(|p| p.len()).sum::<usize>();
        }
        let payload_bytes = coeff_count * 16; // QM31 = 4×M31 = 16 bytes

        // Commitment census (arithmetic).
        let bf_total = MATRIX_POLYS * STAGES * HALF_N; // 30·8·128 = 30,720
        let scale_total = MATRIX_POLYS * N; // 30·256 = 7,680
        // Tier A: spec-literal quotient(3)+carry(4) = 7 columns/row.
        let tier_a = bf_total * 7 + scale_total * 7;
        // Tier B: all free non-derivable arithmetic witnesses, ranges via
        // amortized lookups. Butterfly: out0(3)+out1(3)+diff(3)+quot(3)+
        // carry(4)+reduce(1)+borrow(1)=18. Scaling: out1(3)+quot(3)+carry(4)=10.
        let tier_b = bf_total * 18 + scale_total * 10;
        // Tier C: + canonical range slacks (matches AIR column semantics minus
        // the virtualized in0/in1). Butterfly 18+out0/diff/out1/quot slacks(12)
        // = 30. Scaling 10+out1/quot slacks(6)=16.
        let tier_c = bf_total * 30 + scale_total * 16;
        // Endpoints: stage-0 a_hat input limbs (output = scaling out1, counted
        // in the scaling layer above).
        let endpoints = MATRIX_POLYS * N * 3; // 23,040
        let current = 6_030_000f64;

        println!("\n===== WO-Q10.3 INTT sumcheck spike — measured =====");
        println!("polys={MATRIX_POLYS} stages={STAGES} butterflies/stage={HALF_N}");
        println!("--- prover (30-poly batched, RAYON_NUM_THREADS=1, release) ---");
        println!("  best of 5:            {best:.2} ms   (gate ≤ 500 ms)");
        println!("--- payload (round-poly coeffs × 16 B) ---");
        println!("  coeffs={coeff_count}  bytes={payload_bytes}  ({:.2} KB, gate ≤ 100 KB)", payload_bytes as f64 / 1024.0);
        println!("--- commitment census (cells), current AIR = 6.03 M ---");
        for (name, cells) in [
            ("Tier A (quot+carry only)", tier_a + endpoints),
            ("Tier B (arith core, lookup ranges)", tier_b + endpoints),
            ("Tier C (with canonical slacks)", tier_c + endpoints),
        ] {
            let cells = cells as f64;
            println!(
                "  {name:<38} {cells:>12.0} cells   {:.1}× reduction",
                current / cells
            );
        }
        println!("  (endpoints = {endpoints} input-limb cells, included above)");
        println!("--- gate verdict ---");
        let cells_b = (tier_b + endpoints) as f64;
        let go_cells = cells_b <= 3_000_000.0;
        let go_payload = payload_bytes as f64 <= 100_000.0;
        let go_time = best <= 500.0;
        println!("  cells ≤ 3.0M : {go_cells} ({cells_b:.0})");
        println!("  payload ≤ 100KB: {go_payload} ({payload_bytes} B)");
        println!("  prover ≤ 500ms : {go_time} ({best:.2} ms)");
        println!("  OVERALL: {}", if go_cells && go_payload && go_time { "GO" } else { "NO-GO" });
        println!("====================================================\n");
    }
}
