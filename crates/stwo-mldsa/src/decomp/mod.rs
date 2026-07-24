//! `mldsa_decomp` — FIPS 204 [DECOMP] + [HINT] over each `w_i` coefficient.
//!
//! One AIR row holds a **w1Encode byte pair**: the two consecutive coefficients
//! `(2p, 2p+1)` of a `w_i` poly, `p ∈ [0, N/2)`, `i ∈ [k]`. `k·N/2 = 768` active
//! rows. Packing two coeffs per row keeps the `w1Encode` byte emission fully
//! within a single row — no cross-row mask (which would risk the M4 `+2`
//! composition-bound trap; see [`crate::coeffs`]).
//!
//! ## Per sub-lane `ℓ ∈ {lo, hi}` (a single `w_i` coefficient `w`), the FIPS obligations
//!
//! Decompose (Alg 36) / UseHint (Alg 39), pinned against
//! [`crate::reference::decompose`] as the semantic oracle:
//!
//! 1. **[DECOMP] reconstruction** — `w1·α + w0 = w − wrap_k·q`, `α = 2γ2`,
//!    `wrap_k ∈ {0,1}` (the FIPS borderline `r−r0 = q−1` wrap; verified over ℤ
//!    that `w1·α+w0 − w ∈ {0, −q}`). `w1 ∈ [0,16)` (rc4), `w0 ∈ (−γ2, γ2]`
//!    exact two-sided (M4 z-norm pattern: `a = w0+γ2−1, b = γ2−w0`, both
//!    `∈ [0,2γ2)` via 13+7 split).
//! 2. **[HINT] sign** — `s0 = [w0 > 0] ∈ {0,1}`, bound to `w0`'s two-sided
//!    decomposition so a lying `s0` desyncs the range (see C-DECOMP-S0).
//! 3. **[HINT] UseHint** — `w1' = (w1 + h·(2·s0−1)) mod 16`, `h ∈ {0,1}`.
//!    Encoded as `w1' = w1 + h·(2·s0−1) + wrap16·16` with `wrap16 ∈ {−1,0,1}`
//!    chosen so `w1' ∈ [0,16)` (rc4). (`w1+delta ∈ [−1,16]`.)
//! 4. **[HINT] Σh ≤ ω** — a running accumulator `hint_acc' = hint_acc + h_lo +
//!    h_hi`; the final active row's accumulator is range-checked `≤ ω = 55`
//!    (rc8), enforcing `Σ_i Σ_m h ≤ ω`.
//! 5. **w-binding** — each sub-lane `w` is a USE of the coeffs W-group cell
//!    (`WCellRelation(w_bind_id, w)`), `w_bind_id = i·N + m`. Yielded by coeffs.
//! 6. **w1Encode emission** — `byte = w1'_lo + 16·w1'_hi` yielded into
//!    `HashIoRelation(STREAM_ID_CTILDE_ABSORB, byte_pos, byte)` (768 bytes).
//!
//! ## Degree worksheet — EVERY constraint ≤ 2.
//! | site | expr | degree |
//! |------|------|--------|
//! | boolean `x(1−x)` (enabler, hint, wrap_k, s0) | | 2 |
//! | wrap16 ternary `w16(w16−1)(w16+1)` | — LOOKUP (`w16+1 ∈ {0,1,2}`) | 1 |
//! | decomp recon `w1·α + w0 − w + wrap_k·q` | linear in cells | 1 |
//! | s0 · w0 sign link (see C-DECOMP-S0) | `s0·(…)` | 2 |
//! | UseHint `w1' − (w1 + h·(2s0−1) + 16·w16)` | `h·s0` deg 2 | 2 |
//! | hint_acc transition (interaction `[-1,0]`) | linear | 1 |
//! | final base/interaction hint_acc tie | `is_last·(hint_acc−acc_cur)` | 2 |
//! | w0 / w1 / w1' / byte / hint_acc rc uses | linear | 1 |
//! | w-binding use / w1Encode yield | linear | 1 |
//! Every base constraint is ≤ 2; the LogUp columns batch [`LOGUP_BATCH`] = 4
//! fractions (degree-1 denominators ⇒ batched constraint degree 5), so the
//! bound is log_size + 2 (D ≤ 5, engine composition split ≥ 2).

#![allow(clippy::needless_range_loop)]

pub mod proof;
pub mod relations;
pub mod tables;

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    INTERACTION_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::constants::{GAMMA2, K, N, OMEGA, Q};
use crate::witness::MlDsaWitness;
use relations::DecompRelations;
use tables::{RcKind, RcUses};

/// `α = 2·γ2`, the decomposition modulus.
pub const ALPHA: i64 = 2 * GAMMA2 as i64;
/// Number of `w1` values = `(q−1)/α = 16`.
pub const W1_MODULUS: i64 = 16;
/// Active rows: `k·N/2` byte pairs.
pub const N_PAIRS: usize = K * N / 2; // 768

// --- Base column indices (two sub-lanes ℓ ∈ {0=lo, 1=hi}) ---------------------
// Per sub-lane: w, w1, w0, hint, wrap_k, s0, w1p, wrap16, a_hi, b_hi, sign_val,
// sign_hi.
const PER_LANE: usize = 12;
const L_W: usize = 0;
const L_W1: usize = 1;
const L_W0: usize = 2;
const L_HINT: usize = 3;
const L_WRAPK: usize = 4;
const L_S0: usize = 5;
const L_W1P: usize = 6;
const L_WRAP16: usize = 7;
const L_A_HI: usize = 8;
const L_B_HI: usize = 9;
/// `sign_val = s0·(w0−1) + (1−s0)·(−w0) ∈ [0, γ2−1]`, witnessed so the rc value
/// stays degree 1 (a degree-2 lookup value would push the logup constraint to
/// degree 3 and break the +1 bound — the M4 trap). Pinned by C-DECOMP-S0.
const L_SIGN_VAL: usize = 10;
/// 7-bit hi of `sign_val` (13+7 split).
const L_SIGN_HI: usize = 11;

const COL_ENABLER: usize = 0;
const COL_LANE0: usize = 1; // 10 cols
const COL_LANE1: usize = COL_LANE0 + PER_LANE; // 11
const COL_HINT_ACC: usize = COL_LANE1 + PER_LANE; // 21
/// Total base columns.
pub const N_BASE_COLS: usize = COL_HINT_ACC + 1; // 22

/// Logup entries per row (batched [`LOGUP_BATCH`] per interaction column): 2 lanes
/// × (rc4 w1, rc13 a_lo, rc13 b_lo, rc7 a_hi, rc7 b_hi, rc13 sign_lo, rc7 sign_hi,
/// rc4 w16+1, rc4 w1', wcell use) plus 1 byte yield plus 2 hint_acc rc8 uses (Σh,
/// ω−Σh; final row only) = 2·10 + 1 + 2 = 23.
pub const N_LOGUP_ENTRIES: usize = 2 * 10 + 1 + 2;
pub const LOGUP_BATCH: usize = 4;
pub const N_LOGUP_COLS: usize = N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
const N_ACC_COORD_COLS: usize = SECURE_EXTENSION_DEGREE; // hint_acc is a QM31 running sum
pub const N_INTERACTION_COLS: usize = N_ACC_COORD_COLS + SECURE_EXTENSION_DEGREE * N_LOGUP_COLS;

fn pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_decomp_{name}"),
    }
}

/// Preprocessed column ids in commit order.
pub fn decomp_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    vec![
        pre_id("enabler_pre"),
        pre_id("start"),
        pre_id("w_bind_id_lo"),
        pre_id("w_bind_id_hi"),
        pre_id("byte_pos"),
        pre_id("is_last"),
    ]
}

/// The flat row → (i, p) schedule (active rows contiguous from 0).
fn row_schedule() -> Vec<(usize, usize)> {
    let mut out = Vec::with_capacity(N_PAIRS);
    for i in 0..K {
        for p in 0..(N / 2) {
            out.push((i, p));
        }
    }
    out
}

// =============================================================================
// Preprocessed trace.
// =============================================================================

pub fn gen_decomp_preprocessed(log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();

    let mut enabler = vec![m31(0); rows];
    let mut start = vec![m31(0); rows];
    let mut wbid_lo = vec![m31(0); rows];
    let mut wbid_hi = vec![m31(0); rows];
    let mut byte_pos = vec![m31(0); rows];
    let mut is_last = vec![m31(0); rows];

    for (row, &(i, p)) in sched.iter().enumerate() {
        enabler[row] = m31(1);
        let m_lo = 2 * p;
        let m_hi = 2 * p + 1;
        wbid_lo[row] = m31((i * N + m_lo) as u32);
        wbid_hi[row] = m31((i * N + m_hi) as u32);
        byte_pos[row] = m31(row as u32);
    }
    start[0] = m31(1); // coset row 0 zeroes the accumulator's wraparound acc_prev.
    if !sched.is_empty() {
        is_last[sched.len() - 1] = m31(1);
    }

    vec![enabler, start, wbid_lo, wbid_hi, byte_pos, is_last]
        .into_iter()
        .map(|v| col_eval(log_size, v))
        .collect()
}

// =============================================================================
// Per-lane witness readout.
// =============================================================================

/// The decompose/hint values for one `w_i` coefficient `(i, m)`.
struct LaneVals {
    w: i64,
    w1: i64,
    w0: i64,
    hint: i64,
    wrap_k: i64, // ∈ {0,1}: w1·α + w0 = w − wrap_k·q
    s0: i64,     // [w0 > 0]
    w1p: i64,    // UseHint output ∈ [0,16)
    wrap16: i64, // ∈ {−1,0,1}: w1p = w1 + h·(2s0−1) + 16·wrap16
}

fn lane_vals(witness: &MlDsaWitness, i: usize, m: usize) -> LaneVals {
    let w = witness.rows[i].w[m] as i64;
    // `decomp.w1` is the reference's `trace.w1` = w1' (POST-UseHint). The pre-hint
    // high bits `w1 = Decompose(w).0` are recomputed from the reference oracle.
    let (w1_pre, w0_ref) = crate::reference::decompose::decompose(w as u32);
    let w1 = w1_pre as i64;
    let w0 = witness.decomp.w0[i][m] as i64;
    debug_assert_eq!(w0, w0_ref as i64, "w0 matches reference decompose");
    let hint = witness.decomp.hint[i][m] as i64;
    let w1p = witness.decomp.w1[i][m] as i64; // = UseHint(h, w)
    let wrap_k = (w1 * ALPHA + w0 - w) / -(Q as i64); // 0 or 1
    debug_assert!(wrap_k == 0 || wrap_k == 1, "wrap_k∈{{0,1}} got {wrap_k}");
    debug_assert_eq!(w1 * ALPHA + w0 - w + wrap_k * Q as i64, 0);
    let s0 = i64::from(w0 > 0);
    let delta = hint * (2 * s0 - 1);
    let wrap16 = (w1p - (w1 + delta)) / W1_MODULUS;
    debug_assert!((-1..=1).contains(&wrap16), "wrap16∈{{-1,0,1}} got {wrap16}");
    debug_assert_eq!(w1 + delta + W1_MODULUS * wrap16, w1p);
    LaneVals {
        w,
        w1,
        w0,
        hint,
        wrap_k,
        s0,
        w1p,
        wrap16,
    }
}

// =============================================================================
// Base trace.
// =============================================================================

pub fn gen_decomp_base_trace(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let mut cols: Vec<Vec<M31>> = (0..N_BASE_COLS).map(|_| vec![m31(0); rows]).collect();

    let gamma2 = GAMMA2 as i64;
    let mut hint_acc = 0i64;
    for (row, &(i, p)) in sched.iter().enumerate() {
        cols[COL_ENABLER][row] = m31(1);
        for (lane, &m) in [2 * p, 2 * p + 1].iter().enumerate() {
            let base = COL_LANE0 + lane * PER_LANE;
            let v = lane_vals(witness, i, m);
            cols[base + L_W][row] = m31(v.w as u32);
            cols[base + L_W1][row] = m31(v.w1 as u32);
            cols[base + L_W0][row] = enc_signed(v.w0);
            cols[base + L_HINT][row] = m31(v.hint as u32);
            cols[base + L_WRAPK][row] = m31(v.wrap_k as u32);
            cols[base + L_S0][row] = m31(v.s0 as u32);
            cols[base + L_W1P][row] = m31(v.w1p as u32);
            cols[base + L_WRAP16][row] = enc_signed(v.wrap16);
            // w0 two-sided: a = w0 + γ2 − 1 ∈ [0, 2γ2), b = γ2 − w0 ∈ [0, 2γ2).
            let a = v.w0 + gamma2 - 1;
            let b = gamma2 - v.w0;
            cols[base + L_A_HI][row] = m31((a >> 13) as u32);
            cols[base + L_B_HI][row] = m31((b >> 13) as u32);
            // sign_val ∈ [0, γ2−1] pins s0 = [w0 > 0] (13+7 split).
            let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
            debug_assert!((0..gamma2).contains(&sign_val));
            cols[base + L_SIGN_VAL][row] = m31(sign_val as u32);
            cols[base + L_SIGN_HI][row] = m31((sign_val >> 13) as u32);
            hint_acc += v.hint;
        }
        cols[COL_HINT_ACC][row] = m31(hint_acc as u32);
    }

    cols.into_iter().map(|v| col_eval(log_size, v)).collect()
}

/// Centered M31 encoding of a small signed value.
fn enc_signed(v: i64) -> M31 {
    const P: i64 = (1 << 31) - 1;
    m31((((v % P) + P) % P) as u32)
}

// =============================================================================
// The AIR.
// =============================================================================

#[derive(Clone)]
pub struct DecompEval {
    pub log_size: u32,
    /// The HashIo stream id the 768 `w1Encode` bytes are yielded into. Per
    /// instance under a SHARED keccak relation set: `stream_base +`
    /// [`STREAM_ID_CTILDE_ABSORB`] (the standalone default is the constant).
    pub ct_stream: u32,
    pub relations: DecompRelations,
}

impl FrameworkEval for DecompEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every base constraint ≤ 2; LogUp batch 4 over degree-1 denominators
        // gives constraint degree 5, covered by +2 (D ≤ 5). The hint_acc
        // `[-1,0]` interaction mask is safe: the engine's uniform composition
        // split already evaluates every component at log_size + split.
        self.log_size + 2
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler_pre = eval.get_preprocessed_column(pre_id("enabler_pre"));
        let start = eval.get_preprocessed_column(pre_id("start"));
        let wbid_lo = eval.get_preprocessed_column(pre_id("w_bind_id_lo"));
        let wbid_hi = eval.get_preprocessed_column(pre_id("w_bind_id_hi"));
        let byte_pos = eval.get_preprocessed_column(pre_id("byte_pos"));
        let is_last = eval.get_preprocessed_column(pre_id("is_last"));

        let enabler = eval.next_trace_mask();
        // Two lanes' worth of base columns.
        let lanes: Vec<Vec<E::F>> = (0..2)
            .map(|_| (0..PER_LANE).map(|_| eval.next_trace_mask()).collect())
            .collect();
        let hint_acc = eval.next_trace_mask();

        // hint_acc previous-row value via interaction mask (running sum).
        let acc_coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(acc_coords.each_ref().map(|p| p[0].clone()));
        let acc_cur = E::combine_ef(acc_coords.each_ref().map(|p| p[1].clone()));

        let one = E::F::from(M31::one());
        let alpha = E::F::from(m31(ALPHA as u32));
        let q = E::F::from(m31(Q));
        let gamma2 = E::F::from(m31(GAMMA2));
        let two_pow_13 = E::F::from(m31(1 << 13));
        let sixteen = E::F::from(m31(16));

        // C0: enabler boolean.
        eval.add_constraint(enabler.clone() * (one.clone() - enabler.clone()));

        let wbids = [wbid_lo, wbid_hi];
        let mut hint_sum = E::EF::from(E::F::from(m31(0)));

        for lane in 0..2 {
            let c = &lanes[lane];
            let w = c[L_W].clone();
            let w1 = c[L_W1].clone();
            let w0 = c[L_W0].clone();
            let hint = c[L_HINT].clone();
            let wrap_k = c[L_WRAPK].clone();
            let s0 = c[L_S0].clone();
            let w1p = c[L_W1P].clone();
            let wrap16 = c[L_WRAP16].clone();
            let a_hi = c[L_A_HI].clone();
            let b_hi = c[L_B_HI].clone();
            let sign_val = c[L_SIGN_VAL].clone();
            let sign_hi = c[L_SIGN_HI].clone();

            // C1: booleans (hint, wrap_k, s0) — ungated (padding = 0 ⇒ satisfied).
            eval.add_constraint(hint.clone() * (one.clone() - hint.clone()));
            eval.add_constraint(wrap_k.clone() * (one.clone() - wrap_k.clone()));
            eval.add_constraint(s0.clone() * (one.clone() - s0.clone()));

            // C2: [DECOMP] reconstruction  w1·α + w0 − w + wrap_k·q == 0.
            eval.add_constraint(
                w1.clone() * alpha.clone() + w0.clone() - w.clone() + wrap_k.clone() * q.clone(),
            );

            // C3: w1 ∈ [0,16) (rc4).
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc4,
                enabler_pre.clone(),
                core::slice::from_ref(&w1),
            ));

            // C4: w0 ∈ (−γ2, γ2] exact two-sided. a = w0+γ2−1, b = γ2−w0, both
            // ∈ [0,2γ2) via 13+7 split. a,b ≥ 0 ⇔ w0 ∈ [−γ2+1, γ2] EXACTLY.
            let a = w0.clone() + gamma2.clone() - one.clone();
            let b = gamma2.clone() - w0.clone();
            let a_lo = a - two_pow_13.clone() * a_hi.clone();
            let b_lo = b - two_pow_13.clone() * b_hi.clone();
            for expr in [&a_lo, &b_lo] {
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.rc13,
                    enabler_pre.clone(),
                    core::slice::from_ref(expr),
                ));
            }
            for hi in [&a_hi, &b_hi] {
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.rc7,
                    enabler_pre.clone(),
                    core::slice::from_ref(hi),
                ));
            }

            // C-DECOMP-S0: pin s0 = [w0 > 0] (degree 2, no new table).
            //   sign_val = s0·(w0 − 1) + (1 − s0)·(−w0)
            // Honest s0=1 (w0≥1) ⇒ sign_val = w0−1 ∈ [0, γ2−1];
            // honest s0=0 (w0≤0) ⇒ sign_val = −w0 ∈ [0, γ2−1].
            // A lying s0 makes sign_val negative (e.g. w0=5,s0=0 ⇒ −5), which the
            // [0,2γ2) range-check (13+7) rejects. `w0` is already pinned to
            // [−γ2+1, γ2] by the a/b split, so the branch bound is exact.
            // Pin the witnessed sign_val to the degree-2 selector expression
            // (this constraint is degree 2; the lookup below reads the deg-1 cell).
            eval.add_constraint(
                sign_val.clone()
                    - (s0.clone() * (w0.clone() - one.clone())
                        + (one.clone() - s0.clone()) * (E::F::from(m31(0)) - w0.clone())),
            );
            let sign_lo = sign_val - two_pow_13.clone() * sign_hi.clone();
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc13,
                enabler_pre.clone(),
                core::slice::from_ref(&sign_lo),
            ));
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc7,
                enabler_pre.clone(),
                core::slice::from_ref(&sign_hi),
            ));

            // C5: [HINT] UseHint  w1' = w1 + h·(2s0 − 1) + 16·wrap16.
            let delta_sign = s0.clone() + s0.clone() - one.clone(); // 2s0 − 1
            eval.add_constraint(
                w1p.clone()
                    - (w1.clone() + hint.clone() * delta_sign + sixteen.clone() * wrap16.clone()),
            );

            // C6: wrap16 ∈ {−1,0,1} via `{0,1,2}` membership lookup on (wrap16+1).
            let w16_plus1 = wrap16.clone() + one.clone();
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc4, // rc4 ⊇ {0,1,2}; the value is always < 16
                enabler_pre.clone(),
                core::slice::from_ref(&w16_plus1),
            ));

            // C7: w1' ∈ [0,16) (rc4).
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc4,
                enabler_pre.clone(),
                core::slice::from_ref(&w1p),
            ));

            // C8: w-binding — USE of the coeffs W cell (poly_id·N + m, w).
            let wtuple = [wbids[lane].clone(), w.clone()];
            eval.add_to_relation(RelationEntry::base(
                &self.relations.wcell,
                enabler_pre.clone(),
                &wtuple,
            ));

            hint_sum += E::EF::from(hint);
        }

        // C9: hint accumulator transition  acc_cur = (1−start)·acc_prev + Σ_lane h.
        // `start` (coset row 0) zeroes the `[-1,0]` mask's wraparound acc_prev so
        // the running sum begins at 0. No per-poly reset — Σ_i Σ_m h is the global
        // total. Padding rows carry h=0, so acc stays flat past the last active row.
        let acc_prev_gated = E::EF::from(one.clone() - start.clone()) * acc_prev;
        eval.add_constraint(acc_cur.clone() - (acc_prev_gated + hint_sum));

        // C10: the rc8 lookup reads the base-column copy, so bind that copy to
        // the true interaction running sum on the only row where it is used.
        eval.add_constraint(
            E::EF::from(is_last.clone()) * (E::EF::from(hint_acc.clone()) - acc_cur.clone()),
        );

        // C11: w1Encode byte emission — byte = w1'_lo + 16·w1'_hi, YIELD (+) into
        // HashIo(STREAM_ID_CTILDE_ABSORB, byte_pos, byte). Emitted BEFORE the
        // hint gate to match the interaction generator's fraction order.
        let byte = lanes[0][L_W1P].clone() + sixteen.clone() * lanes[1][L_W1P].clone();
        let stream = E::F::from(m31(self.ct_stream));
        let io_tuple = [stream, byte_pos, byte];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.hash_io,
            enabler_pre.clone(),
            &io_tuple,
        ));

        // C12: final-row hint gate — the last active row's acc = Σ_i Σ_m h is
        // range-checked two-sided into rc8: Σh ∈ [0,256) AND ω−Σh ∈ [0,256).
        // The second use forces Σh ≤ ω = 55 EXACTLY (Σh > ω ⇒ ω−Σh wraps out of
        // [0,256) ⇒ no rc8 row ⇒ imbalance). Gated by is_last (no use elsewhere).
        let omega = E::F::from(m31(OMEGA as u32));
        let acc_room = omega - hint_acc.clone(); // = ω − Σh; ∈ [0,256) ⟺ Σh ≤ ω
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            is_last.clone(),
            core::slice::from_ref(&hint_acc),
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rc8,
            is_last.clone(),
            core::slice::from_ref(&acc_room),
        ));

        let _ = enabler;
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

pub type DecompComponent = FrameworkComponent<DecompEval>;

// =============================================================================
// Interaction trace.
// =============================================================================

/// Output of the decomp interaction generator.
pub struct DecompInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    pub rc_uses: RcUses,
    /// The 768 emitted `w1Encode` bytes, in byte_pos order (for the test balancer
    /// and M6 sponge to consume). `wcell_uses` are the (w_bind_id, w) tuples.
    pub w1_encode_bytes: Vec<u8>,
    /// The (w_bind_id, w) pairs this component consumes (for the test provider).
    pub wcell_uses: Vec<(u32, u32)>,
}

/// Witness-only outputs needed while writing base multiplicity and bridge
/// columns. Computing these does not require Fiat–Shamir relations.
pub struct DecompMetadata {
    pub rc_uses: RcUses,
    pub w1_encode_bytes: Vec<u8>,
    checked_hint_total: u32,
}

pub fn gen_decomp_metadata(witness: &MlDsaWitness) -> DecompMetadata {
    let sched = row_schedule();
    gen_decomp_metadata_inner(witness, &sched, None)
}

#[cfg(test)]
fn gen_decomp_metadata_with_checked_hint_total(
    witness: &MlDsaWitness,
    checked_hint_total: u32,
) -> DecompMetadata {
    let sched = row_schedule();
    gen_decomp_metadata_inner(witness, &sched, Some(checked_hint_total))
}

fn gen_decomp_metadata_inner(
    witness: &MlDsaWitness,
    sched: &[(usize, usize)],
    checked_hint_total: Option<u32>,
) -> DecompMetadata {
    let gamma2 = GAMMA2 as i64;
    let mut rc_uses = RcUses::new();
    let mut w1_encode_bytes = vec![0u8; sched.len()];
    let mut total_h = 0u32;

    for (row, &(i, p)) in sched.iter().enumerate() {
        total_h += witness.decomp.hint[i][2 * p] as u32 + witness.decomp.hint[i][2 * p + 1] as u32;
        let mut byte = 0u32;
        for lane in 0..2 {
            let m = 2 * p + lane;
            let v = lane_vals(witness, i, m);
            rc_uses.rc4[v.w1 as usize] += 1;
            rc_uses.rc4[v.w1p as usize] += 1;
            rc_uses.rc4[(v.wrap16 + 1) as usize] += 1;
            let a = v.w0 + gamma2 - 1;
            let b = gamma2 - v.w0;
            let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
            rc_uses.rc13[(a & ((1 << 13) - 1)) as usize] += 1;
            rc_uses.rc13[(b & ((1 << 13) - 1)) as usize] += 1;
            rc_uses.rc13[(sign_val & ((1 << 13) - 1)) as usize] += 1;
            rc_uses.rc7[(a >> 13) as usize] += 1;
            rc_uses.rc7[(b >> 13) as usize] += 1;
            rc_uses.rc7[(sign_val >> 13) as usize] += 1;
            byte += (v.w1p as u32) << (4 * lane);
        }
        w1_encode_bytes[row] = byte as u8;
    }

    let checked_hint_total = checked_hint_total.unwrap_or(total_h);
    rc_uses.rc8[checked_hint_total as usize] += 1;
    rc_uses.rc8[(OMEGA as u32 - checked_hint_total) as usize] += 1;

    DecompMetadata {
        rc_uses,
        w1_encode_bytes,
        checked_hint_total,
    }
}

pub fn gen_decomp_interaction(
    witness: &MlDsaWitness,
    log_size: u32,
    ct_stream: u32,
    relations: &DecompRelations,
) -> DecompInteraction {
    gen_decomp_interaction_inner(witness, log_size, ct_stream, relations, None)
}

#[cfg(test)]
fn gen_decomp_interaction_with_checked_hint_total(
    witness: &MlDsaWitness,
    log_size: u32,
    ct_stream: u32,
    relations: &DecompRelations,
    checked_hint_total: u32,
) -> DecompInteraction {
    gen_decomp_interaction_inner(
        witness,
        log_size,
        ct_stream,
        relations,
        Some(checked_hint_total),
    )
}

fn gen_decomp_interaction_inner(
    witness: &MlDsaWitness,
    log_size: u32,
    ct_stream: u32,
    relations: &DecompRelations,
    checked_hint_total: Option<u32>,
) -> DecompInteraction {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let active = sched.len();
    let gamma2 = GAMMA2 as i64;
    let metadata = gen_decomp_metadata_inner(witness, &sched, checked_hint_total);
    let checked_total_h = metadata.checked_hint_total;

    // hint accumulator (QM31 running sum over base-field h) in coset order.
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    let mut acc = vec![zero; rows];
    let mut running = 0u32;
    for row in 0..rows {
        if row < active {
            let (i, p) = sched[row];
            let h = witness.decomp.hint[i][2 * p] as u32 + witness.decomp.hint[i][2 * p + 1] as u32;
            running += h;
        }
        acc[row] = SecureField::from(m31(running));
    }

    let mut trace: Vec<ColEval> = (0..N_ACC_COORD_COLS)
        .map(|coord| {
            col_eval(
                log_size,
                acc.iter().map(|v| v.to_m31_array()[coord]).collect(),
            )
        })
        .collect();

    let row_lookup = circle_row_to_coset(log_size);
    let vec_rows = 1usize << (log_size - stwo::prover::backend::simd::m31::LOG_N_LANES);

    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let mut claimed = zero;

    // Precompute per-coset lane values.
    let coset_rows: Vec<Option<(usize, usize)>> = (0..rows)
        .map(|c| if c < active { Some(sched[c]) } else { None })
        .collect();

    let push = |frac: &dyn Fn(usize) -> (SecureField, SecureField),
                entries: &mut Vec<(Vec<PackedQM31>, Vec<PackedQM31>)>,
                claimed: &mut SecureField| {
        let mut nums = Vec::with_capacity(vec_rows);
        let mut dens = Vec::with_capacity(vec_rows);
        for vr in 0..vec_rows {
            let mut n = [zero; N_LANES];
            let mut d = [one; N_LANES];
            for lane in 0..N_LANES {
                let coset = row_lookup[vr * N_LANES + lane];
                let (num, den) = frac(coset);
                n[lane] = num;
                d[lane] = den;
                *claimed += num / den;
            }
            nums.push(PackedQM31::from_array(n));
            dens.push(PackedQM31::from_array(d));
        }
        entries.push((nums, dens));
    };

    // --- Build the logup fraction streams in AIR emission order ---
    // Per-lane: rc4(w1), rc13(a_lo), rc7(a_hi), rc13(b_lo), rc7(b_hi), rc4(w16+1),
    //           rc4(w1'), wcell — then the byte yield, then hint_acc rc (2 uses,
    // but the two rc8 uses share the same is_last gate; emit as ONE combined? No —
    // each rc use is its own fraction). To match N_LOGUP_ENTRIES = 18 we fold the
    // two hint_acc uses into the single final "hint" fraction slot pair. Simpler:
    // emit 16 lane fractions + 1 byte + 1 combined hint (which itself is 2 uses
    // summed). We keep them explicit and set N_LOGUP_ENTRIES accordingly.
    // AIR per-lane emission order: w1, a_lo, b_lo, a_hi, b_hi, sign_lo, sign_hi,
    // w16+1, w1', wcell. Mirror it EXACTLY (kind arg is documentation-only).
    for lane in 0..2 {
        for field in [
            RcField::W1,
            RcField::ALo,
            RcField::BLo,
            RcField::AHi,
            RcField::BHi,
            RcField::SignLo,
            RcField::SignHi,
            RcField::W16,
            RcField::W1P,
        ] {
            push(
                &|coset| {
                    lane_rc(
                        coset,
                        &coset_rows,
                        witness,
                        lane,
                        RcKind::Rc4,
                        field,
                        relations,
                        gamma2,
                    )
                },
                &mut entries,
                &mut claimed,
            );
        }
        // wcell use
        push(
            &|coset| match &coset_rows[coset] {
                Some((i, p)) => {
                    let m = 2 * p + lane;
                    let v = lane_vals(witness, *i, m);
                    let tuple = [m31((i * N + m) as u32), m31(v.w as u32)];
                    (one, relations.wcell.combine(&tuple))
                }
                None => (zero, one),
            },
            &mut entries,
            &mut claimed,
        );
    }
    // byte yield (+) into HashIo.
    push(
        &|coset| match &coset_rows[coset] {
            Some((i, p)) => {
                let mut byte = 0u32;
                for lane in 0..2 {
                    let v = lane_vals(witness, *i, 2 * p + lane);
                    byte += (v.w1p as u32) << (4 * lane);
                }
                let tuple = [m31(ct_stream), m31(coset as u32), m31(byte)];
                (one, relations.hash_io.combine(&tuple))
            }
            None => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // hint_acc final rc8: two SEPARATE uses (Σh, then ω−Σh), last active row only.
    // Each is its own fraction, matching the two `add_to_relation` calls in C10.
    push(
        &|coset| {
            if coset == active - 1 {
                let d: SecureField = relations.rc8.combine(&[m31(checked_total_h)]);
                (one, d)
            } else {
                (zero, one)
            }
        },
        &mut entries,
        &mut claimed,
    );
    push(
        &|coset| {
            if coset == active - 1 {
                let d: SecureField = relations
                    .rc8
                    .combine(&[m31(OMEGA as u32 - checked_total_h)]);
                (one, d)
            } else {
                (zero, one)
            }
        },
        &mut entries,
        &mut claimed,
    );

    let mut logup = LogupTraceGenerator::new(log_size);
    for chunk in entries.chunks(LOGUP_BATCH) {
        logup.col_from_fn(|vr| {
            let mut num = chunk[0].0[vr];
            let mut den = chunk[0].1[vr];
            for (nn, dd) in chunk[1..].iter() {
                num = num * dd[vr] + nn[vr] * den;
                den *= dd[vr];
            }
            (num, den)
        });
    }
    let (logup_trace, claimed_sum) = logup.finalize_last();
    trace.extend(logup_trace);
    debug_assert_eq!(claimed_sum, claimed, "decomp logup claimed sum mismatch");

    let wcell_uses = sched
        .iter()
        .flat_map(|&(i, p)| {
            (0..2).map(move |lane| {
                let m = 2 * p + lane;
                ((i * N + m) as u32, witness.rows[i].w[m])
            })
        })
        .collect();
    let DecompMetadata {
        rc_uses,
        w1_encode_bytes,
        ..
    } = metadata;
    DecompInteraction {
        trace,
        claimed_sum,
        rc_uses,
        w1_encode_bytes,
        wcell_uses,
    }
}

/// Which range value a lane rc fraction targets.
#[derive(Clone, Copy)]
enum RcField {
    W1,
    W1P,
    W16,
    ALo,
    AHi,
    BLo,
    BHi,
    SignLo,
    SignHi,
}

#[allow(clippy::too_many_arguments)]
fn lane_rc(
    coset: usize,
    coset_rows: &[Option<(usize, usize)>],
    witness: &MlDsaWitness,
    lane: usize,
    _kind: RcKind,
    field: RcField,
    relations: &DecompRelations,
    gamma2: i64,
) -> (SecureField, SecureField) {
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    match &coset_rows[coset] {
        Some((i, p)) => {
            let m = 2 * p + lane;
            let v = lane_vals(witness, *i, m);
            let a = v.w0 + gamma2 - 1;
            let b = gamma2 - v.w0;
            let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
            let (val, rel): (u32, &relations::RcRelation) = match field {
                RcField::W1 => (v.w1 as u32, &relations.rc4),
                RcField::W1P => (v.w1p as u32, &relations.rc4),
                RcField::W16 => ((v.wrap16 + 1) as u32, &relations.rc4),
                RcField::ALo => ((a & ((1 << 13) - 1)) as u32, &relations.rc13),
                RcField::AHi => ((a >> 13) as u32, &relations.rc7),
                RcField::BLo => ((b & ((1 << 13) - 1)) as u32, &relations.rc13),
                RcField::BHi => ((b >> 13) as u32, &relations.rc7),
                RcField::SignLo => ((sign_val & ((1 << 13) - 1)) as u32, &relations.rc13),
                RcField::SignHi => ((sign_val >> 13) as u32, &relations.rc7),
            };
            (one, rel.combine(&[m31(val)]))
        }
        None => (zero, one),
    }
}
