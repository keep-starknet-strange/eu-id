//! `mldsa_decomp` — FIPS 204 [DECOMP] + [HINT] over each `w_i` coefficient.
//!
//! One AIR row holds four consecutive coefficients of one `w_i` polynomial,
//! encoded as two 4-bit-packed bytes (768 bytes total, ML-DSA-65's `w1Encode`).
//! The fixed trace stores six polynomial slots, matching ML-DSA-65's `k`. This
//! component is single-profile in practice: `statement.rs` never constructs
//! it with `ML_DSA_44` (the "No ML-DSA-44" policy), so the ML-DSA-44
//! 6-bit/3-byte packing variant it once also supported (pack-bit columns, two
//! rc4 splits, a third output byte, and the `hash_active` gate needed to
//! selectively disable them for the narrower `k`) has been deleted.
//!
//! ## Per-lane FIPS obligations
//!
//! Decompose (Alg 36) / UseHint (Alg 39), pinned against
//! [`crate::reference::decompose`] as the semantic oracle:
//!
//! 1. **[DECOMP] reconstruction** — `w1·α + w0 = w − wrap_k·q`, `α = 2γ2`,
//!    `wrap_k ∈ {0,1}` (the FIPS borderline `r−r0 = q−1` wrap; verified over ℤ
//!    that `w1·α+w0 − w ∈ {0, −q}`). `w1` is range-checked directly via a
//!    single Rc4 lookup (the selected profile's exact `w1_values()`, pinned
//!    to be 16 — see [`DecompEval::new`]), and
//!    `w0 ∈ (−γ2, γ2] ∪ {−γ2 when w1=0}`. For `v = w0+γ2`, the zero flag
//!    `b` obeys `b·v=0` and `b·w1=0`; no separate booleanity or `v=0 ⇒ b=1`
//!    constraint is needed. `b·v=0` forces `b=0` whenever `v≠0` (the standard
//!    case), leaving the honest `a = v−1+b` range-check value unaffected.
//!    When `v=0` (the FIPS wraparound boundary), both equations are trivially
//!    satisfiable for *any* `b` as long as `w1=0`; a dishonest `w1≠0` instead
//!    forces `b=0` via `b·w1=0`, which drives `a=v−1+b=−1`, an out-of-range
//!    value the Rc13/Rc7 lookup rejects (see the `BoundaryZeroFlagUnset`
//!    negative test). The lower range value is shifted to `v−1+b`; the
//!    complementary upper value remains `γ2−w0`. Both use the existing
//!    13+7-bit splits.
//! 2. **[HINT] sign** — `s0 = [w0 > 0] ∈ {0,1}`, bound to `w0`'s two-sided
//!    decomposition so a lying `s0` desyncs the range (see C-DECOMP-S0).
//! 3. **[HINT] UseHint** — `w1' = (w1 + h·(2·s0−1)) mod m`, where
//!    `m = (q−1)/(2γ2)` and `h ∈ {0,1}`. `w1'` is range-checked directly via a
//!    single Rc4 lookup; `wrap_m` itself carries no lookup — once `w1` and
//!    `w1'` are Rc4-pinned to `[0,16)`, this equation is linear in `wrap_m`
//!    with a unique field solution, so any independent range check on it is
//!    redundant (the assessed and closed C8c(c) finding).
//! 4. **[HINT] Σh ≤ ω** — a running accumulator adds the four lane hints. The
//!    final active row is range-checked against the selected `ω`.
//! 5. **w-binding** — each sub-lane `w` is a USE of the coeffs W-group cell
//!    (`WCellRelation(w_bind_id, w)`), `w_bind_id = i·N + m`. Yielded by coeffs.
//! 6. **w1Encode emission** — each row yields two bytes into the
//!    commitment-hash absorb stream.
//!
//! ## Constraint degrees
//!
//! Each constraint has degree 2 or less.
//! | site | expr | degree |
//! |------|------|--------|
//! | boolean `x(1−x)` (hint, wrap_k, s0) | | 2 |
//! | boundary selector `b·v` | product of cells | 2 |
//! | FIPS boundary gate `b·w1` | product of cells | 2 |
//! | decomp recon `w1·α + w0 − w + wrap_k·q` | linear in cells | 1 |
//! | s0 · w0 sign link (see C-DECOMP-S0) | `s0·(…)` | 2 |
//! | UseHint `w1' − (w1 + h·(2s0−1) + m·u)` | `h·s0` deg 2 | 2 |
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
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, enc_signed, m31, ColEval};
#[cfg(test)]
use crate::constants::GAMMA2;
use crate::constants::{K, N, Q};
use crate::profile::{MlDsaProfile, ML_DSA_65};
use crate::witness::MlDsaWitness;
use relations::DecompRelations;
use tables::RcUses;

const LANES_PER_ROW: usize = 4;
/// Active rows: four coefficients per row.
pub const N_ROWS: usize = K * N / LANES_PER_ROW;

// --- Base column indices (four lanes) ----------------------------------------
// Per lane: w, w1, w0, hint, wrap_k, s0, w1p, wrap_m, a_hi, b_hi, sign_val,
// sign_hi. The boundary zero flags are appended after hint_acc so all
// existing lane indices remain stable.
const PER_LANE: usize = 12;
#[cfg(test)]
pub(super) const COL_LANE0: usize = 0;
const L_W: usize = 0;
const L_W1: usize = 1;
const L_W0: usize = 2;
const L_HINT: usize = 3;
const L_WRAPK: usize = 4;
const L_S0: usize = 5;
const L_W1P: usize = 6;
const L_WRAP_M: usize = 7;
const L_A_HI: usize = 8;
const L_B_HI: usize = 9;
/// `sign_val = s0·(w0−1) + (1−s0)·(−w0) ∈ [0, γ2]`, witnessed so the rc value
/// stays at degree 1. A degree-2 lookup value would make the batched LogUp
/// constraint degree 6 and break the component's +2 (D ≤ 5) bound.
/// C-DECOMP-S0 pins this value.
const L_SIGN_VAL: usize = 10;
/// 7-bit hi of `sign_val` (13+7 split).
const L_SIGN_HI: usize = 11;

const COL_HINT_ACC: usize = LANES_PER_ROW * PER_LANE;
const COL_V_ZERO: [usize; LANES_PER_ROW] = [
    COL_HINT_ACC + 1,
    COL_HINT_ACC + 2,
    COL_HINT_ACC + 3,
    COL_HINT_ACC + 4,
];
/// Total base columns.
pub const N_BASE_COLS: usize = COL_HINT_ACC + 5;

/// Logup entries per row, batched by [`LOGUP_BATCH`]: four lanes each emit 8
/// range uses (Rc4 `w1`, Rc4 `w1'`, Rc13/Rc7 `a_lo`/`a_hi`, Rc13/Rc7
/// `b_lo`/`b_hi`, Rc13/Rc7 `sign_lo`/`sign_hi`) and one WCell use. Two
/// hash-byte slots (ML-DSA-65's fixed w1Encode output; the ML-DSA-44 3-byte/
/// 6-bit packing residue was deleted -- this component is single-profile in
/// practice, statement.rs never constructs it with ML_DSA_44) and two final
/// hint-sum checks follow. Total: 40.
pub const N_LOGUP_ENTRIES: usize = LANES_PER_ROW * 9 + 2 + 2;
pub const LOGUP_BATCH: usize = 4;
pub const N_LOGUP_COLS: usize = N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
const N_ACC_COORD_COLS: usize = SECURE_EXTENSION_DEGREE; // hint_acc is a QM31 running sum
pub const N_INTERACTION_COLS: usize = N_ACC_COORD_COLS + SECURE_EXTENSION_DEGREE * N_LOGUP_COLS;

fn pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_decomp_{name}"),
    }
}

/// Preprocessed column IDs for the selected profile, in commit order.
///
/// `profile` is accepted for call-site symmetry with the other components'
/// per-profile preprocessed-id builders wired uniformly in `statement.rs`;
/// this component's own content no longer depends on it (the ML-DSA-44
/// `hash_active` gate was deleted -- production only ever constructs this
/// component with `ML_DSA_65`, K == ML_DSA_65.k(), so every row was always
/// active).
pub fn decomp_preprocessed_ids(_profile: MlDsaProfile) -> Vec<PreProcessedColumnId> {
    vec![
        pre_id("enabler_pre"),
        pre_id("start"),
        pre_id("byte_pos"),
        pre_id("is_last"),
    ]
}

/// The flat row → (i, p) schedule (active rows contiguous from 0).
fn row_schedule() -> Vec<(usize, usize)> {
    let mut out = Vec::with_capacity(N_ROWS);
    for i in 0..K {
        for p in 0..(N / LANES_PER_ROW) {
            out.push((i, p));
        }
    }
    out
}

// =============================================================================
// Preprocessed trace.
// =============================================================================

pub fn gen_decomp_preprocessed(_profile: MlDsaProfile, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();

    let mut enabler = vec![m31(0); rows];
    let mut start = vec![m31(0); rows];
    let mut byte_pos = vec![m31(0); rows];
    let mut is_last = vec![m31(0); rows];

    for (row, _) in sched.iter().enumerate() {
        enabler[row] = m31(1);
        byte_pos[row] = m31(row as u32);
    }
    start[0] = m31(1); // coset row 0 zeroes the accumulator's wraparound acc_prev.
    if !sched.is_empty() {
        is_last[sched.len() - 1] = m31(1);
    }

    vec![enabler, start, byte_pos, is_last]
        .into_iter()
        .map(|v| col_eval(log_size, v))
        .collect()
}

#[cfg(test)]
mod schedule_tests {
    use super::*;

    /// Wave A deleted every ML-DSA-44 branch from this component; constructing
    /// it with the wrong profile must fail loudly instead of silently emitting
    /// the fixed ML-DSA-65 `w1Encode` packing under ML-DSA-44 parameters.
    #[test]
    #[should_panic(expected = "single-profile")]
    fn new_rejects_ml_dsa_44() {
        let _ = DecompEval::new(0, crate::profile::ML_DSA_44, 0, DecompRelations::dummy());
    }

    #[test]
    fn byte_position_derives_all_wcell_keys() {
        assert_eq!(decomp_preprocessed_ids(ML_DSA_65).len(), 4);
        for (row, (i, p)) in row_schedule().into_iter().enumerate() {
            let byte_pos = row as u32;
            for lane in 0..LANES_PER_ROW {
                assert_eq!(
                    LANES_PER_ROW as u32 * byte_pos + lane as u32,
                    (i * N + LANES_PER_ROW * p + lane) as u32
                );
            }
        }
    }
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
    w1p: i64,    // UseHint output in the selected high-bit range.
    wrap_m: i64, // ∈ {−1,0,1}: w1p = w1 + h·(2s0−1) + m·wrap_m
}

fn lane_vals(witness: &MlDsaWitness, i: usize, m: usize) -> LaneVals {
    let profile = witness.profile;
    let w = witness.rows[i].w[m] as i64;
    // `decomp.w1` is the reference's `trace.w1` = w1' (POST-UseHint). The pre-hint
    // high bits `w1 = Decompose(w).0` are recomputed from the reference oracle.
    let (w1_pre, w0_ref) = crate::reference::decompose::decompose(profile, w as u32);
    let w1 = w1_pre as i64;
    let w0 = witness.decomp.w0[i][m] as i64;
    debug_assert_eq!(w0, w0_ref as i64, "w0 matches reference decompose");
    let hint = witness.decomp.hint[i][m] as i64;
    let w1p = witness.decomp.w1[i][m] as i64; // = UseHint(h, w)
    let alpha = 2 * profile.gamma2() as i64;
    let modulus = profile.w1_values() as i64;
    let wrap_k = (w1 * alpha + w0 - w) / -(Q as i64); // 0 or 1
    debug_assert!(wrap_k == 0 || wrap_k == 1, "wrap_k∈{{0,1}} got {wrap_k}");
    debug_assert_eq!(w1 * alpha + w0 - w + wrap_k * Q as i64, 0);
    let s0 = i64::from(w0 > 0);
    let delta = hint * (2 * s0 - 1);
    let wrap_m = (w1p - (w1 + delta)) / modulus;
    debug_assert!((-1..=1).contains(&wrap_m), "wrap_m∈{{-1,0,1}} got {wrap_m}");
    debug_assert_eq!(w1 + delta + modulus * wrap_m, w1p);
    LaneVals {
        w,
        w1,
        w0,
        hint,
        wrap_k,
        s0,
        w1p,
        wrap_m,
    }
}

#[inline]
fn shifted_lower_range_value(profile: MlDsaProfile, w0: i64) -> i64 {
    let v = w0 + profile.gamma2() as i64;
    v - 1 + i64::from(v == 0)
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(super) enum DecompTracePoke {
    BoundaryWithNonzeroW1,
    BelowNegativeGamma2,
    /// C8c(b) negative: the FIPS boundary (v=w0+γ2=0) with a noncanonical
    /// nonzero `w1`, but this time the zero flag `b` is left UNSET (0)
    /// instead of forced to 1. With the `v·v_inv` boundary equation deleted,
    /// `b·v=0` and `b·w1=0` are both trivially satisfied (v=0, b=0), so this
    /// witness must instead be caught by the shifted lower range value
    /// `a=v−1+b=−1` failing its Rc13/Rc7 lookup (imbalance, no provider row).
    BoundaryZeroFlagUnset,
    /// C8c(b) negative: a non-boolean zero flag `b=2` at the same boundary
    /// (v=0) with a nonzero `w1`. `b·v=0` is trivially satisfied (v=0), but
    /// `b·w1=2·w1≠0` fails directly -- proving the deleted booleanity
    /// constraint on `b` is not needed for this gate to hold.
    NonBooleanZeroFlagWithNonzeroW1,
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(super) struct PokedLane {
    pub w: i64,
    pub w1: i64,
    pub w0: i64,
    pub hint: i64,
    pub wrap_k: i64,
    pub s0: i64,
    pub w1p: i64,
    pub wrap_m: i64,
    pub a_hi: i64,
    pub b_hi: i64,
    pub sign_val: i64,
    pub sign_hi: i64,
    pub v_is_zero: i64,
}

#[cfg(test)]
impl DecompTracePoke {
    pub fn lane(self) -> PokedLane {
        let gamma2 = GAMMA2 as i64;
        match self {
            Self::BoundaryWithNonzeroW1 => PokedLane {
                // The noncanonical twin (w1,w0)=(1,−γ2) reconstructs the same
                // w=+γ2 as the canonical (0,+γ2) pair.
                w: gamma2,
                w1: 1,
                w0: -gamma2,
                hint: 0,
                wrap_k: 0,
                s0: 0,
                w1p: 1,
                wrap_m: 0,
                a_hi: 0,
                b_hi: (2 * gamma2) >> 13,
                sign_val: gamma2,
                sign_hi: gamma2 >> 13,
                v_is_zero: 1,
            },
            Self::BelowNegativeGamma2 => PokedLane {
                // This alternative reconstructs w=q−γ2−1. All cells remain
                // coherent except the shifted lower range value a_lo=−2.
                w: Q as i64 - gamma2 - 1,
                w1: 0,
                w0: -gamma2 - 1,
                hint: 0,
                wrap_k: 1,
                s0: 0,
                w1p: 0,
                wrap_m: 0,
                a_hi: 0,
                b_hi: (2 * gamma2 + 1) >> 13,
                sign_val: gamma2 + 1,
                sign_hi: (gamma2 + 1) >> 13,
                v_is_zero: 0,
            },
            Self::BoundaryZeroFlagUnset => PokedLane {
                w: gamma2,
                w1: 1,
                w0: -gamma2,
                hint: 0,
                wrap_k: 0,
                s0: 0,
                w1p: 1,
                wrap_m: 0,
                a_hi: 0,
                b_hi: (2 * gamma2) >> 13,
                sign_val: gamma2,
                sign_hi: gamma2 >> 13,
                v_is_zero: 0,
            },
            Self::NonBooleanZeroFlagWithNonzeroW1 => PokedLane {
                w: gamma2,
                w1: 1,
                w0: -gamma2,
                hint: 0,
                wrap_k: 0,
                s0: 0,
                w1p: 1,
                wrap_m: 0,
                a_hi: 0,
                b_hi: (2 * gamma2) >> 13,
                sign_val: gamma2,
                sign_hi: gamma2 >> 13,
                v_is_zero: 2,
            },
        }
    }
}

#[cfg(test)]
impl PokedLane {
    fn rc_integer(self, field: RcField) -> i64 {
        let gamma2 = GAMMA2 as i64;
        let a = self.w0 + gamma2 - 1 + self.v_is_zero;
        let b = gamma2 - self.w0;
        match field {
            RcField::W1 => self.w1,
            RcField::W1P => self.w1p,
            RcField::ALo => a - (1 << 13) * self.a_hi,
            RcField::AHi => self.a_hi,
            RcField::BLo => b - (1 << 13) * self.b_hi,
            RcField::BHi => self.b_hi,
            RcField::SignLo => self.sign_val - (1 << 13) * self.sign_hi,
            RcField::SignHi => self.sign_hi,
        }
    }
}

// =============================================================================
// Base trace.
// =============================================================================

pub fn gen_decomp_base_trace(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let mut cols: Vec<Vec<M31>> = (0..N_BASE_COLS).map(|_| vec![m31(0); rows]).collect();

    let gamma2 = witness.profile.gamma2() as i64;
    let mut hint_acc = 0i64;
    for (row, &(i, p)) in sched.iter().enumerate() {
        for lane in 0..LANES_PER_ROW {
            let m = LANES_PER_ROW * p + lane;
            let base = lane * PER_LANE;
            let v = lane_vals(witness, i, m);
            cols[base + L_W][row] = m31(v.w as u32);
            cols[base + L_W1][row] = m31(v.w1 as u32);
            cols[base + L_W0][row] = enc_signed(v.w0);
            cols[base + L_HINT][row] = m31(v.hint as u32);
            cols[base + L_WRAPK][row] = m31(v.wrap_k as u32);
            cols[base + L_S0][row] = m31(v.s0 as u32);
            cols[base + L_W1P][row] = m31(v.w1p as u32);
            cols[base + L_WRAP_M][row] = enc_signed(v.wrap_m);
            let shifted_v = v.w0 + gamma2;
            let v_is_zero = i64::from(shifted_v == 0);
            cols[COL_V_ZERO[lane]][row] = m31(v_is_zero as u32);
            // Exact lower endpoint: shift only v−1 by the zero flag so the
            // FIPS (w1,w0)=(0,−γ2) case maps to zero.
            let a = shifted_lower_range_value(witness.profile, v.w0);
            let b = gamma2 - v.w0;
            cols[base + L_A_HI][row] = m31((a >> 13) as u32);
            cols[base + L_B_HI][row] = m31((b >> 13) as u32);
            // sign_val ∈ [0, γ2] pins s0 = [w0 > 0] (13+7 split).
            let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
            debug_assert!((0..=gamma2).contains(&sign_val));
            cols[base + L_SIGN_VAL][row] = m31(sign_val as u32);
            cols[base + L_SIGN_HI][row] = m31((sign_val >> 13) as u32);
            hint_acc += v.hint;
        }
        cols[COL_HINT_ACC][row] = m31(hint_acc as u32);
    }

    cols.into_iter().map(|v| col_eval(log_size, v)).collect()
}

// =============================================================================
// The AIR.
// =============================================================================

#[derive(Clone)]
pub struct DecompEval {
    pub log_size: u32,
    pub profile: MlDsaProfile,
    /// The HashIo stream id the 768 `w1Encode` bytes are yielded into. Per
    /// instance under a SHARED keccak relation set: `stream_base +`
    /// [`STREAM_ID_CTILDE_ABSORB`] (the standalone default is the constant).
    pub ct_stream: u32,
    pub relations: DecompRelations,
}

impl DecompEval {
    /// Wave A deleted the ML-DSA-44 packing branches (pack-bit columns, two
    /// rc4 splits, a third output byte, `hash_active`) from this component's
    /// trace generation and AIR; `profile` is kept only for call-site
    /// symmetry with the other components' per-profile builders. Constructing
    /// with anything but `ML_DSA_65` would silently emit the fixed
    /// ML-DSA-65 `w1Encode` packing under the wrong profile's parameters, so
    /// reject it here rather than let it through to the deleted-branch gap.
    pub fn new(
        log_size: u32,
        profile: MlDsaProfile,
        ct_stream: u32,
        relations: DecompRelations,
    ) -> Self {
        assert_eq!(
            profile, ML_DSA_65,
            "DecompEval is single-profile since the wave-A ML-DSA-44 deletion; \
             only ML_DSA_65 is supported"
        );
        // C8c: the eval below is written generically against `self.profile`,
        // but `w1`/`w1'` are range-checked with a single Rc4 lookup against a
        // FIXED 16-row table (not parametrized by profile). A profile whose
        // `w1_values()` != 16 (e.g. ML-DSA-44's 44) would silently accept any
        // out-of-profile-range w1/w1' value once it wrapped past 16, since
        // the table itself has no notion of the profile's real upper bound.
        // This must be a hard assert, not a debug_assert: it is a soundness
        // precondition of the AIR, not merely a witness sanity check.
        assert_eq!(
            profile.w1_values(),
            16,
            "mldsa_decomp pins w1/w1' range checks to a fixed 16-row Rc4 \
             table; a profile whose w1_values() != 16 would silently under- \
             or over-range-check w1/w1' since the table is not parametrized \
             by profile"
        );
        Self {
            log_size,
            profile,
            ct_stream,
            relations,
        }
    }
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
        let byte_pos = eval.get_preprocessed_column(pre_id("byte_pos"));
        let is_last = eval.get_preprocessed_column(pre_id("is_last"));
        let four = E::F::from(m31(LANES_PER_ROW as u32));
        let wbid_base = byte_pos.clone() * four;

        // Two lanes' worth of base columns.
        let lanes: Vec<Vec<E::F>> = (0..LANES_PER_ROW)
            .map(|_| (0..PER_LANE).map(|_| eval.next_trace_mask()).collect())
            .collect();
        let hint_acc = eval.next_trace_mask();
        let boundary: Vec<E::F> = (0..LANES_PER_ROW).map(|_| eval.next_trace_mask()).collect();

        // hint_acc previous-row value via interaction mask (running sum).
        let acc_coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(acc_coords.each_ref().map(|p| p[0].clone()));
        let acc_cur = E::combine_ef(acc_coords.each_ref().map(|p| p[1].clone()));

        let one = E::F::from(M31::one());
        let alpha = E::F::from(m31(2 * self.profile.gamma2()));
        let q = E::F::from(m31(Q));
        let gamma2 = E::F::from(m31(self.profile.gamma2()));
        let two_pow_13 = E::F::from(m31(1 << 13));
        let w1_modulus = E::F::from(m31(self.profile.w1_values()));

        let wbids: Vec<E::F> = (0..LANES_PER_ROW)
            .map(|lane| wbid_base.clone() + E::F::from(m31(lane as u32)) * enabler_pre.clone())
            .collect();
        let mut hint_sum = E::EF::from(E::F::from(m31(0)));

        for lane in 0..LANES_PER_ROW {
            let c = &lanes[lane];
            let w = c[L_W].clone();
            let w1 = c[L_W1].clone();
            let w0 = c[L_W0].clone();
            let hint = c[L_HINT].clone();
            let wrap_k = c[L_WRAPK].clone();
            let s0 = c[L_S0].clone();
            let w1p = c[L_W1P].clone();
            let wrap_m = c[L_WRAP_M].clone();
            let a_hi = c[L_A_HI].clone();
            let b_hi = c[L_B_HI].clone();
            let sign_val = c[L_SIGN_VAL].clone();
            let sign_hi = c[L_SIGN_HI].clone();
            let v_is_zero = &boundary[lane];

            // The hint, wrap_k, and s0 values are Boolean. Padding uses zero.
            eval.add_constraint(hint.clone() * (one.clone() - hint.clone()));
            eval.add_constraint(wrap_k.clone() * (one.clone() - wrap_k.clone()));
            eval.add_constraint(s0.clone() * (one.clone() - s0.clone()));

            // [DECOMP] reconstruction: w1·α + w0 − w + wrap_k·q = 0.
            eval.add_constraint(
                w1.clone() * alpha.clone() + w0.clone() - w.clone() + wrap_k.clone() * q.clone(),
            );

            // Range-check w1 directly: a single Rc4 lookup on the exact
            // 16-value profile interval (see the `w1_values()==16` assert in
            // `DecompEval::new`). C8c(a): the previous two-sided
            // `w1`/`w1_room` Rc8 pair is redundant once the table matches the
            // value's exact domain.
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc4,
                enabler_pre.clone(),
                core::slice::from_ref(&w1),
            ));

            // Enforce the exact FIPS lower endpoint. For v=w0+γ2: `b·v=0`
            // forces b=0 whenever v≠0 (standard case, a=v−1 unaffected);
            // `b·w1=0` forces b=0 whenever w1≠0. When v=0 and w1=0 (the FIPS
            // wraparound), both are trivially satisfiable for any b, and the
            // honest prover sets b=1 so a=0. A dishonest w1≠0 at v=0 instead
            // forces b=0 (via the second equation), driving a=v−1+b=−1,
            // which the Rc13/Rc7 lookup below rejects (see
            // `BoundaryZeroFlagUnset`). No separate booleanity or `v=0⇒b=1`
            // constraint on b is needed (C8c(b): the deleted `v_inv` column).
            let v = w0.clone() + gamma2.clone();
            // (b) b·v = 0 (degree 2).
            eval.add_constraint(v_is_zero.clone() * v.clone());
            // (c) b·w1 = 0 (degree 2).
            eval.add_constraint(v_is_zero.clone() * w1.clone());

            // Range-check v−1+b and γ2−w0 through the existing 13+7 splits.
            let a = v - one.clone() + v_is_zero.clone();
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
            // honest s0=0 (w0≤0) ⇒ sign_val = −w0 ∈ [0, γ2], with γ2
            // attained only at the FIPS special boundary.
            // A lying s0 makes sign_val negative (e.g. w0=5,s0=0 ⇒ −5), which the
            // [0,2γ2) range-check (13+7) rejects. `w0` is already pinned to
            // [−γ2, γ2] by the a/b split and boundary gate, so the branch
            // bound is exact.
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

            // [HINT] UseHint in the selected high-bits modulus. C8c(c):
            // wrap_m carries no lookup of its own -- with w1 and w1' both
            // Rc4-pinned to [0,16), this equation is linear in wrap_m with a
            // unique field solution, so it is already fully determined by
            // this one constraint; any additional range check on it is
            // redundant.
            let delta_sign = s0.clone() + s0.clone() - one.clone(); // 2s0 − 1
            eval.add_constraint(
                w1p.clone()
                    - (w1.clone()
                        + hint.clone() * delta_sign
                        + w1_modulus.clone() * wrap_m.clone()),
            );

            // Range-check w1' directly: a single Rc4 lookup (C8c(a), see w1
            // above).
            eval.add_to_relation(RelationEntry::base(
                &self.relations.rc4,
                enabler_pre.clone(),
                core::slice::from_ref(&w1p),
            ));

            // Use the coeffs W cell `(poly_id·N + m, w)`.
            let wtuple = [wbids[lane].clone(), w.clone()];
            eval.add_to_relation(RelationEntry::base(
                &self.relations.wcell,
                enabler_pre.clone(),
                &wtuple,
            ));

            hint_sum += E::EF::from(hint);
        }

        // Update the hint accumulator: acc_cur = (1−start)·acc_prev + Σ_lane h.
        // `start` (coset row 0) zeroes the `[-1,0]` mask's wraparound acc_prev so
        // the running sum begins at 0. No per-poly reset — Σ_i Σ_m h is the global
        // total. Padding rows carry h=0, so acc stays flat past the last active row.
        let acc_prev_gated = E::EF::from(one.clone() - start.clone()) * acc_prev;
        eval.add_constraint(acc_cur.clone() - (acc_prev_gated + hint_sum));

        // The rc8 lookup reads the base-column copy. Bind that copy to
        // the true interaction running sum on the only row where it is used.
        eval.add_constraint(
            E::EF::from(is_last.clone()) * (E::EF::from(hint_acc.clone()) - acc_cur.clone()),
        );

        // w1Encode: the fixed ML-DSA-65 packing, two bytes per row
        // (lane0 | lane1<<4, lane2 | lane3<<4). The ML-DSA-44 3-byte/6-bit
        // packing residue (6 pack-bit columns, 2 rc4 splits, a third output
        // byte) was deleted -- this component is single-profile in
        // production (statement.rs never constructs it with ML_DSA_44).
        let output_bytes = [
            lanes[0][L_W1P].clone() + E::F::from(m31(16)) * lanes[1][L_W1P].clone(),
            lanes[2][L_W1P].clone() + E::F::from(m31(16)) * lanes[3][L_W1P].clone(),
        ];
        let stream = E::F::from(m31(self.ct_stream));
        let stride = E::F::from(m31(output_bytes.len() as u32));
        for (output, byte) in output_bytes.into_iter().enumerate() {
            let io_tuple = [
                stream.clone(),
                byte_pos.clone() * stride.clone() + E::F::from(m31(output as u32)),
                byte,
            ];
            eval.add_to_relation(RelationEntry::base(
                &self.relations.hash_io,
                enabler_pre.clone(),
                &io_tuple,
            ));
        }

        // On the last active row, range-check acc = Σ_i Σ_m h
        // range-checked two-sided into rc8: Σh ∈ [0,256) AND ω−Σh ∈ [0,256).
        // The second use forces Σh ≤ the selected ω. If Σh is larger, ω−Σh wraps out of
        // [0,256) ⇒ no rc8 row ⇒ imbalance). Gated by is_last (no use elsewhere).
        let omega = E::F::from(m31(self.profile.omega() as u32));
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

        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

// =============================================================================
// Interaction trace.
// =============================================================================

/// Output of the decomp interaction generator.
pub struct DecompInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    pub rc_uses: RcUses,
    /// The 768 emitted `w1Encode` bytes in byte-position order.
    /// `wcell_uses` are the `(w_bind_id, w)` tuples.
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
fn gen_decomp_metadata_with_test_options(
    witness: &MlDsaWitness,
    checked_hint_total: Option<u32>,
    trace_poke: Option<DecompTracePoke>,
) -> DecompMetadata {
    let sched = row_schedule();
    let metadata = gen_decomp_metadata_inner(witness, &sched, checked_hint_total);
    match trace_poke {
        Some(poke) => apply_trace_poke_to_metadata(metadata, witness, poke),
        None => metadata,
    }
}

fn gen_decomp_metadata_inner(
    witness: &MlDsaWitness,
    sched: &[(usize, usize)],
    checked_hint_total: Option<u32>,
) -> DecompMetadata {
    let profile = witness.profile;
    let gamma2 = profile.gamma2() as i64;
    let mut rc_uses = RcUses::new();
    let mut w1_encode_bytes = Vec::with_capacity(profile.w1_encoded_bytes());
    let mut total_h = 0u32;

    for &(i, p) in sched {
        for lane in 0..LANES_PER_ROW {
            let m = LANES_PER_ROW * p + lane;
            total_h += witness.decomp.hint[i][m] as u32;
            let v = lane_vals(witness, i, m);
            rc_uses.rc4[v.w1 as usize] += 1;
            rc_uses.rc4[v.w1p as usize] += 1;
            let a = shifted_lower_range_value(profile, v.w0);
            let b = gamma2 - v.w0;
            let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
            rc_uses.rc13[(a & ((1 << 13) - 1)) as usize] += 1;
            rc_uses.rc13[(b & ((1 << 13) - 1)) as usize] += 1;
            rc_uses.rc13[(sign_val & ((1 << 13) - 1)) as usize] += 1;
            rc_uses.rc7[(a >> 13) as usize] += 1;
            rc_uses.rc7[(b >> 13) as usize] += 1;
            rc_uses.rc7[(sign_val >> 13) as usize] += 1;
        }
        if i < profile.k() {
            w1_encode_bytes.extend(packed_row_bytes(witness, i, p));
        }
    }

    let checked_hint_total = checked_hint_total.unwrap_or(total_h);
    rc_uses.rc8[checked_hint_total as usize] += 1;
    rc_uses.rc8[(profile.omega() as u32 - checked_hint_total) as usize] += 1;

    debug_assert_eq!(w1_encode_bytes.len(), profile.w1_encoded_bytes());

    DecompMetadata {
        rc_uses,
        w1_encode_bytes,
        checked_hint_total,
    }
}

/// The fixed ML-DSA-65 w1Encode packing: two bytes per row (lane0|lane1<<4,
/// lane2|lane3<<4). The ML-DSA-44 3-byte/6-bit variant was deleted.
fn packed_row_bytes(witness: &MlDsaWitness, i: usize, p: usize) -> Vec<u8> {
    let values: [u32; LANES_PER_ROW] =
        core::array::from_fn(|lane| witness.decomp.w1[i][LANES_PER_ROW * p + lane]);
    vec![
        (values[0] | (values[1] << 4)) as u8,
        (values[2] | (values[3] << 4)) as u8,
    ]
}

#[cfg(test)]
fn honest_lane_rc_integer(profile: MlDsaProfile, v: &LaneVals, field: RcField) -> i64 {
    let gamma2 = profile.gamma2() as i64;
    let a = shifted_lower_range_value(profile, v.w0);
    let b = gamma2 - v.w0;
    let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
    match field {
        RcField::W1 => v.w1,
        RcField::W1P => v.w1p,
        RcField::ALo => a & ((1 << 13) - 1),
        RcField::AHi => a >> 13,
        RcField::BLo => b & ((1 << 13) - 1),
        RcField::BHi => b >> 13,
        RcField::SignLo => sign_val & ((1 << 13) - 1),
        RcField::SignHi => sign_val >> 13,
    }
}

#[cfg(test)]
fn rc_uses_for_field_mut(uses: &mut RcUses, field: RcField) -> &mut [u32] {
    match field {
        RcField::W1 | RcField::W1P => &mut uses.rc4,
        RcField::ALo | RcField::BLo | RcField::SignLo => &mut uses.rc13,
        RcField::AHi | RcField::BHi | RcField::SignHi => &mut uses.rc7,
    }
}

#[cfg(test)]
fn apply_trace_poke_to_metadata(
    mut metadata: DecompMetadata,
    witness: &MlDsaWitness,
    poke: DecompTracePoke,
) -> DecompMetadata {
    const RC_FIELDS: [RcField; 8] = [
        RcField::W1,
        RcField::ALo,
        RcField::BLo,
        RcField::AHi,
        RcField::BHi,
        RcField::SignLo,
        RcField::SignHi,
        RcField::W1P,
    ];

    let honest = lane_vals(witness, 0, 0);
    let attacked = poke.lane();
    debug_assert_eq!(attacked.w, honest.w, "trace poke must preserve WCell");
    debug_assert_eq!(
        attacked.hint, honest.hint,
        "trace poke must preserve the hint accumulator"
    );

    let mut unmatched = 0;
    for field in RC_FIELDS {
        let old = honest_lane_rc_integer(witness.profile, &honest, field);
        let new = attacked.rc_integer(field);
        let uses = rc_uses_for_field_mut(&mut metadata.rc_uses, field);
        debug_assert!((0..uses.len() as i64).contains(&old));
        debug_assert!(uses[old as usize] > 0);
        uses[old as usize] -= 1;
        if (0..uses.len() as i64).contains(&new) {
            uses[new as usize] += 1;
        } else {
            unmatched += 1;
            debug_assert!(matches!(field, RcField::ALo));
            // Out-of-range a_lo values differ by poke (−2 for the wrap-past-
            // negative-γ2 case, −1 for the zero-flag-unset boundary case);
            // both are negative, i.e. genuinely unrepresentable in [0,2^13).
            debug_assert!(new < 0, "unmatched ALo must be negative, got {new}");
        }
    }

    let expected_unmatched = match poke {
        DecompTracePoke::BoundaryWithNonzeroW1 => 0,
        DecompTracePoke::BelowNegativeGamma2 => 1,
        DecompTracePoke::BoundaryZeroFlagUnset => 1,
        DecompTracePoke::NonBooleanZeroFlagWithNonzeroW1 => 0,
    };
    debug_assert_eq!(unmatched, expected_unmatched);
    metadata.w1_encode_bytes[0] = (metadata.w1_encode_bytes[0] & 0xf0) | attacked.w1p as u8;
    metadata
}

pub fn gen_decomp_interaction(
    witness: &MlDsaWitness,
    log_size: u32,
    ct_stream: u32,
    relations: &DecompRelations,
) -> DecompInteraction {
    gen_decomp_interaction_inner(
        witness,
        log_size,
        ct_stream,
        relations,
        None,
        #[cfg(test)]
        None,
    )
}

#[cfg(test)]
fn gen_decomp_interaction_with_test_options(
    witness: &MlDsaWitness,
    log_size: u32,
    ct_stream: u32,
    relations: &DecompRelations,
    checked_hint_total: Option<u32>,
    trace_poke: Option<DecompTracePoke>,
) -> DecompInteraction {
    gen_decomp_interaction_inner(
        witness,
        log_size,
        ct_stream,
        relations,
        checked_hint_total,
        trace_poke,
    )
}

fn gen_decomp_interaction_inner(
    witness: &MlDsaWitness,
    log_size: u32,
    ct_stream: u32,
    relations: &DecompRelations,
    checked_hint_total: Option<u32>,
    #[cfg(test)] trace_poke: Option<DecompTracePoke>,
) -> DecompInteraction {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let active = sched.len();
    let gamma2 = witness.profile.gamma2() as i64;
    let metadata = gen_decomp_metadata_inner(witness, &sched, checked_hint_total);
    #[cfg(test)]
    let metadata = match trace_poke {
        Some(poke) => apply_trace_poke_to_metadata(metadata, witness, poke),
        None => metadata,
    };
    let checked_total_h = metadata.checked_hint_total;

    // hint accumulator (QM31 running sum over base-field h) in coset order.
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    let mut acc = vec![zero; rows];
    let mut running = 0u32;
    for row in 0..rows {
        if row < active {
            let (i, p) = sched[row];
            running += (0..LANES_PER_ROW)
                .map(|lane| witness.decomp.hint[i][LANES_PER_ROW * p + lane] as u32)
                .sum::<u32>();
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
    // Each row has 40 fractions. Each of four lanes has 8 range uses and one
    // WCell use. Two hash-byte slots and two final hint-sum checks follow.
    // Keep this order equal to the AIR order.
    for lane in 0..LANES_PER_ROW {
        for field in [
            RcField::W1,
            RcField::ALo,
            RcField::BLo,
            RcField::AHi,
            RcField::BHi,
            RcField::SignLo,
            RcField::SignHi,
            RcField::W1P,
        ] {
            push(
                &|coset| {
                    lane_rc(
                        coset,
                        &coset_rows,
                        witness,
                        lane,
                        field,
                        relations,
                        gamma2,
                        #[cfg(test)]
                        trace_poke,
                    )
                },
                &mut entries,
                &mut claimed,
            );
        }
        // wcell use
        push(
            &|coset| match &coset_rows[coset] {
                Some((i, p)) if *i < witness.profile.k() => {
                    let m = LANES_PER_ROW * p + lane;
                    let v = lane_vals(witness, *i, m);
                    let tuple = [m31((i * N + m) as u32), m31(v.w as u32)];
                    (one, relations.wcell.combine(&tuple))
                }
                _ => (zero, one),
            },
            &mut entries,
            &mut claimed,
        );
    }
    // Two byte yields into HashIo (the fixed ML-DSA-65 packing).
    for output in 0..2 {
        push(
            &|coset| match &coset_rows[coset] {
                Some((i, p)) if *i < witness.profile.k() => {
                    let bytes = packed_row_bytes(witness, *i, *p);
                    let byte = bytes[output];
                    let position = coset * bytes.len() + output;
                    let tuple = [m31(ct_stream), m31(position as u32), m31(byte as u32)];
                    (one, relations.hash_io.combine(&tuple))
                }
                _ => (zero, one),
            },
            &mut entries,
            &mut claimed,
        );
    }
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
                    .combine(&[m31(witness.profile.omega() as u32 - checked_total_h)]);
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
        .filter(|&&(i, _)| i < witness.profile.k())
        .flat_map(|&(i, p)| {
            (0..LANES_PER_ROW).map(move |lane| {
                let m = LANES_PER_ROW * p + lane;
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
    field: RcField,
    relations: &DecompRelations,
    gamma2: i64,
    #[cfg(test)] trace_poke: Option<DecompTracePoke>,
) -> (SecureField, SecureField) {
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    match &coset_rows[coset] {
        Some((i, p)) => {
            #[cfg(test)]
            if coset == 0 && lane == 0 {
                if let Some(poke) = trace_poke {
                    let alo_out_of_range = matches!(field, RcField::ALo)
                        && matches!(
                            poke,
                            DecompTracePoke::BelowNegativeGamma2
                                | DecompTracePoke::BoundaryZeroFlagUnset
                        );
                    if alo_out_of_range {
                        // There is no Rc13 provider row for a negative a_lo
                        // (−2 for BelowNegativeGamma2, −1 for
                        // BoundaryZeroFlagUnset). Omit exactly this fraction
                        // so the AIR lookup fails during proving; every other
                        // attacked relation stays coherent.
                        return (zero, one);
                    }
                    let rel = match field {
                        RcField::W1 | RcField::W1P => &relations.rc4,
                        RcField::ALo | RcField::BLo | RcField::SignLo => &relations.rc13,
                        RcField::AHi | RcField::BHi | RcField::SignHi => &relations.rc7,
                    };
                    return (
                        one,
                        rel.combine(&[enc_signed(poke.lane().rc_integer(field))]),
                    );
                }
            }
            let m = LANES_PER_ROW * p + lane;
            let v = lane_vals(witness, *i, m);
            let a = shifted_lower_range_value(witness.profile, v.w0);
            let b = gamma2 - v.w0;
            let sign_val = if v.s0 == 1 { v.w0 - 1 } else { -v.w0 };
            let (val, rel): (u32, &relations::RcRelation) = match field {
                RcField::W1 => (v.w1 as u32, &relations.rc4),
                RcField::W1P => (v.w1p as u32, &relations.rc4),
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
