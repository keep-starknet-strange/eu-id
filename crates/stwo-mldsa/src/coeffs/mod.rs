//! `mldsa_coeffs` — the tall stacked AIR component for the S5a integer-lift
//! (worksheet `tasks/parity/S5a-integer-lift-worksheet.md`, option a′).
//!
//! Every witnessed / carry polynomial's balanced base-`B` (`B = 2^9`) digits are
//! stacked into contiguous Horner groups ([`layout`]). Per row the component:
//!   * range-checks every digit cell (dedicated 2^9 table, offset `+2^8`);
//!   * for carry rows, range-checks `|C| ≤ 2^20` via a `C+2^20` 13+8 split;
//!   * binds `recomp_cell = Σ_t d_t·B^t` for z and w (§3.4);
//!   * enforces the exact z-norm `|z| ≤ γ1−β−1 = 524_091` (two-sided offset, §3.4
//!     review flag — NOT a 2^20 window);
//!   * enforces the ternary `c ∈ {−1,0,1}` via a `{0,1,2}` membership lookup;
//!   * runs the bivariate Horner accumulator (interaction tree) at the drawn
//!     `(r,s)`, emitting `P̂(r,s)` at each group end into [`EvalAtRsRelation`].
//!
//! The verifier-native fold ([`crate::verifier_native`]) consumes those claimed
//! evaluations and checks the folded identity `(‡)` against public `Â, t̂1, q̂`.
//!
//! ## Base column layout (uniform over all `2^log_size` rows)
//!
//! | idx | column        | meaning |
//! |-----|---------------|---------|
//! | 0   | `enabler`     | 1 on active rows |
//! | 1-6 | `digit[0..6]` | balanced digits (z/w/e/v/c) or carry cells `C_{m,0..4}` |
//! | 7   | `recomp_cell` | `Σ_t d_t·B^t` (z,w); else 0 |
//! | 8   | `norm_a_hi`   | 7-bit hi of `a = cell + 524_091` (z rows) |
//! | 9   | `norm_b_hi`   | 7-bit hi of `b = 524_091 − cell` (z rows) |
//! |10-14| `carry_hi[0..5]` | 8-bit hi of `C_{m,t}+2^20` (carry rows) |
//!
//! ## Preprocessed columns
//! `start, end, poly_id, live_mask[0..6], is_digit, is_carry, is_recomp,
//!  is_norm, is_c` — all row-index-deterministic.
//!
//! ## Degree worksheet — EVERY constraint degree ≤ 2 ⇒ bound = log_size + 1.
//! The interaction-tree Horner `[-1,0]` mask requires the bound to be EXACTLY
//! `+1`; a degree-3+ constraint would force `+2` and break the OODS consistency
//! check (see [`CoeffsEval::max_constraint_log_degree_bound`]). The ternary is a
//! LOOKUP for this reason, not the cubic `c(c−1)(c+1)`.
//! | site | degree |
//! |------|--------|
//! | enabler boolean `e(1−e)` | 2 |
//! | tail-digit zero `(1−mask)·digit` | 2 |
//! | recomp `is_recomp·(cell − Σ d·B^t)` | 2 |
//! | z-norm rc uses (a/b lo+hi, degree-1 values) | 1 |
//! | carry rc uses (lo degree-1 expr, hi cell) | 1 |
//! | ternary use `c+1 ∈ {0,1,2}` (lookup) | 1 |
//! | Horner `acc − ((1−start)·acc_prev·r + Σ d·s^t)` | 2 |
//! | digit/eval logup | 1–2 |

// This is a numeric kernel: coefficient index `m`, digit index `t`, poly index
// `i/j` carry mathematical meaning, so explicit indexing is the readable form.
#![allow(clippy::needless_range_loop)]

pub mod layout;
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
use crate::witness::{MlDsaWitness, B, T_MAX};
use layout::{groups, Group, Kind, CARRY_DIGITS, MAX_DIGITS};
use relations::CoeffsRelations;
use tables::RcKind;

thread_local! {
    static RANGE_BOUNDARY_ATTACK: core::cell::RefCell<Option<RcKind>> =
        const { core::cell::RefCell::new(None) };
}

/// Test-only range-gate attack. Shared fraction streams cannot isolate one kind
/// without multiplying a witness value by a selector (degree 3), so the hook
/// replaces every stream occupied by `kind` with its first excluded value.
/// This preserves every non-lookup constraint and exercises the real shared
/// relation/table path at the exact `log_size + 1` degree bound.
#[doc(hidden)]
pub struct CoeffsRangeBoundaryGuard;

impl Drop for CoeffsRangeBoundaryGuard {
    fn drop(&mut self) {
        RANGE_BOUNDARY_ATTACK.with(|attack| *attack.borrow_mut() = None);
    }
}

#[doc(hidden)]
pub fn install_range_boundary_attack(kind: RcKind) -> CoeffsRangeBoundaryGuard {
    RANGE_BOUNDARY_ATTACK.with(|attack| *attack.borrow_mut() = Some(kind));
    CoeffsRangeBoundaryGuard
}

fn attacked_stream_boundary(stream: usize) -> Option<u32> {
    RANGE_BOUNDARY_ATTACK.with(|attack| {
        attack.borrow().and_then(|kind| {
            let occupied = match kind {
                RcKind::Rc9 => stream <= 5,
                RcKind::Rc13 => matches!(stream, 0..=4 | 6 | 8),
                RcKind::Rc8 => matches!(stream, 5..=9),
                RcKind::Rc7 => matches!(stream, 7 | 9),
                RcKind::Ternary => stream == 7,
            };
            occupied.then_some(kind.n_values() as u32)
        })
    })
}

fn attacked_stream_value<E: EvalAtRow>(stream: usize, value: E::F) -> E::F {
    attacked_stream_boundary(stream).map_or(value, |boundary| E::F::from(m31(boundary)))
}

// --- Norm bound (worksheet §3.4): γ1 − β − 1 = 524_091. -----------------------
/// `γ1 − β − 1` for ML-DSA-65 (`γ1 = 2^19`, `β = τ·η = 49·4 = 196`).
pub const Z_NORM_BOUND: i64 = 524_091;
/// `a + b = 2·(γ1−β−1)` for the symmetric two-sided norm decomposition.
pub const Z_NORM_SUM: i64 = 2 * Z_NORM_BOUND; // 1_048_182
/// Carry offset `2^20` (worksheet §3.3).
pub const CARRY_OFFSET: i64 = 1 << 20;
/// Digit offset `2^8` into the 2^9 window (worksheet §3.1).
pub const DIGIT_OFFSET: u32 = 1 << 8;

// --- Base column indices ------------------------------------------------------
const COL_ENABLER: usize = 0;
const COL_DIGIT0: usize = 1;
const COL_RECOMP: usize = COL_DIGIT0 + MAX_DIGITS; // 7
const COL_NORM_A_HI: usize = COL_RECOMP + 1; // 8
const COL_NORM_B_HI: usize = COL_NORM_A_HI + 1; // 9
const COL_CARRY_HI0: usize = COL_NORM_B_HI + 1; // 10
/// Total base columns.
pub const N_BASE_COLS: usize = COL_CARRY_HI0 + CARRY_DIGITS; // 15

// --- Preprocessed column names ------------------------------------------------
fn pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_coeffs_{name}"),
    }
}

fn digit_mask_name(t: usize) -> String {
    format!("live_mask_{t}")
}

/// All preprocessed column ids for the coeffs component, in commit order.
pub fn coeffs_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = vec![pre_id("start"), pre_id("end"), pre_id("poly_id")];
    for t in 0..MAX_DIGITS {
        ids.push(pre_id(&digit_mask_name(t)));
    }
    // `is_w` / `w_bind_id` / `c_bind_id` (M6): the row-index-deterministic
    // selectors + keys the WCell / CCell binding yields need. `is_recomp` covers
    // BOTH z and w, so a dedicated `is_w` gate is required to yield only the w
    // cells; `w_bind_id = i·N + m` and `c_bind_id = m` are the consumer keys.
    for name in [
        "is_digit",
        "is_carry",
        "is_recomp",
        "is_norm",
        "is_c",
        "is_w",
    ] {
        ids.push(pre_id(name));
    }
    ids.push(pre_id("w_bind_id"));
    ids.push(pre_id("c_bind_id"));
    ids
}

/// Ten shared range streams plus the three distinct relation yields. Range
/// kinds occupy disjoint row slots and are namespaced by fixed bound ids.
pub const N_RANGE_STREAMS: usize = 10;
pub const N_LOGUP_ENTRIES: usize = N_RANGE_STREAMS
    + 1                                             // eval yield
    + 1                                             // WCell yield (w cells)
    + 1; // CCell yield (c cells)
/// One interaction column per fraction (`finalize_logup`, the air-writer safe
/// default). Batching is a later perf lever, not needed for M4 correctness.
pub const LOGUP_BATCH: usize = 1;
pub const N_LOGUP_COLS: usize = N_LOGUP_ENTRIES.div_ceil(LOGUP_BATCH);
/// The 4 accumulator coordinate columns come first in the interaction tree.
const N_ACC_COORD_COLS: usize = SECURE_EXTENSION_DEGREE;
/// Interaction base-column count: 4 accumulator coords + one batched logup
/// column (`SECURE_EXTENSION_DEGREE` base cols) per fraction pair.
pub const N_INTERACTION_COLS: usize = N_ACC_COORD_COLS + SECURE_EXTENSION_DEGREE * N_LOGUP_COLS;

// =============================================================================
// Row schedule helpers (shared by trace-gen and preprocessed-gen).
// =============================================================================

/// A flat per-row descriptor: which group, in-group coefficient index, and the
/// group metadata. `None` for padding rows.
#[derive(Clone, Copy)]
struct RowInfo {
    group: Group,
    in_group: usize,
}

/// Build the flat row → RowInfo schedule (active rows only, contiguous from 0).
fn row_schedule() -> Vec<RowInfo> {
    let mut rows = Vec::new();
    for group in groups() {
        for in_group in 0..group.coeffs {
            rows.push(RowInfo { group, in_group });
        }
    }
    rows
}

// =============================================================================
// Preprocessed trace.
// =============================================================================

pub fn gen_coeffs_preprocessed(log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();

    let mut start = vec![m31(0); rows];
    let mut end = vec![m31(0); rows];
    let mut poly_id = vec![m31(0); rows];
    let mut live_mask: Vec<Vec<M31>> = (0..MAX_DIGITS).map(|_| vec![m31(0); rows]).collect();
    let mut is_digit = vec![m31(0); rows];
    let mut is_carry = vec![m31(0); rows];
    let mut is_recomp = vec![m31(0); rows];
    let mut is_norm = vec![m31(0); rows];
    let mut is_c = vec![m31(0); rows];
    let mut is_w = vec![m31(0); rows];
    let mut w_bind_id = vec![m31(0); rows];
    let mut c_bind_id = vec![m31(0); rows];

    for (row, info) in sched.iter().enumerate() {
        let g = info.group;
        start[row] = m31(u32::from(info.in_group == 0));
        end[row] = m31(u32::from(info.in_group == g.coeffs - 1));
        poly_id[row] = m31(g.poly_id);
        let live = g.kind.live_digits();
        for t in 0..MAX_DIGITS {
            live_mask[t][row] = m31(u32::from(t < live));
        }
        match g.kind {
            Kind::Carry => is_carry[row] = m31(1),
            _ => is_digit[row] = m31(1),
        }
        if g.kind.has_recomp() {
            is_recomp[row] = m31(1);
        }
        if g.kind == Kind::Z {
            is_norm[row] = m31(1);
        }
        if g.kind == Kind::C {
            is_c[row] = m31(1);
            // c_bind_id = m, the coefficient index (high-to-low: m = coeffs−1−in_group).
            let m = g.coeffs - 1 - info.in_group;
            c_bind_id[row] = m31(m as u32);
        }
        if g.kind == Kind::W {
            is_w[row] = m31(1);
            // w_bind_id = i·N + m, where i = poly_id − POLY_ID_W0.
            let i = (g.poly_id - layout::POLY_ID_W0) as usize;
            let m = g.coeffs - 1 - info.in_group;
            w_bind_id[row] = m31((i * crate::constants::N + m) as u32);
        }
    }

    let mut out = vec![start, end, poly_id];
    out.extend(live_mask);
    out.extend([
        is_digit, is_carry, is_recomp, is_norm, is_c, is_w, w_bind_id, c_bind_id,
    ]);
    out.into_iter().map(|v| col_eval(log_size, v)).collect()
}

// =============================================================================
// Base trace.
// =============================================================================

/// Per-row concrete values, filled from the witness (coset order).
pub fn gen_coeffs_base_trace(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let mut cols: Vec<Vec<M31>> = (0..N_BASE_COLS).map(|_| vec![m31(0); rows]).collect();

    for (row, info) in sched.iter().enumerate() {
        cols[COL_ENABLER][row] = m31(1);
        let digits = row_digits(witness, info);
        for (t, &d) in digits.iter().enumerate() {
            cols[COL_DIGIT0 + t][row] = encode_signed(d);
        }
        match info.group.kind {
            Kind::Z | Kind::W => {
                let cell = recompose(&digits);
                cols[COL_RECOMP][row] = encode_signed(cell);
                if info.group.kind == Kind::Z {
                    // Two-sided norm: a = cell + bound, b = bound − cell.
                    let a = cell + Z_NORM_BOUND as i128;
                    let b = Z_NORM_BOUND as i128 - cell;
                    cols[COL_NORM_A_HI][row] = m31((a >> 13) as u32);
                    cols[COL_NORM_B_HI][row] = m31((b >> 13) as u32);
                }
            }
            Kind::Carry => {
                for t in 0..CARRY_DIGITS {
                    let shifted = digits[t] + CARRY_OFFSET as i128; // ∈ [0, 2^21)
                    cols[COL_CARRY_HI0 + t][row] = m31((shifted >> 13) as u32);
                }
            }
            Kind::C => {
                // Reuse the otherwise-idle norm-a auxiliary as the ternary
                // range-stream value. The AIR binds it to c+1 on c rows.
                cols[COL_NORM_A_HI][row] = encode_signed(digits[0] + 1);
            }
            _ => {}
        }
    }

    cols.into_iter().map(|v| col_eval(log_size, v)).collect()
}

/// The (signed) digit cells for one row, low-first, exactly `MAX_DIGITS` long
/// (unused tail = 0). For carries the "digits" are the 5 carry cells `C_{m,0..4}`.
fn row_digits(witness: &MlDsaWitness, info: &RowInfo) -> [i128; MAX_DIGITS] {
    let g = info.group;
    // Coefficients are laid out HIGH-to-LOW within a group: row `in_group = k`
    // holds coefficient `m = coeffs − 1 − k`. The forward Horner
    // `acc = acc·r + digit_row` over rows then yields the STANDARD bivariate eval
    // `P̂(r,s) = Σ_m d_m(s)·r^m` (coeff m weight r^m). This is the multiplicative
    // convention the fold `(‡)` needs: `Â(r,s)·ẑ(r,s) = û(r,s)`. A low-to-high
    // layout would give `Σ_m d_m·r^(M−1−m)`, whose per-poly length factor `r^(M−1)`
    // differs across polys of different degree and breaks the product identity.
    let m = g.coeffs - 1 - info.in_group;
    let mut out = [0i128; MAX_DIGITS];
    match g.kind {
        Kind::Z => {
            let j = (g.poly_id - layout::POLY_ID_Z0) as usize;
            out[..3].copy_from_slice(&witness.digits.z[j][m]);
        }
        Kind::W => {
            let i = (g.poly_id - layout::POLY_ID_W0) as usize;
            out[..3].copy_from_slice(&witness.digits.w[i][m]);
        }
        Kind::E => {
            let i = (g.poly_id - layout::POLY_ID_E0) as usize;
            out[..4].copy_from_slice(&witness.digits.e[i][m]);
        }
        Kind::V => {
            let i = (g.poly_id - layout::POLY_ID_V0) as usize;
            out[..6].copy_from_slice(&witness.digits.v[i][m]);
        }
        Kind::C => {
            out[0] = witness.digits.c[m];
        }
        Kind::Carry => {
            let i = (g.poly_id - layout::POLY_ID_CARRY0) as usize;
            let carry = &witness.rows[i].carry[m]; // [i128; T_MAX+1]
            out[..CARRY_DIGITS].copy_from_slice(&carry[..CARRY_DIGITS]);
            let _ = T_MAX;
        }
    }
    out
}

fn recompose(digits: &[i128; MAX_DIGITS]) -> i128 {
    let mut acc = 0i128;
    let mut weight = 1i128;
    for &d in digits {
        acc += d * weight;
        weight *= B;
    }
    acc
}

/// Centered M31 encoding of a signed value known to satisfy `|v| < p/2`.
fn encode_signed(v: i128) -> M31 {
    const P: i128 = (1 << 31) - 1;
    let r = ((v % P) + P) % P;
    m31(r as u32)
}

// =============================================================================
// The AIR.
// =============================================================================

#[derive(Clone)]
pub struct CoeffsEval {
    pub log_size: u32,
    pub r: SecureField,
    pub s: SecureField,
    pub relations: CoeffsRelations,
}

impl CoeffsEval {
    /// `s^t` powers as EF constants (drawn, so degree-0).
    fn s_power<E: EvalAtRow>(&self, t: usize) -> E::EF {
        let mut acc = SecureField::one();
        for _ in 0..t {
            acc *= self.s;
        }
        E::EF::from(acc)
    }
}

impl FrameworkEval for CoeffsEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every constraint is degree ≤ 2 (the ternary is enforced by a lookup,
        // not a cubic poly). The interaction-tree Horner `[-1,0]` mask REQUIRES
        // this bound to be exactly `log_size + 1`: at `+2` the composition-domain
        // doubling desynchronizes the shifted interaction mask and the OODS
        // consistency check fails (verified against the toy spike). Do not raise.
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // --- Preprocessed selectors ---
        let start = eval.get_preprocessed_column(pre_id("start"));
        let end = eval.get_preprocessed_column(pre_id("end"));
        let poly_id = eval.get_preprocessed_column(pre_id("poly_id"));
        let live_mask: Vec<E::F> = (0..MAX_DIGITS)
            .map(|t| eval.get_preprocessed_column(pre_id(&digit_mask_name(t))))
            .collect();
        let is_digit = eval.get_preprocessed_column(pre_id("is_digit"));
        let is_carry = eval.get_preprocessed_column(pre_id("is_carry"));
        let is_recomp = eval.get_preprocessed_column(pre_id("is_recomp"));
        let is_norm = eval.get_preprocessed_column(pre_id("is_norm"));
        let is_c = eval.get_preprocessed_column(pre_id("is_c"));
        let is_w = eval.get_preprocessed_column(pre_id("is_w"));
        let w_bind_id = eval.get_preprocessed_column(pre_id("w_bind_id"));
        let c_bind_id = eval.get_preprocessed_column(pre_id("c_bind_id"));

        // --- Base columns ---
        let enabler = eval.next_trace_mask();
        let digit: Vec<E::F> = (0..MAX_DIGITS).map(|_| eval.next_trace_mask()).collect();
        let recomp_cell = eval.next_trace_mask();
        let norm_a_hi = eval.next_trace_mask();
        let norm_b_hi = eval.next_trace_mask();
        let carry_hi: Vec<E::F> = (0..CARRY_DIGITS).map(|_| eval.next_trace_mask()).collect();

        // --- Interaction accumulator (prev, current) ---
        let coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(coords.each_ref().map(|p| p[0].clone()));
        let acc = E::combine_ef(coords.each_ref().map(|p| p[1].clone()));

        let one = E::F::from(M31::one());
        let b_ef = M31::from_u32_unchecked(B as u32);

        // C0: enabler boolean (ungated).
        eval.add_constraint(enabler.clone() * (one.clone() - enabler.clone()));

        // C1: tail-digit zero — cells past the live count must be 0 (I-1 free var).
        for t in 0..MAX_DIGITS {
            eval.add_constraint((one.clone() - live_mask[t].clone()) * digit[t].clone());
        }

        // C2: auxiliary columns are zero outside the row kinds that use them.
        // This lets the ten range denominators select values by addition instead
        // of multiplying witness values by selectors (which would raise degree).
        eval.add_constraint((one.clone() - is_recomp.clone()) * recomp_cell.clone());
        eval.add_constraint((one.clone() - is_norm.clone() - is_c.clone()) * norm_a_hi.clone());
        eval.add_constraint((one.clone() - is_norm.clone()) * norm_b_hi.clone());
        for hi in &carry_hi {
            eval.add_constraint((one.clone() - is_carry.clone()) * hi.clone());
        }
        eval.add_constraint(is_c.clone() * (norm_a_hi.clone() - digit[0].clone() - one.clone()));

        // C3: recomposition binding cell = Σ_t d_t·B^t (z,w rows, §3.4).
        let mut recomp_expr = E::F::from(M31::one()) * digit[0].clone();
        {
            let mut weight = b_ef;
            for d in digit.iter().skip(1) {
                recomp_expr += E::F::from(weight) * d.clone();
                weight *= b_ef;
            }
        }
        eval.add_constraint(is_recomp.clone() * (recomp_cell.clone() - recomp_expr));

        // C4: ten shared range streams. Every bound id is a constant-weighted
        // preprocessed selector; no witness column can choose a wider bound.
        let digit_offset = E::F::from(M31::from_u32_unchecked(DIGIT_OFFSET));
        let two_pow_13 = E::F::from(M31::from_u32_unchecked(1 << 13));
        let carry_offset = E::F::from(M31::from_u32_unchecked(CARRY_OFFSET as u32));
        let rc9_id = E::F::from(m31(RcKind::Rc9.bound_id()));
        let rc13_id = E::F::from(m31(RcKind::Rc13.bound_id()));
        let rc8_id = E::F::from(m31(RcKind::Rc8.bound_id()));
        let rc7_id = E::F::from(m31(RcKind::Rc7.bound_id()));
        let ternary_id = E::F::from(m31(RcKind::Ternary.bound_id()));

        // Slots 0..4: digit rc9 or carry low rc13.
        for t in 0..CARRY_DIGITS {
            let gate = is_digit.clone() * live_mask[t].clone();
            let value = digit[t].clone()
                + is_digit.clone() * digit_offset.clone()
                + is_carry.clone() * carry_offset.clone()
                - two_pow_13.clone() * carry_hi[t].clone();
            let value = attacked_stream_value::<E>(t, value);
            let bound_id = is_digit.clone() * rc9_id.clone() + is_carry.clone() * rc13_id.clone();
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                gate + is_carry.clone(),
                &[value, bound_id],
            ));
        }
        // Slot 5: sixth digit rc9 or first carry high rc8.
        let gate = is_digit.clone() * live_mask[5].clone();
        let value = digit[5].clone() + is_digit.clone() * digit_offset + carry_hi[0].clone();
        let value = attacked_stream_value::<E>(5, value);
        let bound_id = is_digit.clone() * rc9_id + is_carry.clone() * rc8_id.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            gate + is_carry.clone(),
            &[value, bound_id],
        ));

        // Slots 6..9: remaining carry highs or z norm splits. Slot 7 also
        // carries c+1 on c rows via the bound auxiliary above.
        let bound = E::F::from(M31::from_u32_unchecked(Z_NORM_BOUND as u32));
        let value = carry_hi[1].clone() + recomp_cell.clone() + is_norm.clone() * bound.clone()
            - two_pow_13.clone() * norm_a_hi.clone();
        let value = attacked_stream_value::<E>(6, value);
        let bound_id = is_carry.clone() * rc8_id.clone() + is_norm.clone() * rc13_id.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone(),
            &[value, bound_id],
        ));

        let value = attacked_stream_value::<E>(7, carry_hi[2].clone() + norm_a_hi.clone());
        let bound_id = is_carry.clone() * rc8_id.clone()
            + is_norm.clone() * rc7_id.clone()
            + is_c.clone() * ternary_id;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone() + is_c.clone(),
            &[value, bound_id],
        ));

        let value = carry_hi[3].clone() - recomp_cell.clone() + is_norm.clone() * bound
            - two_pow_13 * norm_b_hi.clone();
        let value = attacked_stream_value::<E>(8, value);
        let bound_id = is_carry.clone() * rc8_id.clone() + is_norm.clone() * rc13_id;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone(),
            &[value, bound_id],
        ));

        let value = attacked_stream_value::<E>(9, carry_hi[4].clone() + norm_b_hi.clone());
        let bound_id = is_carry.clone() * rc8_id + is_norm.clone() * rc7_id;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry + is_norm,
            &[value, bound_id],
        ));

        // C7: bivariate Horner (interaction). digit_row(s) = Σ_t d_t·s^t.
        let mut digit_row = E::EF::from(digit[0].clone());
        for (t, d) in digit.iter().enumerate().skip(1) {
            digit_row += self.s_power::<E>(t) * E::EF::from(d.clone());
        }
        let expected =
            E::EF::from(one - start.clone()) * acc_prev * E::EF::from(self.r) + digit_row;
        eval.add_constraint(acc.clone() - expected);

        // C8: EvalAtRs YIELD at group end (−end). Verifier-native fold uses (+).
        let mut tuple = Vec::with_capacity(relations::EVAL_ARITY);
        tuple.push(poly_id);
        tuple.extend(coords.iter().map(|p| p[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.relations.eval, -end, &tuple));

        // C9: WCell YIELD (−is_w) — the coeffs W-cell binding. `recomp_cell`
        // (= Σ_t d_t·B^t = w ∈ [0,q)) is the same value decomp uses; w_bind_id =
        // i·N+m is the shared key. Each w-coefficient is yielded EXACTLY once
        // (one w row per (i,m)); decomp consumes it exactly once. Value degree 1.
        let wtuple = [w_bind_id.clone(), recomp_cell.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.wcell,
            -is_w.clone(),
            &wtuple,
        ));

        // C10: CCell YIELD (−is_c) — the coeffs C-cell binding. digit[0] (= c,
        // encode_signed) with c_bind_id = m. Each challenge coefficient is
        // yielded once; sampleinball consumes it once. Value degree 1.
        let ctuple = [c_bind_id.clone(), digit[0].clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.ccell,
            -is_c.clone(),
            &ctuple,
        ));

        let _ = enabler; // enabler only gates via preprocessed masks (all active rows carry it); its boolean constraint is C0.

        eval.finalize_logup();
        eval
    }
}

pub type CoeffsComponent = FrameworkComponent<CoeffsEval>;

// =============================================================================
// Interaction trace.
// =============================================================================

/// The coeffs interaction claim (its own logup residue) plus the per-group
/// claimed evaluations (consumed by the verifier-native fold).
pub struct CoeffsInteraction {
    pub trace: Vec<ColEval>,
    pub claimed_sum: SecureField,
    /// `group_evals[poly_id]` = `P̂(r,s)` of that group.
    pub group_evals: Vec<SecureField>,
    /// The rc uses each table must provide (indexed by table value).
    pub rc_uses: RcUses,
}

/// Multiplicity seeds for the five tables (indexed by table value).
#[derive(Clone)]
pub struct RcUses {
    pub rc9: Vec<u32>,
    pub rc13: Vec<u32>,
    pub rc8: Vec<u32>,
    pub rc7: Vec<u32>,
    pub ternary: Vec<u32>,
}

impl RcUses {
    fn new() -> Self {
        Self {
            rc9: vec![0; 1 << 9],
            rc13: vec![0; 1 << 13],
            rc8: vec![0; 1 << 8],
            rc7: vec![0; 1 << 7],
            ternary: vec![0; 3],
        }
    }

    /// The multiplicity slice for a table kind.
    pub fn for_kind(&self, kind: RcKind) -> &[u32] {
        match kind {
            RcKind::Rc9 => &self.rc9,
            RcKind::Rc13 => &self.rc13,
            RcKind::Rc8 => &self.rc8,
            RcKind::Rc7 => &self.rc7,
            RcKind::Ternary => &self.ternary,
        }
    }
}

pub fn gen_coeffs_interaction(
    witness: &MlDsaWitness,
    log_size: u32,
    r: SecureField,
    s: SecureField,
    relations: &CoeffsRelations,
) -> CoeffsInteraction {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let active = sched.len();

    // s-powers up to MAX_DIGITS-1.
    let mut s_pow = [SecureField::one(); MAX_DIGITS];
    for t in 1..MAX_DIGITS {
        s_pow[t] = s_pow[t - 1] * s;
    }

    // --- Accumulator chain (coset order) ---
    let zero = SecureField::from(m31(0));
    let mut acc = vec![zero; rows];
    let mut rc_uses = RcUses::new();
    let mut group_evals = vec![zero; layout::N_GROUPS];

    for row in 0..rows {
        let info = if row < active { Some(sched[row]) } else { None };
        let is_start = info.map(|i| i.in_group == 0).unwrap_or(false);
        let prev = if is_start || row == 0 {
            zero
        } else {
            acc[row - 1]
        };
        let digit_row = match info {
            Some(info) => {
                let digits = row_digits(witness, &info);
                let mut dr = zero;
                for t in 0..MAX_DIGITS {
                    dr += s_pow[t] * SecureField::from(encode_signed(digits[t]));
                }
                // Seed rc multiplicities for this row.
                seed_rc_uses(&mut rc_uses, &info, &digits);
                dr
            }
            None => zero,
        };
        acc[row] = prev * r + digit_row;
        if let Some(info) = info {
            if info.in_group == info.group.coeffs - 1 {
                group_evals[info.group.poly_id as usize] = acc[row];
            }
        }
    }

    // 4 accumulator coordinate columns first.
    let mut trace: Vec<ColEval> = (0..N_ACC_COORD_COLS)
        .map(|coord| {
            col_eval(
                log_size,
                acc.iter().map(|v| v.to_m31_array()[coord]).collect(),
            )
        })
        .collect();

    // --- Logup entries (eval order matches evaluate()) ---
    let row_lookup = circle_row_to_coset(log_size);
    let one = SecureField::one();
    let vec_rows = 1usize << (log_size - stwo::prover::backend::simd::m31::LOG_N_LANES);

    // Build every fraction (numerator, denominator) per coset row, in the exact
    // AIR emission order, then pack into vec-rows and batch.
    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let mut claimed = zero;

    // helper closure to push one logup entry stream.
    let push_entry = |frac_of: &dyn Fn(usize) -> (SecureField, SecureField),
                      entries: &mut Vec<(Vec<PackedQM31>, Vec<PackedQM31>)>,
                      claimed: &mut SecureField| {
        let mut nums = Vec::with_capacity(vec_rows);
        let mut dens = Vec::with_capacity(vec_rows);
        for vr in 0..vec_rows {
            let mut n = [zero; N_LANES];
            let mut d = [one; N_LANES];
            for lane in 0..N_LANES {
                let coset = row_lookup[vr * N_LANES + lane];
                let (num, den) = frac_of(coset);
                n[lane] = num;
                d[lane] = den;
                *claimed += num / den;
            }
            nums.push(PackedQM31::from_array(n));
            dens.push(PackedQM31::from_array(d));
        }
        entries.push((nums, dens));
    };

    // Precompute per-coset digits (avoid recomputation across the many streams).
    let coset_digits: Vec<Option<([i128; MAX_DIGITS], Group, usize)>> = (0..rows)
        .map(|coset| {
            if coset < active {
                let info = sched[coset];
                Some((row_digits(witness, &info), info.group, info.in_group))
            } else {
                None
            }
        })
        .collect();

    // C4 ten shared range streams, matching the AIR slot assignment exactly.
    for stream in 0..N_RANGE_STREAMS {
        push_entry(
            &|coset| {
                let selected = match &coset_digits[coset] {
                    Some((digits, group, _)) if group.kind == Kind::Carry => {
                        let t = stream % CARRY_DIGITS;
                        let shifted = digits[t] + CARRY_OFFSET as i128;
                        if stream < CARRY_DIGITS {
                            Some((m31((shifted & ((1 << 13) - 1)) as u32), RcKind::Rc13))
                        } else {
                            Some((m31((shifted >> 13) as u32), RcKind::Rc8))
                        }
                    }
                    Some((digits, group, _)) if stream < group.kind.live_digits() => Some((
                        encode_signed(digits[stream]) + m31(DIGIT_OFFSET),
                        RcKind::Rc9,
                    )),
                    Some((digits, group, _)) if group.kind == Kind::Z && stream >= 6 => {
                        let cell = recompose(digits);
                        let a = cell + Z_NORM_BOUND as i128;
                        let b = Z_NORM_BOUND as i128 - cell;
                        Some(match stream {
                            6 => (m31((a & ((1 << 13) - 1)) as u32), RcKind::Rc13),
                            7 => (m31((a >> 13) as u32), RcKind::Rc7),
                            8 => (m31((b & ((1 << 13) - 1)) as u32), RcKind::Rc13),
                            9 => (m31((b >> 13) as u32), RcKind::Rc7),
                            _ => unreachable!(),
                        })
                    }
                    Some((digits, group, _)) if group.kind == Kind::C && stream == 7 => {
                        Some((encode_signed(digits[0]) + m31(1), RcKind::Ternary))
                    }
                    _ => None,
                };
                match selected {
                    Some((value, kind)) => {
                        let value = attacked_stream_boundary(stream).map_or(value, m31);
                        (one, relations.range.combine(&[value, m31(kind.bound_id())]))
                    }
                    None => (zero, one),
                }
            },
            &mut entries,
            &mut claimed,
        );
    }
    // C8 eval YIELD at group-end (−1).
    push_entry(
        &|coset| match &coset_digits[coset] {
            Some((_, group, in_group)) if *in_group == group.coeffs - 1 => {
                let coords = acc[coset].to_m31_array();
                let tuple = [
                    m31(group.poly_id),
                    coords[0],
                    coords[1],
                    coords[2],
                    coords[3],
                ];
                (-one, relations.eval.combine(&tuple))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // C9 WCell YIELD (−1) — w rows only. Mirrors the evaluate() gate `-is_w`.
    // Value = recompose(digits) = w ∈ [0,q); key = i·N+m.
    push_entry(
        &|coset| match &coset_digits[coset] {
            Some((digits, group, in_group)) if group.kind == Kind::W => {
                let i = (group.poly_id - layout::POLY_ID_W0) as usize;
                let m = group.coeffs - 1 - in_group;
                let w_bind_id = (i * crate::constants::N + m) as u32;
                let w = encode_signed(recompose(digits));
                let tuple = [m31(w_bind_id), w];
                (-one, relations.wcell.combine(&tuple))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );
    // C10 CCell YIELD (−1) — c rows only. Mirrors `-is_c`. Value = digit[0]
    // (encode_signed c); key = m.
    push_entry(
        &|coset| match &coset_digits[coset] {
            Some((digits, group, in_group)) if group.kind == Kind::C => {
                let m = group.coeffs - 1 - in_group;
                let c = encode_signed(digits[0]);
                let tuple = [m31(m as u32), c];
                (-one, relations.ccell.combine(&tuple))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );

    // Batch the fraction streams in pairs, mirroring finalize_logup_batched(2).
    let mut logup = LogupTraceGenerator::new(log_size);
    for chunk in entries.chunks(LOGUP_BATCH) {
        logup.col_from_fn(|vr| {
            let mut num = chunk[0].0[vr];
            let mut den = chunk[0].1[vr];
            for (nn, dd) in chunk[1..].iter() {
                let n2 = nn[vr];
                let d2 = dd[vr];
                num = num * d2 + n2 * den;
                den *= d2;
            }
            (num, den)
        });
    }
    let (logup_trace, claimed_sum) = logup.finalize_last();
    trace.extend(logup_trace);
    debug_assert_eq!(claimed_sum, claimed, "coeffs logup claimed sum mismatch");

    CoeffsInteraction {
        trace,
        claimed_sum,
        group_evals,
        rc_uses,
    }
}

fn seed_rc_uses(rc: &mut RcUses, info: &RowInfo, digits: &[i128; MAX_DIGITS]) {
    match info.group.kind {
        Kind::Carry => {
            for t in 0..CARRY_DIGITS {
                let shifted = digits[t] + CARRY_OFFSET as i128;
                rc.rc13[(shifted & ((1 << 13) - 1)) as usize] += 1;
                rc.rc8[(shifted >> 13) as usize] += 1;
            }
        }
        Kind::Z => {
            let live = info.group.kind.live_digits();
            for t in 0..live {
                let v = (encode_signed(digits[t]) + m31(DIGIT_OFFSET)).0 as usize;
                rc.rc9[v] += 1;
            }
            let cell = recompose(digits);
            let a = cell + Z_NORM_BOUND as i128;
            let b = Z_NORM_BOUND as i128 - cell;
            rc.rc13[(a & ((1 << 13) - 1)) as usize] += 1;
            rc.rc7[(a >> 13) as usize] += 1;
            rc.rc13[(b & ((1 << 13) - 1)) as usize] += 1;
            rc.rc7[(b >> 13) as usize] += 1;
        }
        _ => {
            let live = info.group.kind.live_digits();
            for t in 0..live {
                let v = (encode_signed(digits[t]) + m31(DIGIT_OFFSET)).0 as usize;
                rc.rc9[v] += 1;
            }
            if info.group.kind == Kind::C {
                // Ternary membership use: c+1 ∈ {0,1,2}.
                let v = (encode_signed(digits[0]) + m31(1)).0 as usize;
                rc.ternary[v] += 1;
            }
        }
    }
}
