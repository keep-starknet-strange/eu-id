//! This module implements the tall stacked AIR component for the ML-DSA
//! integer-lift constraints.
//!
//! Every witnessed / carry polynomial's balanced base-`B` (`B = 2^9`) digits are
//! stacked into contiguous Horner groups ([`layout`]). z/w pair two three-digit
//! coefficients in the existing six digit columns; other kinds retain one
//! coefficient per row. Per row the component:
//!   * range-checks every digit cell (dedicated 2^9 table, offset `+2^8`);
//!   * for carry rows, range-checks `|C| ≤ 2^20` via a `C+2^20` 13+8 split;
//!   * recomposes both packed z/w coefficients (the first through
//!     `recomp_cell`, the second directly from its digit triplet);
//!   * enforces the exact z-norm `|z| ≤ γ1−β−1 = 524_091` with a two-sided
//!     offset;
//!   * enforces the ternary `c ∈ {−1,0,1}` via a `{0,1,2}` membership lookup;
//!   * runs the bivariate Horner accumulator (interaction tree) at the drawn
//!     `(r,s)`, emitting `P̂(r,s)` at each group end into [`EvalAtRsRelation`].
//!
//! Public-key mode closes those evaluations with [`crate::verifier_native`].
//! Hosted private-key mode joins them to the proven `A` / scaled-`t1`
//! evaluations and closes the same complete identity in
//! [`crate::private_key_eval`].
//!
//! ## Base column layout (uniform over all `2^log_size` rows)
//!
//! | idx | column        | meaning |
//! |-----|---------------|---------|
//! | 0-5 | `digit[0..6]` | two z/w triplets, one wider coefficient, or carry cells |
//! | 6   | `recomp_cell` | first z/w coefficient `Σ_t d_t·B^t`; else 0 |
//! | 7   | `norm_a_hi`   | first z coefficient: 7-bit hi of `cell + 524_091` |
//! | 8   | `norm_b_hi`   | first z coefficient: 7-bit hi of `524_091 − cell` |
//! | 9-13| `carry_hi[0..5]` | 8-bit hi of `C_{m,t}+2^20` (carry rows) |
//! |14   | `norm2_a_hi` | second z coefficient: 7-bit hi of `cell + 524_091` |
//! |15   | `norm2_b_hi` | second z coefficient: 7-bit hi of `524_091 − cell` |
//!
//! ## Preprocessed columns
//! `start, end, poly_id, live_mask_4, is_carry, is_norm, is_c, is_w,
//!  w_bind_id, c_bind_id, profile_active` — all row-index-deterministic. The
//! AIR derives the other live masks and selectors from these columns
//! (`paired_continue = is_recomp·(1−start)` inline; both factors are already
//! preprocessed/derived columns, so it costs nothing to recompute).
//!
//! ## Constraint degrees
//!
//! Base constraints have degree 2 or less, except the derived paired Horner
//! continuation, which has degree 3.
//! Four-way LogUp batching reaches degree 5, so the unlocked bound is
//! `log_size + 2`. The interaction-tree Horner `[-1,0]` mask remains safe under
//! the engine's uniform composition split. The `decomp` component uses the same
//! design. The ternary remains a LOOKUP, not the cubic `c(c−1)(c+1)`.
//! | site | degree |
//! |------|--------|
//! | tail-digit zero `(1−mask)·digit` | 2 |
//! | recomp `is_recomp·(cell − Σ d·B^t)` | 2 |
//! | z-norm rc uses (a/b lo+hi, degree-1 values) | 1 |
//! | carry rc uses (lo degree-1 expr, hi cell) | 1 |
//! | ternary use `c+1 ∈ {0,1,2}` (lookup) | 1 |
//! | ordinary Horner `acc − ((1−start)·acc_prev·r + Σ d·s^t)` | 2 |
//! | paired Horner `is_recomp·(1−start)·acc_prev·r` | 3 |
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
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::air_util::{circle_row_to_coset, col_eval, enc_signed, m31, ColEval};
use crate::profile::MlDsaProfile;
use crate::witness::{MlDsaWitness, B};
use layout::{groups, Group, Kind, CARRY_DIGITS, MAX_DIGITS};
use relations::CoeffsRelations;
use tables::RcKind;

#[cfg(test)]
thread_local! {
    static RANGE_BOUNDARY_ATTACK: core::cell::RefCell<Option<RcKind>> =
        const { core::cell::RefCell::new(None) };
}

#[cfg(test)]
struct CoeffsRangeBoundaryGuard;

#[cfg(test)]
impl Drop for CoeffsRangeBoundaryGuard {
    fn drop(&mut self) {
        RANGE_BOUNDARY_ATTACK.with(|attack| *attack.borrow_mut() = None);
    }
}

#[cfg(test)]
fn install_range_boundary_attack(kind: RcKind) -> CoeffsRangeBoundaryGuard {
    RANGE_BOUNDARY_ATTACK.with(|attack| *attack.borrow_mut() = Some(kind));
    CoeffsRangeBoundaryGuard
}

#[cfg(test)]
fn attacked_stream_boundary(stream: usize) -> Option<u32> {
    RANGE_BOUNDARY_ATTACK.with(|attack| {
        attack.borrow().and_then(|kind| {
            let occupied = match kind {
                RcKind::Rc9 => stream <= 5,
                RcKind::Rc13 => matches!(stream, 0..=4 | 6 | 8 | 10 | 12),
                RcKind::Rc8 => carry_high_index(stream).is_some(),
                RcKind::Rc7 => matches!(stream, 7 | 9 | 11 | 13),
                RcKind::Ternary => stream == 7,
            };
            occupied.then_some(kind.n_values() as u32)
        })
    })
}

#[cfg(test)]
fn attacked_stream_value<E: EvalAtRow>(stream: usize, value: E::F) -> E::F {
    attacked_stream_boundary(stream).map_or(value, |boundary| E::F::from(m31(boundary)))
}

/// Exact inclusive response norm bound for the selected profile.
pub const fn z_norm_bound(profile: MlDsaProfile) -> i64 {
    (profile.gamma1() - profile.beta() - 1) as i64
}
/// Carry offset `2^20`.
pub const CARRY_OFFSET: i64 = 1 << 20;
/// Digit offset `2^8` into the `2^9` window.
pub const DIGIT_OFFSET: u32 = 1 << 8;

// --- Base column indices ------------------------------------------------------
const COL_DIGIT0: usize = 0;
const COL_RECOMP: usize = COL_DIGIT0 + MAX_DIGITS; // 6
const COL_NORM_A_HI: usize = COL_RECOMP + 1; // 7
const COL_NORM_B_HI: usize = COL_NORM_A_HI + 1; // 8
const COL_CARRY_HI0: usize = COL_NORM_B_HI + 1; // 9
const COL_NORM2_A_HI: usize = COL_CARRY_HI0 + CARRY_DIGITS; // 14
const COL_NORM2_B_HI: usize = COL_NORM2_A_HI + 1; // 15
/// Total base columns.
pub const N_BASE_COLS: usize = COL_NORM2_B_HI + 1; // 16

/// Carry-high streams are interleaved with z norm streams. The permutation
/// lets each carry-high lookup share a stream with a disjoint z norm lookup
/// while keeping every relation key affine and batch-4 legal.
const fn carry_high_index(stream: usize) -> Option<usize> {
    match stream {
        6 => Some(2),
        7 => Some(3),
        8 => Some(4),
        11 => Some(0),
        13 => Some(1),
        _ => None,
    }
}

// --- Preprocessed column names ------------------------------------------------
fn pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_coeffs_{name}"),
    }
}

fn profile_active_id(profile: MlDsaProfile) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_coeffs_{profile:?}_profile_active"),
    }
}

fn profile_pre_id(profile: MlDsaProfile, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_coeffs_{profile:?}_{name}"),
    }
}

/// All preprocessed column IDs for the selected profile, in commit order.
pub fn coeffs_preprocessed_ids(profile: MlDsaProfile) -> Vec<PreProcessedColumnId> {
    // On a paired w row, `w_bind_id` is the first WCell key and the otherwise
    // idle `c_bind_id` is the second key. On c rows, `c_bind_id = m`.
    vec![
        profile_pre_id(profile, "start"),
        pre_id("end"),
        pre_id("poly_id"),
        profile_pre_id(profile, "live_mask_4"),
        profile_pre_id(profile, "is_carry"),
        profile_pre_id(profile, "is_norm"),
        profile_pre_id(profile, "is_c"),
        profile_pre_id(profile, "is_w"),
        pre_id("w_bind_id"),
        pre_id("c_bind_id"),
        profile_active_id(profile),
    ]
}

/// Fourteen shared range streams plus the four distinct relation yields. Range
/// kinds occupy disjoint row slots and are namespaced by fixed bound ids.
pub const N_RANGE_STREAMS: usize = 14;
pub const N_LOGUP_ENTRIES: usize = N_RANGE_STREAMS
    + 1                                             // eval yield
    + 2                                             // two WCell yields per paired w row
    + 1; // CCell yield (c cells)
/// Four fractions per interaction column, matching the `decomp` precedent.
pub const LOGUP_BATCH: usize = 4;
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
        for in_group in 0..group.rows() {
            rows.push(RowInfo { group, in_group });
        }
    }
    rows
}

// =============================================================================
// Preprocessed trace.
// =============================================================================

fn group_is_active(profile: MlDsaProfile, group: Group) -> bool {
    let index = group.poly_id as usize;
    match group.kind {
        Kind::Z => index - (layout::POLY_ID_Z0 as usize) < profile.l(),
        Kind::W => index - (layout::POLY_ID_W0 as usize) < profile.k(),
        Kind::E => index - (layout::POLY_ID_E0 as usize) < profile.k(),
        Kind::V => index - (layout::POLY_ID_V0 as usize) < profile.k(),
        Kind::C => true,
        Kind::Carry => index - (layout::POLY_ID_CARRY0 as usize) < profile.k(),
    }
}

pub fn gen_coeffs_preprocessed(profile: MlDsaProfile, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();

    let mut start = vec![m31(0); rows];
    let mut end = vec![m31(0); rows];
    let mut poly_id = vec![m31(0); rows];
    let mut live_mask_4 = vec![m31(0); rows];
    let mut is_carry = vec![m31(0); rows];
    let mut is_norm = vec![m31(0); rows];
    let mut is_c = vec![m31(0); rows];
    let mut is_w = vec![m31(0); rows];
    let mut w_bind_id = vec![m31(0); rows];
    let mut c_bind_id = vec![m31(0); rows];
    let mut profile_active = vec![m31(0); rows];

    for (row, info) in sched.iter().enumerate() {
        let g = info.group;
        poly_id[row] = m31(g.poly_id);
        let group_active = group_is_active(profile, g);
        profile_active[row] = m31(u32::from(group_active));
        end[row] = m31(u32::from(info.in_group == g.rows() - 1));
        if group_active {
            start[row] = m31(u32::from(info.in_group == 0));
            live_mask_4[row] = m31(u32::from(g.kind.row_live_digits() > 4));
            is_carry[row] = m31(u32::from(g.kind == Kind::Carry));
            is_norm[row] = m31(u32::from(g.kind == Kind::Z));
            is_c[row] = m31(u32::from(g.kind == Kind::C));
            is_w[row] = m31(u32::from(g.kind == Kind::W));
        }
        if g.kind == Kind::C {
            let m = g
                .coefficient_index(info.in_group, 0)
                .expect("c row has one coefficient");
            c_bind_id[row] = m31(m as u32);
        }
        if g.kind == Kind::W {
            let i = (g.poly_id - layout::POLY_ID_W0) as usize;
            let first = g
                .coefficient_index(info.in_group, 0)
                .expect("paired w row has a first coefficient");
            let second = g
                .coefficient_index(info.in_group, 1)
                .expect("paired w row has a second coefficient");
            w_bind_id[row] = m31((i * crate::constants::N + first) as u32);
            c_bind_id[row] = m31((i * crate::constants::N + second) as u32);
        }
    }

    [
        start,
        end,
        poly_id,
        live_mask_4,
        is_carry,
        is_norm,
        is_c,
        is_w,
        w_bind_id,
        c_bind_id,
    ]
    .into_iter()
    .map(|v| col_eval(log_size, v))
    .chain([col_eval(log_size, profile_active)])
    .collect()
}

// =============================================================================
// Base trace.
// =============================================================================

/// Per-row concrete values, filled from the witness (coset order).
pub fn gen_coeffs_base_trace(witness: &MlDsaWitness, log_size: u32) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    let sched = row_schedule();
    let mut cols: Vec<Vec<M31>> = (0..N_BASE_COLS).map(|_| vec![m31(0); rows]).collect();

    let norm_bound = z_norm_bound(witness.profile);
    for (row, info) in sched.iter().enumerate() {
        if !group_is_active(witness.profile, info.group) {
            continue;
        }
        let digits = row_digits(witness, info);
        for (t, &d) in digits.iter().enumerate() {
            cols[COL_DIGIT0 + t][row] = enc_signed(d);
        }
        match info.group.kind {
            Kind::Z | Kind::W => {
                let [first, second] = paired_recompositions(&digits);
                cols[COL_RECOMP][row] = enc_signed(first);
                if info.group.kind == Kind::Z {
                    // Both packed z coefficients receive the exact two-sided
                    // norm decomposition.
                    let first_a = first + norm_bound as i128;
                    let first_b = norm_bound as i128 - first;
                    let second_a = second + norm_bound as i128;
                    let second_b = norm_bound as i128 - second;
                    cols[COL_NORM_A_HI][row] = m31((first_a >> 13) as u32);
                    cols[COL_NORM_B_HI][row] = m31((first_b >> 13) as u32);
                    cols[COL_NORM2_A_HI][row] = m31((second_a >> 13) as u32);
                    cols[COL_NORM2_B_HI][row] = m31((second_b >> 13) as u32);
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
                cols[COL_NORM_A_HI][row] = enc_signed(digits[0] + 1);
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
    // Coefficients are laid out HIGH-to-LOW. z/w rows hold adjacent
    // `(m, m−1)` coefficients and the `r²/r` transition below is exactly two
    // ordinary Horner steps.
    let mut out = [0i128; MAX_DIGITS];
    match g.kind {
        Kind::Z => {
            let j = (g.poly_id - layout::POLY_ID_Z0) as usize;
            let first = g
                .coefficient_index(info.in_group, 0)
                .expect("paired z row has a first coefficient");
            let second = g
                .coefficient_index(info.in_group, 1)
                .expect("paired z row has a second coefficient");
            out[..3].copy_from_slice(&witness.digits.z[j][first]);
            out[3..].copy_from_slice(&witness.digits.z[j][second]);
        }
        Kind::W => {
            let i = (g.poly_id - layout::POLY_ID_W0) as usize;
            let first = g
                .coefficient_index(info.in_group, 0)
                .expect("paired w row has a first coefficient");
            let second = g
                .coefficient_index(info.in_group, 1)
                .expect("paired w row has a second coefficient");
            out[..3].copy_from_slice(&witness.digits.w[i][first]);
            out[3..].copy_from_slice(&witness.digits.w[i][second]);
        }
        Kind::E => {
            let i = (g.poly_id - layout::POLY_ID_E0) as usize;
            let m = g.coefficient_index(info.in_group, 0).unwrap();
            out[..4].copy_from_slice(&witness.digits.e[i][m]);
        }
        Kind::V => {
            let i = (g.poly_id - layout::POLY_ID_V0) as usize;
            let m = g.coefficient_index(info.in_group, 0).unwrap();
            out[..6].copy_from_slice(&witness.digits.v[i][m]);
        }
        Kind::C => {
            let m = g.coefficient_index(info.in_group, 0).unwrap();
            out[0] = witness.digits.c[m];
        }
        Kind::Carry => {
            let i = (g.poly_id - layout::POLY_ID_CARRY0) as usize;
            let m = g.coefficient_index(info.in_group, 0).unwrap();
            let carry = &witness.rows[i].carry[m]; // [i128; T_MAX+1]
            out[..CARRY_DIGITS].copy_from_slice(&carry[..CARRY_DIGITS]);
        }
    }
    out
}

fn recompose_digits(digits: &[i128]) -> i128 {
    let mut acc = 0i128;
    let mut weight = 1i128;
    for &d in digits {
        acc += d * weight;
        weight *= B;
    }
    acc
}

fn paired_recompositions(digits: &[i128; MAX_DIGITS]) -> [i128; 2] {
    let split = Kind::Z.live_digits();
    [
        recompose_digits(&digits[..split]),
        recompose_digits(&digits[split..]),
    ]
}

// =============================================================================
// The AIR.
// =============================================================================

#[derive(Clone)]
pub struct CoeffsEval {
    pub log_size: u32,
    pub profile: MlDsaProfile,
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
        // Every base constraint is degree ≤ 2. Four-way LogUp over degree-1
        // denominators reaches degree 5, covered by `log_size + 2`. The Horner
        // `[-1,0]` mask is safe under the engine's uniform composition split,
        // matching the `decomp` precedent.
        self.log_size + 2
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // --- Preprocessed selectors ---
        let start = eval.get_preprocessed_column(profile_pre_id(self.profile, "start"));
        // Every fixed-shape polynomial, including an inactive profile tail,
        // yields an evaluation. Inactive traces are constrained to zero, so
        // this binds the fold claim to `(poly_id, 0)` instead of leaving it
        // unconstrained.
        let end = eval.get_preprocessed_column(pre_id("end"));
        let poly_id = eval.get_preprocessed_column(pre_id("poly_id"));
        let live_mask_4 = eval.get_preprocessed_column(profile_pre_id(self.profile, "live_mask_4"));
        let is_carry = eval.get_preprocessed_column(profile_pre_id(self.profile, "is_carry"));
        let is_norm = eval.get_preprocessed_column(profile_pre_id(self.profile, "is_norm"));
        let is_c = eval.get_preprocessed_column(profile_pre_id(self.profile, "is_c"));
        let is_w = eval.get_preprocessed_column(profile_pre_id(self.profile, "is_w"));
        let w_bind_id = eval.get_preprocessed_column(pre_id("w_bind_id"));
        let c_bind_id = eval.get_preprocessed_column(pre_id("c_bind_id"));
        let profile_active = eval.get_preprocessed_column(profile_active_id(self.profile));

        let active = profile_active.clone();

        let is_digit = active.clone() - is_carry.clone();
        let is_recomp = is_norm.clone() + is_w.clone();
        let live_mask = [
            active.clone(),
            active.clone() - is_c.clone(),
            active.clone() - is_c.clone(),
            active.clone() - is_c.clone(),
            live_mask_4.clone(),
            live_mask_4 - is_carry.clone(),
        ];

        // --- Base columns ---
        let digit: Vec<E::F> = (0..MAX_DIGITS).map(|_| eval.next_trace_mask()).collect();
        let recomp_cell = eval.next_trace_mask();
        let norm_a_hi = eval.next_trace_mask();
        let norm_b_hi = eval.next_trace_mask();
        let carry_hi: Vec<E::F> = (0..CARRY_DIGITS).map(|_| eval.next_trace_mask()).collect();
        let norm2_a_hi = eval.next_trace_mask();
        let norm2_b_hi = eval.next_trace_mask();

        // --- Interaction accumulator (prev, current) ---
        let coords: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(coords.each_ref().map(|p| p[0].clone()));
        let acc = E::combine_ef(coords.each_ref().map(|p| p[1].clone()));

        let one = E::F::from(M31::one());
        let b_ef = M31::from_u32_unchecked(B as u32);

        // The internal trace retains the maximum ML-DSA shape. Rows outside
        // the verifier-selected profile are fixed to zero and cannot affect
        // the live identity.
        let inactive = one.clone() - profile_active;
        for value in digit
            .iter()
            .chain(core::iter::once(&recomp_cell))
            .chain(core::iter::once(&norm_a_hi))
            .chain(core::iter::once(&norm_b_hi))
            .chain(carry_hi.iter())
            .chain(core::iter::once(&norm2_a_hi))
            .chain(core::iter::once(&norm2_b_hi))
        {
            eval.add_constraint(inactive.clone() * value.clone());
        }

        // Cells after the live digit count must be zero.
        for t in 0..MAX_DIGITS {
            eval.add_constraint((one.clone() - live_mask[t].clone()) * digit[t].clone());
        }

        // Auxiliary columns are zero outside the row kinds that use them.
        // This lets the range denominators select values by addition instead
        // of multiplying witness values by selectors (which would raise degree).
        eval.add_constraint((one.clone() - is_recomp.clone()) * recomp_cell.clone());
        eval.add_constraint((one.clone() - is_norm.clone() - is_c.clone()) * norm_a_hi.clone());
        eval.add_constraint((one.clone() - is_norm.clone()) * norm_b_hi.clone());
        for hi in &carry_hi {
            eval.add_constraint((one.clone() - is_carry.clone()) * hi.clone());
        }
        eval.add_constraint((one.clone() - is_norm.clone()) * norm2_a_hi.clone());
        eval.add_constraint((one.clone() - is_norm.clone()) * norm2_b_hi.clone());
        eval.add_constraint(is_c.clone() * (norm_a_hi.clone() - digit[0].clone() - one.clone()));

        // The first packed coefficient uses a recomposition cell. The second
        // coefficient is recomposed directly from its triplet wherever it is
        // consumed (norm and WCell), leaving no auxiliary value to bind.
        let split = Kind::Z.live_digits();
        let mut first_recomp_expr = E::F::from(M31::one()) * digit[0].clone();
        let mut second_recomp_expr = E::F::from(M31::one()) * digit[split].clone();
        let mut weight = b_ef;
        for t in 1..split {
            first_recomp_expr += E::F::from(weight) * digit[t].clone();
            second_recomp_expr += E::F::from(weight) * digit[split + t].clone();
            weight *= b_ef;
        }
        eval.add_constraint(is_recomp.clone() * (recomp_cell.clone() - first_recomp_expr.clone()));

        // Fourteen shared range streams. Every bound id is a constant-weighted
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
            #[cfg(test)]
            let value = attacked_stream_value::<E>(t, value);
            let bound_id = is_digit.clone() * rc9_id.clone() + is_carry.clone() * rc13_id.clone();
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                gate + is_carry.clone(),
                &[value, bound_id],
            ));
        }
        // Slot 5: sixth digit rc9. Carry highs are interleaved below.
        let gate = is_digit.clone() * live_mask[5].clone();
        let value = digit[5].clone() + is_digit.clone() * digit_offset;
        #[cfg(test)]
        let value = attacked_stream_value::<E>(5, value);
        let bound_id = is_digit.clone() * rc9_id;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            gate,
            &[value, bound_id],
        ));

        // Slots 6..9: first z coefficient's exact norm, interleaved with carry
        // highs 2..4. Slot 7 also carries c+1 on c rows.
        let bound = E::F::from(M31::from_u32_unchecked(z_norm_bound(self.profile) as u32));
        let value = carry_hi[2].clone() + recomp_cell.clone() + is_norm.clone() * bound.clone()
            - two_pow_13.clone() * norm_a_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(6, value);
        let bound_id = is_carry.clone() * rc8_id.clone() + is_norm.clone() * rc13_id.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone(),
            &[value, bound_id],
        ));

        let value = carry_hi[3].clone() + norm_a_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(7, value);
        let bound_id = is_carry.clone() * rc8_id.clone()
            + is_norm.clone() * rc7_id.clone()
            + is_c.clone() * ternary_id;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone() + is_c.clone(),
            &[value, bound_id],
        ));

        let value = carry_hi[4].clone() - recomp_cell.clone() + is_norm.clone() * bound.clone()
            - two_pow_13.clone() * norm_b_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(8, value);
        let bound_id = is_carry.clone() * rc8_id.clone() + is_norm.clone() * rc13_id.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone(),
            &[value, bound_id],
        ));

        let value = norm_b_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(9, value);
        let bound_id = is_norm.clone() * rc7_id.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_norm.clone(),
            &[value, bound_id],
        ));

        // Slots 10..13: second z coefficient's exact norm. Streams 11/13
        // simultaneously range-check carry highs 0/1 on disjoint carry rows.
        let value = second_recomp_expr.clone() + is_norm.clone() * bound.clone()
            - two_pow_13.clone() * norm2_a_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(10, value);
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_norm.clone(),
            &[value, is_norm.clone() * rc13_id.clone()],
        ));

        let value = carry_hi[0].clone() + norm2_a_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(11, value);
        let bound_id = is_carry.clone() * rc8_id.clone() + is_norm.clone() * rc7_id.clone();
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone(),
            &[value, bound_id],
        ));

        let value =
            -second_recomp_expr.clone() + is_norm.clone() * bound - two_pow_13 * norm2_b_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(12, value);
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_norm.clone(),
            &[value, is_norm.clone() * rc13_id],
        ));

        let value = carry_hi[1].clone() + norm2_b_hi.clone();
        #[cfg(test)]
        let value = attacked_stream_value::<E>(13, value);
        let bound_id = is_carry.clone() * rc8_id + is_norm.clone() * rc7_id;
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            is_carry.clone() + is_norm.clone(),
            &[value, bound_id],
        ));

        // The bivariate Horner step. z/w perform two ordinary steps in one
        // row. `paired_continue = is_recomp·(1−start)` is derived from the
        // fixed schedule. The resulting degree-3 term remains below the
        // component's degree-5 bound.
        let mut ordinary_digit_row = E::EF::from(digit[0].clone());
        for (t, d) in digit.iter().enumerate().skip(1) {
            ordinary_digit_row += self.s_power::<E>(t) * E::EF::from(d.clone());
        }
        let mut first_digit_row = E::EF::from(digit[0].clone());
        let mut second_digit_row = E::EF::from(digit[split].clone());
        for t in 1..split {
            let s_power = self.s_power::<E>(t);
            first_digit_row += s_power.clone() * E::EF::from(digit[t].clone());
            second_digit_row += s_power * E::EF::from(digit[split + t].clone());
        }
        let r_ef = E::EF::from(self.r);
        let paired_digit_row = first_digit_row * r_ef.clone() + second_digit_row;
        let digit_row = ordinary_digit_row.clone()
            + E::EF::from(is_recomp.clone()) * (paired_digit_row - ordinary_digit_row);
        let paired_continue = is_recomp.clone() * (one.clone() - start.clone());
        let expected = E::EF::from(active.clone() - start) * acc_prev.clone() * r_ef
            + E::EF::from(paired_continue) * acc_prev * E::EF::from(self.r * self.r - self.r)
            + digit_row;
        eval.add_constraint(acc.clone() - expected);

        // EvalAtRs yields at group end (−end). The verifier-native fold uses (+).
        let mut tuple = Vec::with_capacity(relations::EVAL_ARITY);
        tuple.push(poly_id);
        tuple.extend(coords.iter().map(|p| p[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.relations.eval, -end, &tuple));

        // Two WCell yields (−is_w), one for each packed w coefficient.
        // `c_bind_id` is otherwise idle on w rows and carries the second exact
        // key. Both recompositions are affine in the digit cells.
        let wtuple = [w_bind_id.clone(), recomp_cell.clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.wcell,
            -is_w.clone(),
            &wtuple,
        ));
        let wtuple = [c_bind_id.clone(), second_recomp_expr];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.wcell,
            -is_w.clone(),
            &wtuple,
        ));

        // CCell yields (−is_c) for the coeffs C-cell binding. digit[0] (= c,
        // enc_signed) with c_bind_id = m. Each challenge coefficient is
        // yielded once; sampleinball consumes it once. Value degree 1.
        let ctuple = [c_bind_id.clone(), digit[0].clone()];
        eval.add_to_relation(RelationEntry::base(
            &self.relations.ccell,
            -is_c.clone(),
            &ctuple,
        ));

        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

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
    /// Empty proof-wide range-use accumulator.
    ///
    /// Hosted sibling components such as `ExpandA` reuse the same range table,
    /// so they build one of these before the shared provider is constructed.
    pub fn new() -> Self {
        Self {
            rc9: vec![0; 1 << 9],
            rc13: vec![0; 1 << 13],
            rc8: vec![0; 1 << 8],
            rc7: vec![0; 1 << 7],
            ternary: vec![0; 3],
        }
    }

    /// Record one lookup against `kind`.
    pub fn record(&mut self, kind: RcKind, value: u32) {
        let uses = match kind {
            RcKind::Rc9 => &mut self.rc9,
            RcKind::Rc13 => &mut self.rc13,
            RcKind::Rc8 => &mut self.rc8,
            RcKind::Rc7 => &mut self.rc7,
            RcKind::Ternary => &mut self.ternary,
        };
        uses[value as usize] += 1;
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

    /// Merge another component's uses into this proof-wide table census.
    pub fn add_assign(&mut self, other: &Self) {
        for kind in RcKind::ALL {
            let lhs = match kind {
                RcKind::Rc9 => &mut self.rc9,
                RcKind::Rc13 => &mut self.rc13,
                RcKind::Rc8 => &mut self.rc8,
                RcKind::Rc7 => &mut self.rc7,
                RcKind::Ternary => &mut self.ternary,
            };
            let rhs = other.for_kind(kind);
            assert_eq!(lhs.len(), rhs.len(), "range census shape mismatch");
            for (count, &extra) in lhs.iter_mut().zip(rhs) {
                *count = count
                    .checked_add(extra)
                    .expect("ML-DSA range multiplicity overflow");
            }
        }
    }
}

impl Default for RcUses {
    fn default() -> Self {
        Self::new()
    }
}

/// Count the coefficient component's five range-table multisets without
/// constructing its challenge-dependent interaction trace.
pub fn gen_coeffs_rc_uses(witness: &MlDsaWitness) -> RcUses {
    let mut rc_uses = RcUses::new();
    for group in groups() {
        if !group_is_active(witness.profile, group) {
            continue;
        }
        for in_group in 0..group.rows() {
            let info = RowInfo { group, in_group };
            let digits = row_digits(witness, &info);
            seed_rc_uses(&mut rc_uses, &info, &digits, z_norm_bound(witness.profile));
        }
    }
    rc_uses
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
        let info = info.filter(|info| group_is_active(witness.profile, info.group));
        let is_start = info.map(|i| i.in_group == 0).unwrap_or(false);
        let prev = if info.is_none() || is_start || row == 0 {
            zero
        } else {
            acc[row - 1]
        };
        let digit_row = match info {
            Some(info) => {
                let digits = row_digits(witness, &info);
                let dr = if info.group.kind.has_recomp() {
                    let split = info.group.kind.live_digits();
                    let mut first = zero;
                    let mut second = zero;
                    for t in 0..split {
                        first += s_pow[t] * SecureField::from(enc_signed(digits[t]));
                        second += s_pow[t] * SecureField::from(enc_signed(digits[split + t]));
                    }
                    first * r + second
                } else {
                    let mut ordinary = zero;
                    for t in 0..MAX_DIGITS {
                        ordinary += s_pow[t] * SecureField::from(enc_signed(digits[t]));
                    }
                    ordinary
                };
                // Seed rc multiplicities for this row.
                seed_rc_uses(&mut rc_uses, &info, &digits, z_norm_bound(witness.profile));
                dr
            }
            None => zero,
        };
        let step = match info {
            Some(info) if info.group.kind.has_recomp() => r * r,
            _ => r,
        };
        acc[row] = prev * step + digit_row;
        if let Some(info) = info {
            if info.in_group == info.group.rows() - 1 {
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
    let coset_schedule: Vec<Option<(Group, usize)>> = (0..rows)
        .map(|coset| {
            (coset < active).then(|| {
                let info = sched[coset];
                (info.group, info.in_group)
            })
        })
        .collect();
    let coset_digits: Vec<Option<([i128; MAX_DIGITS], Group, usize)>> = (0..rows)
        .map(|coset| {
            if coset < active {
                let info = sched[coset];
                group_is_active(witness.profile, info.group)
                    .then(|| (row_digits(witness, &info), info.group, info.in_group))
            } else {
                None
            }
        })
        .collect();

    // Fourteen shared range streams, matching the AIR slot assignment.
    for stream in 0..N_RANGE_STREAMS {
        push_entry(
            &|coset| {
                let selected = match &coset_digits[coset] {
                    Some((digits, group, _))
                        if group.kind == Kind::Carry && stream < CARRY_DIGITS =>
                    {
                        let t = stream;
                        let shifted = digits[t] + CARRY_OFFSET as i128;
                        Some((m31((shifted & ((1 << 13) - 1)) as u32), RcKind::Rc13))
                    }
                    Some((digits, group, _)) if group.kind == Kind::Carry => {
                        carry_high_index(stream).map(|t| {
                            let shifted = digits[t] + CARRY_OFFSET as i128;
                            (m31((shifted >> 13) as u32), RcKind::Rc8)
                        })
                    }
                    Some((digits, group, _)) if stream < group.kind.row_live_digits() => {
                        Some((enc_signed(digits[stream]) + m31(DIGIT_OFFSET), RcKind::Rc9))
                    }
                    Some((digits, group, _)) if group.kind == Kind::Z && stream >= 6 => {
                        let [first, second] = paired_recompositions(digits);
                        let norm_bound = z_norm_bound(witness.profile) as i128;
                        let first_a = first + norm_bound;
                        let first_b = norm_bound - first;
                        let second_a = second + norm_bound;
                        let second_b = norm_bound - second;
                        Some(match stream {
                            6 => (m31((first_a & ((1 << 13) - 1)) as u32), RcKind::Rc13),
                            7 => (m31((first_a >> 13) as u32), RcKind::Rc7),
                            8 => (m31((first_b & ((1 << 13) - 1)) as u32), RcKind::Rc13),
                            9 => (m31((first_b >> 13) as u32), RcKind::Rc7),
                            10 => (m31((second_a & ((1 << 13) - 1)) as u32), RcKind::Rc13),
                            11 => (m31((second_a >> 13) as u32), RcKind::Rc7),
                            12 => (m31((second_b & ((1 << 13) - 1)) as u32), RcKind::Rc13),
                            13 => (m31((second_b >> 13) as u32), RcKind::Rc7),
                            _ => unreachable!(),
                        })
                    }
                    Some((digits, group, _)) if group.kind == Kind::C && stream == 7 => {
                        Some((enc_signed(digits[0]) + m31(1), RcKind::Ternary))
                    }
                    _ => None,
                };
                match selected {
                    Some((value, kind)) => {
                        #[cfg(test)]
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
    // EvalAtRs yields at group end (−1).
    push_entry(
        &|coset| match &coset_schedule[coset] {
            Some((group, in_group)) if *in_group == group.rows() - 1 => {
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
    // Two WCell yields (−1), one for each `(i·N+m, w)` tuple.
    for slot in 0..Kind::W.coefficients_per_row() {
        push_entry(
            &|coset| match &coset_digits[coset] {
                Some((digits, group, in_group)) if group.kind == Kind::W => {
                    let i = (group.poly_id - layout::POLY_ID_W0) as usize;
                    let m = group
                        .coefficient_index(*in_group, slot)
                        .expect("paired w slot exists");
                    let w_bind_id = (i * crate::constants::N + m) as u32;
                    let w = enc_signed(paired_recompositions(digits)[slot]);
                    let tuple = [m31(w_bind_id), w];
                    (-one, relations.wcell.combine(&tuple))
                }
                _ => (zero, one),
            },
            &mut entries,
            &mut claimed,
        );
    }
    // CCell yields (−1) on c rows only. This mirrors `-is_c`. Value = digit[0]
    // (enc_signed c); key = m.
    push_entry(
        &|coset| match &coset_digits[coset] {
            Some((digits, group, in_group)) if group.kind == Kind::C => {
                let m = group
                    .coefficient_index(*in_group, 0)
                    .expect("c coefficient exists");
                let c = enc_signed(digits[0]);
                let tuple = [m31(m as u32), c];
                (-one, relations.ccell.combine(&tuple))
            }
            _ => (zero, one),
        },
        &mut entries,
        &mut claimed,
    );

    debug_assert_eq!(entries.len(), N_LOGUP_ENTRIES);

    // Batch the fraction streams in evaluator order, matching `LOGUP_BATCH`.
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

fn seed_rc_uses(rc: &mut RcUses, info: &RowInfo, digits: &[i128; MAX_DIGITS], norm_bound: i64) {
    match info.group.kind {
        Kind::Carry => {
            for t in 0..CARRY_DIGITS {
                let shifted = digits[t] + CARRY_OFFSET as i128;
                rc.rc13[(shifted & ((1 << 13) - 1)) as usize] += 1;
                rc.rc8[(shifted >> 13) as usize] += 1;
            }
        }
        Kind::Z => {
            let live = info.group.kind.row_live_digits();
            for t in 0..live {
                let v = (enc_signed(digits[t]) + m31(DIGIT_OFFSET)).0 as usize;
                rc.rc9[v] += 1;
            }
            for cell in paired_recompositions(digits) {
                let a = cell + norm_bound as i128;
                let b = norm_bound as i128 - cell;
                rc.rc13[(a & ((1 << 13) - 1)) as usize] += 1;
                rc.rc7[(a >> 13) as usize] += 1;
                rc.rc13[(b & ((1 << 13) - 1)) as usize] += 1;
                rc.rc7[(b >> 13) as usize] += 1;
            }
        }
        _ => {
            let live = info.group.kind.row_live_digits();
            for t in 0..live {
                let v = (enc_signed(digits[t]) + m31(DIGIT_OFFSET)).0 as usize;
                rc.rc9[v] += 1;
            }
            if info.group.kind == Kind::C {
                // Ternary membership use: c+1 ∈ {0,1,2}.
                let v = (enc_signed(digits[0]) + m31(1)).0 as usize;
                rc.ternary[v] += 1;
            }
        }
    }
}

#[cfg(test)]
mod packed_tests {
    use super::*;
    use crate::profile::{ML_DSA_44, ML_DSA_65};
    use crate::proof::{prove_coeffs, verify_coeffs};
    use crate::reference::encoding::{pk_decode, sig_decode};
    use crate::reference::sponge::shake256;
    use crate::{generate_witness, MlDsaVerifyInput};
    use ml_dsa::signature::{Keypair, Signer};
    use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa44, MlDsa65, SigningKey};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::pcs::PcsConfig;

    fn boundary_input(seed: u64, message: &[u8]) -> MlDsaVerifyInput {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut secret_seed = [0; 32];
        rng.fill(&mut secret_seed);
        let signing_key = SigningKey::<MlDsa65>::from_seed(&secret_seed.into());
        let verifying_key = signing_key.verifying_key();
        let signature = signing_key.sign(message);
        let public_key: EncodedVerifyingKey<MlDsa65> = verifying_key.encode();
        let signature: EncodedSignature<MlDsa65> = signature.encode();
        let public_key_decoded =
            pk_decode(ML_DSA_65, public_key.as_slice()).expect("public key decodes");
        let signature_decoded =
            sig_decode(ML_DSA_65, signature.as_slice()).expect("signature decodes");
        let (tr, _) = shake256(&[public_key.as_slice()], 64);
        MlDsaVerifyInput::from_decoded(
            ML_DSA_65,
            &public_key_decoded,
            &signature_decoded,
            tr.try_into().expect("tr has 64 bytes"),
            message.to_vec(),
        )
    }

    fn boundary_proof_rejects(kind: RcKind, seed: u64, message: &[u8]) {
        let _guard = install_range_boundary_attack(kind);
        let input = boundary_input(seed, message);
        let witness = generate_witness(ML_DSA_65, &input).expect("witness builds");
        let rejected =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                match prove_coeffs(witness, input, PcsConfig::default()) {
                    Ok(proof) => verify_coeffs(&proof, PcsConfig::default()).is_err(),
                    Err(_) => true,
                }
            }))
            .unwrap_or(true);
        assert!(
            rejected,
            "{} first-excluded value must be rejected",
            kind.name()
        );
    }

    #[test]
    fn paired_recomposition_uses_independent_base_b_triplets() {
        let digits = [1, 2, 3, 4, 5, 6];
        assert_eq!(
            paired_recompositions(&digits),
            [1 + 2 * B + 3 * B * B, 4 + 5 * B + 6 * B * B,]
        );
    }

    #[test]
    fn compact_schedule_derives_every_original_selector() {
        let schedule = row_schedule();
        for row in 0..schedule.len().next_power_of_two() {
            let info = schedule.get(row);
            let kind = info.map(|row| row.group.kind);
            let active = info.is_some();
            let is_c = kind == Some(Kind::C);
            let is_carry = kind == Some(Kind::Carry);
            let is_norm = kind == Some(Kind::Z);
            let is_w = kind == Some(Kind::W);
            let live_mask_4 = kind.is_some_and(|kind| kind.row_live_digits() > 4);
            let derived_masks = [
                active,
                active && !is_c,
                active && !is_c,
                active && !is_c,
                live_mask_4,
                live_mask_4 && !is_carry,
            ];
            let original_masks = std::array::from_fn(|digit| {
                kind.is_some_and(|kind| digit < kind.row_live_digits())
            });
            assert_eq!(
                derived_masks, original_masks,
                "digit masks differ at row {row}"
            );
            assert_eq!(
                active && !is_carry,
                kind.is_some_and(|kind| kind != Kind::Carry)
            );
            let is_recomp = is_norm || is_w;
            assert_eq!(is_recomp, kind.is_some_and(Kind::has_recomp));
            let start = info.is_some_and(|row| row.in_group == 0);
            assert_eq!(
                is_recomp && !start,
                is_recomp && info.is_some_and(|row| row.in_group != 0)
            );
        }
    }

    #[test]
    fn mldsa44_inactive_fixed_tail_is_zero_and_relation_bound() {
        let message = b"ML-DSA-44 inactive coefficient tail";
        let key = SigningKey::<MlDsa44>::from_seed(&[0x44; 32].into());
        let public_key: EncodedVerifyingKey<MlDsa44> = key.verifying_key().encode();
        let signature: EncodedSignature<MlDsa44> = key.sign(message).encode();
        let decoded_key = pk_decode(ML_DSA_44, public_key.as_slice()).expect("decode key");
        let decoded_signature =
            sig_decode(ML_DSA_44, signature.as_slice()).expect("decode signature");
        let (tr, _) = shake256(&[public_key.as_slice()], 64);
        let input = MlDsaVerifyInput::from_decoded(
            ML_DSA_44,
            &decoded_key,
            &decoded_signature,
            tr.try_into().expect("64-byte tr"),
            message.to_vec(),
        );
        let witness =
            crate::witness::generate_witness(ML_DSA_44, &input).expect("generate witness");
        let log_size = crate::air_util::padded_log_size(layout::active_rows());
        let interaction = gen_coeffs_interaction(
            &witness,
            log_size,
            SecureField::from(m31(7)),
            SecureField::from(m31(11)),
            &CoeffsRelations::dummy(),
        );
        let schedule = row_schedule();
        let inactive_ids: Vec<_> = groups()
            .into_iter()
            .filter(|group| !group_is_active(ML_DSA_44, *group))
            .map(|group| group.poly_id as usize)
            .collect();
        assert_eq!(inactive_ids, [4, 9, 10, 15, 16, 21, 22, 28, 29]);
        assert_eq!(interaction.group_evals.len(), layout::N_GROUPS);
        for &id in &inactive_ids {
            assert_eq!(
                interaction.group_evals[id],
                SecureField::from(m31(0)),
                "inactive evaluation {id} must be fixed to zero"
            );
        }

        let preprocessed: Vec<_> = gen_coeffs_preprocessed(ML_DSA_44, log_size)
            .into_iter()
            .map(|column| column.to_cpu().values)
            .collect();
        let base: Vec<_> = gen_coeffs_base_trace(&witness, log_size)
            .into_iter()
            .map(|column| column.to_cpu().values)
            .collect();
        let accumulator: Vec<_> = interaction.trace[..N_ACC_COORD_COLS]
            .iter()
            .map(|column| column.to_cpu().values)
            .collect();
        for (circle_row, coset) in crate::air_util::circle_row_to_coset(log_size)
            .into_iter()
            .enumerate()
        {
            let Some(info) = schedule.get(coset) else {
                assert!(
                    preprocessed
                        .iter()
                        .all(|column| column[circle_row] == m31(0)),
                    "padding selectors must be zero at coset row {coset}"
                );
                assert!(
                    base.iter().all(|column| column[circle_row] == m31(0)),
                    "padding base cells must be zero at coset row {coset}"
                );
                assert!(
                    accumulator
                        .iter()
                        .all(|column| column[circle_row] == m31(0)),
                    "padding accumulator must reset at coset row {coset}"
                );
                continue;
            };
            if group_is_active(ML_DSA_44, info.group) {
                continue;
            }

            for selector in [0, 3, 4, 5, 6, 7, 10] {
                assert_eq!(
                    preprocessed[selector][circle_row],
                    m31(0),
                    "profile selector {selector} is live in inactive group {}",
                    info.group.poly_id
                );
            }
            assert_eq!(
                preprocessed[1][circle_row],
                m31(u32::from(info.in_group == info.group.rows() - 1)),
                "raw group-end selector must retain the zero-evaluation yield"
            );
            assert!(
                base.iter().all(|column| column[circle_row] == m31(0)),
                "inactive base cells must be zero in group {}",
                info.group.poly_id
            );
            assert!(
                accumulator
                    .iter()
                    .all(|column| column[circle_row] == m31(0)),
                "inactive accumulator must reset in group {}",
                info.group.poly_id
            );
        }
    }

    #[test]
    fn carry_high_stream_permutation_covers_every_carry_digit_once() {
        let mut seen: Vec<_> = (0..N_RANGE_STREAMS).filter_map(carry_high_index).collect();
        seen.sort_unstable();
        assert_eq!(seen, (0..CARRY_DIGITS).collect::<Vec<_>>());
    }

    #[test]
    fn second_norm_highs_do_not_alias_carry_split_columns() {
        let carry_end = COL_CARRY_HI0 + CARRY_DIGITS;
        assert_eq!(COL_NORM2_A_HI, carry_end);
        assert_eq!(COL_NORM2_B_HI, carry_end + 1);
        assert_eq!(N_BASE_COLS, carry_end + 2);
    }

    #[test]
    fn range_censuses_merge_per_kind_without_cross_talk() {
        let mut left = RcUses::new();
        let mut right = RcUses::new();
        left.record(RcKind::Rc8, 17);
        right.record(RcKind::Rc8, 17);
        right.record(RcKind::Rc9, 17);
        right.record(RcKind::Ternary, 2);
        left.add_assign(&right);
        assert_eq!(left.for_kind(RcKind::Rc8)[17], 2);
        assert_eq!(left.for_kind(RcKind::Rc9)[17], 1);
        assert_eq!(left.for_kind(RcKind::Ternary)[2], 1);
        assert_eq!(left.for_kind(RcKind::Rc13).iter().sum::<u32>(), 0);
        assert_eq!(left.for_kind(RcKind::Rc7).iter().sum::<u32>(), 0);
    }

    #[test]
    fn split_coeffs_rc9_boundary_rejects() {
        boundary_proof_rejects(RcKind::Rc9, 3010, b"split-rc9");
    }

    #[test]
    fn split_coeffs_rc13_boundary_rejects() {
        boundary_proof_rejects(RcKind::Rc13, 3011, b"split-rc13");
    }

    #[test]
    fn split_coeffs_rc8_boundary_rejects() {
        boundary_proof_rejects(RcKind::Rc8, 3012, b"split-rc8");
    }

    #[test]
    fn split_coeffs_rc7_boundary_rejects() {
        boundary_proof_rejects(RcKind::Rc7, 3013, b"split-rc7");
    }

    #[test]
    fn split_coeffs_ternary_boundary_rejects() {
        boundary_proof_rejects(RcKind::Ternary, 3014, b"split-ternary");
    }
}
