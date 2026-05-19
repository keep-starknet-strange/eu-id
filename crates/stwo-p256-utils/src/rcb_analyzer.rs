//! Symbolic analyzer for Renes-Costello-Batina Algorithm 5 (mixed addition
//! for `a = −3`, `Z2 = 1`) and Algorithm 6 (exception-free doubling for
//! `a = −3`).
//!
//! Both algorithms are sequences of Fp operations (mul, add, sub, mul-by-`b`,
//! mul-by-`−3`) on intermediate variables. Each intermediate, when expressed
//! as a 20-limb signed convolution of the inputs, has a worst-case
//! per-output-limb coefficient bound.
//!
//! The analyzer simulates each line symbolically over limb coefficient bounds
//! (not concrete values) and reports the worst-case `|combined_expression|`
//! per output limb for every line. That feeds the `headroom` audit, which
//! decides whether a single line fits centered M31 directly or needs an
//! intermediate witness column.
//!
//! Without this analyzer, the `rcb_projective_add_double` headroom audit
//! stays `PendingFormula` and the AIR cannot enable any EC row.

use crate::constants::N_LIMBS;

/// One step in an RCB schedule. Mirrors EFD `madd-2015-rcb-3` /
/// `dbl-2015-rcb-3` notation; see AIR spec sections EC_DOUBLE and EC_ADD for
/// the verbatim step lists.
#[derive(Clone, Debug)]
pub enum Step {
    /// `out = a + b` over Fp.
    Add { out: Var, a: Var, b: Var },
    /// `out = a - b` over Fp.
    Sub { out: Var, a: Var, b: Var },
    /// `out = a * b` over Fp; the unreduced product may need Solinas folding.
    Mul { out: Var, a: Var, b: Var },
    /// `out = b * a` where `b` is the small curve constant (P-256 `b`).
    MulByB { out: Var, a: Var },
    /// `out = (-3) * a` (the `a` curve parameter for `a = −3`).
    MulByAEqMinus3 { out: Var, a: Var },
    /// `out = a` (renaming; useful when a temporary becomes an output).
    Copy { out: Var, a: Var },
}

/// Variable names used in the RCB schedules.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Var {
    // Inputs
    X1,
    Y1,
    Z1,
    X2,
    Y2,
    // Intermediate scratch (named `t0..t5` in EFD).
    T0,
    T1,
    T2,
    T3,
    T4,
    T5,
    // Outputs
    X3,
    Y3,
    Z3,
}

/// Per-limb signed bound on a symbolic variable. Index 0 = least significant.
pub type LimbBounds = [i128; 2 * N_LIMBS - 1];

/// Bounds report for a full RCB schedule.
#[derive(Clone, Debug)]
pub struct ScheduleReport {
    pub algorithm: &'static str,
    /// Per-step bound: `step_max_abs_combined[i]` is the worst-case
    /// `|combined_expression|` across all output limbs of step `i`.
    pub step_max_abs_combined: Vec<i128>,
    /// Overall worst-case `|combined_expression|` across the whole schedule.
    pub max_abs_combined: i128,
    /// Output bounds, one per limb, for each of `(X3, Y3, Z3)`.
    pub output_bounds: ((LimbBounds, LimbBounds, LimbBounds),),
}

/// EFD `madd-2015-rcb-3` schedule. See AIR spec section EC_ADD for the
/// verbatim listing this should mirror.
pub fn algorithm_5_schedule() -> Vec<Step> {
    todo!("Transcribe madd-2015-rcb-3 verbatim from AIR spec section EC_ADD")
}

/// EFD `dbl-2015-rcb-3` schedule. See AIR spec section EC_DOUBLE for the
/// verbatim listing this should mirror.
pub fn algorithm_6_schedule() -> Vec<Step> {
    todo!("Transcribe dbl-2015-rcb-3 verbatim from AIR spec section EC_DOUBLE")
}

/// Run the symbolic analyzer on a schedule with given input bounds and the
/// Solinas reduction matrix. Returns the per-step and overall bounds report.
pub fn analyze(
    _algorithm: &'static str,
    _schedule: &[Step],
    _input_bounds_x1: &LimbBounds,
    _input_bounds_y1: &LimbBounds,
    _input_bounds_z1: &LimbBounds,
    _input_bounds_x2: &LimbBounds,
    _input_bounds_y2: &LimbBounds,
) -> ScheduleReport {
    todo!(
        "Walk the schedule. Track per-limb bounds on each variable. \
         For Mul: convolve bounds, then apply Solinas fold via `solinas::compute_reduction_matrix`. \
         For Add/Sub: pointwise sum of bounds. \
         For MulByB / MulByAEqMinus3: scale bounds by |b| or 3. \
         Cross-check against property tests with random concrete inputs (big-int reference)."
    )
}

/// Property test harness: run the schedule on random Fp inputs in big-int
/// reference, run it again with the analyzer's bound tracking, and assert
/// `concrete_combined_expr <= bound_at_that_limb` for every limb across many
/// trials. If this ever fails, the analyzer is unsound and every audit it
/// validated is suspect.
pub fn verify_analyzer(_algorithm: &'static str, _schedule: &[Step]) -> Result<(), &'static str> {
    todo!(
        "Pick random (X1, Y1, Z1, X2, Y2) < p. Run the schedule via the analyzer for bounds and \
         via big-int Fp arithmetic for concrete values. Assert no concrete |limb| exceeds the \
         predicted bound at any step. Required before any analyzer result is fed to `headroom`."
    )
}
