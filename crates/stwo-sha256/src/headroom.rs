//! M31 headroom audit for the SHA-256 mod-2³² limb-add equation families.
//!
//! Every mod-2³² addition in the SHA-256 AIR is constrained by two linear
//! identities — one per 16-bit limb `(lo, hi)`:
//!
//! ```text
//! Σⱼ addendⱼ.lo +     0    − result.lo − 2¹⁶ · carry_lo = 0
//! Σⱼ addendⱼ.hi + carry_lo − result.hi − 2¹⁶ · carry_hi = 0
//! ```
//!
//! The combined polynomial expression must lie strictly inside centered M31,
//! i.e. `|expr| < M31_CENTER_LIMIT = (2³¹ − 2) / 2 = 2³⁰ − 1`, otherwise the
//! M31 equation could be satisfied with a non-zero integer value and the
//! constraint would not actually pin down `result`. The validated design
//! (§3 of `docs/research/sha256-air-design.md`) shows that even the widest add —
//! `T1` with 5 addends — has roughly 12 bits of headroom, so for SHA-256
//! every family fits centered M31 directly. But per the AIR-soundness
//! convention, the assertion must come from **code**, not a paragraph in
//! the design doc; that's what this module does, and what the fail-closed
//! tests at the bottom guard against drift.
//!
//! ## What's simpler than the P-256 audit
//!
//! - **All addend coefficients are `+1`.** SHA-256 only adds; no
//!   subtraction, no signed coefficient mixing. The bound shape is just
//!   `Σ addends − result − 2¹⁶ · carry` per limb.
//! - **Carries are non-negative.** Every carry lives in `[0, k)` for a
//!   k-addend add; the range-check table is unsigned. The
//!   [`EquationHeadroom::signed_carry_bound`] field records that exclusive
//!   upper bound for compatibility with the existing audit helpers.
//! - **Only 2 limbs.** A SHA-256 word is stored as `(lo, hi)`; the carry
//!   chain has length 2, not 20+.

use crate::types::{LIMB_BASE, LIMB_MAX};

/// M31 modulus `p = 2³¹ − 1`. AIR field elements are reduced modulo this.
pub const M31_MODULUS: i128 = (1i128 << 31) - 1;

/// Centered-representative bound `(M31_MODULUS − 1) / 2 = 2³⁰ − 1`. Every
/// audited equation's `|combined_expression|` must lie **strictly below**
/// this for the M31 equation to imply the integer equation — otherwise the
/// equation could be satisfied in M31 by a witness whose integer LHS is a
/// non-zero multiple of `p`.
pub const M31_CENTER_LIMIT: i128 = (M31_MODULUS - 1) / 2;

// ---- Per-family carry-range bounds (exclusive upper bounds / table sizes) ----
//
// For a k-addend mod-2³² limb-add, the honest carry per limb lies in
// `[0, k)` — equivalently, in `{0, 1, …, k − 1}` (k values). Downstream
// lookup wiring sizes the preprocessed carry range-check table to match.
// The exclusive upper bound — also the table row count — is what we
// publish here as `RANGE_k`.

/// Carry-range upper bound (exclusive) for **2-addend** mod-2³² adds. Used
/// by `T2 = Σ0 + Maj`, `e_new = d + T1`, `a_new = T1 + T2`, and the
/// finalization adds `Hⱼ⁽ᵗ⁺¹⁾ = Hⱼ⁽ᵗ⁾ + working_varⱼ`. The associated
/// preprocessed `Range_2` table has 2 rows (`{0, 1}`).
pub const RANGE_2: u32 = 2;

/// Carry-range upper bound (exclusive) for the **4-addend**
/// message-schedule recurrence
/// `W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]`. The associated
/// preprocessed `Range_4` table has 4 rows (`{0, 1, 2, 3}`).
pub const RANGE_4: u32 = 4;

/// Carry-range upper bound (exclusive) for the **5-addend** round add
/// `T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]` — the widest add in
/// SHA-256. The associated preprocessed `Range_5` table has 5 rows
/// (`{0, 1, 2, 3, 4}`).
pub const RANGE_5: u32 = 5;

// ---- Headroom audit data types ----

/// Outcome of a single equation-family headroom check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeadroomStatus {
    /// `|combined_expression| < M31_CENTER_LIMIT` across every limb. The
    /// equation fits centered M31 directly; no algebraic split is required.
    Fits,
    /// At least one limb's `|combined_expression|` reaches or exceeds
    /// `M31_CENTER_LIMIT`. The equation must be split before its AIR row
    /// type is enabled. Not expected for any SHA-256 family.
    RequiresSplit,
    /// The audit formula for this equation is not yet derived. The AIR
    /// must refuse to enable a row family in this state; the tests below
    /// enforce that no SHA-256 audit reaches the prover with
    /// `PendingFormula`.
    PendingFormula,
}

/// Per-limb worst-case bounds used to compute the carry-out and the
/// limb's combined-expression bound.
#[derive(Clone, Debug)]
pub struct LimbHeadroom {
    /// Limb index in the chain — `0 = lo`, `1 = hi`.
    pub limb_index: usize,
    /// Upper bound on `|Σⱼ addendⱼ.limb| + |result.limb|`, the coefficient
    /// terms in the per-limb equation, before adding the carry chain
    /// (`(k + 1) · LIMB_MAX` for a k-addend SHA-256 add).
    pub coefficient_bound_before_carry: i128,
    /// Upper bound on the **incoming** carry (from the previous limb).
    /// Always `0` for `limb_index == 0`.
    pub carry_bound_in: i128,
    /// Upper bound on the **outgoing** carry — equivalently, the range
    /// the AIR's `Range_k` table pins this carry into.
    pub carry_bound_out: i128,
    /// Upper bound on `|combined_expression|` for this limb. The audit
    /// status is `Fits` iff every limb's bound is below
    /// `M31_CENTER_LIMIT`.
    pub max_abs_combined_expression: i128,
}

/// Headroom record for one mod-2³² equation family.
#[derive(Clone, Debug)]
pub struct EquationHeadroom {
    pub name: &'static str,
    pub status: HeadroomStatus,
    /// Upper bound on the carry magnitude across every limb. For SHA-256
    /// the carries are **non-negative** (`∈ [0, RANGE_k)`), so the value
    /// is `k − 1` — the inclusive maximum carry. The field name is the
    /// same as the signed P-256 audit's so the eventual generalisation is
    /// a rename, not a redesign.
    pub signed_carry_bound: Option<i128>,
    /// Worst-case `|combined_expression|` across every limb of this
    /// equation. Must be `< M31_CENTER_LIMIT` for `status == Fits`.
    pub max_abs_combined_expression: Option<i128>,
    /// The per-limb breakdown — always length 2 for SHA-256 (lo, hi).
    pub limbs: Vec<LimbHeadroom>,
    pub note: &'static str,
}

impl EquationHeadroom {
    /// True iff `max_abs_combined_expression` is below `M31_CENTER_LIMIT`,
    /// i.e. the equation fits centered M31 without a split. The `Fits`
    /// status agrees with this predicate by construction.
    pub fn direct_equation_fits(&self) -> bool {
        matches!(self.max_abs_combined_expression, Some(max) if max < M31_CENTER_LIMIT)
    }
}

/// Every mod-2³² limb-add equation family the SHA-256 AIR exercises.
///
/// The four families partition every add in the AIR (validated design
/// §10.2):
///
/// - [`audit_schedule_recurrence`] — `W[t] = σ1(W[t−2]) + W[t−7] +
///   σ0(W[t−15]) + W[t−16]` (4 addends), one per schedule entry
///   `t ∈ [16, 64)`.
/// - [`audit_round_t1`] — `T1 = h + Σ1 + Ch + K + W` (5 addends), one per
///   round `t ∈ [0, 64)`.
/// - [`audit_round_short_adds`] — the three 2-addend adds inside each
///   round (`T2 = Σ0 + Maj`, `e_new = d + T1`, `a_new = T1 + T2`).
/// - [`audit_finalization`] — the eight 2-addend finalization adds
///   `Hⱼ = h_inⱼ + working_varⱼ` per block.
///
/// The fail-closed test `tests::every_add_family_fits_centered_m31`
/// asserts every entry's status is `Fits`, so adding a new add shape
/// without an audit, or a drift in the bound formula, triggers a test
/// failure rather than silently passing — no warnings, no skipped
/// equations.
pub fn current_headroom_audits() -> Vec<EquationHeadroom> {
    vec![
        audit_schedule_recurrence(),
        audit_round_t1(),
        audit_round_short_adds(),
        audit_finalization(),
    ]
}

/// 4-addend audit: `W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16]`.
/// Carries are range-checked to `[0, RANGE_4) = [0, 4)`.
pub fn audit_schedule_recurrence() -> EquationHeadroom {
    audit_mod_2_32_add(
        "schedule_recurrence",
        4,
        "Message-schedule recurrence (FIPS 180-4 §6.2.2): W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16].",
    )
}

/// 5-addend audit: `T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]`. The widest
/// add in the AIR — and therefore the family whose bound `T1` produces is
/// the one design §3's "~12 bits of headroom" is measured against.
/// Carries are range-checked to `[0, RANGE_5) = [0, 5)`.
pub fn audit_round_t1() -> EquationHeadroom {
    audit_mod_2_32_add(
        "t1",
        5,
        "Round T1 (FIPS 180-4 §6.2.2): T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t].",
    )
}

/// 2-addend audit for the three round-internal short adds: `T2 = Σ0 +
/// Maj`, `e_new = d + T1`, `a_new = T1 + T2`. All three share the same
/// limb-bound shape so a single audit entry covers them. Carries are
/// range-checked to `[0, RANGE_2) = [0, 2)`.
pub fn audit_round_short_adds() -> EquationHeadroom {
    audit_mod_2_32_add(
        "t2_and_state_update",
        2,
        "Round 2-addend adds (FIPS 180-4 §6.2.2): T2 = Σ0 + Maj, e_new = d + T1, a_new = T1 + T2.",
    )
}

/// 2-addend audit for the eight finalization adds per block:
/// `Hⱼ⁽ᵗ⁺¹⁾ = Hⱼ⁽ᵗ⁾ + working_varⱼ` for `j ∈ [0, 8)`. Same limb shape as
/// the round short adds; tracked separately for traceability with the
/// validated design §10.3. Carries are range-checked
/// to `[0, RANGE_2) = [0, 2)`.
pub fn audit_finalization() -> EquationHeadroom {
    audit_mod_2_32_add(
        "finalization",
        2,
        "Block finalization (FIPS 180-4 §6.2.2): H[j] = h_in[j] + working[j] for j = 0..8.",
    )
}

/// Audit one mod-2³² limb-add equation family with `k = addends` addends.
///
/// The per-limb constraint is `Σⱼ addendⱼ.limb + carry_in − result.limb −
/// 2¹⁶ · carry_out = 0`, with every addend limb and the result limb in
/// `[0, 2¹⁶)` and every carry in `[0, k)` (range-checked by the family's
/// `Range_k` table).
///
/// We use the **loose** per-limb bound
///
/// ```text
/// |combined| ≤ (k + 1) · LIMB_MAX + carry_in + LIMB_BASE · carry_out
/// ```
///
/// — the P-256 stream's `audit_direct_limb_equation` shape, instantiated
/// for two 16-bit limbs and `+1`-only addend coefficients. The loose bound
/// sums magnitudes (it does *not* claim cancellation between "addends
/// are large" and "result is small"), so the audit is conservative by
/// design — any tighter sign-aware bound is still ≤ this loose one.
fn audit_mod_2_32_add(name: &'static str, addends: usize, note: &'static str) -> EquationHeadroom {
    let limb_max = i128::from(LIMB_MAX);
    let limb_base = i128::from(LIMB_BASE);
    let k = addends as i128;
    // Carries are range-checked to `[0, k)` ⇒ inclusive maximum `k − 1`.
    let carry_bound = k - 1;
    // (k addend limbs) + (1 result limb) all in `[0, LIMB_MAX]`.
    let coefficient_bound_before_carry = (k + 1) * limb_max;

    let mut limbs = Vec::with_capacity(2);
    let mut max_abs_combined_expression: i128 = 0;
    let mut carry_bound_in = 0i128;
    for limb_index in 0..2usize {
        let carry_bound_out = carry_bound;
        let max_abs_for_limb =
            coefficient_bound_before_carry + carry_bound_in + limb_base * carry_bound_out;
        max_abs_combined_expression = max_abs_combined_expression.max(max_abs_for_limb);
        limbs.push(LimbHeadroom {
            limb_index,
            coefficient_bound_before_carry,
            carry_bound_in,
            carry_bound_out,
            max_abs_combined_expression: max_abs_for_limb,
        });
        carry_bound_in = carry_bound_out;
    }

    let status = if max_abs_combined_expression < M31_CENTER_LIMIT {
        HeadroomStatus::Fits
    } else {
        HeadroomStatus::RequiresSplit
    };

    EquationHeadroom {
        name,
        status,
        signed_carry_bound: Some(carry_bound),
        max_abs_combined_expression: Some(max_abs_combined_expression),
        limbs,
        note,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn audit(name: &str) -> EquationHeadroom {
        current_headroom_audits()
            .into_iter()
            .find(|a| a.name == name)
            .unwrap_or_else(|| panic!("missing headroom audit for {name}"))
    }

    /// Fail-closed gate for the build: every mod-2³² add family the AIR
    /// emits must have a `Fits` audit. Any new family without a matching
    /// audit, or a drift in the limb bounds that pushes a family into
    /// `RequiresSplit` / `PendingFormula`, triggers this test.
    #[test]
    fn every_add_family_fits_centered_m31() {
        let audits = current_headroom_audits();
        let expected_names = [
            "schedule_recurrence",
            "t1",
            "t2_and_state_update",
            "finalization",
        ];
        assert_eq!(
            audits.len(),
            expected_names.len(),
            "expected {} add families; found {}",
            expected_names.len(),
            audits.len()
        );
        for name in expected_names {
            let a = audit(name);
            assert_eq!(
                a.status,
                HeadroomStatus::Fits,
                "{name}: must be Fits (max |combined| = {:?}; limit = {})",
                a.max_abs_combined_expression,
                M31_CENTER_LIMIT
            );
            assert!(
                a.direct_equation_fits(),
                "{name}: direct_equation_fits() must agree with Fits"
            );
            assert!(
                a.max_abs_combined_expression.unwrap() < M31_CENTER_LIMIT,
                "{name}: max combined must be strictly below M31_CENTER_LIMIT"
            );
        }
    }

    /// The per-family carry bound exposed for downstream lookup wiring
    /// matches the family's `Range_k` table size: `signed_carry_bound =
    /// k − 1`, `RANGE_k = k`. The downstream lookup wiring consumes
    /// `RANGE_k` to size its preprocessed range-check tables; this test
    /// pins the correspondence between the audit and those constants so
    /// they cannot drift apart silently.
    #[test]
    fn carry_bounds_match_range_constants() {
        assert_eq!(
            audit("schedule_recurrence").signed_carry_bound,
            Some(i128::from(RANGE_4) - 1)
        );
        assert_eq!(
            audit("t1").signed_carry_bound,
            Some(i128::from(RANGE_5) - 1)
        );
        assert_eq!(
            audit("t2_and_state_update").signed_carry_bound,
            Some(i128::from(RANGE_2) - 1)
        );
        assert_eq!(
            audit("finalization").signed_carry_bound,
            Some(i128::from(RANGE_2) - 1)
        );
    }

    /// Sanity: the widest family (`T1`, k = 5) has a combined-expression
    /// bound below 2²⁰, matching the validated design's "~12 bits of
    /// headroom" estimate in §3 of `docs/research/sha256-air-design.md`.
    #[test]
    fn headroom_matches_design_estimate() {
        let widest = audit("t1");
        let max = widest
            .max_abs_combined_expression
            .expect("audit produces a bound");
        // 2²⁰ = 1_048_576. The loose bound (P-256-style) is
        //   (k+1)·(2¹⁶ − 1) + (k − 1) + 2¹⁶·(k − 1)
        // = 6·65535 + 4 + 65536·4 = 655_358 < 2²⁰.
        assert!(max < 1i128 << 20, "T1 bound {max} not < 2²⁰");
        // Headroom margin: ratio to M31_CENTER_LIMIT. ~10 bits free
        // even under the conservative bound.
        assert!(
            M31_CENTER_LIMIT / max > 1024_i128,
            "T1 must have > 10 bits of headroom; ratio = {}",
            M31_CENTER_LIMIT / max
        );
    }

    /// Every audit's per-limb carry chain is internally consistent: limb
    /// 0 starts with `carry_in = 0`, limb 1's `carry_in` equals limb 0's
    /// `carry_out`, and `signed_carry_bound` is the maximum `carry_out`
    /// across both limbs.
    #[test]
    fn audit_per_limb_carry_chain_is_consistent() {
        for a in current_headroom_audits() {
            assert_eq!(a.limbs.len(), 2, "{}: SHA-256 has 2 limbs/word", a.name);
            assert_eq!(
                a.limbs[0].carry_bound_in, 0,
                "{}: limb 0 must have carry_in = 0",
                a.name
            );
            assert_eq!(
                a.limbs[1].carry_bound_in, a.limbs[0].carry_bound_out,
                "{}: limb 1 carry_in must equal limb 0 carry_out",
                a.name
            );
            let expected_signed = a.limbs.iter().map(|l| l.carry_bound_out).max().unwrap();
            assert_eq!(
                a.signed_carry_bound,
                Some(expected_signed),
                "{}: signed_carry_bound aggregates per-limb carry_out",
                a.name
            );
        }
    }

    /// `direct_equation_fits` agrees with the `Fits` discriminator across
    /// every audit, and no SHA-256 audit reaches the prover with
    /// `PendingFormula` (fail-closed against unaudited families).
    #[test]
    fn fits_status_implies_direct_fit() {
        for a in current_headroom_audits() {
            match a.status {
                HeadroomStatus::Fits => assert!(
                    a.direct_equation_fits(),
                    "{}: Fits status but direct_equation_fits()=false",
                    a.name
                ),
                HeadroomStatus::RequiresSplit => assert!(
                    !a.direct_equation_fits(),
                    "{}: RequiresSplit but direct_equation_fits()=true",
                    a.name
                ),
                HeadroomStatus::PendingFormula => panic!(
                    "{}: SHA-256 AIR must not enter the prover with a PendingFormula audit",
                    a.name
                ),
            }
        }
    }

    /// `RANGE_k` constants name the exclusive upper bound — i.e. the
    /// preprocessed table size — for each family's carry range-check.
    /// The numeric values are documented in the constant docs above; this
    /// test pins them against accidental edits.
    #[test]
    fn range_constants_are_explicit() {
        assert_eq!(RANGE_2, 2);
        assert_eq!(RANGE_4, 4);
        assert_eq!(RANGE_5, 5);
    }

    /// M31 constants match their canonical values.
    #[test]
    fn m31_constants_are_canonical() {
        assert_eq!(M31_MODULUS, (1i128 << 31) - 1);
        assert_eq!(M31_CENTER_LIMIT, (M31_MODULUS - 1) / 2);
        assert_eq!(M31_CENTER_LIMIT, (1i128 << 30) - 1);
    }
}
