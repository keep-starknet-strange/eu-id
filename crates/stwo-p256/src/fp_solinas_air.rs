use stwo::core::fields::m31::M31;
use stwo_constraint_framework::EvalAtRow;
use stwo_p256_utils::constants::LIMB_BITS;

use crate::fp_solinas::M31_CENTERED_BOUND;
use crate::range_checks::{add_range_check, RangeCheckRelation};

// AIR DESIGN ARTIFACTS (air-writer)
//
// Property:
//   For each active split Solinas reduction digit,
//     folded_digit - result_limb - correction_limb * modulus_limb
//       + prev_carry - 2^13 * carry = 0.
//
// Algorithm choice:
//   This helper proves one narrow digit recurrence after raw product generation
//   and Solinas matrix folding have been split into 13-bit digits. Encoding the
//   whole folded coefficient directly is rejected because observed bounds exceed
//   centered M31 headroom.
//
// Layout manifest:
//   Pattern A, same-row helper. Columns are read by caller in this order:
//   folded_digit, result_limb, correction_limb, modulus_limb, prev_carry, carry.
//   No preprocessed columns, no cross-row masks, no interaction finalization in
//   this helper. Callers own carry-link relations and padding/enabler policy.
//
// Relation contracts:
//   Uses Range13 for folded/result/correction/modulus digits and a signed carry
//   range for prev_carry/carry. All are positive lookup uses through the existing
//   `add_range_check` helper.
//
// Degree worksheet:
//   Range uses are linear in `gate`. The recurrence has base degree 2 from
//   correction_limb * modulus_limb; with a linear gate, total degree is 3.
//
// Adversarial plan:
//   Mutating any digit or carry should violate the recurrence or a range lookup.
//   Out-of-range digits should fail Range13; out-of-bound carries should fail the
//   signed carry range. Full malicious trace tests are deferred to the component
//   that owns trace generation and interaction columns.
pub const FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS: usize = 6;
pub const FP_SOLINAS_REDUCTION_MAX_ABS_EXPR: i128 = 67_256_337;

#[derive(Clone, Copy)]
pub struct FpSolinasReductionRelations<'a> {
    /// 13-bit range table for canonical limbs and split correction digits.
    pub range13: &'a RangeCheckRelation,
    /// Signed carry table configured for the Solinas reduction carry bound.
    pub signed_carry: &'a RangeCheckRelation,
}

pub struct FpSolinasReductionDigitColumns<E: EvalAtRow> {
    pub folded_digit: E::F,
    pub result_limb: E::F,
    pub correction_limb: E::F,
    pub modulus_limb: E::F,
    pub prev_carry: E::F,
    pub carry: E::F,
}

/// Enforce one split Solinas reduction digit:
///
/// ```text
/// folded_digit - result_limb - correction_limb * modulus_limb
///     + prev_carry - 2^13 * carry = 0
/// ```
///
/// This is the row-local recurrence used after high-product terms have been
/// folded through the P-256 Solinas matrix and split into 13-bit digits. It is
/// intentionally narrower than a whole field multiplication row; raw product
/// generation, matrix folding, and carry-link relations are separate rows.
pub fn add_fp_solinas_reduction_digit<E: EvalAtRow>(
    eval: &mut E,
    relations: FpSolinasReductionRelations<'_>,
    gate: E::F,
    columns: &FpSolinasReductionDigitColumns<E>,
) {
    add_range_check(
        eval,
        relations.range13,
        gate.clone(),
        columns.folded_digit.clone(),
    );
    add_range_check(
        eval,
        relations.range13,
        gate.clone(),
        columns.result_limb.clone(),
    );
    add_range_check(
        eval,
        relations.range13,
        gate.clone(),
        columns.correction_limb.clone(),
    );
    add_range_check(
        eval,
        relations.range13,
        gate.clone(),
        columns.modulus_limb.clone(),
    );
    add_range_check(
        eval,
        relations.signed_carry,
        gate.clone(),
        columns.prev_carry.clone(),
    );
    add_range_check(
        eval,
        relations.signed_carry,
        gate.clone(),
        columns.carry.clone(),
    );

    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let recurrence = columns.folded_digit.clone()
        - columns.result_limb.clone()
        - columns.correction_limb.clone() * columns.modulus_limb.clone()
        + columns.prev_carry.clone()
        - limb_base * columns.carry.clone();
    eval.add_constraint(gate * recurrence);
}

pub fn fp_solinas_reduction_digit_fits_m31() -> bool {
    FP_SOLINAS_REDUCTION_MAX_ABS_EXPR < M31_CENTERED_BOUND
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fp_solinas::FP_SOLINAS_LIMB_BASE;

    #[test]
    fn fp_solinas_reduction_digit_row_shape_is_narrow() {
        assert_eq!(FP_SOLINAS_REDUCTION_DIGIT_TRACE_COLUMNS, 6);
    }

    #[test]
    fn fp_solinas_reduction_digit_expression_has_m31_headroom() {
        let limb_max = FP_SOLINAS_LIMB_BASE - 1;
        let carry_bound = 18;
        let max_abs = limb_max
            + limb_max
            + limb_max * limb_max
            + carry_bound
            + FP_SOLINAS_LIMB_BASE * carry_bound;

        assert_eq!(max_abs, FP_SOLINAS_REDUCTION_MAX_ABS_EXPR);
        assert!(fp_solinas_reduction_digit_fits_m31());
    }
}
