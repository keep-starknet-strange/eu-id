//! M31 headroom audit for each arithmetic equation family in the AIR.
//!
//! For every limb equation of the form
//! `prod_coeff[i] − qn_coeff[i] − result_limb[i] + carry[i] − B · carry[i+1]`,
//! this module computes the worst-case `|combined_expr|` per limb and decides
//! whether the equation fits centered M31 directly or requires a split.
//!
//! Per the AIR spec, no arithmetic row type can be enabled until its combined
//! carry equation has been machine-checked against M31. The
//! `SignedCarryRange` lookup for that row family must use exactly the audited
//! bound with the centered encoding.

use crate::constants::{LIMB_BASE, LIMB_MAX, M31_CENTER_LIMIT, N_LIMBS};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeadroomStatus {
    Fits,
    RequiresSplit,
    PendingFormula,
}

#[derive(Clone, Debug)]
pub struct LimbHeadroom {
    pub limb_index: usize,
    pub coefficient_bound_before_carry: i128,
    pub carry_bound_in: i128,
    pub carry_bound_out: i128,
    pub max_abs_combined_expression: i128,
}

#[derive(Clone, Debug)]
pub struct EquationHeadroom {
    pub name: &'static str,
    pub status: HeadroomStatus,
    pub signed_carry_bound: Option<i128>,
    pub max_abs_combined_expression: Option<i128>,
    pub limbs: Vec<LimbHeadroom>,
    pub note: &'static str,
}

impl EquationHeadroom {
    pub fn direct_equation_fits(&self) -> bool {
        matches!(self.max_abs_combined_expression, Some(max) if max < M31_CENTER_LIMIT)
    }
}

pub fn current_headroom_audits() -> Vec<EquationHeadroom> {
    vec![
        audit_generic_quotient_mul_256x256(),
        audit_fake_glv_scalar_mul_256x128(),
        audit_mod_add_sub_limb_equation(),
        pending_formula(
            "fp_solinas_mul_reduction",
            "Pending until the signed Solinas reduction matrix and carry-normalization schedule are implemented in `solinas`.",
        ),
        pending_formula(
            "rcb_projective_add_double",
            "Pending until the RCB Algorithm 5/6 limb-coefficient simulator in `rcb_analyzer` is implemented.",
        ),
    ]
}

pub fn audit_generic_quotient_mul_256x256() -> EquationHeadroom {
    let limb_max = LIMB_MAX as i128;
    let mut bounds = Vec::with_capacity(2 * N_LIMBS);

    for limb_index in 0..(2 * N_LIMBS) {
        let product_terms = convolution_term_count(limb_index, N_LIMBS, N_LIMBS) as i128;
        let quotient_terms = convolution_term_count(limb_index, N_LIMBS, N_LIMBS) as i128;
        let result_bound = if limb_index < N_LIMBS { limb_max } else { 0 };

        bounds.push(
            product_terms * limb_max * limb_max
                + quotient_terms * limb_max * limb_max
                + result_bound,
        );
    }

    audit_direct_limb_equation(
        "generic_quotient_mul_256x256",
        bounds,
        "Single-equation 256x256 quotient multiplication exceeds centered M31; split product/quotient/carry checks before using this shape in AIR.",
    )
}

pub fn audit_fake_glv_scalar_mul_256x128() -> EquationHeadroom {
    let limb_max = LIMB_MAX as i128;
    let full_limb_bounds = vec![limb_max; N_LIMBS];
    let scalar_128_limb_bounds = limb_bounds_128();
    let mut bounds = Vec::with_capacity(N_LIMBS + scalar_128_limb_bounds.len());

    for limb_index in 0..(N_LIMBS + scalar_128_limb_bounds.len()) {
        let product_bound =
            convolution_bound(limb_index, &full_limb_bounds, &scalar_128_limb_bounds);
        let quotient_bound =
            convolution_bound(limb_index, &scalar_128_limb_bounds, &full_limb_bounds);
        let signed_s1_bound = scalar_128_limb_bounds.get(limb_index).copied().unwrap_or(0);

        bounds.push(product_bound + quotient_bound + signed_s1_bound);
    }

    audit_direct_limb_equation(
        "fake_glv_scalar_mul_256x128",
        bounds,
        "Single-equation fake-GLV scalar multiplication exceeds centered M31; split the 256x128 product, q*n subtraction, or carry normalization.",
    )
}

pub fn audit_mod_add_sub_limb_equation() -> EquationHeadroom {
    let limb_max = LIMB_MAX as i128;
    let mut bounds = Vec::with_capacity(N_LIMBS + 1);

    for limb_index in 0..=N_LIMBS {
        let bound = if limb_index < N_LIMBS {
            // a +/- b +/- modulus - result, with each dynamic or constant limb
            // conservatively bounded by one full 13-bit limb.
            4 * limb_max
        } else {
            0
        };
        bounds.push(bound);
    }

    audit_direct_limb_equation(
        "mod_add_sub_limb_equation",
        bounds,
        "Addition/subtraction limb equations fit centered M31 directly with small signed carries.",
    )
}

fn pending_formula(name: &'static str, note: &'static str) -> EquationHeadroom {
    EquationHeadroom {
        name,
        status: HeadroomStatus::PendingFormula,
        signed_carry_bound: None,
        max_abs_combined_expression: None,
        limbs: Vec::new(),
        note,
    }
}

fn audit_direct_limb_equation(
    name: &'static str,
    coefficient_bounds: Vec<i128>,
    note: &'static str,
) -> EquationHeadroom {
    let mut limbs = Vec::with_capacity(coefficient_bounds.len());
    let mut carry_bound_in = 0;
    let mut signed_carry_bound = 0;
    let mut max_abs_combined_expression = 0;

    for (limb_index, coefficient_bound_before_carry) in coefficient_bounds.into_iter().enumerate() {
        let carry_bound_out =
            ceil_div_nonnegative(coefficient_bound_before_carry + carry_bound_in, LIMB_BASE);
        let max_abs_for_limb =
            coefficient_bound_before_carry + carry_bound_in + LIMB_BASE * carry_bound_out;

        signed_carry_bound = signed_carry_bound.max(carry_bound_out);
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
        signed_carry_bound: Some(signed_carry_bound),
        max_abs_combined_expression: Some(max_abs_combined_expression),
        limbs,
        note,
    }
}

fn convolution_term_count(limb_index: usize, left_len: usize, right_len: usize) -> usize {
    (0..left_len)
        .filter(|left_index| {
            let right_index = limb_index.saturating_sub(*left_index);
            limb_index >= *left_index && right_index < right_len
        })
        .count()
}

fn convolution_bound(limb_index: usize, left: &[i128], right: &[i128]) -> i128 {
    left.iter()
        .enumerate()
        .filter_map(|(left_index, left_bound)| {
            let right_index = limb_index.checked_sub(left_index)?;
            right
                .get(right_index)
                .map(|right_bound| left_bound * right_bound)
        })
        .sum()
}

fn limb_bounds_128() -> Vec<i128> {
    let mut bounds = vec![LIMB_MAX as i128; 10];
    bounds[9] = (1 << 11) - 1;
    bounds
}

fn ceil_div_nonnegative(numerator: i128, denominator: i128) -> i128 {
    debug_assert!(numerator >= 0);
    debug_assert!(denominator > 0);
    (numerator + denominator - 1) / denominator
}

#[cfg(test)]
mod tests {
    use super::*;

    fn audit(name: &str) -> EquationHeadroom {
        current_headroom_audits()
            .into_iter()
            .find(|audit| audit.name == name)
            .unwrap_or_else(|| panic!("missing headroom audit for {name}"))
    }

    #[test]
    fn test_current_headroom_statuses_are_explicit() {
        assert_eq!(
            audit("mod_add_sub_limb_equation").status,
            HeadroomStatus::Fits
        );
        assert_eq!(
            audit("generic_quotient_mul_256x256").status,
            HeadroomStatus::RequiresSplit
        );
        assert_eq!(
            audit("fake_glv_scalar_mul_256x128").status,
            HeadroomStatus::RequiresSplit
        );
        assert_eq!(
            audit("fp_solinas_mul_reduction").status,
            HeadroomStatus::PendingFormula
        );
        assert_eq!(
            audit("rcb_projective_add_double").status,
            HeadroomStatus::PendingFormula
        );
    }

    #[test]
    fn test_fit_status_matches_centered_m31_limit() {
        for audit in current_headroom_audits() {
            match audit.status {
                HeadroomStatus::Fits => {
                    assert!(
                        audit.direct_equation_fits(),
                        "{} is marked Fits but exceeds centered M31: {:?}",
                        audit.name,
                        audit.max_abs_combined_expression
                    );
                }
                HeadroomStatus::RequiresSplit => {
                    assert!(
                        !audit.direct_equation_fits(),
                        "{} is marked RequiresSplit but fits centered M31",
                        audit.name
                    );
                }
                HeadroomStatus::PendingFormula => {
                    assert!(
                        audit.limbs.is_empty()
                            && audit.signed_carry_bound.is_none()
                            && audit.max_abs_combined_expression.is_none(),
                        "{} is pending but already has concrete bounds",
                        audit.name
                    );
                }
            }
        }
    }

    #[test]
    fn test_add_sub_has_small_signed_carry_bound() {
        let audit = audit("mod_add_sub_limb_equation");
        assert_eq!(audit.signed_carry_bound, Some(4));
        assert!(
            audit.max_abs_combined_expression.unwrap() < M31_CENTER_LIMIT,
            "add/sub should fit centered M31"
        );
    }
}
