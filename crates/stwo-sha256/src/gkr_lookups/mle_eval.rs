//! Multilinear extension (MLE) eval-at-point constraints vendored from Stwo examples.

#![allow(dead_code)]

use std::iter::{once, zip};

use num_traits::{One, Zero};
use stwo::core::air::accumulation::PointEvaluationAccumulator;
use stwo::core::air::Component;
use stwo::core::circle::{CirclePoint, Coset};
use stwo::core::constraints::{coset_vanishing, point_vanishing};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fields::{Field, FieldExpOps};
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::poly::circle::CircleDomain;
use stwo::core::utils::{bit_reverse, bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::column::{SecureColumn, VeryPackedSecureColumnByCoords};
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::prefix_sum::inclusive_prefix_sum;
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::very_packed_m31::{VeryPackedBaseField, LOG_N_VERY_PACKED_ELEMS};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column};
use stwo::prover::lookups::gkr_prover::GkrOps;
use stwo::prover::lookups::mle::Mle;
use stwo::prover::lookups::utils::eq;
use stwo::prover::poly::circle::{CircleEvaluation, SecureCirclePoly, SecureEvaluation};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::secure_column::SecureColumnByCoords;
use stwo::prover::{ComponentProver, DomainEvaluationAccumulator, Trace};
use stwo_constraint_framework::{
    EvalAtRow, InfoEvaluator, PointEvaluator, SimdDomainEvaluator, TraceLocationAllocator,
};

use super::IsFirst;

#[cfg(test)]
use super::test::mle_eval_at_point;

/// Prover component that carries out a univariate IOP for multilinear eval at point.
pub struct MleEvalProverComponent<O: MleCoeffColumnOracle> {
    mle_coeff_column_poly: SecureCirclePoly<SimdBackend>,
    mle_coeff_column_oracle: O,
    mle_eval_point: MleEvalPoint,
    mle_claim_shift: SecureField,
    interaction: usize,
    pad_log_size: Option<u32>,
    max_constraint_log_degree_bound: u32,
    trace_locations: TreeVec<TreeSubspan>,
}

impl<O: MleCoeffColumnOracle> MleEvalProverComponent<O> {
    /// Generates a prover component that carries out univariate IOP for MLE eval at point.
    ///
    /// # Panics
    ///
    /// Panics if the eval point is empty or has a coordinate equal to zero or one.
    pub fn generate(
        location_allocator: &mut TraceLocationAllocator,
        mle_coeff_column_oracle: O,
        mle_eval_point: &[SecureField],
        mle: Mle<SimdBackend, SecureField>,
        mle_claim: SecureField,
        interaction: usize,
    ) -> Self {
        Self::generate_inner(
            location_allocator,
            mle_coeff_column_oracle,
            mle_eval_point,
            mle,
            mle_claim,
            interaction,
            None,
        )
    }

    pub fn generate_with_pad_column(
        location_allocator: &mut TraceLocationAllocator,
        mle_coeff_column_oracle: O,
        mle_eval_point: &[SecureField],
        mle: Mle<SimdBackend, SecureField>,
        mle_claim: SecureField,
        interaction: usize,
        pad_log_size: u32,
    ) -> Self {
        Self::generate_inner(
            location_allocator,
            mle_coeff_column_oracle,
            mle_eval_point,
            mle,
            mle_claim,
            interaction,
            Some(pad_log_size),
        )
    }

    fn generate_inner(
        location_allocator: &mut TraceLocationAllocator,
        mle_coeff_column_oracle: O,
        mle_eval_point: &[SecureField],
        mle: Mle<SimdBackend, SecureField>,
        mle_claim: SecureField,
        interaction: usize,
        pad_log_size: Option<u32>,
    ) -> Self {
        #[cfg(test)]
        assert_eq!(mle_claim, mle_eval_at_point(&mle, mle_eval_point));
        let n_variables = mle.n_variables();
        let mle_claim_shift = mle_claim / BaseField::from(1 << n_variables);

        let domain = CanonicCoset::new(n_variables as u32).circle_domain();
        let values = mle.into_evals().into_secure_column_by_coords();
        let mle_trace = SecureEvaluation::<SimdBackend, BitReversedOrder>::new(domain, values);
        let mle_coeff_column_poly = SecureCirclePoly(
            mle_trace
                .into_coordinate_evals()
                .map(CircleEvaluation::interpolate),
        );

        let trace_structure = mle_eval_trace_structure(interaction, n_variables, pad_log_size);
        let trace_locations = location_allocator.next_for_structure(&trace_structure);

        Self {
            mle_coeff_column_poly,
            mle_coeff_column_oracle,
            mle_eval_point: MleEvalPoint::new(mle_eval_point),
            mle_claim_shift,
            interaction,
            pad_log_size,
            max_constraint_log_degree_bound: n_variables as u32 + 1,
            trace_locations,
        }
    }

    pub fn with_max_constraint_log_degree_bound(mut self, bound: u32) -> Self {
        assert!(bound >= self.log_size() + 1);
        self.max_constraint_log_degree_bound = bound;
        self
    }

    pub const fn log_size(&self) -> u32 {
        self.mle_eval_point.n_variables() as u32
    }

    pub fn eval_info(&self) -> InfoEvaluator {
        let n_variables = self.mle_eval_point.n_variables();
        mle_eval_info(self.interaction, n_variables)
    }

    fn trace_structure(&self) -> TreeVec<ColumnVec<Vec<isize>>> {
        mle_eval_trace_structure(
            self.interaction,
            self.mle_eval_point.n_variables(),
            self.pad_log_size,
        )
    }
}

impl<O: MleCoeffColumnOracle> Component for MleEvalProverComponent<O> {
    fn n_constraints(&self) -> usize {
        self.eval_info().n_constraints
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_constraint_log_degree_bound
    }

    fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        let log_size = self.log_size();
        let mut bounds = self
            .trace_structure()
            .map(|tree_offsets| vec![log_size; tree_offsets.len()]);
        if let Some(pad_log_size) = self.pad_log_size {
            *bounds[self.interaction]
                .last_mut()
                .expect("pad column is present") = pad_log_size;
        }
        bounds
    }

    fn mask_points(
        &self,
        point: CirclePoint<SecureField>,
        max_log_degree_bound: u32,
    ) -> TreeVec<ColumnVec<Vec<CirclePoint<SecureField>>>> {
        let trace_step = CanonicCoset::new(max_log_degree_bound).step();
        self.trace_structure().map_cols(|col_offsets| {
            col_offsets
                .iter()
                .map(|offset| point + trace_step.mul_signed(*offset).into_ef())
                .collect()
        })
    }

    fn preprocessed_column_indices(&self) -> ColumnVec<usize> {
        vec![]
    }

    fn evaluate_constraint_quotients_at_point(
        &self,
        point: CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
        accumulator: &mut PointEvaluationAccumulator,
        max_log_degree_bound: u32,
    ) {
        let trace_point = point.repeated_double(max_log_degree_bound - self.log_size());
        let mle_coeff_col_eval = self.mle_coeff_column_poly.eval_at_point(trace_point);
        let oracle_mle_coeff_col_eval = self.mle_coeff_column_oracle.evaluate_at_point(point, mask);
        assert_eq!(mle_coeff_col_eval, oracle_mle_coeff_col_eval);

        let component_mask = mask.sub_tree(&self.trace_locations);
        let trace_coset = CanonicCoset::new(self.log_size()).coset;
        let quotient_coset = CanonicCoset::new(max_log_degree_bound).coset;
        let vanish_on_trace_eval_inv = coset_vanishing(quotient_coset, point).inverse();
        let mut eval = PointEvaluator::new(
            component_mask,
            accumulator,
            vanish_on_trace_eval_inv,
            self.log_size(),
            SecureField::zero(),
        );

        let carry_quotients_col_eval = eval_carry_quotient_col(&self.mle_eval_point, trace_point);
        let is_first = eval_is_first(trace_coset, trace_point);
        let is_second = eval_is_first(trace_coset, trace_point - trace_coset.step.into_ef());

        eval_mle_eval_constraints(
            self.interaction,
            &mut eval,
            mle_coeff_col_eval,
            &self.mle_eval_point,
            self.mle_claim_shift,
            carry_quotients_col_eval,
            is_first,
            is_second,
        )
    }
}

impl<O: MleCoeffColumnOracle> ComponentProver<SimdBackend> for MleEvalProverComponent<O> {
    fn evaluate_constraint_quotients_on_domain(
        &self,
        trace: &Trace<'_, SimdBackend>,
        accumulator: &mut DomainEvaluationAccumulator<SimdBackend>,
    ) {
        let eval_domain = CanonicCoset::new(self.max_constraint_log_degree_bound()).circle_domain();
        let trace_domain = CanonicCoset::new(self.log_size());
        let mut component_trace = trace
            .polys
            .sub_tree(&self.trace_locations)
            .map_cols(|c| &c.evals);

        let mle_coeffs_column_lde = self
            .mle_coeff_column_poly
            .evaluate_on_domain(eval_domain)
            .into_coordinate_evals();
        let carry_quotients_column_lde =
            secure_eval_to_poly(gen_carry_quotient_col(&self.mle_eval_point.p))
                .evaluate_on_domain(eval_domain)
                .into_coordinate_evals();
        let is_first_lde = IsFirst::new(self.log_size())
            .gen_column_simd()
            .interpolate()
            .evaluate(eval_domain);
        let aux_interaction = self
            .interaction
            .checked_sub(1)
            .expect("MLE eval trace needs a spare auxiliary interaction slot");
        let aux_trace = mle_coeffs_column_lde
            .iter()
            .chain(carry_quotients_column_lde.iter())
            .chain(once(&is_first_lde))
            .collect();
        debug_assert!(component_trace[aux_interaction].is_empty());
        component_trace[aux_interaction] = aux_trace;

        let log_expand = eval_domain.log_size() - trace_domain.log_size();
        let mut denom_inv = (0..1 << log_expand)
            .map(|i| coset_vanishing(trace_domain.coset(), eval_domain.at(i)).inverse())
            .collect::<Vec<_>>();
        bit_reverse(&mut denom_inv);

        let [mut acc] = accumulator.columns([(eval_domain.log_size(), self.n_constraints())]);
        acc.random_coeff_powers.reverse();
        let acc_col = unsafe { VeryPackedSecureColumnByCoords::transform_under_mut(acc.col) };
        let n_very_packed_rows =
            1 << (eval_domain.log_size() - LOG_N_LANES - LOG_N_VERY_PACKED_ELEMS);

        for vec_row in 0..n_very_packed_rows {
            let mut eval = SimdDomainEvaluator::new(
                &component_trace,
                vec_row,
                &acc.random_coeff_powers,
                trace_domain.log_size(),
                eval_domain.log_size(),
                self.log_size(),
                SecureField::zero(),
            );
            let [mle_coeffs_col_eval] = eval.next_extension_interaction_mask(aux_interaction, [0]);
            let [carry_quotients_col_eval] =
                eval.next_extension_interaction_mask(aux_interaction, [0]);
            let [is_first, is_second] = eval.next_interaction_mask(aux_interaction, [0, -1]);
            eval_mle_eval_constraints(
                self.interaction,
                &mut eval,
                mle_coeffs_col_eval,
                &self.mle_eval_point,
                self.mle_claim_shift,
                carry_quotients_col_eval,
                is_first,
                is_second,
            );

            let row_res = eval.row_res;
            let denom_inv = VeryPackedBaseField::broadcast(
                denom_inv
                    [vec_row >> (trace_domain.log_size() - LOG_N_LANES - LOG_N_VERY_PACKED_ELEMS)],
            );
            unsafe { acc_col.set_packed(vec_row, acc_col.packed_at(vec_row) + row_res * denom_inv) }
        }
    }
}

/// Verifier component that carries out a univariate IOP for multilinear eval at point.
pub struct MleEvalVerifierComponent<O: MleCoeffColumnOracle> {
    mle_coeff_column_oracle: O,
    mle_eval_point: MleEvalPoint,
    mle_claim_shift: SecureField,
    interaction: usize,
    pad_log_size: Option<u32>,
    max_constraint_log_degree_bound: u32,
    trace_location: TreeVec<TreeSubspan>,
}

impl<O: MleCoeffColumnOracle> MleEvalVerifierComponent<O> {
    pub fn new(
        location_allocator: &mut TraceLocationAllocator,
        mle_coeff_column_oracle: O,
        eval_point: &[SecureField],
        claim: SecureField,
        interaction: usize,
    ) -> Self {
        Self::new_inner(
            location_allocator,
            mle_coeff_column_oracle,
            eval_point,
            claim,
            interaction,
            None,
        )
    }

    pub fn new_with_pad_column(
        location_allocator: &mut TraceLocationAllocator,
        mle_coeff_column_oracle: O,
        eval_point: &[SecureField],
        claim: SecureField,
        interaction: usize,
        pad_log_size: u32,
    ) -> Self {
        Self::new_inner(
            location_allocator,
            mle_coeff_column_oracle,
            eval_point,
            claim,
            interaction,
            Some(pad_log_size),
        )
    }

    fn new_inner(
        location_allocator: &mut TraceLocationAllocator,
        mle_coeff_column_oracle: O,
        eval_point: &[SecureField],
        claim: SecureField,
        interaction: usize,
        pad_log_size: Option<u32>,
    ) -> Self {
        let mle_eval_point = MleEvalPoint::new(eval_point);
        let n_variables = mle_eval_point.n_variables();
        let mle_claim_shift = claim / BaseField::from(1 << n_variables);
        let trace_structure = mle_eval_trace_structure(interaction, n_variables, pad_log_size);
        let trace_location = location_allocator.next_for_structure(&trace_structure);

        Self {
            mle_coeff_column_oracle,
            mle_eval_point,
            mle_claim_shift,
            interaction,
            pad_log_size,
            max_constraint_log_degree_bound: n_variables as u32 + 1,
            trace_location,
        }
    }

    pub fn with_max_constraint_log_degree_bound(mut self, bound: u32) -> Self {
        assert!(bound >= self.log_size() + 1);
        self.max_constraint_log_degree_bound = bound;
        self
    }

    pub const fn log_size(&self) -> u32 {
        self.mle_eval_point.n_variables() as u32
    }

    pub fn eval_info(&self) -> InfoEvaluator {
        let n_variables = self.mle_eval_point.n_variables();
        mle_eval_info(self.interaction, n_variables)
    }

    fn trace_structure(&self) -> TreeVec<ColumnVec<Vec<isize>>> {
        mle_eval_trace_structure(
            self.interaction,
            self.mle_eval_point.n_variables(),
            self.pad_log_size,
        )
    }
}

impl<O: MleCoeffColumnOracle> Component for MleEvalVerifierComponent<O> {
    fn n_constraints(&self) -> usize {
        self.eval_info().n_constraints
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.max_constraint_log_degree_bound
    }

    fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        let log_size = self.log_size();
        let mut bounds = self
            .trace_structure()
            .map(|tree_offsets| vec![log_size; tree_offsets.len()]);
        if let Some(pad_log_size) = self.pad_log_size {
            *bounds[self.interaction]
                .last_mut()
                .expect("pad column is present") = pad_log_size;
        }
        bounds
    }

    fn mask_points(
        &self,
        point: CirclePoint<SecureField>,
        max_log_degree_bound: u32,
    ) -> TreeVec<ColumnVec<Vec<CirclePoint<SecureField>>>> {
        let trace_step = CanonicCoset::new(max_log_degree_bound).step();
        self.trace_structure().map_cols(|col_offsets| {
            col_offsets
                .iter()
                .map(|offset| point + trace_step.mul_signed(*offset).into_ef())
                .collect()
        })
    }

    fn preprocessed_column_indices(&self) -> ColumnVec<usize> {
        vec![]
    }

    fn evaluate_constraint_quotients_at_point(
        &self,
        point: CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
        accumulator: &mut PointEvaluationAccumulator,
        max_log_degree_bound: u32,
    ) {
        let trace_point = point.repeated_double(max_log_degree_bound - self.log_size());
        let component_mask = mask.sub_tree(&self.trace_location);
        let trace_coset = CanonicCoset::new(self.log_size()).coset;
        let quotient_coset = CanonicCoset::new(max_log_degree_bound).coset;
        let vanish_on_trace_eval_inv = coset_vanishing(quotient_coset, point).inverse();
        let mut eval = PointEvaluator::new(
            component_mask,
            accumulator,
            vanish_on_trace_eval_inv,
            self.log_size(),
            SecureField::zero(),
        );

        let mle_coeff_col_eval = self.mle_coeff_column_oracle.evaluate_at_point(point, mask);
        let carry_quotients_col_eval = eval_carry_quotient_col(&self.mle_eval_point, trace_point);
        let is_first = eval_is_first(trace_coset, trace_point);
        let is_second = eval_is_first(trace_coset, trace_point - trace_coset.step.into_ef());

        eval_mle_eval_constraints(
            self.interaction,
            &mut eval,
            mle_coeff_col_eval,
            &self.mle_eval_point,
            self.mle_claim_shift,
            carry_quotients_col_eval,
            is_first,
            is_second,
        )
    }
}

fn mle_eval_info(interaction: usize, n_variables: usize) -> InfoEvaluator {
    let mut eval = InfoEvaluator::empty();
    let mle_eval_point = MleEvalPoint::new(&vec![SecureField::from(2); n_variables]);
    let mle_claim_shift = SecureField::zero();
    let mle_coeffs_col_eval = SecureField::zero().into();
    let carry_quotients_col_eval = SecureField::zero().into();
    let is_first = BaseField::zero().into();
    let is_second = BaseField::zero().into();
    eval_mle_eval_constraints(
        interaction,
        &mut eval,
        mle_coeffs_col_eval,
        &mle_eval_point,
        mle_claim_shift,
        carry_quotients_col_eval,
        is_first,
        is_second,
    );
    eval
}

fn mle_eval_trace_structure(
    interaction: usize,
    n_variables: usize,
    pad_log_size: Option<u32>,
) -> TreeVec<ColumnVec<Vec<isize>>> {
    let mut structure = mle_eval_info(interaction, n_variables).mask_offsets;
    if pad_log_size.is_some() {
        if structure.len() <= interaction {
            structure.resize(interaction + 1, vec![]);
        }
        structure[interaction].push(vec![]);
    }
    structure
}

/// Oracle for the polynomial encoding the MLE coefficients in multilinear Lagrange basis.
pub trait MleCoeffColumnOracle {
    fn evaluate_at_point(
        &self,
        point: CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
    ) -> SecureField;
}

trait SecureCirclePolyExt {
    fn evaluate_on_domain(
        &self,
        domain: CircleDomain,
    ) -> SecureEvaluation<SimdBackend, BitReversedOrder>;
}

impl SecureCirclePolyExt for SecureCirclePoly<SimdBackend> {
    fn evaluate_on_domain(
        &self,
        domain: CircleDomain,
    ) -> SecureEvaluation<SimdBackend, BitReversedOrder> {
        SecureEvaluation::new(
            domain,
            SecureColumnByCoords {
                columns: self.0.each_ref().map(|poly| poly.evaluate(domain).values),
            },
        )
    }
}

fn secure_eval_to_poly(
    eval: SecureEvaluation<SimdBackend, BitReversedOrder>,
) -> SecureCirclePoly<SimdBackend> {
    SecureCirclePoly(
        eval.into_coordinate_evals()
            .map(CircleEvaluation::interpolate),
    )
}

impl<T: MleCoeffColumnOracle + ?Sized> MleCoeffColumnOracle for &T {
    fn evaluate_at_point(
        &self,
        point: CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
    ) -> SecureField {
        (*self).evaluate_at_point(point, mask)
    }
}

#[allow(clippy::too_many_arguments)]
pub fn eval_mle_eval_constraints<E: EvalAtRow>(
    interaction: usize,
    eval: &mut E,
    mle_coeffs_col_eval: E::EF,
    mle_eval_point: &MleEvalPoint,
    mle_claim_shift: SecureField,
    carry_quotients_col_eval: E::EF,
    is_first: E::F,
    is_second: E::F,
) {
    let eq_col_eval = eval_eq_constraints(
        interaction,
        eval,
        mle_eval_point,
        carry_quotients_col_eval,
        is_first,
        is_second,
    );
    let terms_col_eval = mle_coeffs_col_eval * eq_col_eval;
    eval_prefix_sum_constraints(interaction, eval, terms_col_eval, mle_claim_shift)
}

#[derive(Debug, Clone)]
pub struct MleEvalPoint {
    eq_0_p: SecureField,
    eq_1_p: SecureField,
    eq_carry_quotients: Vec<SecureField>,
    p: Vec<SecureField>,
}

impl MleEvalPoint {
    pub fn new(p: &[SecureField]) -> Self {
        assert!(!p.is_empty());
        let n_variables = p.len();
        let zero = SecureField::zero();
        let one = SecureField::one();

        Self {
            eq_0_p: eq(&vec![zero; n_variables], p),
            eq_1_p: eq(&vec![one; n_variables], p),
            eq_carry_quotients: (0..n_variables)
                .map(|i| {
                    let mut numerator_assignment = vec![one; i + 1];
                    numerator_assignment[i] = zero;
                    let mut denom_assignment = vec![zero; i + 1];
                    denom_assignment[i] = one;
                    eq(&numerator_assignment, &p[..i + 1]) / eq(&denom_assignment, &p[..i + 1])
                })
                .collect(),
            p: p.to_vec(),
        }
    }

    pub const fn n_variables(&self) -> usize {
        self.p.len()
    }
}

fn eval_eq_constraints<E: EvalAtRow>(
    eq_interaction: usize,
    eval: &mut E,
    mle_eval_point: &MleEvalPoint,
    carry_quotients_col_eval: E::EF,
    is_first: E::F,
    is_second: E::F,
) -> E::EF {
    let [curr, next_next] = eval.next_extension_interaction_mask(eq_interaction, [0, 2]);
    let half_coset0_initial_check = (curr.clone() - mle_eval_point.eq_0_p) * is_first;
    let half_coset1_final_check = (curr.clone() - mle_eval_point.eq_1_p) * is_second;
    eval.add_constraint(half_coset0_initial_check + half_coset1_final_check);
    eval.add_constraint(curr.clone() - next_next * carry_quotients_col_eval);
    curr
}

fn eval_prefix_sum_constraints<E: EvalAtRow>(
    interaction: usize,
    eval: &mut E,
    row_diff: E::EF,
    cumulative_sum_shift: SecureField,
) {
    let [curr, prev] = eval.next_extension_interaction_mask(interaction, [0, -1]);
    eval.add_constraint(curr - prev - row_diff + cumulative_sum_shift);
}

pub fn build_trace(
    mle: &Mle<SimdBackend, SecureField>,
    eval_point: &[SecureField],
    claim: SecureField,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let eq_evals = SimdBackend::gen_eq_evals(eval_point, SecureField::one()).into_evals();
    let mle_terms = hadamard_product(mle, &eq_evals);
    let eq_evals_cols = eq_evals.into_secure_column_by_coords().columns;
    let mle_terms_cols = mle_terms.into_secure_column_by_coords().columns;

    #[cfg(test)]
    debug_assert_eq!(claim, mle_eval_at_point(mle, eval_point));
    let shift = claim / BaseField::from(mle.len());
    let packed_shift_coords = PackedSecureField::broadcast(shift).into_packed_m31s();
    let mut shifted_mle_terms_cols = mle_terms_cols;
    zip(&mut shifted_mle_terms_cols, packed_shift_coords)
        .for_each(|(col, shift_coord)| col.data.iter_mut().for_each(|v| *v -= shift_coord));
    let shifted_prefix_sum_cols = shifted_mle_terms_cols.map(inclusive_prefix_sum);

    let log_trace_domain_size = mle.n_variables() as u32;
    let trace_domain = CanonicCoset::new(log_trace_domain_size).circle_domain();
    eq_evals_cols
        .into_iter()
        .chain(shifted_prefix_sum_cols)
        .map(|c| CircleEvaluation::new(trace_domain, c))
        .collect()
}

fn gen_carry_quotient_col(
    eval_point: &[SecureField],
) -> SecureEvaluation<SimdBackend, BitReversedOrder> {
    assert!(!eval_point.is_empty());
    let mle_eval_point = MleEvalPoint::new(eval_point);
    let (half_coset0_carry_quotients, half_coset1_carry_quotients) =
        gen_half_coset_carry_quotients(&mle_eval_point);

    let log_size = mle_eval_point.n_variables() as u32;
    let size = 1 << log_size;
    let half_coset_size = size / 2;
    let mut col = SecureColumnByCoords::<SimdBackend>::zeros(size);

    for i in 0..half_coset_size {
        let half_coset0_index = coset_index_to_circle_domain_index(i * 2, log_size);
        let half_coset1_index = coset_index_to_circle_domain_index(i * 2 + 1, log_size);
        let half_coset0_index_bit_rev = bit_reverse_index(half_coset0_index, log_size);
        let half_coset1_index_bit_rev = bit_reverse_index(half_coset1_index, log_size);

        let n_trailing_ones = i.trailing_ones() as usize;
        let half_coset0_carry_quotient = half_coset0_carry_quotients[n_trailing_ones];
        let half_coset1_carry_quotient = half_coset1_carry_quotients[n_trailing_ones];

        col.set(half_coset0_index_bit_rev, half_coset0_carry_quotient);
        col.set(half_coset1_index_bit_rev, half_coset1_carry_quotient);
    }

    let domain = CanonicCoset::new(log_size).circle_domain();
    SecureEvaluation::new(domain, col)
}

fn eval_carry_quotient_col(eval_point: &MleEvalPoint, p: CirclePoint<SecureField>) -> SecureField {
    let n_variables = eval_point.n_variables();
    let log_size = n_variables as u32;
    let coset = CanonicCoset::new(log_size).coset();
    let (half_coset0_carry_quotients, half_coset1_carry_quotients) =
        gen_half_coset_carry_quotients(eval_point);
    let mut eval = SecureField::zero();

    for variable_i in 0..n_variables.saturating_sub(1) {
        let log_step = variable_i as u32 + 2;
        let offset = (1 << (log_step - 1)) - 2;
        let half_coset0_selector = eval_step_selector_with_offset(coset, offset, log_step, p);
        let half_coset1_selector = eval_step_selector_with_offset(coset, offset + 1, log_step, p);
        eval += half_coset0_selector * half_coset0_carry_quotients[variable_i];
        eval += half_coset1_selector * half_coset1_carry_quotients[variable_i];
    }

    let half_coset0_last = eval_is_first(coset, p + coset.step.double().into_ef());
    let half_coset1_first = eval_is_first(coset, p + coset.step.into_ef());
    eval += *half_coset0_carry_quotients.last().unwrap() * half_coset0_last;
    eval += *half_coset1_carry_quotients.last().unwrap() * half_coset1_first;
    eval
}

fn eval_step_selector_with_offset(
    coset: Coset,
    offset: usize,
    log_step: u32,
    p: CirclePoint<SecureField>,
) -> SecureField {
    let offset_step = coset.step.mul(offset as u128);
    eval_step_selector(coset, log_step, p - offset_step.into_ef())
}

fn eval_step_selector(coset: Coset, log_step: u32, p: CirclePoint<SecureField>) -> SecureField {
    if log_step == 0 {
        return SecureField::one();
    }

    let p = p - coset.initial.into_ef();
    let mut vanish_at_log_step = (0..coset.log_size)
        .scan(p, |p, _| {
            let res = *p;
            *p = p.double();
            Some(res.y)
        })
        .collect::<Vec<_>>();
    vanish_at_log_step.reverse();
    vanish_at_log_step.truncate(log_step as usize);
    let vanish_at_log_step_inv = SecureField::batch_inverse(&vanish_at_log_step);

    let half_coset_selector_dbl = (vanish_at_log_step[0] * vanish_at_log_step_inv[1]).square();
    let vanish_substep_inv_sum = vanish_at_log_step_inv[1..].iter().sum::<SecureField>();
    (half_coset_selector_dbl + vanish_at_log_step[0] * vanish_substep_inv_sum.double())
        / BaseField::from(1 << (log_step + 1))
}

fn eval_is_first(coset: Coset, p: CirclePoint<SecureField>) -> SecureField {
    coset_vanishing(coset, p)
        / (point_vanishing(coset.initial, p) * BaseField::from(1 << coset.log_size))
}

fn gen_half_coset_carry_quotients(
    eval_point: &MleEvalPoint,
) -> (Vec<SecureField>, Vec<SecureField>) {
    let last_variable = *eval_point.p.last().unwrap();
    let mut half_coset0_carry_quotients = eval_point.eq_carry_quotients.clone();
    *half_coset0_carry_quotients.last_mut().unwrap() *=
        eq(&[SecureField::one()], &[last_variable]) / eq(&[SecureField::zero()], &[last_variable]);
    let half_coset1_carry_quotients = half_coset0_carry_quotients
        .iter()
        .map(|v| v.inverse())
        .collect();
    (half_coset0_carry_quotients, half_coset1_carry_quotients)
}

fn hadamard_product(
    a: &Col<SimdBackend, SecureField>,
    b: &Col<SimdBackend, SecureField>,
) -> Col<SimdBackend, SecureField> {
    assert_eq!(a.len(), b.len());
    SecureColumn {
        data: a.data.iter().zip(&b.data).map(|(&a, &b)| a * b).collect(),
        length: a.len(),
    }
}
