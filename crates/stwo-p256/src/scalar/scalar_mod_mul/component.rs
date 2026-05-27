use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_p256_utils::constants::LIMB_BITS;

use crate::limbs::P256BigInt;
use crate::range_checks::add_range_check;

use super::canonical::{add_canonical_lt_n, CanonicalLtNColumns, CanonicalLtNRelations};
use super::schedule::{ProductFamily, ScalarModMulScheduleColumnIds};
use super::{
    ScalarLimbRelation, ScalarModMulComponentRelations, ScalarProductChunkDigitRelation,
    ScalarProductDigitRelation, ScalarReductionCarryRelation, PRODUCT_DIGIT_ACCUMULATOR_TERMS,
    ROLE_A, ROLE_B, ROLE_QUOTIENT, ROLE_RESULT, SCALAR_LIMB_RELATION_ARITY,
    SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS, SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS, SIDE_AB, SIDE_QN,
};

pub type CanonicalScalarComponent = FrameworkComponent<CanonicalScalarEval>;
pub type AbProductChunkComponent = FrameworkComponent<AbProductChunkEval>;
pub type QnProductChunkComponent = FrameworkComponent<QnProductChunkEval>;
pub type ProductDigitAccumulatorComponent = FrameworkComponent<ProductDigitAccumulatorEval>;
pub type ScalarReductionDigitComponent = FrameworkComponent<ScalarReductionDigitEval>;

#[derive(Clone)]
pub struct CanonicalScalarEval {
    pub log_size: u32,
    pub mul_id: u32,
    pub relations: ScalarModMulComponentRelations,
}

impl FrameworkEval for CanonicalScalarEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::canonical_active());
        let role = eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::canonical_role());
        let multiplicity =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::canonical_multiplicity());

        let value = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let slack = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let carries = core::array::from_fn(|_| eval.next_trace_mask());

        add_canonical_lt_n(
            &mut eval,
            CanonicalLtNRelations {
                range13: &self.relations.range13,
            },
            active.clone(),
            &CanonicalLtNColumns {
                value: value.clone(),
                slack,
                carries,
            },
        );

        let mul_id: E::F = constant(self.mul_id);
        for (limb_index, limb) in value.limbs().iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.relations.scalar_limb,
                -E::EF::from(active.clone() * multiplicity.clone()),
                &[
                    mul_id.clone(),
                    role.clone(),
                    constant(limb_index as u32),
                    limb.clone(),
                ],
            ));
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct AbProductChunkEval {
    pub log_size: u32,
    pub mul_id: u32,
    pub relations: ScalarModMulComponentRelations,
}

impl FrameworkEval for AbProductChunkEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let meta = ProductMetadata::read(&mut eval, ProductFamily::Ab);
        let terms: [(E::F, E::F); SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS] =
            core::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));
        let digits: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS] =
            core::array::from_fn(|_| eval.next_trace_mask());

        let mut product_sum = E::F::from(M31::from_u32_unchecked(0));
        for (term_index, (lhs, rhs)) in terms.iter().enumerate() {
            let term_active = meta.term_active[term_index].clone();
            product_sum += term_active.clone() * lhs.clone() * rhs.clone();
            constrain_unused(
                &mut eval,
                meta.active.clone(),
                term_active.clone(),
                lhs.clone(),
            );
            constrain_unused(
                &mut eval,
                meta.active.clone(),
                term_active.clone(),
                rhs.clone(),
            );
            consume_scalar_limb_dynamic(
                &mut eval,
                &self.relations.scalar_limb,
                meta.active.clone() * term_active.clone(),
                self.mul_id,
                ROLE_A,
                meta.lhs_index[term_index].clone(),
                lhs.clone(),
            );
            consume_scalar_limb_dynamic(
                &mut eval,
                &self.relations.scalar_limb,
                meta.active.clone() * term_active,
                self.mul_id,
                ROLE_B,
                meta.rhs_index[term_index].clone(),
                rhs.clone(),
            );
        }

        finish_product_chunk_dynamic(
            &mut eval,
            &self.relations,
            meta.active,
            self.mul_id,
            SIDE_AB,
            meta.coeff,
            meta.chunk,
            meta.digit_active,
            product_sum,
            digits,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct QnProductChunkEval {
    pub log_size: u32,
    pub mul_id: u32,
    pub relations: ScalarModMulComponentRelations,
}

impl FrameworkEval for QnProductChunkEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let meta = ProductMetadata::read(&mut eval, ProductFamily::Qn);
        let quotient_limbs: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let digits: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS] =
            core::array::from_fn(|_| eval.next_trace_mask());

        let mut product_sum = E::F::from(M31::from_u32_unchecked(0));
        for (term_index, quotient_limb) in quotient_limbs.iter().enumerate() {
            let term_active = meta.term_active[term_index].clone();
            let n_limb = eval.get_preprocessed_column(
                ScalarModMulScheduleColumnIds::qn_modulus_limb(term_index),
            );
            product_sum += term_active.clone() * quotient_limb.clone() * n_limb;
            constrain_unused(
                &mut eval,
                meta.active.clone(),
                term_active.clone(),
                quotient_limb.clone(),
            );
            consume_scalar_limb_dynamic(
                &mut eval,
                &self.relations.scalar_limb,
                meta.active.clone() * term_active,
                self.mul_id,
                ROLE_QUOTIENT,
                meta.lhs_index[term_index].clone(),
                quotient_limb.clone(),
            );
        }

        finish_product_chunk_dynamic(
            &mut eval,
            &self.relations,
            meta.active,
            self.mul_id,
            SIDE_QN,
            meta.coeff,
            meta.chunk,
            meta.digit_active,
            product_sum,
            digits,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct ProductDigitAccumulatorEval {
    pub log_size: u32,
    pub mul_id: u32,
    pub relations: ScalarModMulComponentRelations,
}

impl FrameworkEval for ProductDigitAccumulatorEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::accumulator_active());
        let side = eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::accumulator_side());
        let digit =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::accumulator_digit());
        let terms: [E::F; PRODUCT_DIGIT_ACCUMULATOR_TERMS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let product_digit = eval.next_trace_mask();

        let mut acc = E::F::from(M31::from_u32_unchecked(0));
        for (term_index, term) in terms.iter().enumerate() {
            let term_active = eval.get_preprocessed_column(
                ScalarModMulScheduleColumnIds::accumulator_term_active(term_index),
            );
            let coeff = eval.get_preprocessed_column(
                ScalarModMulScheduleColumnIds::accumulator_coeff(term_index),
            );
            let chunk = eval.get_preprocessed_column(
                ScalarModMulScheduleColumnIds::accumulator_chunk(term_index),
            );
            let offset = eval.get_preprocessed_column(
                ScalarModMulScheduleColumnIds::accumulator_offset(term_index),
            );
            acc += term_active.clone() * term.clone();
            constrain_unused(&mut eval, active.clone(), term_active.clone(), term.clone());
            add_product_chunk_digit_relation_dynamic(
                &mut eval,
                &self.relations.product_chunk_digit,
                E::EF::from(active.clone() * term_active),
                self.mul_id,
                side.clone(),
                coeff,
                chunk,
                offset,
                term.clone(),
            );
        }

        eval.add_constraint(active.clone() * (acc - product_digit.clone()));
        add_product_digit_relation_dynamic(
            &mut eval,
            &self.relations.product_digit,
            -E::EF::from(active),
            self.mul_id,
            side,
            digit,
            product_digit,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

#[derive(Clone)]
pub struct ScalarReductionDigitEval {
    pub log_size: u32,
    pub mul_id: u32,
    pub relations: ScalarModMulComponentRelations,
}

impl FrameworkEval for ScalarReductionDigitEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::reduction_active());
        let digit = eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::reduction_digit());
        let has_result_limb = eval
            .get_preprocessed_column(ScalarModMulScheduleColumnIds::reduction_has_result_limb());
        let has_prev_carry =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::reduction_has_prev_carry());
        let has_next_carry =
            eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::reduction_has_next_carry());

        let ab_digit = eval.next_trace_mask();
        let qn_digit = eval.next_trace_mask();
        let result_limb = eval.next_trace_mask();
        let prev_carry = eval.next_trace_mask();
        let carry = eval.next_trace_mask();

        add_product_digit_relation_dynamic(
            &mut eval,
            &self.relations.product_digit,
            E::EF::from(active.clone()),
            self.mul_id,
            constant(SIDE_AB),
            digit.clone(),
            ab_digit.clone(),
        );
        add_product_digit_relation_dynamic(
            &mut eval,
            &self.relations.product_digit,
            E::EF::from(active.clone()),
            self.mul_id,
            constant(SIDE_QN),
            digit.clone(),
            qn_digit.clone(),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relations.scalar_limb,
            E::EF::from(active.clone() * has_result_limb.clone()),
            &[
                constant(self.mul_id),
                constant(ROLE_RESULT),
                digit.clone(),
                result_limb.clone(),
            ],
        ));
        eval.add_constraint(active.clone() * (one::<E>() - has_result_limb) * result_limb.clone());
        eval.add_constraint(
            active.clone() * (one::<E>() - has_prev_carry.clone()) * prev_carry.clone(),
        );
        add_reduction_carry_relation_dynamic(
            &mut eval,
            &self.relations.reduction_carry,
            E::EF::from(active.clone() * has_prev_carry),
            self.mul_id,
            digit.clone() - one::<E>(),
            prev_carry.clone(),
        );
        add_range_check(
            &mut eval,
            &self.relations.signed_carry,
            active.clone(),
            carry.clone(),
        );

        let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
        eval.add_constraint(
            active.clone()
                * (ab_digit - qn_digit - result_limb + prev_carry - limb_base * carry.clone()),
        );
        eval.add_constraint(active.clone() * (one::<E>() - has_next_carry.clone()) * carry.clone());
        add_reduction_carry_relation_dynamic(
            &mut eval,
            &self.relations.reduction_carry,
            -E::EF::from(active * has_next_carry),
            self.mul_id,
            digit,
            carry,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

struct ProductMetadata<F> {
    active: F,
    coeff: F,
    chunk: F,
    term_active: [F; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    lhs_index: [F; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    rhs_index: [F; SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS],
    digit_active: [F; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
}

impl<F> ProductMetadata<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E, family: ProductFamily) -> Self {
        Self {
            active: eval
                .get_preprocessed_column(ScalarModMulScheduleColumnIds::product_active(family)),
            coeff: eval
                .get_preprocessed_column(ScalarModMulScheduleColumnIds::product_coeff(family)),
            chunk: eval
                .get_preprocessed_column(ScalarModMulScheduleColumnIds::product_chunk(family)),
            term_active: core::array::from_fn(|i| {
                eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::product_term_active(
                    family, i,
                ))
            }),
            lhs_index: core::array::from_fn(|i| {
                eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::product_lhs_index(
                    family, i,
                ))
            }),
            rhs_index: core::array::from_fn(|i| {
                eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::product_rhs_index(
                    family, i,
                ))
            }),
            digit_active: core::array::from_fn(|i| {
                eval.get_preprocessed_column(ScalarModMulScheduleColumnIds::product_digit_active(
                    family, i,
                ))
            }),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn finish_product_chunk_dynamic<E: EvalAtRow>(
    eval: &mut E,
    relations: &ScalarModMulComponentRelations,
    active: E::F,
    mul_id: u32,
    side: u32,
    coeff: E::F,
    chunk: E::F,
    digit_active: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
    product_sum: E::F,
    digits: [E::F; SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS],
) {
    add_range_check(eval, &relations.range13, active.clone(), digits[0].clone());
    add_range_check(eval, &relations.range13, active.clone(), digits[1].clone());
    eval.add_constraint(active.clone() * digits[2].clone() * (digits[2].clone() - one::<E>()));

    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    eval.add_constraint(
        active.clone()
            * (product_sum
                - digits[0].clone()
                - limb_base.clone() * digits[1].clone()
                - limb_base.clone() * limb_base * digits[2].clone()),
    );

    for (offset, digit) in digits.into_iter().enumerate() {
        add_product_chunk_digit_relation_dynamic(
            eval,
            &relations.product_chunk_digit,
            -E::EF::from(active.clone() * digit_active[offset].clone()),
            mul_id,
            constant(side),
            coeff.clone(),
            chunk.clone(),
            constant(offset as u32),
            digit,
        );
    }
}

fn constrain_unused<E: EvalAtRow>(eval: &mut E, active: E::F, term_active: E::F, value: E::F) {
    eval.add_constraint(active * (one::<E>() - term_active) * value);
}

fn consume_scalar_limb_dynamic<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarLimbRelation,
    gate: E::F,
    mul_id: u32,
    role: u32,
    limb_index: E::F,
    limb_value: E::F,
) {
    let values: [E::F; SCALAR_LIMB_RELATION_ARITY] =
        [constant(mul_id), constant(role), limb_index, limb_value];
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), &values));
}

#[allow(clippy::too_many_arguments)]
fn add_product_chunk_digit_relation_dynamic<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductChunkDigitRelation,
    numerator: E::EF,
    mul_id: u32,
    side: E::F,
    coeff: E::F,
    chunk: E::F,
    offset: E::F,
    value: E::F,
) {
    let values = [constant(mul_id), side, coeff, chunk, offset, value];
    eval.add_to_relation(RelationEntry::new(relation, numerator, &values));
}

fn add_product_digit_relation_dynamic<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarProductDigitRelation,
    numerator: E::EF,
    mul_id: u32,
    side: E::F,
    digit: E::F,
    value: E::F,
) {
    let values = [constant(mul_id), side, digit, value];
    eval.add_to_relation(RelationEntry::new(relation, numerator, &values));
}

fn add_reduction_carry_relation_dynamic<E: EvalAtRow>(
    eval: &mut E,
    relation: &ScalarReductionCarryRelation,
    numerator: E::EF,
    mul_id: u32,
    digit: E::F,
    value: E::F,
) {
    let values = [constant(mul_id), digit, value];
    eval.add_to_relation(RelationEntry::new(relation, numerator, &values));
}

fn constant<F: From<M31>>(value: u32) -> F {
    F::from(M31::from_u32_unchecked(value))
}

fn one<E: EvalAtRow>() -> E::F {
    constant(1)
}

#[cfg(test)]
fn p256_order_limb(index: usize) -> M31 {
    let order_limbs = stwo_p256_utils::scalar_arithmetic::words_to_limbs(
        &stwo_p256_utils::scalar_arithmetic::P256_ORDER,
    );
    M31::from_u32_unchecked(order_limbs[index])
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use stwo::core::air::Component;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::TraceLocationAllocator;

    use crate::range_checks::RangeCheckRelation;

    use super::super::columns::padded_log_size;
    use super::super::layout::{
        AB_PRODUCT_CHUNK_TRACE_COLUMNS, CANONICAL_SCALAR_TRACE_COLUMNS,
        PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS, QN_PRODUCT_CHUNK_TRACE_COLUMNS,
        SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS,
    };
    use super::*;

    fn relations() -> ScalarModMulComponentRelations {
        ScalarModMulComponentRelations {
            range13: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            scalar_limb: ScalarLimbRelation::dummy(),
            product_chunk_digit: ScalarProductChunkDigitRelation::dummy(),
            product_digit: ScalarProductDigitRelation::dummy(),
            reduction_carry: ScalarReductionCarryRelation::dummy(),
        }
    }

    #[test]
    fn scalar_mod_mul_components_allocate_expected_base_widths() {
        let mut allocator = TraceLocationAllocator::default();
        let rel = relations();

        let canonical = CanonicalScalarComponent::new(
            &mut allocator,
            CanonicalScalarEval {
                log_size: padded_log_size(4),
                mul_id: 0,
                relations: rel.clone(),
            },
            SecureField::zero(),
        );
        let ab = AbProductChunkComponent::new(
            &mut allocator,
            AbProductChunkEval {
                log_size: 8,
                mul_id: 0,
                relations: rel.clone(),
            },
            SecureField::zero(),
        );
        let qn = QnProductChunkComponent::new(
            &mut allocator,
            QnProductChunkEval {
                log_size: 8,
                mul_id: 0,
                relations: rel.clone(),
            },
            SecureField::zero(),
        );
        let accumulator = ProductDigitAccumulatorComponent::new(
            &mut allocator,
            ProductDigitAccumulatorEval {
                log_size: 7,
                mul_id: 0,
                relations: rel.clone(),
            },
            SecureField::zero(),
        );
        let reduction = ScalarReductionDigitComponent::new(
            &mut allocator,
            ScalarReductionDigitEval {
                log_size: 6,
                mul_id: 0,
                relations: rel,
            },
            SecureField::zero(),
        );

        assert_eq!(
            canonical.trace_log_degree_bounds()[1].len(),
            CANONICAL_SCALAR_TRACE_COLUMNS
        );
        assert_eq!(
            ab.trace_log_degree_bounds()[1].len(),
            AB_PRODUCT_CHUNK_TRACE_COLUMNS
        );
        assert_eq!(
            qn.trace_log_degree_bounds()[1].len(),
            QN_PRODUCT_CHUNK_TRACE_COLUMNS
        );
        assert_eq!(
            accumulator.trace_log_degree_bounds()[1].len(),
            PRODUCT_DIGIT_ACCUMULATOR_TRACE_COLUMNS
        );
        assert_eq!(
            reduction.trace_log_degree_bounds()[1].len(),
            SCALAR_REDUCTION_DIGIT_TRACE_COLUMNS
        );
    }

    #[test]
    fn scalar_mod_mul_components_request_fixed_schedule_columns() {
        let mut allocator = TraceLocationAllocator::default();
        let rel = relations();
        let _ = CanonicalScalarComponent::new(
            &mut allocator,
            CanonicalScalarEval {
                log_size: padded_log_size(4),
                mul_id: 0,
                relations: rel.clone(),
            },
            SecureField::zero(),
        );
        let _ = AbProductChunkComponent::new(
            &mut allocator,
            AbProductChunkEval {
                log_size: 8,
                mul_id: 0,
                relations: rel,
            },
            SecureField::zero(),
        );

        assert!(allocator
            .preprocessed_columns()
            .contains(&ScalarModMulScheduleColumnIds::canonical_role()));
        assert!(allocator.preprocessed_columns().contains(
            &ScalarModMulScheduleColumnIds::product_coeff(ProductFamily::Ab)
        ));
    }

    #[test]
    fn p256_order_limb_matches_fixed_qn_metadata_source() {
        let order_limbs = stwo_p256_utils::scalar_arithmetic::words_to_limbs(
            &stwo_p256_utils::scalar_arithmetic::P256_ORDER,
        );
        assert_eq!(p256_order_limb(0), M31::from_u32_unchecked(order_limbs[0]));
    }

    #[test]
    fn scalar_mod_mul_components_reserve_degree_for_paired_logup() {
        let rel = relations();

        assert_eq!(
            CanonicalScalarEval {
                log_size: padded_log_size(4),
                mul_id: 0,
                relations: rel.clone(),
            }
            .max_constraint_log_degree_bound(),
            padded_log_size(4) + 2
        );
        assert_eq!(
            ProductDigitAccumulatorEval {
                log_size: 7,
                mul_id: 0,
                relations: rel.clone(),
            }
            .max_constraint_log_degree_bound(),
            9
        );
        assert_eq!(
            ScalarReductionDigitEval {
                log_size: 6,
                mul_id: 0,
                relations: rel,
            }
            .max_constraint_log_degree_bound(),
            8
        );
    }
}
