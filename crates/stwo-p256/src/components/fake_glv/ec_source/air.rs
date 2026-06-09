use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{
            m31::{PackedM31, LOG_N_LANES},
            qm31::PackedQM31,
            SimdBackend,
        }, ComponentProver,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

use crate::projective::{ProjectiveEcOp, ProjectiveEcTraceClaim};
use crate::projective_air::{
    projective_rcb_op_mul_limbs, ConsumedMulLimbs, ProjectiveRcbMulComponentRelations,
    ProjectiveRcbMulResultRelation, CONSUMED_MUL_LIMBS_COLUMNS, PROJECTIVE_RCB_MUL_ROLE_LHS,
    PROJECTIVE_RCB_MUL_ROLE_RESULT, PROJECTIVE_RCB_MUL_ROLE_RHS, PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS,
};
use crate::projective_air::{projective_rcb_signed_carry_log_size, PROJECTIVE_RCB_SIGNED_CARRY_EQUATION};
use crate::range_checks::{
    RangeCheckClaim, RangeCheckComponent, RangeCheckEval, RangeCheckInteractionClaim,
    RangeCheckRelation, SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
};
use super::double_formula::{
    bind_double_formula, DoubleFormulaColumns, DOUBLE_FORMULA_COLUMNS, DOUBLE_TOTAL_REDUCTIONS,
};

/// Signed-carry preprocessed-column namespace for the fake-GLV projective-source
/// Double-formula reductions. Reuses the projective-RCB equation so the shared
/// value/active preprocessed columns (same bound) are deduplicated; the consumer
/// draws its OWN signed-carry relation instance, giving an independent balance.
const FAKE_GLV_PROJECTIVE_SIGNED_CARRY_EQUATION: &str = PROJECTIVE_RCB_SIGNED_CARRY_EQUATION;
use stwo_p256_utils::constants::N_LIMBS;
use crate::scalar::fake_glv_chain::{
    FakeGlvChainError, FakeGlvPrimitiveEcOp, FakeGlvPrimitiveEcRow, FakeGlvPrimitiveEcTraceClaim,
};
use crate::scalar::prepared_table::{
    prepared_table_ec_point_values, PreparedTableEcEvalPoint, PREPARED_TABLE_EC_OP_DOUBLE,
    PREPARED_TABLE_EC_OP_MIXED_ADD, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

relation!(
    FakeGlvPrimitiveEcRowRelation,
    FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY
);

pub type FakeGlvPrimitiveEcRowProviderComponent =
    FrameworkComponent<FakeGlvPrimitiveEcRowProviderEval>;
pub type FakeGlvProjectiveSourceComponent = FrameworkComponent<FakeGlvProjectiveSourceEval>;

pub const FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY: usize = 4 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;
/// Provider base-trace width: `active` + the EC-row relation columns. The
/// provider (`FakeGlvPrimitiveEcRowProviderEval`) does NOT carry consumed-mul
/// columns.
pub const FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY;
/// Consumer base-trace width: the provider columns PLUS the C5 consumed-mul
/// block (`has_muls` flag + the mul-limb columns) PLUS the C5-2 Double-formula
/// block (`x3,y3,z3` working values + per-reduction quotient/carry witnesses),
/// each appended LAST so the existing relation-value column offsets are
/// unchanged.
pub const FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS: usize =
    FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS + CONSUMED_MUL_LIMBS_COLUMNS + DOUBLE_FORMULA_COLUMNS;
/// Column index where the C5-2 Double-formula block begins (after the
/// consumed-mul block). The first `N_LIMBS` columns are the `x3` working value
/// (then `y3`, `z3`, then the reduction witnesses).
pub const FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET: usize =
    FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS + CONSUMED_MUL_LIMBS_COLUMNS;
/// Column index of the consumed-mul block's `has_muls` flag (the limb columns
/// follow at `+ 1`).
const FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL: usize = FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS;
/// Column index where the consumed-mul LIMB block begins (after `has_muls`).
const FAKE_GLV_PRIMITIVE_EC_MUL_LIMB_OFFSET: usize = FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL + 1;

const FAKE_GLV_PRIMITIVE_EC_ROW_INDEX_COLUMN: &str = "p256_fake_glv_primitive_ec_row_index";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvProjectiveSourceProofClaim {
    pub log_size: u32,
    pub source_offset: u32,
}

impl FakeGlvProjectiveSourceProofClaim {
    pub fn from_fake_glv_trace(trace: &FakeGlvPrimitiveEcTraceClaim, source_offset: usize) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
            source_offset: source_offset as u32,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.source_offset as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.source_offset,
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &RangeCheckRelation::dummy(),
            &RangeCheckRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.source_offset,
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &RangeCheckRelation::dummy(),
            &RangeCheckRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.source_offset,
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &RangeCheckRelation::dummy(),
            &RangeCheckRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Debug)]
pub struct FakeGlvProjectiveSourceInteractionClaim {
    pub provider_claimed_sum: SecureField,
    /// `FakeGlvPrimitiveEcRowRelation` consumer sum (the EC-row self-loop).
    pub consumer_claimed_sum: SecureField,
    /// C5 plumbing: `ProjectiveRcbMulResultRelation` consumer sum (the silo mul
    /// limbs consumed on the consumer component). Lives in the SAME trace/column
    /// group as `consumer_claimed_sum`, but is balanced separately under
    /// `ProjectiveRcbMulResult`.
    pub mul_result_consumer_claimed_sum: SecureField,
    /// C5-2: Range13 USE sum on the consumer component (Double-formula coord +
    /// working-value limb checks). Shares the consumer's single `finalize_logup`;
    /// netted against `range13` (the provider) in the `FakeGlvProjectiveRange13`
    /// balance.
    pub range13_consumer_claimed_sum: SecureField,
    /// C5-2: signed-carry USE sum on the consumer component (Double-formula
    /// reduction carries). Netted against `signed_carry` (the provider).
    pub signed_carry_consumer_claimed_sum: SecureField,
    /// C5-2: the self-contained Range13 PROVIDER (yield) sum.
    pub range13: RangeCheckInteractionClaim,
    /// C5-2: the self-contained signed-carry PROVIDER (yield) sum.
    pub signed_carry: RangeCheckInteractionClaim,
}

impl FakeGlvProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider_claimed_sum: secure_zero(),
            consumer_claimed_sum: secure_zero(),
            mul_result_consumer_claimed_sum: secure_zero(),
            range13_consumer_claimed_sum: secure_zero(),
            signed_carry_consumer_claimed_sum: secure_zero(),
            range13: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
            signed_carry: RangeCheckInteractionClaim {
                claimed_sum: secure_zero(),
            },
        }
    }

    /// `FakeGlvProjectiveSource` balance term: provider yield + EC-row consume.
    /// EXCLUDES the mul-result consume (balanced under `ProjectiveRcbMulResult`)
    /// and the range13/signed-carry consume+provide (balanced under their own
    /// `FakeGlvProjective{Range13,SignedCarry}` relations).
    pub fn total(&self) -> SecureField {
        self.provider_claimed_sum + self.consumer_claimed_sum
    }

    /// `FakeGlvProjectiveRange13` balance: consumer Range13 uses + the provider
    /// yield. Internal to this sub-graph, nets to zero.
    pub fn range13_total(&self) -> SecureField {
        self.range13_consumer_claimed_sum + self.range13.claimed_sum
    }

    /// `FakeGlvProjectiveSignedCarry` balance: consumer signed-carry uses + the
    /// provider yield. Internal to this sub-graph, nets to zero.
    pub fn signed_carry_total(&self) -> SecureField {
        self.signed_carry_consumer_claimed_sum + self.signed_carry.claimed_sum
    }

    /// The single claimed sum the consumer FrameworkComponent declares: the
    /// EC-row + mul-result + range13 + signed-carry consumes all share one
    /// interaction trace (one `finalize_logup`), so the component's sum is their
    /// combination.
    pub fn consumer_component_claimed_sum(&self) -> SecureField {
        self.consumer_claimed_sum
            + self.mul_result_consumer_claimed_sum
            + self.range13_consumer_claimed_sum
            + self.signed_carry_consumer_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.provider_claimed_sum,
            self.consumer_claimed_sum,
            self.mul_result_consumer_claimed_sum,
            self.range13_consumer_claimed_sum,
            self.signed_carry_consumer_claimed_sum,
            self.range13.claimed_sum,
            self.signed_carry.claimed_sum,
        ]);
    }
}

pub struct FakeGlvProjectiveSourceComponents {
    pub provider: FakeGlvPrimitiveEcRowProviderComponent,
    pub consumer: FakeGlvProjectiveSourceComponent,
    /// C5-2: self-contained Range13 provider for the Double-formula coordinate
    /// limb range checks (mirrors `public_key_curve`).
    pub range13: RangeCheckComponent,
    /// C5-2: self-contained signed-carry provider for the Double-formula
    /// reduction carries.
    pub signed_carry: SignedCarryRangeComponent,
}

impl FakeGlvProjectiveSourceComponents {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        source_offset: u32,
        interaction_claim: &FakeGlvProjectiveSourceInteractionClaim,
        relation: &FakeGlvPrimitiveEcRowRelation,
        mul_relations: &ProjectiveRcbMulComponentRelations,
        range13: &RangeCheckRelation,
        signed_carry: &RangeCheckRelation,
    ) -> Self {
        Self {
            provider: FakeGlvPrimitiveEcRowProviderComponent::new(
                allocator,
                FakeGlvPrimitiveEcRowProviderEval {
                    log_size,
                    source_offset,
                    relation: relation.clone(),
                },
                interaction_claim.provider_claimed_sum,
            ),
            consumer: FakeGlvProjectiveSourceComponent::new(
                allocator,
                FakeGlvProjectiveSourceEval {
                    log_size,
                    relation: relation.clone(),
                    mul_relations: mul_relations.clone(),
                    range13: range13.clone(),
                    signed_carry: signed_carry.clone(),
                },
                // EC-row + mul-result consumes share one interaction trace.
                interaction_claim.consumer_component_claimed_sum(),
            ),
            range13: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(range13.clone(), RANGE13_BITS),
                interaction_claim.range13.claimed_sum,
            ),
            signed_carry: SignedCarryRangeComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    signed_carry.clone(),
                    projective_rcb_signed_carry_log_size(),
                    FAKE_GLV_PROJECTIVE_SIGNED_CARRY_EQUATION,
                ),
                interaction_claim.signed_carry.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.provider as &dyn Component,
            &self.consumer as &dyn Component,
            &self.range13 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.provider as &dyn ComponentProver<SimdBackend>,
            &self.consumer as &dyn ComponentProver<SimdBackend>,
            &self.range13 as &dyn ComponentProver<SimdBackend>,
            &self.signed_carry as &dyn ComponentProver<SimdBackend>,
        ]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            self.components()
                .into_iter()
                .map(|component| component.trace_log_degree_bounds()),
        )
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
}

#[derive(Clone)]
pub struct FakeGlvPrimitiveEcRowProviderEval {
    pub log_size: u32,
    pub source_offset: u32,
    pub relation: FakeGlvPrimitiveEcRowRelation,
}

impl FrameworkEval for FakeGlvPrimitiveEcRowProviderEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let row_index = eval.get_preprocessed_column(fake_glv_primitive_ec_row_index_column_id());
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let op = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));
        let source_offset = E::F::from(M31::from_u32_unchecked(self.source_offset));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(active.clone() * (source_index.clone() - row_index - source_offset));
        eval.add_constraint(op.clone() * (op.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = fake_glv_primitive_ec_row_relation_values(
            &[source_index, sig_id, cert_id, op],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(active),
            &relation_values,
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct FakeGlvProjectiveSourceEval {
    pub log_size: u32,
    pub relation: FakeGlvPrimitiveEcRowRelation,
    /// C5 plumbing: relations bundle carrying `mul_result`, the relation the
    /// silo provides its proven mul limbs on and this source consumes.
    pub mul_relations: ProjectiveRcbMulComponentRelations,
    /// C5-2 (Double formula): consumer-local Range13 relation. The consumer
    /// PROVIDES this table itself (a self-contained provider, like
    /// `public_key_curve`); the affine coords + working-value limbs of the
    /// Double formula are range-checked (used) against it.
    pub range13: RangeCheckRelation,
    /// C5-2 (Double formula): consumer-local signed-carry relation for the
    /// reduction carries. Also self-provided. Bound covers the Double formula's
    /// reduction carries (worst ~30, well within `PROJECTIVE_RCB_SIGNED_CARRY_BOUND`).
    pub signed_carry: RangeCheckRelation,
}

impl FrameworkEval for FakeGlvProjectiveSourceEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let op = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        // C5 plumbing: the consumed silo mul limbs. The LogUp consume pins them
        // equal to the silo's proven values; C5-2 (below) binds their operands
        // and the output to the Double-op coordinate formula.
        let consumed_muls = ConsumedMulLimbs::<E>::read(&mut eval);
        // C5-2: the Double-formula working values + reduction witnesses, read
        // LAST (matching the base-trace layout appended after the consumed-mul
        // block).
        let double_columns = DoubleFormulaColumns::<E>::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(op.clone() * (op.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        // C5 plumbing: `has_muls` gate. The silo emits
        // `PROJECTIVE_RCB_MAX_MUL_ROWS_PER_OP` muls for Double (op == 1) and
        // finite-operand MixedAdd (op == 0), but ZERO for an infinity-operand
        // MixedAdd. So expected = 1 - (1 - op)·operand_inf (operand = `rhs`).
        // Constrain the committed flag to this and gate the consumes by it so a
        // 0-mul op consumes nothing (matches the silo).
        let expected_has_muls =
            one.clone() - (one.clone() - op.clone()) * rhs.inf();
        consumed_muls.constrain_has_muls(&mut eval, &active, &expected_has_muls);

        let relation_values = fake_glv_primitive_ec_row_relation_values(
            &[source_index.clone(), sig_id, cert_id, op.clone()],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(active.clone()),
            &relation_values,
        ));
        // CONSUME (use, `+has_muls`) the silo's proven mul limbs for this op,
        // keyed `(source_index, mul_index, role, limb_index, limb)`.
        consumed_muls.consume(&mut eval, &self.mul_relations.mul_result, &source_index);

        // C5-2: constrain the Double-op coordinate formula. `double_active`
        // (= active·op) is 1 only on active Double rows (op==1 == DOUBLE);
        // MixedAdd (op==0) and padding (active==0) are unaffected.
        let double_active = active.clone() * op.clone();
        let muls_view = consumed_muls.view();
        bind_double_formula(
            &mut eval,
            &double_active,
            &active,
            &lhs.x_bigint(),
            &lhs.y_bigint(),
            &output.x_bigint(),
            &output.y_bigint(),
            &output.inf(),
            &muls_view,
            &double_columns,
            &self.range13,
        );
        // Range-check (use) the reduction carries against the consumer-local
        // signed-carry table, and force the Double-formula working values +
        // reduction witnesses to zero on non-Double / padding rows so they leak
        // nothing and the lookup counts stay fixed (carries checked `active`).
        for reduction in &double_columns.reductions {
            for carry in &reduction.carries {
                crate::range_checks::add_range_check(
                    &mut eval,
                    &self.signed_carry,
                    active.clone(),
                    carry.clone(),
                );
            }
        }
        let not_double = one.clone() - double_active.clone();
        for value in double_columns
            .x3
            .limbs()
            .iter()
            .chain(double_columns.y3.limbs())
            .chain(double_columns.z3.limbs())
        {
            eval.add_constraint(not_double.clone() * value.clone());
        }
        for reduction in &double_columns.reductions {
            eval.add_constraint(not_double.clone() * reduction.q.clone());
            for carry in &reduction.carries {
                eval.add_constraint(not_double.clone() * carry.clone());
            }
        }
        eval.finalize_logup();
        eval
    }
}

pub(crate) fn gen_fake_glv_primitive_ec_preprocessed_trace(
    log_size: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    // C5-2 preprocessed columns the self-contained Range13 / signed-carry
    // providers declare (shared by id with the silo's, deduplicated globally).
    let range13_value_id = crate::range_checks::range_check_value_column_id(RANGE13_BITS);
    let signed_carry_value_id =
        crate::range_checks::signed_carry_value_column_id(FAKE_GLV_PROJECTIVE_SIGNED_CARRY_EQUATION);
    let signed_carry_active_id = crate::range_checks::signed_carry_active_column_id(
        FAKE_GLV_PROJECTIVE_SIGNED_CARRY_EQUATION,
    );
    let signed_carry_claim = crate::projective_air::projective_rcb_signed_carry_claim();
    ids.iter()
        .map(|id| {
            if id == &fake_glv_primitive_ec_row_index_column_id() {
                Ok(m31_column_eval(
                    log_size,
                    (0..(1usize << log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
            } else if id == &range13_value_id {
                Ok(crate::range_checks::RangeCheckClaim::new(RANGE13_BITS)
                    .gen_preprocessed_column())
            } else if id == &signed_carry_value_id {
                Ok(signed_carry_claim.gen_value_column())
            } else if id == &signed_carry_active_id {
                Ok(signed_carry_claim.gen_active_column())
            } else {
                Err(FakeGlvChainError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

pub(crate) fn gen_fake_glv_primitive_ec_source_base_trace(
    trace: &FakeGlvPrimitiveEcTraceClaim,
    source_offset: usize,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    if trace.rows.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: trace.rows.len(),
            domain: padded_rows,
        });
    }
    let mut rows = trace
        .rows
        .iter()
        .enumerate()
        .map(|(row_index, row)| {
            fake_glv_primitive_ec_source_trace_values(source_offset + row_index, row)
        })
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_fake_glv_projective_source_base_trace(
    fake_glv: &FakeGlvPrimitiveEcTraceClaim,
    projective: &ProjectiveEcTraceClaim,
    source_offset: usize,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    if fake_glv.rows.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: fake_glv.rows.len(),
            domain: padded_rows,
        });
    }
    let end = source_offset + fake_glv.rows.len();
    if projective.rows.len() < end {
        return Err(FakeGlvChainError::ProjectiveSourceTooShort {
            source_offset,
            fake_glv: fake_glv.rows.len(),
            projective: projective.rows.len(),
        });
    }
    let mut rows = projective.rows[source_offset..end]
        .iter()
        .enumerate()
        .map(|(row_index, projective_row)| {
            fake_glv_projective_source_trace_values(source_offset + row_index, projective_row)
        })
        .collect::<Result<Vec<_>, _>>()?;
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_fake_glv_primitive_ec_source_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvPrimitiveEcRowRelation,
    multiplicity: RelationMultiplicity,
) -> (
    ColumnVec<M31ColumnEval>,
    FakeGlvPrimitiveEcRowInteractionClaim,
) {
    assert_eq!(base.len(), FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = fake_glv_primitive_ec_row_packed_relation_values(base, vec_row);
        let active = PackedQM31::from(base[0].data[vec_row]);
        let numerator = match multiplicity {
            RelationMultiplicity::Provider => -active,
            RelationMultiplicity::Consumer => active,
        };
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, FakeGlvPrimitiveEcRowInteractionClaim { claimed_sum })
}

/// Canonical role order for the consumed mul-limb columns, matching
/// `projective_rcb_op_mul_limbs` and `ConsumedMulLimbs`.
const PROJECTIVE_RCB_MUL_RESULT_ROLES: [u32; 3] = [
    PROJECTIVE_RCB_MUL_ROLE_LHS,
    PROJECTIVE_RCB_MUL_ROLE_RHS,
    PROJECTIVE_RCB_MUL_ROLE_RESULT,
];

/// C5 plumbing: interaction trace for the fake-GLV projective-source CONSUMER.
/// Emits, in the exact order `FakeGlvProjectiveSourceEval::evaluate` does under
/// one `finalize_logup`:
///   1. the `FakeGlvPrimitiveEcRowRelation` consume (col 0, `+active`),
///   2. the `ProjectiveRcbMulResultRelation` consume for every committed mul
///      limb (one col per fraction, canonical mul/role/limb order, `+active`).
/// Returns the columns, the EC-row consumer sum, and the mul-result consumer sum
/// (the latter feeds the 3-way `ProjectiveRcbMulResult` balance).
pub(crate) fn gen_fake_glv_projective_source_consumer_interaction_trace(
    base: &[M31ColumnEval],
    ec_row_relation: &FakeGlvPrimitiveEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
    range13_relation: &RangeCheckRelation,
    signed_carry_relation: &RangeCheckRelation,
) -> FakeGlvProjectiveSourceConsumerInteraction {
    assert_eq!(base.len(), FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    // ONE LogupTraceGenerator over all columns so the combined cumulative sum
    // matches the single `finalize_logup` in the consumer AIR (the EC-row
    // consume column followed by one column per consumed mul limb).
    let mut logup = LogupTraceGenerator::new(log_size);

    // Column 0: the existing EC-row consume (+active).
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = fake_glv_primitive_ec_row_packed_relation_values(base, vec_row);
        let active = PackedQM31::from(base[0].data[vec_row]);
        col.write_frac(vec_row, active, ec_row_relation.combine(&values));
    }
    col.finalize_col();

    // Mul-result consume columns (one per fraction, gated by the `has_muls`
    // column so 0-mul ops consume nothing), canonical order (mul_index outer,
    // role `[LHS, RHS, RESULT]`, limb_index), matching `ConsumedMulLimbs`.
    for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
        for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
            for limb_index in 0..N_LIMBS {
                let base_col = FAKE_GLV_PRIMITIVE_EC_MUL_LIMB_OFFSET
                    + mul_index * (3 * N_LIMBS)
                    + role_index * N_LIMBS
                    + limb_index;
                let mut col = logup.new_col();
                for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
                    let source_index = base[1].data[vec_row];
                    let limb = base[base_col].data[vec_row];
                    let has_muls =
                        PackedQM31::from(base[FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL].data[vec_row]);
                    let values = [
                        source_index,
                        PackedM31::broadcast(M31::from_u32_unchecked(mul_index as u32)),
                        PackedM31::broadcast(M31::from_u32_unchecked(role)),
                        PackedM31::broadcast(M31::from_u32_unchecked(limb_index as u32)),
                        limb,
                    ];
                    col.write_frac(vec_row, has_muls, mul_result_relation.combine(&values));
                }
                col.finalize_col();
            }
        }
    }
    // C5-2: Range13 USE columns (one per fraction, `+active`), in the SAME order
    // `bind_double_formula` emits them: lhs.x, lhs.y, output.x, output.y limbs,
    // then x3, y3, z3 working-value limbs.
    for base_col in double_formula_range13_use_columns() {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let active = PackedQM31::from(base[0].data[vec_row]);
            let limb = base[base_col].data[vec_row];
            col.write_frac(vec_row, active, range13_relation.combine(&[limb]));
        }
        col.finalize_col();
    }

    // C5-2: signed-carry USE columns (one per fraction, `+active`), in the SAME
    // order the consumer AIR emits them: reduction slot outer, carry limb inner.
    for carry_col in double_formula_signed_carry_use_columns() {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let active = PackedQM31::from(base[0].data[vec_row]);
            let carry = base[carry_col].data[vec_row];
            col.write_frac(vec_row, active, signed_carry_relation.combine(&[carry]));
        }
        col.finalize_col();
    }

    let (columns, _total) = logup.finalize_last();

    // Sub-sums (unpacked `SecureField`): the EC-row consumer sum, mul-result
    // consumer sum, and the range13/signed-carry consumer-use sums. Computed
    // analytically so the proof's `relation_balances()` can net each relation
    // independently.
    let (ec_row_sum, mul_result_sum) =
        fake_glv_projective_source_consumer_sums(base, ec_row_relation, mul_result_relation);
    let range13_use_sum = sum_use_fractions(
        base,
        range13_relation,
        double_formula_range13_use_columns(),
    );
    let signed_carry_use_sum = sum_use_fractions(
        base,
        signed_carry_relation,
        double_formula_signed_carry_use_columns(),
    );
    FakeGlvProjectiveSourceConsumerInteraction {
        columns,
        ec_row_sum,
        mul_result_sum,
        range13_use_sum,
        signed_carry_use_sum,
    }
}

/// Output of the fake-GLV projective-source consumer interaction-trace
/// generator: the interaction columns and the per-relation analytic use sums.
pub(crate) struct FakeGlvProjectiveSourceConsumerInteraction {
    pub columns: ColumnVec<M31ColumnEval>,
    pub ec_row_sum: SecureField,
    pub mul_result_sum: SecureField,
    pub range13_use_sum: SecureField,
    pub signed_carry_use_sum: SecureField,
}

/// Base-trace column indices the Range13 USES read, in `bind_double_formula`
/// emission order: lhs.x, lhs.y, output.x, output.y limbs, then x3, y3, z3.
fn double_formula_range13_use_columns() -> Vec<usize> {
    let lhs_x = 5; // after [active, source_index, sig_id, cert_id, op]
    let lhs_y = lhs_x + N_LIMBS;
    let output_x = 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let output_y = output_x + N_LIMBS;
    // x3, y3, z3 are the first 3·N_LIMBS columns of the Double-formula block.
    let x3 = FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET;
    let mut cols = Vec::with_capacity(7 * N_LIMBS);
    for start in [lhs_x, lhs_y, output_x, output_y, x3, x3 + N_LIMBS, x3 + 2 * N_LIMBS] {
        for limb in 0..N_LIMBS {
            cols.push(start + limb);
        }
    }
    cols
}

/// Base-trace column indices the signed-carry USES read, in consumer-AIR
/// emission order (reduction slot outer, carry limb inner). The Double-formula
/// block layout is `x3,y3,z3` (3·N_LIMBS) then per reduction `(q, carries)`.
fn double_formula_signed_carry_use_columns() -> Vec<usize> {
    let block = FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET;
    let reductions_start = block + 3 * N_LIMBS;
    let mut cols = Vec::with_capacity(DOUBLE_TOTAL_REDUCTIONS * N_LIMBS);
    for slot in 0..DOUBLE_TOTAL_REDUCTIONS {
        let q_col = reductions_start + slot * (1 + N_LIMBS);
        for limb in 0..N_LIMBS {
            cols.push(q_col + 1 + limb); // skip the quotient column
        }
    }
    cols
}

/// Range13 USE values the consumer base trace contributes (per active row): the
/// `lhs.x, lhs.y, output.x, output.y, x3, y3, z3` limbs the Double formula
/// range-checks. Fed into the self-contained Range13 provider's multiplicity.
pub(crate) fn fake_glv_projective_source_range13_uses_from_base(base: &[M31ColumnEval]) -> Vec<M31> {
    let columns = double_formula_range13_use_columns();
    collect_active_use_values(base, &columns)
}

/// signed-carry USE values (decoded `i64`) the consumer base trace contributes
/// (per active row): every Double-formula reduction carry. Fed into the
/// self-contained signed-carry provider's multiplicity.
pub(crate) fn fake_glv_projective_source_signed_carry_uses_from_base(
    base: &[M31ColumnEval],
) -> Vec<i64> {
    let columns = double_formula_signed_carry_use_columns();
    collect_active_use_values(base, &columns)
        .into_iter()
        .map(crate::range_checks::decode_signed_carry)
        .collect()
}

fn collect_active_use_values(base: &[M31ColumnEval], columns: &[usize]) -> Vec<M31> {
    let log_size = base[0].domain.log_size();
    let mut uses = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active == M31::from_u32_unchecked(0) {
                continue;
            }
            for &col in columns {
                uses.push(base[col].data[vec_row].to_array()[lane]);
            }
        }
    }
    uses
}

/// Analytic `Σ active / relation.combine([base[col]])` over the given USE columns
/// (each gated by `active`, the consumer's column 0).
fn sum_use_fractions(
    base: &[M31ColumnEval],
    relation: &RangeCheckRelation,
    columns: Vec<usize>,
) -> SecureField {
    let log_size = base[0].domain.log_size();
    let mut sum = secure_zero();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active == M31::from_u32_unchecked(0) {
                continue;
            }
            let active_ef = SecureField::from(active);
            for &col in &columns {
                let value = base[col].data[vec_row].to_array()[lane];
                let denom: SecureField = relation.combine(&[value]);
                sum += active_ef / denom;
            }
        }
    }
    sum
}

/// Analytic `(ec_row_consumer_sum, mul_result_consumer_sum)` over the consumer
/// base trace, using unpacked `SecureField` combines. The EC-row sum is gated by
/// `active`; the mul-result sum by the committed `has_muls` flag.
fn fake_glv_projective_source_consumer_sums(
    base: &[M31ColumnEval],
    ec_row_relation: &FakeGlvPrimitiveEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
) -> (SecureField, SecureField) {
    let log_size = base[0].domain.log_size();
    let mut ec_row_sum = secure_zero();
    let mut mul_result_sum = secure_zero();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active != M31::from_u32_unchecked(0) {
                let ec_values: [M31; FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY] =
                    core::array::from_fn(|index| base[index + 1].data[vec_row].to_array()[lane]);
                let denom: SecureField = ec_row_relation.combine(&ec_values);
                ec_row_sum += SecureField::from(active) / denom;
            }

            let has_muls = base[FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL].data[vec_row].to_array()[lane];
            if has_muls == M31::from_u32_unchecked(0) {
                continue;
            }
            let has_muls_ef = SecureField::from(has_muls);
            let source_index = base[1].data[vec_row].to_array()[lane];
            for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
                for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
                    for limb_index in 0..N_LIMBS {
                        let base_col = FAKE_GLV_PRIMITIVE_EC_MUL_LIMB_OFFSET
                            + mul_index * (3 * N_LIMBS)
                            + role_index * N_LIMBS
                            + limb_index;
                        let limb = base[base_col].data[vec_row].to_array()[lane];
                        let denom: SecureField = mul_result_relation.combine(&[
                            source_index,
                            M31::from_u32_unchecked(mul_index as u32),
                            M31::from_u32_unchecked(role),
                            M31::from_u32_unchecked(limb_index as u32),
                            limb,
                        ]);
                        mul_result_sum += has_muls_ef / denom;
                    }
                }
            }
        }
    }
    (ec_row_sum, mul_result_sum)
}

fn fake_glv_primitive_ec_row_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| base[index + 1].data[vec_row])
}

fn fake_glv_primitive_ec_row_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: FAKE_GLV_PRIMITIVE_EC_ROW_INDEX_COLUMN.into(),
    }
}

fn fake_glv_primitive_ec_source_trace_values(
    source_index: usize,
    row: &FakeGlvPrimitiveEcRow,
) -> [M31; FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = row.sig_id;
    column += 1;
    values[column] = row.cert_id;
    column += 1;
    values[column] = fake_glv_primitive_ec_op_code(row.op);
    column += 1;
    for value in prepared_table_ec_point_values(&row.lhs) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.rhs) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.output) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS);
    values
}

fn fake_glv_projective_source_trace_values(
    source_index: usize,
    row: &crate::projective::ProjectiveEcRow,
) -> Result<[M31; FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS], FakeGlvChainError> {
    let mut values =
        [M31::from_u32_unchecked(0); FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = row.sig_id;
    column += 1;
    values[column] = row.cert_id;
    column += 1;
    values[column] = projective_ec_op_code(row.op);
    column += 1;
    for value in prepared_table_ec_point_values(&row.lhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.rhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.output_affine) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL);
    // C5 plumbing: the `has_muls` flag, then the silo's proven mul limbs for this
    // op in canonical order. An infinity-operand MixedAdd is a 0-mul no-op
    // (`has_muls = 0`, all-zero limbs) the consumer must NOT consume, so it
    // matches the silo (which provides nothing for it).
    let (mul_limbs, has_muls) = projective_rcb_op_mul_limbs(source_index, row)
        .map_err(|_| FakeGlvChainError::ProjectiveSourceInvalid)?;
    values[column] = M31::from_u32_unchecked(has_muls as u32);
    column += 1;
    for value in mul_limbs {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET);
    // C5-2: the Double-formula working values + reduction witnesses. Emitted only
    // for Double rows (op == DOUBLE); MixedAdd / padding leave this block zero,
    // matching the `double_active`-gated constraints + off-Double zero gates.
    if row.op == crate::projective::ProjectiveEcOp::Double {
        let witness = super::double_formula::solve_double_formula_witness(
            &mul_limbs,
            &row.output_projective,
        )
        .ok_or(FakeGlvChainError::ProjectiveSourceInvalid)?;
        for value in super::double_formula::double_formula_trace_values(&witness) {
            values[column] = value;
            column += 1;
        }
    } else {
        column += DOUBLE_FORMULA_COLUMNS;
    }
    debug_assert_eq!(column, FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS);
    Ok(values)
}

fn fake_glv_primitive_ec_row_relation_values<F: Clone>(
    header: &[F; 4],
    lhs: &PreparedTableEcEvalPoint<F>,
    rhs: &PreparedTableEcEvalPoint<F>,
    output: &PreparedTableEcEvalPoint<F>,
) -> [F; FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY] {
    let lhs = lhs.relation_values();
    let rhs = rhs.relation_values();
    let output = output.relation_values();
    core::array::from_fn(|index| match index {
        0..=3 => header[index].clone(),
        4..=44 => lhs[index - 4].clone(),
        45..=85 => rhs[index - 45].clone(),
        86..=126 => output[index - 86].clone(),
        _ => unreachable!("fake-GLV primitive EC relation index is in range"),
    })
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

fn fake_glv_primitive_ec_op_code(op: FakeGlvPrimitiveEcOp) -> M31 {
    let code = match op {
        FakeGlvPrimitiveEcOp::Double => PREPARED_TABLE_EC_OP_DOUBLE,
        FakeGlvPrimitiveEcOp::Add => PREPARED_TABLE_EC_OP_MIXED_ADD,
    };
    M31::from_u32_unchecked(code)
}

fn projective_ec_op_code(op: ProjectiveEcOp) -> M31 {
    let code = match op {
        ProjectiveEcOp::Double => PREPARED_TABLE_EC_OP_DOUBLE,
        ProjectiveEcOp::MixedAdd => PREPARED_TABLE_EC_OP_MIXED_ADD,
    };
    M31::from_u32_unchecked(code)
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FakeGlvPrimitiveEcRowInteractionClaim {
    pub claimed_sum: SecureField,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RelationMultiplicity {
    Provider,
    Consumer,
}
