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
use stwo::prover::backend::simd::m31::N_LANES;

use crate::components::gamma_digest::{
    gamma_collect_group_values, gamma_digest_of_values, gamma_digest_tuple,
    gamma_digest_yield_sum, gamma_row_index_of, yield_gamma_digest,
    GammaChallenge, GammaDigestRelation, GammaTallComponent, GammaTallEval,
    GammaTallInstance, GammaTallInteractionClaim, GammaTallLayout,
    GAMMA_TAG_FAKE_GLV_RANGE13, GAMMA_TAG_FAKE_GLV_SIGNED,
};
use crate::range_checks::{
    RangeCheckComponent, RangeCheckEval, RangeCheckInteractionClaim,
    RangeCheckRelation, SignedCarryRangeComponent, SignedCarryRangeEval, RANGE13_BITS,
};
use super::double_formula::{
    bind_double_formula, DoubleFormulaColumns, DOUBLE_FORMULA_COLUMNS, DOUBLE_TOTAL_REDUCTIONS,
};
use super::mixed_add_formula::{
    bind_mixed_add_formula, MixedAddFormulaColumns, MIXED_ADD_FORMULA_COLUMNS,
    MIXED_ADD_TOTAL_REDUCTIONS,
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
/// block (`has_muls` flag + the mul-limb columns) PLUS the C5-2a Double-formula
/// block PLUS the C5-2b MixedAdd-formula block (each `x3,y3,z3` working values +
/// per-reduction quotient/carry witnesses), all appended LAST so the existing
/// relation-value column offsets are unchanged.
pub const FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS: usize =
    FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS
        + CONSUMED_MUL_LIMBS_COLUMNS
        + DOUBLE_FORMULA_COLUMNS
        + MIXED_ADD_FORMULA_COLUMNS;
/// Column index where the C5-2a Double-formula block begins (after the
/// consumed-mul block). The first `N_LIMBS` columns are the `x3` working value
/// (then `y3`, `z3`, then the reduction witnesses).
pub const FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET: usize =
    FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS + CONSUMED_MUL_LIMBS_COLUMNS;
/// Column index where the C5-2b MixedAdd-formula block begins (right after the
/// Double-formula block).
pub const FAKE_GLV_PROJECTIVE_MIXED_ADD_FORMULA_OFFSET: usize =
    FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET + DOUBLE_FORMULA_COLUMNS;
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
    /// Active EC rows (= γ-digest groups; the tall expanders' schedule).
    pub rows: u32,
}

impl FakeGlvProjectiveSourceProofClaim {
    pub fn from_fake_glv_trace(trace: &FakeGlvPrimitiveEcTraceClaim, source_offset: usize) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
            source_offset: source_offset as u32,
            rows: trace.rows.len() as u32,
        }
    }

    /// The two γ-digest tall layouts (range13 kind, signed kind).
    pub fn gamma_layouts(&self) -> [GammaTallLayout; 2] {
        fake_glv_gamma_layouts(self.rows as usize)
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.source_offset as u64);
        channel.mix_u64(self.rows as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.source_offset,
            self.rows,
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &RangeCheckRelation::dummy(),
            &RangeCheckRelation::dummy(),
            &GammaDigestRelation::dummy(),
            &dummy_gamma_challenge(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.source_offset,
            self.rows,
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &RangeCheckRelation::dummy(),
            &RangeCheckRelation::dummy(),
            &GammaDigestRelation::dummy(),
            &dummy_gamma_challenge(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            self.source_offset,
            self.rows,
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &RangeCheckRelation::dummy(),
            &RangeCheckRelation::dummy(),
            &GammaDigestRelation::dummy(),
            &dummy_gamma_challenge(),
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
    /// γ-digest: the consumer's two digest YIELDS (−active, range13 + signed
    /// kinds). Netted against the tall expanders' `digest_use_sum`s under the
    /// `GammaDigest` balance.
    pub gamma_yield_sum: SecureField,
    /// γ-digest: the range13-kind tall expander (digest use + range uses).
    pub gamma_range13: GammaTallInteractionClaim,
    /// γ-digest: the signed-kind tall expander.
    pub gamma_signed: GammaTallInteractionClaim,
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
            gamma_yield_sum: secure_zero(),
            gamma_range13: GammaTallInteractionClaim::zero(),
            gamma_signed: GammaTallInteractionClaim::zero(),
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

    /// `FakeGlvProjectiveRange13` balance: the tall expander's range uses +
    /// the provider yield. Internal to this sub-graph, nets to zero.
    pub fn range13_total(&self) -> SecureField {
        self.gamma_range13.range_use_sum + self.range13.claimed_sum
    }

    /// `FakeGlvProjectiveSignedCarry` balance: the tall expander's range uses
    /// + the provider yield. Internal to this sub-graph, nets to zero.
    pub fn signed_carry_total(&self) -> SecureField {
        self.gamma_signed.range_use_sum + self.signed_carry.claimed_sum
    }

    /// `GammaDigest` balance for this sub-graph: the consumer's two yields +
    /// the two tall expanders' digest uses. Nets to zero.
    pub fn gamma_digest_total(&self) -> SecureField {
        self.gamma_yield_sum
            + self.gamma_range13.digest_use_sum
            + self.gamma_signed.digest_use_sum
    }

    /// The single claimed sum the consumer FrameworkComponent declares: the
    /// EC-row + mul-result consumes and the two γ-digest yields share one
    /// interaction trace (one `finalize_logup`), so the component's sum is
    /// their combination.
    pub fn consumer_component_claimed_sum(&self) -> SecureField {
        self.consumer_claimed_sum + self.mul_result_consumer_claimed_sum + self.gamma_yield_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.provider_claimed_sum,
            self.consumer_claimed_sum,
            self.mul_result_consumer_claimed_sum,
            self.gamma_yield_sum,
            self.range13.claimed_sum,
            self.signed_carry.claimed_sum,
        ]);
        self.gamma_range13.mix_into(channel);
        self.gamma_signed.mix_into(channel);
    }
}

pub struct FakeGlvProjectiveSourceComponents {
    pub provider: FakeGlvPrimitiveEcRowProviderComponent,
    pub consumer: FakeGlvProjectiveSourceComponent,
    /// γ-digest tall expanders (range13 kind, signed kind): re-expand the
    /// consumer's digested formula values and emit the actual range uses.
    pub gamma_range13: GammaTallComponent,
    pub gamma_signed: GammaTallComponent,
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
        rows: u32,
        interaction_claim: &FakeGlvProjectiveSourceInteractionClaim,
        relation: &FakeGlvPrimitiveEcRowRelation,
        mul_relations: &ProjectiveRcbMulComponentRelations,
        range13: &RangeCheckRelation,
        signed_carry: &RangeCheckRelation,
        gamma_digest: &GammaDigestRelation,
        gamma_challenge: &GammaChallenge,
    ) -> Self {
        let [gamma_range13_layout, gamma_signed_layout] = fake_glv_gamma_layouts(rows as usize);
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
                    gamma_digest: gamma_digest.clone(),
                    gamma_challenge: gamma_challenge.clone(),
                },
                // EC-row + mul-result consumes share one interaction trace.
                interaction_claim.consumer_component_claimed_sum(),
            ),
            gamma_range13: GammaTallComponent::new(
                allocator,
                GammaTallEval {
                    layout: gamma_range13_layout,
                    challenge: gamma_challenge.clone(),
                    digest: gamma_digest.clone(),
                    range: range13.clone(),
                },
                interaction_claim.gamma_range13.claimed_sum,
            ),
            gamma_signed: GammaTallComponent::new(
                allocator,
                GammaTallEval {
                    layout: gamma_signed_layout,
                    challenge: gamma_challenge.clone(),
                    digest: gamma_digest.clone(),
                    range: signed_carry.clone(),
                },
                interaction_claim.gamma_signed.claimed_sum,
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
            &self.gamma_range13 as &dyn Component,
            &self.gamma_signed as &dyn Component,
            &self.range13 as &dyn Component,
            &self.signed_carry as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.provider as &dyn ComponentProver<SimdBackend>,
            &self.consumer as &dyn ComponentProver<SimdBackend>,
            &self.gamma_range13 as &dyn ComponentProver<SimdBackend>,
            &self.gamma_signed as &dyn ComponentProver<SimdBackend>,
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
    /// γ-digest reshape (docs/gamma-digest-design.md): the formula blocks'
    /// range13 + signed-carry values are bound into two per-row digests
    /// yielded on this relation; the tall expander components re-expand them
    /// and emit the actual range uses against the consumer-local providers.
    pub gamma_digest: GammaDigestRelation,
    pub gamma_challenge: GammaChallenge,
}

impl FrameworkEval for FakeGlvProjectiveSourceEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // +2 supports the batched logup columns (batch 4 ⟹ constraint degree
        // ≤ 5 = 2^2 + 1). The per-component bound is capped by the committed
        // LDE size (log_size + log_blowup = +2), so batch 4 is the ceiling at
        // the current 4x blowup.
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
        let mut consumed_muls = ConsumedMulLimbs::<E>::read(&mut eval);
        // C5-2a: the Double-formula working values + reduction witnesses, read
        // after the consumed-mul block.
        let double_columns = DoubleFormulaColumns::<E>::read(&mut eval);
        // C5-2b: the MixedAdd-formula working values + reduction witnesses, read
        // LAST (matching the base-trace layout appended after the Double block).
        let mixed_columns = MixedAddFormulaColumns::<E>::read(&mut eval);
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
        // Operand dedup: install the dropped slots' consume expressions.
        consumed_muls.fill_dropped(&crate::projective_air::ConsumedMulWiring {
            op: op.clone(),
            x1: lhs.x_bigint(),
            y1: lhs.y_bigint(),
            x2: rhs.x_bigint(),
            y2: rhs.y_bigint(),
            output_x: output.x_bigint(),
            output_y: output.y_bigint(),
            z3_double: double_columns.z3.clone(),
            z3_mixed: mixed_columns.z3.clone(),
        });

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
        // MixedAdd (op==0) and padding (active==0) are unaffected. The
        // formulas' range13/signed-carry values are collected into the two
        // γ-digest sinks (fixed order: Double block then MixedAdd block).
        let mut range13_values: Vec<E::F> = Vec::new();
        let mut signed_carry_values: Vec<E::F> = Vec::new();
        let double_active = active.clone() * op.clone();
        let muls_view = consumed_muls.view();
        bind_double_formula(
            &mut eval,
            &double_active,
            &lhs.x_bigint(),
            &lhs.y_bigint(),
            &output.x_bigint(),
            &output.y_bigint(),
            &output.inf(),
            &muls_view,
            &double_columns,
            &mut range13_values,
        );
        // Collect the reduction carries for the signed-carry digest, and force
        // the Double-formula working values + reduction witnesses to zero on
        // non-Double / padding rows so they leak nothing and the digested
        // value lists stay fixed.
        for reduction in &double_columns.reductions {
            for carry in &reduction.carries {
                signed_carry_values.push(carry.clone());
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

        // C5-2b: constrain the MixedAdd-op coordinate formula. `mixed_active`
        // (= active·(1−op)) is 1 only on active MixedAdd rows (op==0 ==
        // MixedAdd); Double (op==1) and padding (active==0) are unaffected. The
        // formula itself is additionally gated by `has_muls` inside the binder
        // (an infinity-operand MixedAdd is a 0-mul no-op constrained `output =
        // lhs`).
        let mixed_active = active.clone() * (one.clone() - op.clone());
        bind_mixed_add_formula(
            &mut eval,
            &mixed_active,
            &rhs.inf(),
            &lhs.x_bigint(),
            &lhs.y_bigint(),
            &rhs.x_bigint(),
            &rhs.y_bigint(),
            &lhs.inf(),
            &output.x_bigint(),
            &output.y_bigint(),
            &output.inf(),
            &muls_view,
            &mixed_columns,
            &mut range13_values,
        );
        // Collect the MixedAdd reduction carries for the signed-carry digest,
        // and force the MixedAdd working values + reduction witnesses to zero
        // on non-MixedAdd / padding rows.
        for reduction in &mixed_columns.reductions {
            for carry in &reduction.carries {
                signed_carry_values.push(carry.clone());
            }
        }
        let not_mixed = one.clone() - mixed_active.clone();
        for value in mixed_columns
            .x3
            .limbs()
            .iter()
            .chain(mixed_columns.y3.limbs())
            .chain(mixed_columns.z3.limbs())
        {
            eval.add_constraint(not_mixed.clone() * value.clone());
        }
        for reduction in &mixed_columns.reductions {
            eval.add_constraint(not_mixed.clone() * reduction.q.clone());
            for carry in &reduction.carries {
                eval.add_constraint(not_mixed.clone() * carry.clone());
            }
        }
        // γ-digest yields (one per kind): bind the collected value lists to
        // the tall expanders' digests. `row_index` is the shared preprocessed
        // index column; presence = `active` (any deviation from the talls'
        // preprocessed schedule unbalances the GammaDigest relation).
        let row_index = eval.get_preprocessed_column(fake_glv_primitive_ec_row_index_column_id());
        yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            GAMMA_TAG_FAKE_GLV_RANGE13,
            row_index.clone(),
            active.clone(),
            M31::from_u32_unchecked(0),
            &range13_values,
        );
        yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            GAMMA_TAG_FAKE_GLV_SIGNED,
            row_index,
            active.clone(),
            crate::range_checks::encode_signed_carry(0),
            &signed_carry_values,
        );

        eval.finalize_logup_batched(&fake_glv_consumer_logup_batching());
        eval
    }
}

pub(crate) fn gen_fake_glv_primitive_ec_preprocessed_trace(
    log_size: u32,
    rows: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let gamma_layouts = fake_glv_gamma_layouts(rows as usize);
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
            } else if let Some(column) = gamma_layouts.iter().find_map(|layout| {
                crate::components::gamma_digest::gamma_tall_preprocessed_column(layout, id)
            }) {
                Ok(column)
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

/// LogUp batch size for the projective-source consumer: 2 fractions per
/// interaction column (the `finalize_logup_in_pairs` layout, expressed via
/// `consecutive_batching`). Degree ≤ 3 at the `log_size + 1` bound. Larger
/// batches need a bound past +1, which empirically fails OODS in this stwo.
pub(crate) const FAKE_GLV_CONSUMER_LOGUP_BATCH: usize = 2;

/// Total LogUp entries the consumer eval emits (EC-row consume + wide mul
/// consumes + the two γ-digest yields), in emission order.
pub(crate) fn fake_glv_consumer_logup_entries() -> usize {
    1 + (PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) * 3 + 2
}

/// Consumer logup batching: pairs, except the operand-dedup slots whose
/// consume values are degree-2 op-mixes — those entries sit in solo batches
/// (denominator degree 2 + cumulative term = 3, the `log_size + 1` ceiling).
pub(crate) fn fake_glv_consumer_logup_batching() -> Vec<usize> {
    let solo: Vec<usize> = (0..PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS))
        .flat_map(|mul| (0..3usize).map(move |role| (mul, role)))
        .filter(|&(mul, role)| crate::projective_air::consumed_mul_slot_degree2(mul, role))
        .map(|(mul, role)| 1 + mul * 3 + role)
        .collect();
    crate::range_checks::batching_with_solo(
        fake_glv_consumer_logup_entries(),
        FAKE_GLV_CONSUMER_LOGUP_BATCH,
        &solo,
    )
}

/// Gen-side layout for [`consumed_mul_slot_packed_limbs`] over the fake-GLV
/// consumer base trace.
fn fake_glv_consumed_mul_gen_layout() -> crate::projective_air::ConsumedMulGenLayout {
    crate::projective_air::ConsumedMulGenLayout {
        op_col: 4,
        x1_col: 5,
        y1_col: 5 + N_LIMBS,
        x2_col: 5 + PREPARED_TABLE_EC_POINT_COLUMNS,
        y2_col: 5 + PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
        output_x_col: 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS,
        output_y_col: 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
        z3_double_col: FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET + 2 * N_LIMBS,
        z3_mixed_col: FAKE_GLV_PROJECTIVE_MIXED_ADD_FORMULA_OFFSET + 2 * N_LIMBS,
        mul_limb_offset: FAKE_GLV_PRIMITIVE_EC_MUL_LIMB_OFFSET,
    }
}

/// Range13 digest value order: the Double-formula list then the MixedAdd list
/// (matching the two binder collection passes in the eval).
pub(crate) fn fake_glv_gamma_range13_columns() -> Vec<usize> {
    let mut columns = double_formula_range13_use_columns();
    columns.extend(mixed_add_formula_range13_use_columns());
    columns
}

/// Signed-carry digest value order: Double reduction carries then MixedAdd
/// reduction carries.
pub(crate) fn fake_glv_gamma_signed_carry_columns() -> Vec<usize> {
    let mut columns = double_formula_signed_carry_use_columns();
    columns.extend(mixed_add_formula_signed_carry_use_columns());
    columns
}

/// Largest lane-padded digest value-list length across this component's two
/// kinds — the γ-power table must cover it.
pub fn fake_glv_gamma_max_padded_values() -> usize {
    crate::components::gamma_digest::gamma_padded_values(fake_glv_gamma_range13_columns().len())
        .max(crate::components::gamma_digest::gamma_padded_values(
            fake_glv_gamma_signed_carry_columns().len(),
        ))
}

/// Dummy γ challenge for preprocessed-id / degree-bound queries (the powers
/// table is sized to the larger of the two value lists).
pub(crate) fn dummy_gamma_challenge() -> GammaChallenge {
    GammaChallenge::from_gamma(
        SecureField::from(M31::from_u32_unchecked(2)),
        fake_glv_gamma_max_padded_values(),
    )
}

/// The two γ-digest tall layouts for `rows` scheduled EC rows.
pub fn fake_glv_gamma_layouts(rows: usize) -> [GammaTallLayout; 2] {
    [
        GammaTallLayout {
            tag: GAMMA_TAG_FAKE_GLV_RANGE13,
            group_count: rows,
            values_per_group: fake_glv_gamma_range13_columns().len(),
        },
        GammaTallLayout {
            tag: GAMMA_TAG_FAKE_GLV_SIGNED,
            group_count: rows,
            values_per_group: fake_glv_gamma_signed_carry_columns().len(),
        },
    ]
}

/// Build the two γ-digest tall instances from the consumer base trace: one
/// group per active row (the schedule), values gathered in digest order.
pub(crate) fn fake_glv_gamma_instances(base: &[M31ColumnEval]) -> [GammaTallInstance; 2] {
    let r13_columns = fake_glv_gamma_range13_columns();
    let signed_columns = fake_glv_gamma_signed_carry_columns();
    let r13_groups = gamma_collect_group_values(base, &r13_columns);
    let signed_groups = gamma_collect_group_values(base, &signed_columns);
    [
        GammaTallInstance::new(
            GAMMA_TAG_FAKE_GLV_RANGE13,
            r13_columns.len(),
            M31::from_u32_unchecked(0),
            r13_groups,
        ),
        GammaTallInstance::new(
            GAMMA_TAG_FAKE_GLV_SIGNED,
            signed_columns.len(),
            crate::range_checks::encode_signed_carry(0),
            signed_groups,
        ),
    ]
}

pub(crate) fn gen_fake_glv_projective_source_consumer_interaction_trace(
    base: &[M31ColumnEval],
    ec_row_relation: &FakeGlvPrimitiveEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
    gamma_digest_relation: &GammaDigestRelation,
    gamma_challenge: &GammaChallenge,
) -> FakeGlvProjectiveSourceConsumerInteraction {
    assert_eq!(base.len(), FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    // Collect every fraction in the consumer AIR's emission order, then write
    // them `FAKE_GLV_CONSUMER_LOGUP_BATCH` per interaction column to mirror
    // the eval's `finalize_logup_batched(consecutive_batching(..))` layout.
    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let active_numerators: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| PackedQM31::from(base[0].data[vec_row]))
        .collect();

    // Entry 0: the EC-row consume (+active).
    entries.push((
        active_numerators.clone(),
        (0..vec_rows)
            .map(|vec_row| {
                let values = fake_glv_primitive_ec_row_packed_relation_values(base, vec_row);
                ec_row_relation.combine(&values)
            })
            .collect(),
    ));

    // Wide mul-result consumes (+has_muls), canonical order (mul_index outer,
    // role `[LHS, RHS, RESULT]`), matching `ConsumedMulLimbs`.
    let has_muls_numerators: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| PackedQM31::from(base[FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL].data[vec_row]))
        .collect();
    let layout = fake_glv_consumed_mul_gen_layout();
    for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
        for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
            entries.push((
                has_muls_numerators.clone(),
                (0..vec_rows)
                    .map(|vec_row| {
                        let mut values = Vec::with_capacity(3 + N_LIMBS);
                        values.push(base[1].data[vec_row]);
                        values.push(PackedM31::broadcast(M31::from_u32_unchecked(mul_index as u32)));
                        values.push(PackedM31::broadcast(M31::from_u32_unchecked(role)));
                        values.extend(crate::projective_air::consumed_mul_slot_packed_limbs(
                            base, vec_row, &layout, mul_index, role_index,
                        ));
                        mul_result_relation.combine(&values)
                    })
                    .collect(),
            ));
        }
    }
    // γ-digest yields (−active), in eval order: range13 kind then signed
    // kind. The digest of a padding row (all-zero values, zero numerator) is
    // computed from the actual column values, mirroring the eval.
    let instances = fake_glv_gamma_instances(base);
    for instance in &instances {
        let columns = match instance.layout.tag {
            GAMMA_TAG_FAKE_GLV_RANGE13 => fake_glv_gamma_range13_columns(),
            _ => fake_glv_gamma_signed_carry_columns(),
        };
        let mut numerators = Vec::with_capacity(vec_rows);
        let mut denominators = Vec::with_capacity(vec_rows);
        for vec_row in 0..vec_rows {
            let mut numerator = [SecureField::from(M31::from_u32_unchecked(0)); N_LANES];
            let mut denominator = [SecureField::from(M31::from_u32_unchecked(1)); N_LANES];
            for lane in 0..N_LANES {
                let active = base[0].data[vec_row].to_array()[lane];
                let row_index = gamma_row_index_of(vec_row, lane, log_size);
                let values: Vec<M31> = columns
                    .iter()
                    .map(|&col| base[col].data[vec_row].to_array()[lane])
                    .collect();
                let digest =
                    gamma_digest_of_values(gamma_challenge, instance.pad_value, &values);
                let tuple = gamma_digest_tuple(
                    instance.layout.tag,
                    M31::from_u32_unchecked(row_index),
                    digest,
                );
                numerator[lane] = -SecureField::from(active);
                denominator[lane] = gamma_digest_relation.combine(&tuple);
            }
            numerators.push(PackedQM31::from_array(numerator));
            denominators.push(PackedQM31::from_array(denominator));
        }
        entries.push((numerators, denominators));
    }

    assert_eq!(entries.len(), fake_glv_consumer_logup_entries());
    let mut logup = LogupTraceGenerator::new(log_size);
    crate::range_checks::write_logup_columns_with_batching(
        &mut logup,
        &entries,
        &fake_glv_consumer_logup_batching(),
    );
    let (columns, _total) = logup.finalize_last();

    // Sub-sums (unpacked `SecureField`): the EC-row consumer sum, mul-result
    // consumer sum, and the γ-digest yield sum. Computed analytically so the
    // proof's `relation_balances()` can net each relation independently.
    let (ec_row_sum, mul_result_sum) =
        fake_glv_projective_source_consumer_sums(base, ec_row_relation, mul_result_relation);
    let gamma_yield_sum = instances
        .iter()
        .map(|instance| gamma_digest_yield_sum(instance, gamma_challenge, gamma_digest_relation))
        .sum();
    FakeGlvProjectiveSourceConsumerInteraction {
        columns,
        ec_row_sum,
        mul_result_sum,
        gamma_yield_sum,
    }
}

/// Output of the fake-GLV projective-source consumer interaction-trace
/// generator: the interaction columns and the per-relation analytic use sums.
pub(crate) struct FakeGlvProjectiveSourceConsumerInteraction {
    pub columns: ColumnVec<M31ColumnEval>,
    pub ec_row_sum: SecureField,
    pub mul_result_sum: SecureField,
    /// Σ of the two γ-digest yields (−active); balances against the tall
    /// expanders' `digest_use_sum`s.
    pub gamma_yield_sum: SecureField,
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

/// Base-trace column indices the Range13 USES read for the MixedAdd formula, in
/// `bind_mixed_add_formula` emission order: lhs.x, lhs.y, rhs.x, rhs.y, output.x,
/// output.y limbs, then x3, y3, z3 working-value limbs. (MixedAdd reads both
/// affine operands, hence the extra rhs pair vs the Double list.)
fn mixed_add_formula_range13_use_columns() -> Vec<usize> {
    let lhs_x = 5; // after [active, source_index, sig_id, cert_id, op]
    let lhs_y = lhs_x + N_LIMBS;
    let rhs_x = 5 + PREPARED_TABLE_EC_POINT_COLUMNS;
    let rhs_y = rhs_x + N_LIMBS;
    let output_x = 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS;
    let output_y = output_x + N_LIMBS;
    // x3, y3, z3 are the first 3·N_LIMBS columns of the MixedAdd-formula block.
    let x3 = FAKE_GLV_PROJECTIVE_MIXED_ADD_FORMULA_OFFSET;
    let mut cols = Vec::with_capacity(9 * N_LIMBS);
    for start in [
        lhs_x,
        lhs_y,
        rhs_x,
        rhs_y,
        output_x,
        output_y,
        x3,
        x3 + N_LIMBS,
        x3 + 2 * N_LIMBS,
    ] {
        for limb in 0..N_LIMBS {
            cols.push(start + limb);
        }
    }
    cols
}

/// Base-trace column indices the signed-carry USES read for the MixedAdd
/// formula, in consumer-AIR emission order (reduction slot outer, carry limb
/// inner). The MixedAdd-formula block layout is `x3,y3,z3` (3·N_LIMBS) then per
/// reduction `(q, carries)`.
fn mixed_add_formula_signed_carry_use_columns() -> Vec<usize> {
    let block = FAKE_GLV_PROJECTIVE_MIXED_ADD_FORMULA_OFFSET;
    let reductions_start = block + 3 * N_LIMBS;
    let mut cols = Vec::with_capacity(MIXED_ADD_TOTAL_REDUCTIONS * N_LIMBS);
    for slot in 0..MIXED_ADD_TOTAL_REDUCTIONS {
        let q_col = reductions_start + slot * (1 + N_LIMBS);
        for limb in 0..N_LIMBS {
            cols.push(q_col + 1 + limb); // skip the quotient column
        }
    }
    cols
}

/// Range13 USE values the wide consumer's values contribute via the γ-digest
/// tall expander (per scheduled row: the digest-ordered list lane-padded with
/// zeros). Fed into the self-contained Range13 provider's multiplicity. The
/// tall instance is the single source of truth, so provider tallies can never
/// drift from the expander's consumption.
pub(crate) fn fake_glv_projective_source_range13_uses_from_base(base: &[M31ColumnEval]) -> Vec<M31> {
    let [r13, _] = fake_glv_gamma_instances(base);
    r13.all_scheduled_values()
}

/// signed-carry USE values (decoded `i64`) consumed by the γ-digest tall
/// expander (per scheduled row, lane-padded with `encode_signed_carry(0)`).
pub(crate) fn fake_glv_projective_source_signed_carry_uses_from_base(
    base: &[M31ColumnEval],
) -> Vec<i64> {
    let [_, signed] = fake_glv_gamma_instances(base);
    signed
        .all_scheduled_values()
        .into_iter()
        .map(crate::range_checks::decode_signed_carry)
        .collect()
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
    let mut ec_row_denominators = Vec::new();
    let mut mul_result_denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active != M31::from_u32_unchecked(0) {
                let ec_values: [M31; FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY] =
                    core::array::from_fn(|index| base[index + 1].data[vec_row].to_array()[lane]);
                ec_row_denominators.push(ec_row_relation.combine(&ec_values));
            }

            let has_muls = base[FAKE_GLV_PRIMITIVE_EC_HAS_MULS_COL].data[vec_row].to_array()[lane];
            if has_muls == M31::from_u32_unchecked(0) {
                continue;
            }
            let source_index = base[1].data[vec_row].to_array()[lane];
            let layout = fake_glv_consumed_mul_gen_layout();
            for mul_index in 0..(PROJECTIVE_RCB_OP_MUL_LIMB_COLUMNS / (3 * N_LIMBS)) {
                for (role_index, &role) in PROJECTIVE_RCB_MUL_RESULT_ROLES.iter().enumerate() {
                    let limbs = crate::projective_air::consumed_mul_slot_packed_limbs(
                        base, vec_row, &layout, mul_index, role_index,
                    );
                    let mut values = Vec::with_capacity(3 + N_LIMBS);
                    values.push(source_index);
                    values.push(M31::from_u32_unchecked(mul_index as u32));
                    values.push(M31::from_u32_unchecked(role));
                    values.extend(limbs.iter().map(|packed| packed.to_array()[lane]));
                    mul_result_denominators.push(mul_result_relation.combine(&values));
                }
            }
        }
    }
    (
        crate::range_checks::batched_inverse_sum(&ec_row_denominators),
        crate::range_checks::batched_inverse_sum(&mul_result_denominators),
    )
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
    // Operand dedup: only the KEPT slots are committed; dropped operands are
    // consume-tuple expressions of other row columns.
    for value in crate::projective_air::projective_rcb_kept_mul_limbs(&mul_limbs) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, FAKE_GLV_PROJECTIVE_DOUBLE_FORMULA_OFFSET);
    // C5-2a: the Double-formula working values + reduction witnesses. Emitted
    // only for Double rows (op == DOUBLE); MixedAdd / padding leave this block
    // zero, matching the `double_active`-gated constraints + off-Double zero
    // gates.
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
    debug_assert_eq!(column, FAKE_GLV_PROJECTIVE_MIXED_ADD_FORMULA_OFFSET);
    // C5-2b: the MixedAdd-formula working values + reduction witnesses. Emitted
    // only for FINITE-operand MixedAdd rows (op == MIXED_ADD && has_muls); an
    // infinity-operand MixedAdd (`has_muls = 0`) is a 0-mul no-op whose formula
    // is gated off — its block stays zero (the no-op `output = lhs` constraint
    // needs no witness columns). Double / padding also leave this block zero,
    // matching the `mixed_active·has_muls`-gated constraints + off-MixedAdd zero
    // gates.
    let is_mixed = row.op == crate::projective::ProjectiveEcOp::MixedAdd;
    if is_mixed && has_muls {
        let witness = super::mixed_add_formula::solve_mixed_add_formula_witness(
            &mul_limbs,
            &row.output_projective,
        )
        .ok_or(FakeGlvChainError::ProjectiveSourceInvalid)?;
        // `mixed_add_formula_trace_values` already writes the two witnessed gate
        // columns as `(mixed_active, formula_gate) = (1, 1)` for this finite-mul
        // MixedAdd row.
        for value in super::mixed_add_formula::mixed_add_formula_trace_values(&witness) {
            values[column] = value;
            column += 1;
        }
    } else {
        // No witness block (Double / padding / infinity-operand no-op MixedAdd):
        // the x3/y3/z3 + reduction cells stay zero. But the two witnessed gate
        // columns are constrained on EVERY row to `mixed_active = active·(1−op)`
        // and `formula_gate = mixed_active·(1−rhs.inf)`, so they must be written
        // here too: a no-op MixedAdd (op == MIXED_ADD, has_muls == false ⇔
        // rhs.inf == 1) has `mixed_active = 1`, `formula_gate = 0`; a Double has
        // both `0`. (Padding rows are produced by the all-zero `resize`, where
        // `active = 0` ⇒ both gates `0`, matching the definition.)
        let gate_base = column + super::mixed_add_formula::MIXED_ADD_GATE_OFFSET_IN_BLOCK;
        let gates = super::mixed_add_formula::mixed_add_gate_trace_values(is_mixed, false);
        values[gate_base] = gates[0];
        values[gate_base + 1] = gates[1];
        column += MIXED_ADD_FORMULA_COLUMNS;
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
