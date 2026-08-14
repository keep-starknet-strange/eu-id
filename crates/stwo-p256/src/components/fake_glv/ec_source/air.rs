use serde::{Deserialize, Serialize};
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
    },
    ComponentProver,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

use crate::projective::{ProjectiveEcOp, ProjectiveEcTraceClaim};
use crate::projective_air::{ProjectiveRcbMulComponentRelations, ProjectiveRcbMulResultRelation};

use crate::components::fake_glv::prepared_table::air::add_projective_source_narrow_mul_consumes;
use crate::components::fake_glv::prepared_table::interaction::{
    narrow_mul_consume_sum, narrow_mul_gate_lanes, push_narrow_mul_consume_entries,
    NarrowMulConsumeColumns, NARROW_MUL_CONSUME_SLOTS,
};
use crate::components::ComponentInteractionClaim;

use crate::scalar::fake_glv_chain::{
    FakeGlvChainError, FakeGlvPrimitiveEcOp, FakeGlvPrimitiveEcRow, FakeGlvPrimitiveEcTraceClaim,
};
use crate::scalar::prepared_table::{
    prepared_table_ec_point_values, PreparedTableEcEvalPoint, PREPARED_TABLE_EC_OP_DOUBLE,
    PREPARED_TABLE_EC_OP_MIXED_ADD, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use stwo_p256_utils::constants::N_LIMBS;

relation!(
    FakeGlvPrimitiveEcRowRelation,
    FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY
);

pub type FakeGlvPrimitiveEcRowProviderComponent =
    FrameworkComponent<FakeGlvPrimitiveEcRowProviderEval>;
pub type FakeGlvProjectiveSourceComponent = FrameworkComponent<FakeGlvProjectiveSourceEval>;

pub const FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY: usize = 4 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;
/// Provider base-trace width: `active` + the EC-row relation columns. The
/// provider (`FakeGlvPrimitiveEcRowProviderEval`) does not carry multiplication-consumer
/// columns.
pub const FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY;
/// Consumer base-trace width.
///
/// The layout contains metadata and three committed points.
/// The hinted multiplication silo owns multiplication and formula columns.
pub const FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS: usize =
    FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS;

const FAKE_GLV_PRIMITIVE_EC_ROW_INDEX_COLUMN: &str = "p256_fake_glv_primitive_ec_row_index";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvProjectiveSourceProofClaim {
    pub log_size: u32,
    pub source_offset: u32,
    /// Active EC rows equal the γ-digest groups in the tall expander schedule.
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
            &FakeGlvProjectiveSourceInteractionClaim::zero(),
            &FakeGlvPrimitiveEcRowRelation::dummy(),
            &ProjectiveRcbMulComponentRelations::dummy(),
            &crate::components::hinted_mul::EcOpHeaderRelation::dummy(),
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
            &crate::components::hinted_mul::EcOpHeaderRelation::dummy(),
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
            &crate::components::hinted_mul::EcOpHeaderRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FakeGlvProjectiveSourceInteractionClaim {
    pub provider: ComponentInteractionClaim,
    pub consumer: ComponentInteractionClaim,
}

impl FakeGlvProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider: ComponentInteractionClaim::zero(),
            consumer: ComponentInteractionClaim::zero(),
        }
    }

    /// `FakeGlvProjectiveSource` balance term: provider yield + EC-row consume.
    /// EXCLUDES the mul-result consume (balanced under `ProjectiveRcbMulResult`)
    /// and the header yield (balanced under `EcOpHeader`).
    pub fn total(&self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub(crate) fn component_claimed_sum(&self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.provider.mix_into(channel);
        self.consumer.mix_into(channel);
    }
}

pub struct FakeGlvProjectiveSourceComponents {
    pub provider: FakeGlvPrimitiveEcRowProviderComponent,
    pub consumer: FakeGlvProjectiveSourceComponent,
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
        header: &crate::components::hinted_mul::EcOpHeaderRelation,
    ) -> Self {
        Self {
            provider: FakeGlvPrimitiveEcRowProviderComponent::new(
                allocator,
                FakeGlvPrimitiveEcRowProviderEval {
                    log_size,
                    source_offset,
                    relation: relation.clone(),
                },
                interaction_claim.provider.claimed_sum,
            ),
            consumer: FakeGlvProjectiveSourceComponent::new(
                allocator,
                FakeGlvProjectiveSourceEval {
                    log_size,
                    relation: relation.clone(),
                    mul_result: mul_relations.mul_result.clone(),
                    header: header.clone(),
                },
                // EC-row + narrow mul consumes + header yield share one
                // interaction trace.
                interaction_claim.consumer.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.provider as &dyn Component,
            &self.consumer as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.provider as &dyn ComponentProver<SimdBackend>,
            &self.consumer as &dyn ComponentProver<SimdBackend>,
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
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            -active,
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
    /// Hinted multiplication relation for six narrow group slots.
    ///
    /// These consumes bind committed points to silo operand columns.
    /// The hinted multiplication component binds all other operands and results.
    pub mul_result: crate::projective_air::ProjectiveRcbMulResultRelation,
    /// Provides the EC operation header link for the silo.
    pub header: crate::components::hinted_mul::EcOpHeaderRelation,
}

impl FrameworkEval for FakeGlvProjectiveSourceEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Keep the component bound at `log_size + 1`.
        // Solo LogUp batches keep each constraint at degree 3 or less.
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

        // Group-existence gate (≡ the old committed `has_muls`): the silo emits
        // a 15-mul group for Double (op == 1) and finite-operand MixedAdd, ZERO
        // for an infinity-operand MixedAdd. `active − (1−op)·rhs.inf` equals
        // `active·(1 − (1−op)·rhs.inf)` on every row because `op` and `rhs.inf`
        // are zeroed on padding (constraints above). Degree 2.
        let gate = active.clone() - (one.clone() - op.clone()) * rhs.inf();

        let relation_values = fake_glv_primitive_ec_row_relation_values(
            &[source_index.clone(), sig_id, cert_id, op.clone()],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            active.clone(),
            &relation_values,
        ));
        // The 6 narrow mul-result consumes (`+gate`): pin the consumer's own
        // committed point coordinates to the silo group's operand columns.
        add_projective_source_narrow_mul_consumes(
            &mut eval,
            &self.mul_result,
            &source_index,
            &op,
            &gate,
            &lhs,
            &rhs,
            &output,
        );

        // Infinity-operand no-op: `lhs + ∞ = lhs` has no silo group, so pin the
        // output to the accumulator directly. `noop = (1−op)·rhs.inf` equals
        // `active·(1−op)·rhs.inf` on every row (padding zeroing above). The
        // copies are degree 3.
        let noop = (one.clone() - op.clone()) * rhs.inf();
        let (lhs_x, lhs_y) = (lhs.x_bigint(), lhs.y_bigint());
        let (out_x, out_y) = (output.x_bigint(), output.y_bigint());
        for i in 0..N_LIMBS {
            eval.add_constraint(
                noop.clone() * (out_x.limbs()[i].clone() - lhs_x.limbs()[i].clone()),
            );
            eval.add_constraint(
                noop.clone() * (out_y.limbs()[i].clone() - lhs_y.limbs()[i].clone()),
            );
        }
        eval.add_constraint(noop.clone() * (output.inf() - lhs.inf()));

        // EC-op header YIELD (−gate): tuple
        // (source_index, op, output_inf, lhs_inf, rhs_inf), consumed 1:1 by the
        // silo group header. Infinity-operand MixedAdd rows have gate = 0 and
        // no silo group, so they yield nothing — the relation nets to zero.
        eval.add_to_relation(RelationEntry::base(
            &self.header,
            -gate,
            &[
                source_index.clone(),
                op.clone(),
                output.inf(),
                lhs.inf(),
                rhs.inf(),
            ],
        ));

        eval.finalize_logup_batched(FAKE_GLV_CONSUMER_LOGUP_BATCH);
        eval
    }
}

pub(crate) fn gen_fake_glv_primitive_ec_preprocessed_trace(
    log_size: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &fake_glv_primitive_ec_row_index_column_id() {
                Ok(m31_column_eval(
                    log_size,
                    (0..(1usize << log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
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
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

/// Provider (yield, `-active`) interaction trace for the EC-row relation.
pub(crate) fn gen_fake_glv_primitive_ec_source_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvPrimitiveEcRowRelation,
) -> (
    ColumnVec<M31ColumnEval>,
    FakeGlvPrimitiveEcRowInteractionClaim,
) {
    assert_eq!(base.len(), FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let values = fake_glv_primitive_ec_row_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        (numerator, denominator)
    });
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, FakeGlvPrimitiveEcRowInteractionClaim { claimed_sum })
}

// Interaction trace for the narrow fake-GLV projective-source consumer.
// It emits entries in evaluator order under one
// `finalize_logup_batched`:
//   0. the `FakeGlvPrimitiveEcRowRelation` consume (+active),
//   1..=6. the 6 narrow `ProjectiveRcbMulResultRelation` consumes (+gate),
//   7. the `EcOpHeaderRelation` yield (−gate),
// where `gate = active − (1−op)·rhs.inf` (the group-existence gate).
//
// LogUp batch size: 1 fraction per interaction column. The op-mux consume
// entries (M0.rhs at index 2, M1.rhs at index 4) have degree-2 tuple values.
// Pairing them with a neighbor pushes the logup constraint past degree 3,
// which overflows the `log_size + 1` bound. `finalize_logup_batched` only
// supports a uniform batch size, so everything goes solo.
pub(crate) const FAKE_GLV_CONSUMER_LOGUP_BATCH: usize = 1;

/// Total LogUp entries the consumer eval emits (EC-row consume + 6 narrow mul
/// consumes + the EC-op header yield), in emission order.
pub(crate) fn fake_glv_consumer_logup_entries() -> usize {
    1 + NARROW_MUL_CONSUME_SLOTS.len() + 1
}

/// The fake-GLV consumer's narrow-consume column layout (5 metadata columns,
/// points start at column 5).
fn fake_glv_narrow_mul_columns() -> NarrowMulConsumeColumns {
    NarrowMulConsumeColumns {
        source: 1,
        op: 4,
        lhs_x: 5,
        lhs_y: 5 + N_LIMBS,
        rhs_x: 5 + PREPARED_TABLE_EC_POINT_COLUMNS,
        rhs_y: 5 + PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
        rhs_inf: 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS - 1,
        out_x: 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS,
        out_y: 5 + 2 * PREPARED_TABLE_EC_POINT_COLUMNS + N_LIMBS,
    }
}

pub(crate) fn gen_fake_glv_projective_source_consumer_interaction_trace(
    base: &[M31ColumnEval],
    ec_row_relation: &FakeGlvPrimitiveEcRowRelation,
    mul_result_relation: &ProjectiveRcbMulResultRelation,
    header_relation: &crate::components::hinted_mul::EcOpHeaderRelation,
) -> FakeGlvProjectiveSourceConsumerInteraction {
    assert_eq!(
        base.len(),
        FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS
    );
    let log_size = base[0].domain.log_size();
    let vec_rows = 1usize << (log_size - LOG_N_LANES);
    let cols = fake_glv_narrow_mul_columns();
    let gate = narrow_mul_gate_lanes(base, &cols, vec_rows);
    // Collect every fraction in the consumer AIR's emission order, then write
    // them with the eval's exact batching.
    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
    let active_numerators: Vec<PackedQM31> = (0..vec_rows)
        .map(|vec_row| PackedQM31::from(base[0].data[vec_row]))
        .collect();

    // Entry 0: the EC-row consume (+active).
    entries.push((
        active_numerators,
        (0..vec_rows)
            .map(|vec_row| {
                let values = fake_glv_primitive_ec_row_packed_relation_values(base, vec_row);
                ec_row_relation.combine(&values)
            })
            .collect(),
    ));

    // Entries 1..=6: the narrow mul-result consumes (+gate).
    push_narrow_mul_consume_entries(
        &mut entries,
        base,
        &cols,
        &gate,
        mul_result_relation,
        vec_rows,
    );

    // Entry 7: EC-op header YIELD (−gate): tuple
    // (source_index, op, output_inf, lhs_inf, rhs_inf).
    let lhs_inf_col = 5 + PREPARED_TABLE_EC_POINT_COLUMNS - 1;
    let output_inf_col = 5 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS - 1;
    entries.push((
        gate.iter().map(|&lanes| -PackedQM31::from(lanes)).collect(),
        (0..vec_rows)
            .map(|vec_row| {
                header_relation.combine(&[
                    base[1].data[vec_row],
                    base[4].data[vec_row],
                    base[output_inf_col].data[vec_row],
                    base[lhs_inf_col].data[vec_row],
                    base[cols.rhs_inf].data[vec_row],
                ])
            })
            .collect(),
    ));

    assert_eq!(entries.len(), fake_glv_consumer_logup_entries());
    let mut logup = LogupTraceGenerator::new(log_size);
    crate::range_checks::write_batched_logup_columns(
        &mut logup,
        &entries,
        FAKE_GLV_CONSUMER_LOGUP_BATCH,
    );
    let (columns, _total) = logup.finalize_last();

    // Sub-sums (unpacked `SecureField`): the EC-row consumer sum, the narrow
    // mul-result consumer sum, and the header yield sum. Computed analytically
    // so the proof's `relation_balances()` can net each relation independently.
    let ec_row_sum = fake_glv_projective_source_ec_row_sum(base, ec_row_relation);
    let mul_result_sum = narrow_mul_consume_sum(base, &cols, mul_result_relation);
    let header_yield_sum = fake_glv_projective_source_header_yield_sum(
        base,
        header_relation,
        &cols,
        lhs_inf_col,
        output_inf_col,
    );
    FakeGlvProjectiveSourceConsumerInteraction {
        columns,
        ec_row_sum,
        mul_result_sum,
        header_yield_sum,
    }
}

/// Analytic header-yield sum (−gate over rows with a silo group), matching the
/// eval's header yield entry. `gate = active − (1−op)·rhs.inf`.
fn fake_glv_projective_source_header_yield_sum(
    base: &[M31ColumnEval],
    header_relation: &crate::components::hinted_mul::EcOpHeaderRelation,
    cols: &NarrowMulConsumeColumns,
    lhs_inf_col: usize,
    output_inf_col: usize,
) -> SecureField {
    let log_size = base[0].domain.log_size();
    let one = M31::from_u32_unchecked(1);
    let mut denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let cell = |col: usize| base[col].data[vec_row].to_array()[lane];
            let gate = cell(0) - (one - cell(cols.op)) * cell(cols.rhs_inf);
            if gate == M31::from_u32_unchecked(0) {
                continue;
            }
            denominators.push(header_relation.combine(&[
                cell(cols.source),
                cell(cols.op),
                cell(output_inf_col),
                cell(lhs_inf_col),
                cell(cols.rhs_inf),
            ]));
        }
    }
    -crate::range_checks::batched_inverse_sum(&denominators)
}

/// Output of the fake-GLV projective-source consumer interaction-trace
/// generator: the interaction columns and the per-relation analytic use sums.
pub(crate) struct FakeGlvProjectiveSourceConsumerInteraction {
    pub columns: ColumnVec<M31ColumnEval>,
    pub ec_row_sum: SecureField,
    pub mul_result_sum: SecureField,
    /// Σ of the EC-op header yields (−gate). Balances against the silo's
    /// header consume.
    pub header_yield_sum: SecureField,
}

/// Analytic EC-row consume sum over the consumer base trace's active rows.
fn fake_glv_projective_source_ec_row_sum(
    base: &[M31ColumnEval],
    ec_row_relation: &FakeGlvPrimitiveEcRowRelation,
) -> SecureField {
    let log_size = base[0].domain.log_size();
    let mut ec_row_denominators = Vec::new();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        for lane in 0..(1 << LOG_N_LANES) {
            let active = base[0].data[vec_row].to_array()[lane];
            if active != M31::from_u32_unchecked(0) {
                let ec_values: [M31; FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY] =
                    core::array::from_fn(|index| base[index + 1].data[vec_row].to_array()[lane]);
                ec_row_denominators.push(ec_row_relation.combine(&ec_values));
            }
        }
    }
    crate::range_checks::batched_inverse_sum(&ec_row_denominators)
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
) -> [M31; FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS] {
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
    debug_assert_eq!(column, FAKE_GLV_PROJECTIVE_SOURCE_CONSUMER_TRACE_COLUMNS);
    values
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FakeGlvPrimitiveEcRowInteractionClaim {
    pub claimed_sum: SecureField,
}
