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
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};
use stwo_p256_utils::constants::N_LIMBS;

use crate::components::ComponentInteractionClaim;
use crate::range_checks::{add_range_check, RangeCheckRelation};
use crate::scalar::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError};
use crate::scalar::prepared_point::{
    PreparedPointInstance, PreparedPointProvider, PreparedPointRelation, PreparedPointTraceClaim,
    PREPARED_POINT_ARITY,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

pub type PreparedPointProviderComponent = FrameworkComponent<PreparedPointProviderEval>;
pub type FakeGlvPreparedPointConsumerComponent =
    FrameworkComponent<FakeGlvPreparedPointConsumerEval>;

pub const PREPARED_POINT_PROVIDER_TRACE_COLUMNS: usize = 2 + PREPARED_POINT_ARITY;
pub const FAKE_GLV_PREPARED_POINT_CONSUMER_TRACE_COLUMNS: usize = 1 + PREPARED_POINT_ARITY;

const PREPARED_POINT_SOURCE_ZERO_COLUMN: &str = "p256_prepared_point_source_zero";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvPreparedPointSourceProofClaim {
    pub provider_log_size: u32,
    pub consumer_log_size: u32,
}

impl FakeGlvPreparedPointSourceProofClaim {
    pub fn from_claims(prepared: &PreparedPointTraceClaim, chain: &FakeGlvChainClaim) -> Self {
        Self {
            provider_log_size: padded_log_size(nonzero_prepared_provider_count(prepared)),
            consumer_log_size: padded_log_size(chain.prepared_point_consumers().len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.provider_log_size as u64);
        channel.mix_u64(self.consumer_log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvPreparedPointSourceComponents::new(
            &mut allocator,
            *self,
            &FakeGlvPreparedPointSourceInteractionClaim::zero(),
            &PreparedPointRelation::dummy(),
            &RangeCheckRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvPreparedPointSourceComponents::new(
            &mut allocator,
            *self,
            &FakeGlvPreparedPointSourceInteractionClaim::zero(),
            &PreparedPointRelation::dummy(),
            &RangeCheckRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvPreparedPointSourceComponents::new(
            &mut allocator,
            *self,
            &FakeGlvPreparedPointSourceInteractionClaim::zero(),
            &PreparedPointRelation::dummy(),
            &RangeCheckRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvPreparedPointSourceInteractionClaim {
    pub provider: ComponentInteractionClaim,
    pub consumer: ComponentInteractionClaim,
}

impl FakeGlvPreparedPointSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider: ComponentInteractionClaim::zero(),
            consumer: ComponentInteractionClaim::zero(),
        }
    }

    pub fn total(self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub(crate) fn component_claimed_sum(self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.provider.mix_into(channel);
        self.consumer.mix_into(channel);
    }
}

pub struct FakeGlvPreparedPointSourceComponents {
    pub provider: PreparedPointProviderComponent,
    pub consumer: FakeGlvPreparedPointConsumerComponent,
}

impl FakeGlvPreparedPointSourceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvPreparedPointSourceProofClaim,
        interaction_claim: &FakeGlvPreparedPointSourceInteractionClaim,
        relation: &PreparedPointRelation,
        range7: &RangeCheckRelation,
    ) -> Self {
        Self {
            provider: PreparedPointProviderComponent::new(
                allocator,
                PreparedPointProviderEval {
                    log_size: claim.provider_log_size,
                    relation: relation.clone(),
                    range7: range7.clone(),
                },
                interaction_claim.provider.claimed_sum,
            ),
            consumer: FakeGlvPreparedPointConsumerComponent::new(
                allocator,
                FakeGlvPreparedPointConsumerEval {
                    log_size: claim.consumer_log_size,
                    relation: relation.clone(),
                },
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
pub struct PreparedPointProviderEval {
    pub log_size: u32,
    pub relation: PreparedPointRelation,
    pub range7: RangeCheckRelation,
}

impl FrameworkEval for PreparedPointProviderEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let zero = eval.get_preprocessed_column(prepared_point_source_zero_column_id());
        let active = eval.next_trace_mask();
        let use_count = eval.next_trace_mask();
        let instance = PreparedPointEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(zero * active.clone());
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint((one.clone() - active.clone()) * use_count.clone());
        instance.add_constraints(&mut eval, &active, &one);

        let values = instance.relation_values();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(use_count.clone()),
            &values,
        ));
        add_range_check(&mut eval, &self.range7, active, use_count);
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct FakeGlvPreparedPointConsumerEval {
    pub log_size: u32,
    pub relation: PreparedPointRelation,
}

impl FrameworkEval for FakeGlvPreparedPointConsumerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let instance = PreparedPointEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        instance.add_constraints(&mut eval, &active, &one);

        let values = instance.relation_values();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(active),
            &values,
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone, Debug)]
struct PreparedPointEvalInstance<F> {
    sig_id: F,
    cert_id: F,
    table_index: F,
    x: [F; N_LIMBS],
    y: [F; N_LIMBS],
    inf: F,
}

impl<F> PreparedPointEvalInstance<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            table_index: eval.next_trace_mask(),
            x: core::array::from_fn(|_| eval.next_trace_mask()),
            y: core::array::from_fn(|_| eval.next_trace_mask()),
            inf: eval.next_trace_mask(),
        }
    }
}

impl<F: Clone> PreparedPointEvalInstance<F> {
    fn relation_values(&self) -> [F; PREPARED_POINT_ARITY] {
        core::array::from_fn(|index| match index {
            0 => self.sig_id.clone(),
            1 => self.cert_id.clone(),
            2 => self.table_index.clone(),
            3..=22 => self.x[index - 3].clone(),
            23..=42 => self.y[index - 23].clone(),
            43 => self.inf.clone(),
            _ => unreachable!("prepared-point relation index is in range"),
        })
    }
}

impl<F> PreparedPointEvalInstance<F>
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
{
    fn add_constraints<E: EvalAtRow<F = F>>(&self, eval: &mut E, active: &F, one: &F) {
        eval.add_constraint(self.inf.clone() * (self.inf.clone() - one.clone()));
        for value in [&self.sig_id, &self.cert_id, &self.table_index] {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }
        for limb in self.x.iter().chain(self.y.iter()) {
            eval.add_constraint(self.inf.clone() * limb.clone());
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }
        eval.add_constraint((one.clone() - active.clone()) * self.inf.clone());
    }
}

pub(crate) fn gen_fake_glv_prepared_point_source_preprocessed_trace(
    claim: &FakeGlvPreparedPointSourceProofClaim,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &prepared_point_source_zero_column_id() {
                Ok(m31_column_eval(
                    claim.provider_log_size,
                    vec![M31::from_u32_unchecked(0); 1usize << claim.provider_log_size],
                ))
            } else {
                Err(FakeGlvChainError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

pub(crate) fn gen_prepared_point_provider_base_trace(
    trace: &PreparedPointTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    let active_providers = trace
        .providers
        .iter()
        .filter(|provider| provider.use_count.0 != 0)
        .collect::<Vec<_>>();
    if active_providers.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: active_providers.len(),
            domain: padded_rows,
        });
    }
    let mut rows = active_providers
        .into_iter()
        .map(prepared_point_provider_trace_values)
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_POINT_PROVIDER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_fake_glv_prepared_point_consumer_base_trace(
    consumers: &[PreparedPointInstance<M31>],
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    if consumers.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: consumers.len(),
            domain: padded_rows,
        });
    }
    let mut rows = consumers
        .iter()
        .map(prepared_point_consumer_trace_values)
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_PREPARED_POINT_CONSUMER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_prepared_point_provider_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedPointRelation,
    range7: &RangeCheckRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField, SecureField) {
    assert_eq!(base.len(), PREPARED_POINT_PROVIDER_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_point_provider_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[1].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let active = PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = range7.combine(&[base[1].data[vec_row]]);
        col.write_frac(vec_row, active, denominator);
    }
    col.finalize_col();
    let (trace, total_claimed_sum) = logup.finalize_last();
    let provider_claimed_sum: SecureField = storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .map(|row| -> SecureField {
            let values = prepared_point_provider_relation_values(&row);
            let denominator: SecureField = relation.combine(&values);
            -SecureField::from(row[1]) / denominator
        })
        .sum();
    let range7_consumer_claimed_sum = total_claimed_sum - provider_claimed_sum;
    (trace, provider_claimed_sum, range7_consumer_claimed_sum)
}

pub(crate) fn gen_fake_glv_prepared_point_consumer_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedPointRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(base.len(), FAKE_GLV_PREPARED_POINT_CONSUMER_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_point_consumer_packed_relation_values(base, vec_row);
        let numerator = PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    logup.finalize_last()
}

fn prepared_point_provider_trace_values(
    provider: &PreparedPointProvider,
) -> [M31; PREPARED_POINT_PROVIDER_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_POINT_PROVIDER_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[1] = provider.use_count;
    values[2..].copy_from_slice(&prepared_point_instance_values(&provider.instance));
    values
}

fn prepared_point_consumer_trace_values(
    consumer: &PreparedPointInstance<M31>,
) -> [M31; FAKE_GLV_PREPARED_POINT_CONSUMER_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_PREPARED_POINT_CONSUMER_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[1..].copy_from_slice(&prepared_point_instance_values(consumer));
    values
}

fn prepared_point_instance_values(
    instance: &PreparedPointInstance<M31>,
) -> [M31; PREPARED_POINT_ARITY] {
    instance.relation_values()
}

fn prepared_point_provider_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_POINT_ARITY] {
    core::array::from_fn(|index| base[index + 2].data[vec_row])
}

fn prepared_point_consumer_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_POINT_ARITY] {
    core::array::from_fn(|index| base[index + 1].data[vec_row])
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

fn prepared_point_source_zero_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: PREPARED_POINT_SOURCE_ZERO_COLUMN.into(),
    }
}

fn nonzero_prepared_provider_count(trace: &PreparedPointTraceClaim) -> usize {
    trace
        .providers
        .iter()
        .filter(|provider| provider.use_count.0 != 0)
        .count()
}

fn storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(|row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}

fn prepared_point_provider_relation_values(row: &[M31]) -> [M31; PREPARED_POINT_ARITY] {
    core::array::from_fn(|index| row[index + 2])
}
