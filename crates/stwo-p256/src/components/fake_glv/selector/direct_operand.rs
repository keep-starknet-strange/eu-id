use serde::{Deserialize, Serialize};
use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{m31::PackedM31, qm31::PackedQM31, SimdBackend},
    ComponentProver,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};
use stwo_p256_utils::constants::N_LIMBS;

use crate::components::ComponentInteractionClaim;
use crate::scalar::fake_glv_chain::{
    FakeGlvChainClaim, FakeGlvChainError, FakeGlvChainRow, FakeGlvChainRowKind,
};
use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
use crate::scalar::prepared_point::{PreparedPointInstance, PreparedPointRelation, TABLE16_INDEX};
use crate::scalar::prepared_table::{PreparedAffinePoint, PreparedTableClaim};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

pub type DirectPreparedOperandProviderComponent =
    FrameworkComponent<DirectPreparedOperandProviderEval>;
pub type DirectPreparedOperandConsumerComponent =
    FrameworkComponent<DirectPreparedOperandConsumerEval>;

pub const DIRECT_PREPARED_OPERAND_PROVIDER_TRACE_COLUMNS: usize = 2 + DIRECT_OPERAND_ARITY;
pub const DIRECT_PREPARED_OPERAND_CONSUMER_TRACE_COLUMNS: usize = 1 + DIRECT_OPERAND_ARITY;

const DIRECT_OPERAND_ARITY: usize = 3 + 2 * N_LIMBS + 1;
const DIRECT_OPERAND_ZERO_COLUMN: &str = "p256_fake_glv_direct_prepared_operand_zero";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvDirectPreparedOperandProofClaim {
    pub provider_log_size: u32,
    pub consumer_log_size: u32,
}

impl FakeGlvDirectPreparedOperandProofClaim {
    pub fn from_claims(selectors: &FakeGlvSelectorClaim, chain: &FakeGlvChainClaim) -> Self {
        let active_certs = selectors
            .rows
            .iter()
            .filter(|row| row.cert_active.0 == 1)
            .count();
        Self {
            provider_log_size: padded_log_size(2 * active_certs),
            consumer_log_size: padded_log_size(2 * active_chain_cert_count(chain)),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.provider_log_size as u64);
        channel.mix_u64(self.consumer_log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvDirectPreparedOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvDirectPreparedOperandInteractionClaim::zero(),
            &PreparedPointRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvDirectPreparedOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvDirectPreparedOperandInteractionClaim::zero(),
            &PreparedPointRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvDirectPreparedOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvDirectPreparedOperandInteractionClaim::zero(),
            &PreparedPointRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvDirectPreparedOperandInteractionClaim {
    pub provider: ComponentInteractionClaim,
    pub consumer: ComponentInteractionClaim,
}

impl FakeGlvDirectPreparedOperandInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider: ComponentInteractionClaim::zero(),
            consumer: ComponentInteractionClaim::zero(),
        }
    }

    pub fn total(self) -> SecureField {
        self.provider.claimed_sum + self.consumer.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.provider.mix_into(channel);
        self.consumer.mix_into(channel);
    }
}

pub struct FakeGlvDirectPreparedOperandComponents {
    pub provider: DirectPreparedOperandProviderComponent,
    pub consumer: DirectPreparedOperandConsumerComponent,
}

impl FakeGlvDirectPreparedOperandComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvDirectPreparedOperandProofClaim,
        interaction_claim: &FakeGlvDirectPreparedOperandInteractionClaim,
        relation: &PreparedPointRelation,
    ) -> Self {
        Self {
            provider: DirectPreparedOperandProviderComponent::new(
                allocator,
                DirectPreparedOperandProviderEval {
                    log_size: claim.provider_log_size,
                    relation: relation.clone(),
                },
                interaction_claim.provider.claimed_sum,
            ),
            consumer: DirectPreparedOperandConsumerComponent::new(
                allocator,
                DirectPreparedOperandConsumerEval {
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
pub struct DirectPreparedOperandProviderEval {
    pub log_size: u32,
    pub relation: PreparedPointRelation,
}

impl FrameworkEval for DirectPreparedOperandProviderEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let zero = eval.get_preprocessed_column(direct_operand_zero_column_id());
        let active = eval.next_trace_mask();
        let use_count = eval.next_trace_mask();
        let instance = DirectOperandEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(zero * active.clone());
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint((one.clone() - active.clone()) * use_count.clone());
        instance.add_constraints(&mut eval, &active, &one);

        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            -use_count,
            &instance.relation_values(),
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct DirectPreparedOperandConsumerEval {
    pub log_size: u32,
    pub relation: PreparedPointRelation,
}

impl FrameworkEval for DirectPreparedOperandConsumerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let instance = DirectOperandEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        instance.add_constraints(&mut eval, &active, &one);
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            active,
            &instance.relation_values(),
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone, Debug)]
struct DirectOperandEvalInstance<F> {
    sig_id: F,
    cert_id: F,
    table_index: F,
    x: [F; N_LIMBS],
    y: [F; N_LIMBS],
    inf: F,
}

impl<F> DirectOperandEvalInstance<F> {
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

impl<F: Clone> DirectOperandEvalInstance<F> {
    fn relation_values(&self) -> [F; DIRECT_OPERAND_ARITY] {
        core::array::from_fn(|index| match index {
            0 => self.sig_id.clone(),
            1 => self.cert_id.clone(),
            2 => self.table_index.clone(),
            3..=22 => self.x[index - 3].clone(),
            23..=42 => self.y[index - 23].clone(),
            43 => self.inf.clone(),
            _ => unreachable!("direct operand relation index is in range"),
        })
    }
}

impl<F> DirectOperandEvalInstance<F>
where
    F: Clone + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
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

pub(crate) fn gen_direct_operand_preprocessed_trace(
    claim: &FakeGlvDirectPreparedOperandProofClaim,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &direct_operand_zero_column_id() {
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

pub(crate) fn gen_direct_operand_provider_base_trace(
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    let providers = direct_operand_providers(prepared, selectors)?;
    if providers.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: providers.len(),
            domain: padded_rows,
        });
    }
    let mut rows = providers
        .iter()
        .map(direct_operand_provider_trace_values)
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); DIRECT_PREPARED_OPERAND_PROVIDER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

pub(crate) fn gen_direct_operand_consumer_base_trace(
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    let consumers = direct_operand_consumers(selectors, chain)?;
    if consumers.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: consumers.len(),
            domain: padded_rows,
        });
    }
    let mut rows = consumers
        .iter()
        .map(direct_operand_consumer_trace_values)
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); DIRECT_PREPARED_OPERAND_CONSUMER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn direct_operand_providers(
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
) -> Result<Vec<PreparedPointInstance<M31>>, FakeGlvChainError> {
    let mut providers = Vec::new();
    for selector in selectors.rows.iter().filter(|row| row.cert_active.0 == 1) {
        providers.push(prepared_instance(
            prepared,
            selector.sig_id,
            selector.cert_id,
            selector.init_base_index.0,
        )?);
        providers.push(prepared_instance(
            prepared,
            selector.sig_id,
            selector.cert_id,
            TABLE16_INDEX,
        )?);
    }
    Ok(providers)
}

fn direct_operand_consumers(
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
) -> Result<Vec<PreparedPointInstance<M31>>, FakeGlvChainError> {
    if chain.certs.len() != selectors.rows.len() {
        return Err(FakeGlvChainError::RowCountMismatch {
            certs: chain.certs.len(),
            fake_glv: chain.certs.len(),
            selectors: selectors.rows.len(),
            tables: selectors.rows.len(),
        });
    }
    let mut consumers = Vec::new();
    for (cert, selector) in chain.certs.iter().zip(&selectors.rows) {
        if cert.rows.is_empty() {
            continue;
        }
        let msb = row_with_kind(&cert.rows, |kind| kind == FakeGlvChainRowKind::MsbInit)?;
        consumers.push(point_instance(
            &msb.operand,
            msb.sig_id,
            msb.cert_id,
            selector.init_base_index.0,
        ));
        let table16 = row_with_kind(&cert.rows, |kind| kind == FakeGlvChainRowKind::Table16Step)?;
        consumers.push(point_instance(
            &table16.operand,
            table16.sig_id,
            table16.cert_id,
            TABLE16_INDEX,
        ));
    }
    Ok(consumers)
}

fn row_with_kind(
    rows: &[FakeGlvChainRow],
    predicate: impl Fn(FakeGlvChainRowKind) -> bool,
) -> Result<&FakeGlvChainRow, FakeGlvChainError> {
    rows.iter()
        .find(|row| predicate(row.kind))
        .ok_or(FakeGlvChainError::ChainTraceMismatch {
            expected: rows.len(),
            actual: rows.len().saturating_sub(1),
        })
}

fn prepared_instance(
    prepared: &PreparedTableClaim,
    sig_id: M31,
    cert_id: M31,
    table_index: u32,
) -> Result<PreparedPointInstance<M31>, FakeGlvChainError> {
    prepared
        .instance(sig_id, cert_id, table_index)
        .ok_or(FakeGlvChainError::MissingTablePoint { table_index })
}

fn point_instance(
    point: &PreparedAffinePoint,
    sig_id: M31,
    cert_id: M31,
    table_index: u32,
) -> PreparedPointInstance<M31> {
    point.instance(sig_id, cert_id, table_index)
}

pub(crate) fn gen_direct_operand_provider_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedPointRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(base.len(), DIRECT_PREPARED_OPERAND_PROVIDER_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let values = direct_operand_provider_packed_relation_values(base, vec_row);
        (
            -PackedQM31::from(base[1].data[vec_row]),
            relation.combine(&values),
        )
    });
    logup.finalize_last()
}

pub(crate) fn gen_direct_operand_consumer_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedPointRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(base.len(), DIRECT_PREPARED_OPERAND_CONSUMER_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let values = direct_operand_consumer_packed_relation_values(base, vec_row);
        (
            PackedQM31::from(base[0].data[vec_row]),
            relation.combine(&values),
        )
    });
    logup.finalize_last()
}

fn direct_operand_provider_trace_values(
    instance: &PreparedPointInstance<M31>,
) -> [M31; DIRECT_PREPARED_OPERAND_PROVIDER_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); DIRECT_PREPARED_OPERAND_PROVIDER_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[1] = M31::from_u32_unchecked(1);
    values[2..].copy_from_slice(&instance.relation_values());
    values
}

fn direct_operand_consumer_trace_values(
    instance: &PreparedPointInstance<M31>,
) -> [M31; DIRECT_PREPARED_OPERAND_CONSUMER_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); DIRECT_PREPARED_OPERAND_CONSUMER_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[1..].copy_from_slice(&instance.relation_values());
    values
}

fn direct_operand_provider_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; DIRECT_OPERAND_ARITY] {
    core::array::from_fn(|index| base[index + 2].data[vec_row])
}

fn direct_operand_consumer_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; DIRECT_OPERAND_ARITY] {
    core::array::from_fn(|index| base[index + 1].data[vec_row])
}

fn active_chain_cert_count(chain: &FakeGlvChainClaim) -> usize {
    chain
        .certs
        .iter()
        .filter(|cert| !cert.rows.is_empty())
        .count()
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

fn direct_operand_zero_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: DIRECT_OPERAND_ZERO_COLUMN.into(),
    }
}
