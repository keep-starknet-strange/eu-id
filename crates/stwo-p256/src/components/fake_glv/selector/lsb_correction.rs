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
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

use crate::components::ComponentInteractionClaim;
use crate::constants::P256_MODULUS;
use crate::curve::scalar_mul;
use crate::field_ops::sub_mod_witness;
use crate::limbs::P256M31BigInt;
use crate::scalar::cert_bind::CertScalarInputClaim;
use crate::scalar::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError, FakeGlvChainRowKind};
use crate::scalar::fake_glv_scalar::FakeGlvScalarHintClaim;
use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
use crate::scalar::prepared_table::{
    prepared_table_ec_point_values, PreparedAffinePoint, PreparedTableClaim,
    PreparedTableEcEvalPoint, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::{AffinePoint, U256};

relation!(
    FakeGlvLsbCorrectionOperandRelation,
    FAKE_GLV_LSB_CORRECTION_OPERAND_RELATION_ARITY
);

pub type FakeGlvLsbCorrectionOperandProviderComponent =
    FrameworkComponent<FakeGlvLsbCorrectionOperandProviderEval>;
pub type FakeGlvLsbCorrectionOperandConsumerComponent =
    FrameworkComponent<FakeGlvLsbCorrectionOperandConsumerEval>;

pub const FAKE_GLV_LSB_CORRECTION_OPERAND_RELATION_ARITY: usize =
    4 + PREPARED_TABLE_EC_POINT_COLUMNS;
pub const FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_LSB_CORRECTION_OPERAND_RELATION_ARITY;

const LSB_CORRECTION_OPERAND_ZERO_COLUMN: &str = "p256_fake_glv_lsb_correction_operand_zero";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvLsbCorrectionOperandProofClaim {
    pub provider_log_size: u32,
    pub consumer_log_size: u32,
}

impl FakeGlvLsbCorrectionOperandProofClaim {
    pub fn from_claims(selectors: &FakeGlvSelectorClaim, chain: &FakeGlvChainClaim) -> Self {
        let active_selectors = selectors
            .rows
            .iter()
            .filter(|row| row.cert_active.0 == 1)
            .count();
        Self {
            provider_log_size: padded_log_size(active_selectors),
            consumer_log_size: padded_log_size(lsb_correction_row_count(chain)),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.provider_log_size as u64);
        channel.mix_u64(self.consumer_log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvLsbCorrectionOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvLsbCorrectionOperandInteractionClaim::zero(),
            &FakeGlvLsbCorrectionOperandRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvLsbCorrectionOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvLsbCorrectionOperandInteractionClaim::zero(),
            &FakeGlvLsbCorrectionOperandRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvLsbCorrectionOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvLsbCorrectionOperandInteractionClaim::zero(),
            &FakeGlvLsbCorrectionOperandRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FakeGlvLsbCorrectionOperandInteractionClaim {
    pub provider: ComponentInteractionClaim,
    pub consumer: ComponentInteractionClaim,
}

impl FakeGlvLsbCorrectionOperandInteractionClaim {
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

pub struct FakeGlvLsbCorrectionOperandComponents {
    pub provider: FakeGlvLsbCorrectionOperandProviderComponent,
    pub consumer: FakeGlvLsbCorrectionOperandConsumerComponent,
}

impl FakeGlvLsbCorrectionOperandComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvLsbCorrectionOperandProofClaim,
        interaction_claim: &FakeGlvLsbCorrectionOperandInteractionClaim,
        relation: &FakeGlvLsbCorrectionOperandRelation,
    ) -> Self {
        Self {
            provider: FakeGlvLsbCorrectionOperandProviderComponent::new(
                allocator,
                FakeGlvLsbCorrectionOperandProviderEval {
                    log_size: claim.provider_log_size,
                    relation: relation.clone(),
                },
                interaction_claim.provider.claimed_sum,
            ),
            consumer: FakeGlvLsbCorrectionOperandConsumerComponent::new(
                allocator,
                FakeGlvLsbCorrectionOperandConsumerEval {
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
pub struct FakeGlvLsbCorrectionOperandProviderEval {
    pub log_size: u32,
    pub relation: FakeGlvLsbCorrectionOperandRelation,
}

impl FrameworkEval for FakeGlvLsbCorrectionOperandProviderEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let zero = eval.get_preprocessed_column(lsb_correction_operand_zero_column_id());
        let instance = LsbCorrectionOperandEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(zero * instance.active.clone());
        instance.add_constraints(&mut eval, &one);
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            -(instance.active.clone()),
            &instance.relation_values(),
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct FakeGlvLsbCorrectionOperandConsumerEval {
    pub log_size: u32,
    pub relation: FakeGlvLsbCorrectionOperandRelation,
}

impl FrameworkEval for FakeGlvLsbCorrectionOperandConsumerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let instance = LsbCorrectionOperandEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        instance.add_constraints(&mut eval, &one);
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            instance.active.clone(),
            &instance.relation_values(),
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
struct LsbCorrectionOperandEvalInstance<F> {
    active: F,
    sig_id: F,
    cert_id: F,
    s1_lsb: F,
    s2_lsb: F,
    operand: PreparedTableEcEvalPoint<F>,
}

impl<F> LsbCorrectionOperandEvalInstance<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            active: eval.next_trace_mask(),
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            s1_lsb: eval.next_trace_mask(),
            s2_lsb: eval.next_trace_mask(),
            operand: PreparedTableEcEvalPoint::read(eval),
        }
    }
}

impl<F: Clone> LsbCorrectionOperandEvalInstance<F> {
    fn relation_values(&self) -> [F; FAKE_GLV_LSB_CORRECTION_OPERAND_RELATION_ARITY] {
        lsb_correction_operand_relation_values(
            &[
                self.sig_id.clone(),
                self.cert_id.clone(),
                self.s1_lsb.clone(),
                self.s2_lsb.clone(),
            ],
            &self.operand.relation_values(),
        )
    }
}

impl<F> LsbCorrectionOperandEvalInstance<F>
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
{
    fn add_constraints<E: EvalAtRow<F = F>>(&self, eval: &mut E, one: &F) {
        eval.add_constraint(self.active.clone() * (self.active.clone() - one.clone()));
        eval.add_constraint(self.s1_lsb.clone() * (self.s1_lsb.clone() - one.clone()));
        eval.add_constraint(self.s2_lsb.clone() * (self.s2_lsb.clone() - one.clone()));
        for value in [
            self.sig_id.clone(),
            self.cert_id.clone(),
            self.s1_lsb.clone(),
            self.s2_lsb.clone(),
        ] {
            eval.add_constraint((one.clone() - self.active.clone()) * value);
        }
        self.operand.add_constraints(eval, &self.active, one);
    }
}

pub(crate) fn gen_lsb_correction_operand_preprocessed_trace(
    claim: &FakeGlvLsbCorrectionOperandProofClaim,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &lsb_correction_operand_zero_column_id() {
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

pub(crate) fn gen_lsb_correction_operand_provider_base_trace(
    cert_inputs: &CertScalarInputClaim,
    fake_glv_scalars: &FakeGlvScalarHintClaim,
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let rows =
        lsb_correction_operand_providers(cert_inputs, fake_glv_scalars, prepared, selectors)?;
    rows_to_base_trace(rows, log_size)
}

pub(crate) fn gen_lsb_correction_operand_consumer_base_trace(
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let rows = lsb_correction_operand_consumers(selectors, chain)?;
    rows_to_base_trace(rows, log_size)
}

fn rows_to_base_trace(
    mut rows: Vec<[M31; FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS]>,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    if rows.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: rows.len(),
            domain: padded_rows,
        });
    }
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn lsb_correction_operand_providers(
    cert_inputs: &CertScalarInputClaim,
    fake_glv_scalars: &FakeGlvScalarHintClaim,
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
) -> Result<Vec<[M31; FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS]>, FakeGlvChainError> {
    if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
        || cert_inputs.rows.len() != selectors.rows.len()
        || cert_inputs.rows.len() != prepared.certs.len()
    {
        return Err(FakeGlvChainError::RowCountMismatch {
            certs: cert_inputs.rows.len(),
            fake_glv: fake_glv_scalars.rows.len(),
            selectors: selectors.rows.len(),
            tables: prepared.certs.len(),
        });
    }

    let mut rows = Vec::new();
    for (((cert, fake_glv), selector), table) in cert_inputs
        .rows
        .iter()
        .zip(&fake_glv_scalars.rows)
        .zip(&selectors.rows)
        .zip(&prepared.certs)
    {
        if selector.cert_active.0 == 0 {
            continue;
        }
        let operand = expected_lsb_correction_operand(cert, fake_glv, selector, table)?;
        rows.push(lsb_correction_operand_trace_values(
            selector.sig_id,
            selector.cert_id,
            selector.s1_lsb,
            selector.s2_lsb,
            &operand,
        ));
    }
    Ok(rows)
}

fn lsb_correction_operand_consumers(
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
) -> Result<Vec<[M31; FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS]>, FakeGlvChainError> {
    if chain.certs.len() != selectors.rows.len() {
        return Err(FakeGlvChainError::RowCountMismatch {
            certs: chain.certs.len(),
            fake_glv: chain.certs.len(),
            selectors: selectors.rows.len(),
            tables: selectors.rows.len(),
        });
    }
    let mut rows = Vec::new();
    for (cert, selector) in chain.certs.iter().zip(&selectors.rows) {
        for row in &cert.rows {
            if row.kind != FakeGlvChainRowKind::LsbCorrection {
                continue;
            }
            rows.push(lsb_correction_operand_trace_values(
                row.sig_id,
                row.cert_id,
                selector.s1_lsb,
                selector.s2_lsb,
                &row.operand,
            ));
        }
    }
    Ok(rows)
}

fn expected_lsb_correction_operand(
    cert: &crate::scalar::cert_bind::CertScalarInputRow,
    fake_glv: &crate::scalar::fake_glv_scalar::FakeGlvScalarHintRow,
    selector: &crate::scalar::fake_glv_selector::FakeGlvSelectorRow,
    table: &crate::scalar::prepared_table::PreparedTableCert,
) -> Result<PreparedAffinePoint, FakeGlvChainError> {
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    match (selector.s1_lsb.0, selector.s2_lsb.0) {
        (1, 1) => Ok(PreparedAffinePoint::infinity()),
        (0, 1) => Ok(negate_prepared(&p)),
        (1, 0) => {
            let h = scalar_mul(
                &cert.scalar.to_u256(),
                &p.to_option()
                    .expect("active certificate base point is finite"),
            )
            .ok_or(FakeGlvChainError::MissingHintPoint {
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            })?;
            let r = match fake_glv.hint.s2_sign_bit.0 {
                0 => PreparedAffinePoint::from_affine(h),
                1 => negate_prepared(&PreparedAffinePoint::from_affine(h)),
                actual => {
                    return Err(FakeGlvChainError::NonBooleanFlag {
                        field: "s2_sign_bit",
                        actual,
                    })
                }
            };
            Ok(negate_prepared(&r))
        }
        (0, 0) => Ok(negate_prepared(&table.base[2])),
        (actual, _) if actual > 1 => Err(FakeGlvChainError::NonBooleanFlag {
            field: "s1_lsb",
            actual,
        }),
        (_, actual) => Err(FakeGlvChainError::NonBooleanFlag {
            field: "s2_lsb",
            actual,
        }),
    }
}

fn lsb_correction_operand_trace_values(
    sig_id: M31,
    cert_id: M31,
    s1_lsb: M31,
    s2_lsb: M31,
    operand: &PreparedAffinePoint,
) -> [M31; FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[1] = sig_id;
    values[2] = cert_id;
    values[3] = s1_lsb;
    values[4] = s2_lsb;
    values[5..].copy_from_slice(&prepared_table_ec_point_values(operand));
    values
}

fn negate_prepared(point: &PreparedAffinePoint) -> PreparedAffinePoint {
    if point.inf.0 == 1 {
        return PreparedAffinePoint::infinity();
    }
    PreparedAffinePoint {
        x: point.x.clone(),
        y: P256M31BigInt::from_u256(
            &sub_mod_witness(
                &U256::from_le_u64s(&P256_MODULUS),
                &point.y.to_u256(),
                &U256::from_le_u64s(&P256_MODULUS),
            )
            .result
            .to_u256(),
        ),
        inf: M31::from_u32_unchecked(0),
    }
}

pub(crate) fn gen_lsb_correction_operand_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvLsbCorrectionOperandRelation,
    provider: bool,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(base.len(), FAKE_GLV_LSB_CORRECTION_OPERAND_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let values = lsb_correction_operand_packed_relation_values(base, vec_row);
        let numerator = PackedQM31::from(base[0].data[vec_row]);
        let numerator = if provider { -numerator } else { numerator };
        (numerator, relation.combine(&values))
    });
    logup.finalize_last()
}

fn lsb_correction_operand_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_LSB_CORRECTION_OPERAND_RELATION_ARITY] {
    core::array::from_fn(|index| base[index + 1].data[vec_row])
}

fn lsb_correction_operand_relation_values<F: Clone>(
    header: &[F; 4],
    operand: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
) -> [F; FAKE_GLV_LSB_CORRECTION_OPERAND_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0..=3 => header[index].clone(),
        4..=44 => operand[index - 4].clone(),
        _ => unreachable!("fake-GLV LSB correction operand relation index is in range"),
    })
}

fn lsb_correction_row_count(chain: &FakeGlvChainClaim) -> usize {
    chain
        .certs
        .iter()
        .flat_map(|cert| cert.rows.iter())
        .filter(|row| row.kind == FakeGlvChainRowKind::LsbCorrection)
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

fn lsb_correction_operand_zero_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: LSB_CORRECTION_OPERAND_ZERO_COLUMN.into(),
    }
}
