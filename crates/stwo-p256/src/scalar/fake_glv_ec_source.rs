use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec},
    poly::circle::CanonicCoset,
    proof::StarkProof,
    verifier::verify,
    ColumnVec,
};
use stwo::prover::{
    backend::{
        simd::{
            m31::{PackedM31, LOG_N_LANES},
            qm31::PackedQM31,
            SimdBackend,
        },
        BackendForChannel,
    },
    poly::circle::PolyOps,
    prove, CommitmentSchemeProver, ComponentProver,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

use crate::projective::{ProjectiveEcOp, ProjectiveEcTraceClaim};
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
pub const FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_PRIMITIVE_EC_ROW_RELATION_ARITY;

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
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvProjectiveSourceInteractionClaim {
    pub provider_claimed_sum: SecureField,
    pub consumer_claimed_sum: SecureField,
}

impl FakeGlvProjectiveSourceInteractionClaim {
    pub fn zero() -> Self {
        Self {
            provider_claimed_sum: secure_zero(),
            consumer_claimed_sum: secure_zero(),
        }
    }

    pub fn total(self) -> SecureField {
        self.provider_claimed_sum + self.consumer_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.provider_claimed_sum, self.consumer_claimed_sum]);
    }
}

#[derive(Clone, Debug)]
pub struct FakeGlvProjectiveSourceProof<
    H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted,
> {
    pub claim: FakeGlvProjectiveSourceProofClaim,
    pub interaction_claim: FakeGlvProjectiveSourceInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

pub struct FakeGlvProjectiveSourceComponents {
    pub provider: FakeGlvPrimitiveEcRowProviderComponent,
    pub consumer: FakeGlvProjectiveSourceComponent,
}

impl FakeGlvProjectiveSourceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        source_offset: u32,
        interaction_claim: &FakeGlvProjectiveSourceInteractionClaim,
        relation: &FakeGlvPrimitiveEcRowRelation,
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
                },
                interaction_claim.consumer_claimed_sum,
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

        let relation_values = fake_glv_primitive_ec_row_relation_values(
            &[source_index, sig_id, cert_id, op],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(active),
            &relation_values,
        ));
        eval.finalize_logup();
        eval
    }
}

pub fn prove_fake_glv_projective_source_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    fake_glv: &FakeGlvPrimitiveEcTraceClaim,
    projective: &ProjectiveEcTraceClaim,
    source_offset: usize,
    config: PcsConfig,
) -> Result<FakeGlvProjectiveSourceProof<MC::H>, FakeGlvChainError>
where
    SimdBackend: BackendForChannel<MC>,
{
    fake_glv.verify()?;
    projective
        .verify()
        .map_err(|_| FakeGlvChainError::ProjectiveSourceInvalid)?;
    let claim = FakeGlvProjectiveSourceProofClaim::from_fake_glv_trace(fake_glv, source_offset);
    let ids = claim.preprocessed_column_ids();
    let max_constraint_log_degree_bound = claim.max_constraint_log_degree_bound(&ids);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            config
                .lifting_log_size
                .unwrap_or(max_constraint_log_degree_bound + config.fri_config.log_blowup_factor),
        )
        .circle_domain()
        .half_coset,
    );

    let mut channel = MC::C::default();
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, MC>::new(config, &twiddles);
    commitment_scheme.set_store_polynomials_coefficients();

    let preprocessed = gen_fake_glv_primitive_ec_preprocessed_trace(claim.log_size, &ids)?;
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let provider_base =
        gen_fake_glv_primitive_ec_source_base_trace(fake_glv, source_offset, claim.log_size)?;
    let consumer_base = gen_fake_glv_projective_source_base_trace(
        fake_glv,
        projective,
        source_offset,
        claim.log_size,
    )?;
    let mut base = provider_base.clone();
    base.extend(consumer_base.clone());
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relation = FakeGlvPrimitiveEcRowRelation::draw(&mut channel);
    let (provider_interaction, provider_claim) = gen_fake_glv_primitive_ec_source_interaction_trace(
        &provider_base,
        &relation,
        RelationMultiplicity::Provider,
    );
    let (consumer_interaction, consumer_claim) = gen_fake_glv_primitive_ec_source_interaction_trace(
        &consumer_base,
        &relation,
        RelationMultiplicity::Consumer,
    );
    let interaction_claim = FakeGlvProjectiveSourceInteractionClaim {
        provider_claimed_sum: provider_claim.claimed_sum,
        consumer_claimed_sum: consumer_claim.claimed_sum,
    };
    if interaction_claim.total() != secure_zero() {
        return Err(FakeGlvChainError::RelationImbalance {
            relation: "FakeGlvProjectiveSource",
        });
    }
    interaction_claim.mix_into(&mut channel);
    let mut interaction = provider_interaction;
    interaction.extend(consumer_interaction);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = FakeGlvProjectiveSourceComponents::new(
        &mut allocator,
        claim.log_size,
        claim.source_offset,
        &interaction_claim,
        &relation,
    );
    assert_eq!(
        commitment_scheme
            .polynomials()
            .as_cols_ref()
            .map_cols(|column| column.evals.domain.log_size() - config.fri_config.log_blowup_factor)
            .0,
        components.trace_log_degree_bounds().0
    );
    let stark_proof = prove(
        &components.component_provers(),
        &mut channel,
        commitment_scheme,
    )
    .map_err(|_| FakeGlvChainError::ProofLayer)?;

    Ok(FakeGlvProjectiveSourceProof {
        claim,
        interaction_claim,
        stark_proof,
    })
}

pub fn verify_fake_glv_projective_source_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    proof: FakeGlvProjectiveSourceProof<MC::H>,
) -> Result<(), FakeGlvChainError> {
    let FakeGlvProjectiveSourceProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;

    if interaction_claim.total() != secure_zero() {
        return Err(FakeGlvChainError::RelationImbalance {
            relation: "FakeGlvProjectiveSource",
        });
    }

    let ids = claim.preprocessed_column_ids();
    let log_degree_bounds = claim.trace_log_degree_bounds(&ids);
    let mut channel = MC::C::default();
    let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(stark_proof.config);

    commitment_scheme.commit(
        stark_proof.commitments[0],
        &log_degree_bounds[0],
        &mut channel,
    );

    claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[1],
        &log_degree_bounds[1],
        &mut channel,
    );

    let relation = FakeGlvPrimitiveEcRowRelation::draw(&mut channel);

    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = FakeGlvProjectiveSourceComponents::new(
        &mut allocator,
        claim.log_size,
        claim.source_offset,
        &interaction_claim,
        &relation,
    );
    verify(
        &components.components(),
        &mut channel,
        commitment_scheme,
        stark_proof,
    )
    .map_err(|_| FakeGlvChainError::ProofLayer)
}

fn gen_fake_glv_primitive_ec_preprocessed_trace(
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

fn gen_fake_glv_primitive_ec_source_base_trace(
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

fn gen_fake_glv_projective_source_base_trace(
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
        [M31::from_u32_unchecked(0); FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn gen_fake_glv_primitive_ec_source_interaction_trace(
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
    debug_assert_eq!(column, FAKE_GLV_PRIMITIVE_EC_SOURCE_TRACE_COLUMNS);
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

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FakeGlvPrimitiveEcRowInteractionClaim {
    claimed_sum: SecureField,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RelationMultiplicity {
    Provider,
    Consumer,
}
