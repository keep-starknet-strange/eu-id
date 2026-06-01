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
            m31::{LOG_N_LANES, N_LANES},
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

use crate::scalar::fake_glv_chain::{
    FakeGlvChainClaim, FakeGlvChainError, FakeGlvChainRow, FakeGlvChainRowKind,
    FakeGlvPrimitiveEcOp, FakeGlvPrimitiveEcRow, FakeGlvPrimitiveEcTraceClaim,
};
use crate::scalar::prepared_table::{
    prepared_table_ec_point_values, PreparedAffinePoint, PreparedTableEcEvalPoint,
    PREPARED_TABLE_EC_OP_DOUBLE, PREPARED_TABLE_EC_OP_MIXED_ADD, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

relation!(
    FakeGlvChainPrimitiveExpansionRelation,
    FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY
);

pub type FakeGlvChainExpansionComponent = FrameworkComponent<FakeGlvChainExpansionEval>;
pub type FakeGlvPrimitiveExpansionConsumerComponent =
    FrameworkComponent<FakeGlvPrimitiveExpansionConsumerEval>;

pub const FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY: usize =
    4 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;
const FAKE_GLV_CHAIN_EXPANSION_POINTS: usize = 5;
pub const FAKE_GLV_CHAIN_EXPANSION_TRACE_COLUMNS: usize =
    5 + FAKE_GLV_CHAIN_EXPANSION_POINTS * PREPARED_TABLE_EC_POINT_COLUMNS;
pub const FAKE_GLV_PRIMITIVE_EXPANSION_CONSUMER_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY;

const FAKE_GLV_PRIMITIVE_EXPANSION_ROW_INDEX_COLUMN: &str =
    "p256_fake_glv_primitive_expansion_row_index";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvChainExpansionProofClaim {
    pub expansion_log_size: u32,
    pub primitive_log_size: u32,
    pub source_offset: u32,
}

impl FakeGlvChainExpansionProofClaim {
    pub fn from_claims(
        chain: &FakeGlvChainClaim,
        primitive: &FakeGlvPrimitiveEcTraceClaim,
        source_offset: usize,
    ) -> Self {
        Self {
            expansion_log_size: padded_log_size(primitive_producing_chain_row_count(chain)),
            primitive_log_size: padded_log_size(primitive.rows.len()),
            source_offset: source_offset as u32,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.expansion_log_size as u64);
        channel.mix_u64(self.primitive_log_size as u64);
        channel.mix_u64(self.source_offset as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvChainExpansionComponents::new(
            &mut allocator,
            *self,
            &FakeGlvChainExpansionInteractionClaim::zero(),
            &FakeGlvChainPrimitiveExpansionRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvChainExpansionComponents::new(
            &mut allocator,
            *self,
            &FakeGlvChainExpansionInteractionClaim::zero(),
            &FakeGlvChainPrimitiveExpansionRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvChainExpansionComponents::new(
            &mut allocator,
            *self,
            &FakeGlvChainExpansionInteractionClaim::zero(),
            &FakeGlvChainPrimitiveExpansionRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvChainExpansionInteractionClaim {
    pub expansion_claimed_sum: SecureField,
    pub primitive_claimed_sum: SecureField,
}

impl FakeGlvChainExpansionInteractionClaim {
    pub fn zero() -> Self {
        Self {
            expansion_claimed_sum: secure_zero(),
            primitive_claimed_sum: secure_zero(),
        }
    }

    pub fn total(self) -> SecureField {
        self.expansion_claimed_sum + self.primitive_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.expansion_claimed_sum, self.primitive_claimed_sum]);
    }
}

#[derive(Clone, Debug)]
pub struct FakeGlvChainExpansionProof<H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>
{
    pub claim: FakeGlvChainExpansionProofClaim,
    pub interaction_claim: FakeGlvChainExpansionInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

pub struct FakeGlvChainExpansionComponents {
    pub expansion: FakeGlvChainExpansionComponent,
    pub primitive: FakeGlvPrimitiveExpansionConsumerComponent,
}

impl FakeGlvChainExpansionComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvChainExpansionProofClaim,
        interaction_claim: &FakeGlvChainExpansionInteractionClaim,
        relation: &FakeGlvChainPrimitiveExpansionRelation,
    ) -> Self {
        Self {
            expansion: FakeGlvChainExpansionComponent::new(
                allocator,
                FakeGlvChainExpansionEval {
                    log_size: claim.expansion_log_size,
                    relation: relation.clone(),
                },
                interaction_claim.expansion_claimed_sum,
            ),
            primitive: FakeGlvPrimitiveExpansionConsumerComponent::new(
                allocator,
                FakeGlvPrimitiveExpansionConsumerEval {
                    log_size: claim.primitive_log_size,
                    source_offset: claim.source_offset,
                    relation: relation.clone(),
                },
                interaction_claim.primitive_claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![
            &self.expansion as &dyn Component,
            &self.primitive as &dyn Component,
        ]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.expansion as &dyn ComponentProver<SimdBackend>,
            &self.primitive as &dyn ComponentProver<SimdBackend>,
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
pub struct FakeGlvChainExpansionEval {
    pub log_size: u32,
    pub relation: FakeGlvChainPrimitiveExpansionRelation,
}

impl FrameworkEval for FakeGlvChainExpansionEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let triple = eval.next_trace_mask();
        let primitive_start_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let acc_before = PreparedTableEcEvalPoint::read(&mut eval);
        let operand = PreparedTableEcEvalPoint::read(&mut eval);
        let acc_after = PreparedTableEcEvalPoint::read(&mut eval);
        let doubled = PreparedTableEcEvalPoint::read(&mut eval);
        let quadrupled = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));
        let double = E::F::from(M31::from_u32_unchecked(PREPARED_TABLE_EC_OP_DOUBLE));
        let mixed_add = E::F::from(M31::from_u32_unchecked(PREPARED_TABLE_EC_OP_MIXED_ADD));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(triple.clone() * (triple.clone() - one.clone()));
        eval.add_constraint((one.clone() - active.clone()) * triple.clone());
        for value in [
            primitive_start_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }
        acc_before.add_constraints(&mut eval, &active, &one);
        operand.add_constraints(&mut eval, &active, &one);
        acc_after.add_constraints(&mut eval, &active, &one);
        doubled.add_constraints(&mut eval, &triple, &one);
        quadrupled.add_constraints(&mut eval, &triple, &one);

        let single = active.clone() - triple.clone();
        let tuple0 = selected_first_tuple_values(FirstTupleSelection {
            primitive_index: primitive_start_index.clone(),
            sig_id: sig_id.clone(),
            cert_id: cert_id.clone(),
            triple: triple.clone(),
            single: single.clone(),
            double: double.clone(),
            mixed_add: mixed_add.clone(),
            acc_before: &acc_before,
            operand: &operand,
            acc_after: &acc_after,
            doubled: &doubled,
        });
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(active.clone()),
            &tuple0,
        ));

        let tuple1 = fake_glv_chain_primitive_relation_values(
            &[
                primitive_start_index.clone() + one.clone(),
                sig_id.clone(),
                cert_id.clone(),
                double,
            ],
            &doubled.relation_values(),
            &infinity_relation_values(),
            &quadrupled.relation_values(),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(triple.clone()),
            &tuple1,
        ));

        let tuple2 = fake_glv_chain_primitive_relation_values(
            &[
                primitive_start_index + E::F::from(M31::from_u32_unchecked(2)),
                sig_id,
                cert_id,
                mixed_add,
            ],
            &quadrupled.relation_values(),
            &operand.relation_values(),
            &acc_after.relation_values(),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(triple),
            &tuple2,
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct FakeGlvPrimitiveExpansionConsumerEval {
    pub log_size: u32,
    pub source_offset: u32,
    pub relation: FakeGlvChainPrimitiveExpansionRelation,
}

impl FrameworkEval for FakeGlvPrimitiveExpansionConsumerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let row_index =
            eval.get_preprocessed_column(fake_glv_primitive_expansion_row_index_column_id());
        let active = eval.next_trace_mask();
        let primitive_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let op = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));
        let source_offset = E::F::from(M31::from_u32_unchecked(self.source_offset));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(active.clone() * (primitive_index.clone() - row_index - source_offset));
        eval.add_constraint(op.clone() * (op.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);
        for value in [
            primitive_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = fake_glv_chain_primitive_relation_values(
            &[primitive_index, sig_id, cert_id, op],
            &lhs.relation_values(),
            &rhs.relation_values(),
            &output.relation_values(),
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

pub fn prove_fake_glv_chain_expansion_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    chain: &FakeGlvChainClaim,
    primitive: &FakeGlvPrimitiveEcTraceClaim,
    source_offset: usize,
    config: PcsConfig,
) -> Result<FakeGlvChainExpansionProof<MC::H>, FakeGlvChainError>
where
    SimdBackend: BackendForChannel<MC>,
{
    chain.verify()?;
    primitive.verify()?;
    let claim = FakeGlvChainExpansionProofClaim::from_claims(chain, primitive, source_offset);
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

    let preprocessed = gen_fake_glv_chain_expansion_preprocessed_trace(claim, &ids)?;
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let expansion_base = gen_fake_glv_chain_expansion_base_trace(
        chain,
        primitive,
        source_offset,
        claim.expansion_log_size,
    )?;
    let primitive_base = gen_fake_glv_primitive_expansion_consumer_base_trace(
        primitive,
        source_offset,
        claim.primitive_log_size,
    )?;
    let mut base = expansion_base.clone();
    base.extend(primitive_base.clone());
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relation = FakeGlvChainPrimitiveExpansionRelation::draw(&mut channel);
    let (expansion_interaction, expansion_claimed_sum) =
        gen_fake_glv_chain_expansion_interaction_trace(&expansion_base, &relation);
    let (primitive_interaction, primitive_claimed_sum) =
        gen_fake_glv_primitive_expansion_consumer_interaction_trace(&primitive_base, &relation);
    let interaction_claim = FakeGlvChainExpansionInteractionClaim {
        expansion_claimed_sum,
        primitive_claimed_sum,
    };
    if interaction_claim.total() != secure_zero() {
        return Err(FakeGlvChainError::RelationImbalance {
            relation: "FakeGlvChainExpansion",
        });
    }
    interaction_claim.mix_into(&mut channel);
    let mut interaction = expansion_interaction;
    interaction.extend(primitive_interaction);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        FakeGlvChainExpansionComponents::new(&mut allocator, claim, &interaction_claim, &relation);
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

    Ok(FakeGlvChainExpansionProof {
        claim,
        interaction_claim,
        stark_proof,
    })
}

pub fn verify_fake_glv_chain_expansion_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    proof: FakeGlvChainExpansionProof<MC::H>,
) -> Result<(), FakeGlvChainError> {
    let FakeGlvChainExpansionProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;

    if interaction_claim.total() != secure_zero() {
        return Err(FakeGlvChainError::RelationImbalance {
            relation: "FakeGlvChainExpansion",
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

    let relation = FakeGlvChainPrimitiveExpansionRelation::draw(&mut channel);

    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        FakeGlvChainExpansionComponents::new(&mut allocator, claim, &interaction_claim, &relation);
    verify(
        &components.components(),
        &mut channel,
        commitment_scheme,
        stark_proof,
    )
    .map_err(|_| FakeGlvChainError::ProofLayer)
}

fn gen_fake_glv_chain_expansion_preprocessed_trace(
    claim: FakeGlvChainExpansionProofClaim,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &fake_glv_primitive_expansion_row_index_column_id() {
                Ok(m31_column_eval(
                    claim.primitive_log_size,
                    (0..(1usize << claim.primitive_log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
            } else {
                Err(FakeGlvChainError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

fn gen_fake_glv_chain_expansion_base_trace(
    chain: &FakeGlvChainClaim,
    primitive: &FakeGlvPrimitiveEcTraceClaim,
    source_offset: usize,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    let producing_rows = primitive_producing_chain_row_count(chain);
    if producing_rows > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: producing_rows,
            domain: padded_rows,
        });
    }

    let mut primitive_index = 0usize;
    let mut rows = Vec::with_capacity(producing_rows);
    for row in chain.certs.iter().flat_map(|cert| cert.rows.iter()) {
        match row.kind {
            FakeGlvChainRowKind::MsbInit => {}
            FakeGlvChainRowKind::ChainStep(_) | FakeGlvChainRowKind::Table16Step => {
                let doubled = primitive
                    .rows
                    .get(primitive_index)
                    .ok_or(FakeGlvChainError::PrimitiveTraceMismatch {
                        expected: primitive_index + 1,
                        actual: primitive.rows.len(),
                    })?
                    .output
                    .clone();
                let quadrupled = primitive
                    .rows
                    .get(primitive_index + 1)
                    .ok_or(FakeGlvChainError::PrimitiveTraceMismatch {
                        expected: primitive_index + 2,
                        actual: primitive.rows.len(),
                    })?
                    .output
                    .clone();
                rows.push(fake_glv_chain_expansion_trace_values(
                    source_offset + primitive_index,
                    true,
                    row,
                    Some(&doubled),
                    Some(&quadrupled),
                ));
                primitive_index += 3;
            }
            FakeGlvChainRowKind::LsbCorrection => {
                rows.push(fake_glv_chain_expansion_trace_values(
                    source_offset + primitive_index,
                    false,
                    row,
                    None,
                    None,
                ));
                primitive_index += 1;
            }
        }
    }
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_CHAIN_EXPANSION_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn gen_fake_glv_primitive_expansion_consumer_base_trace(
    primitive: &FakeGlvPrimitiveEcTraceClaim,
    source_offset: usize,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let padded_rows = 1usize << log_size;
    if primitive.rows.len() > padded_rows {
        return Err(FakeGlvChainError::EcTraceRowsExceedDomain {
            rows: primitive.rows.len(),
            domain: padded_rows,
        });
    }
    let mut rows = primitive
        .rows
        .iter()
        .enumerate()
        .map(|(index, row)| {
            fake_glv_primitive_expansion_consumer_trace_values(source_offset + index, row)
        })
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); FAKE_GLV_PRIMITIVE_EXPANSION_CONSUMER_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn gen_fake_glv_chain_expansion_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvChainPrimitiveExpansionRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(base.len(), FAKE_GLV_CHAIN_EXPANSION_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    for slot in 0..3 {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let numerator = chain_expansion_slot_numerator(base, vec_row, lane, slot);
                let values = chain_expansion_slot_relation_values(base, vec_row, lane, slot);
                numerators[lane] = numerator;
                denominators[lane] = relation.combine(&values);
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    logup.finalize_last()
}

fn gen_fake_glv_primitive_expansion_consumer_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvChainPrimitiveExpansionRelation,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(
        base.len(),
        FAKE_GLV_PRIMITIVE_EXPANSION_CONSUMER_TRACE_COLUMNS
    );
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let mut numerators = [secure_zero(); N_LANES];
        let mut denominators = [secure_one(); N_LANES];
        for lane in 0..N_LANES {
            let active = lane_value(base, 0, vec_row, lane);
            let values = primitive_expansion_consumer_relation_values(base, vec_row, lane);
            numerators[lane] = SecureField::from(active);
            denominators[lane] = relation.combine(&values);
        }
        col.write_frac(
            vec_row,
            PackedQM31::from_array(numerators),
            PackedQM31::from_array(denominators),
        );
    }
    col.finalize_col();
    logup.finalize_last()
}

fn fake_glv_chain_expansion_trace_values(
    primitive_start_index: usize,
    triple: bool,
    row: &FakeGlvChainRow,
    doubled: Option<&PreparedAffinePoint>,
    quadrupled: Option<&PreparedAffinePoint>,
) -> [M31; FAKE_GLV_CHAIN_EXPANSION_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_CHAIN_EXPANSION_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(u32::from(triple));
    column += 1;
    values[column] = M31::from_u32_unchecked(primitive_start_index as u32);
    column += 1;
    values[column] = row.sig_id;
    column += 1;
    values[column] = row.cert_id;
    column += 1;
    for value in prepared_table_ec_point_values(&row.acc_before) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.operand) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&row.acc_after) {
        values[column] = value;
        column += 1;
    }
    write_point_or_zero(&mut values, &mut column, doubled);
    write_point_or_zero(&mut values, &mut column, quadrupled);
    debug_assert_eq!(column, FAKE_GLV_CHAIN_EXPANSION_TRACE_COLUMNS);
    values
}

fn fake_glv_primitive_expansion_consumer_trace_values(
    primitive_index: usize,
    row: &FakeGlvPrimitiveEcRow,
) -> [M31; FAKE_GLV_PRIMITIVE_EXPANSION_CONSUMER_TRACE_COLUMNS] {
    let mut values =
        [M31::from_u32_unchecked(0); FAKE_GLV_PRIMITIVE_EXPANSION_CONSUMER_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(primitive_index as u32);
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
    debug_assert_eq!(column, FAKE_GLV_PRIMITIVE_EXPANSION_CONSUMER_TRACE_COLUMNS);
    values
}

struct FirstTupleSelection<'a, F> {
    primitive_index: F,
    sig_id: F,
    cert_id: F,
    triple: F,
    single: F,
    double: F,
    mixed_add: F,
    acc_before: &'a PreparedTableEcEvalPoint<F>,
    operand: &'a PreparedTableEcEvalPoint<F>,
    acc_after: &'a PreparedTableEcEvalPoint<F>,
    doubled: &'a PreparedTableEcEvalPoint<F>,
}

fn selected_first_tuple_values<F>(
    selection: FirstTupleSelection<'_, F>,
) -> [F; FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY]
where
    F: Clone + From<M31> + core::ops::Add<Output = F> + core::ops::Mul<Output = F>,
{
    let acc_before = selection.acc_before.relation_values();
    let operand = selection.operand.relation_values();
    let acc_after = selection.acc_after.relation_values();
    let doubled = selection.doubled.relation_values();
    let lhs = scale_point_relation_values(
        &acc_before,
        active_sum(selection.triple.clone(), selection.single.clone()),
    );
    let rhs = select_point_relation_values(
        &infinity_relation_values(),
        &operand,
        &selection.triple,
        &selection.single,
    );
    let output =
        select_point_relation_values(&doubled, &acc_after, &selection.triple, &selection.single);
    let op = selection.triple * selection.double + selection.single * selection.mixed_add;
    fake_glv_chain_primitive_relation_values(
        &[
            selection.primitive_index,
            selection.sig_id,
            selection.cert_id,
            op,
        ],
        &lhs,
        &rhs,
        &output,
    )
}

fn fake_glv_chain_primitive_relation_values<F: Clone>(
    header: &[F; 4],
    lhs: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
    rhs: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
    output: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
) -> [F; FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0..=3 => header[index].clone(),
        4..=44 => lhs[index - 4].clone(),
        45..=85 => rhs[index - 45].clone(),
        86..=126 => output[index - 86].clone(),
        _ => unreachable!("fake-GLV chain primitive relation index is in range"),
    })
}

fn select_point_relation_values<F>(
    when_triple: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
    when_single: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
    triple: &F,
    single: &F,
) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS]
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Mul<Output = F>,
{
    core::array::from_fn(|index| {
        triple.clone() * when_triple[index].clone() + single.clone() * when_single[index].clone()
    })
}

fn scale_point_relation_values<F>(
    values: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
    scale: F,
) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS]
where
    F: Clone + core::ops::Mul<Output = F>,
{
    core::array::from_fn(|index| scale.clone() * values[index].clone())
}

fn active_sum<F>(triple: F, single: F) -> F
where
    F: core::ops::Add<Output = F>,
{
    triple + single
}

fn chain_expansion_slot_numerator(
    base: &[M31ColumnEval],
    vec_row: usize,
    lane: usize,
    slot: usize,
) -> SecureField {
    let value = match slot {
        0 => lane_value(base, 0, vec_row, lane),
        1 | 2 => lane_value(base, 1, vec_row, lane),
        _ => unreachable!("fake-GLV expansion slot is in range"),
    };
    -SecureField::from(value)
}

fn chain_expansion_slot_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
    lane: usize,
    slot: usize,
) -> [M31; FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY] {
    let active = lane_value(base, 0, vec_row, lane);
    let triple = lane_value(base, 1, vec_row, lane);
    let single = active - triple;
    let primitive_start_index = lane_value(base, 2, vec_row, lane);
    let sig_id = lane_value(base, 3, vec_row, lane);
    let cert_id = lane_value(base, 4, vec_row, lane);
    let acc_before = point_relation_values_from_base(base, 5, vec_row, lane);
    let operand = point_relation_values_from_base(base, 46, vec_row, lane);
    let acc_after = point_relation_values_from_base(base, 87, vec_row, lane);
    let doubled = point_relation_values_from_base(base, 128, vec_row, lane);
    let quadrupled = point_relation_values_from_base(base, 169, vec_row, lane);

    match slot {
        0 => {
            let lhs = scale_point_relation_values(&acc_before, active);
            let rhs = select_point_relation_values(
                &infinity_relation_values(),
                &operand,
                &triple,
                &single,
            );
            let output = select_point_relation_values(&doubled, &acc_after, &triple, &single);
            let op = triple * M31::from_u32_unchecked(PREPARED_TABLE_EC_OP_DOUBLE)
                + single * M31::from_u32_unchecked(PREPARED_TABLE_EC_OP_MIXED_ADD);
            fake_glv_chain_primitive_relation_values(
                &[primitive_start_index, sig_id, cert_id, op],
                &lhs,
                &rhs,
                &output,
            )
        }
        1 => fake_glv_chain_primitive_relation_values(
            &[
                M31::from_u32_unchecked(primitive_start_index.0 + 1),
                sig_id,
                cert_id,
                M31::from_u32_unchecked(PREPARED_TABLE_EC_OP_DOUBLE),
            ],
            &doubled,
            &infinity_relation_values(),
            &quadrupled,
        ),
        2 => fake_glv_chain_primitive_relation_values(
            &[
                M31::from_u32_unchecked(primitive_start_index.0 + 2),
                sig_id,
                cert_id,
                M31::from_u32_unchecked(PREPARED_TABLE_EC_OP_MIXED_ADD),
            ],
            &quadrupled,
            &operand,
            &acc_after,
        ),
        _ => unreachable!("fake-GLV expansion slot is in range"),
    }
}

fn primitive_expansion_consumer_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
    lane: usize,
) -> [M31; FAKE_GLV_CHAIN_PRIMITIVE_EXPANSION_RELATION_ARITY] {
    core::array::from_fn(|index| lane_value(base, index + 1, vec_row, lane))
}

fn point_relation_values_from_base(
    base: &[M31ColumnEval],
    start: usize,
    vec_row: usize,
    lane: usize,
) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
    core::array::from_fn(|index| lane_value(base, start + index, vec_row, lane))
}

fn lane_value(base: &[M31ColumnEval], column: usize, vec_row: usize, lane: usize) -> M31 {
    base[column].data[vec_row].to_array()[lane]
}

fn write_point_or_zero<const N: usize>(
    values: &mut [M31; N],
    column: &mut usize,
    point: Option<&PreparedAffinePoint>,
) {
    let point_values = point
        .map(prepared_table_ec_point_values)
        .unwrap_or([M31::from_u32_unchecked(0); PREPARED_TABLE_EC_POINT_COLUMNS]);
    for value in point_values {
        values[*column] = value;
        *column += 1;
    }
}

fn infinity_relation_values<F>() -> [F; PREPARED_TABLE_EC_POINT_COLUMNS]
where
    F: Clone + From<M31>,
{
    core::array::from_fn(|index| {
        if index == PREPARED_TABLE_EC_POINT_COLUMNS - 1 {
            F::from(M31::from_u32_unchecked(1))
        } else {
            F::from(M31::from_u32_unchecked(0))
        }
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

fn fake_glv_primitive_expansion_row_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: FAKE_GLV_PRIMITIVE_EXPANSION_ROW_INDEX_COLUMN.into(),
    }
}

fn primitive_producing_chain_row_count(chain: &FakeGlvChainClaim) -> usize {
    chain
        .certs
        .iter()
        .flat_map(|cert| cert.rows.iter())
        .filter(|row| row.kind != FakeGlvChainRowKind::MsbInit)
        .count()
}

fn fake_glv_primitive_ec_op_code(op: FakeGlvPrimitiveEcOp) -> M31 {
    let code = match op {
        FakeGlvPrimitiveEcOp::Double => PREPARED_TABLE_EC_OP_DOUBLE,
        FakeGlvPrimitiveEcOp::Add => PREPARED_TABLE_EC_OP_MIXED_ADD,
    };
    M31::from_u32_unchecked(code)
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

fn secure_one() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(1))
}
