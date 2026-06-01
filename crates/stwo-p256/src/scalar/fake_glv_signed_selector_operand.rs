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

use crate::constants::P256_MODULUS;
use crate::field_ops::sub_mod_witness;
use crate::limbs::P256M31BigInt;
use crate::scalar::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError, FakeGlvChainRowKind};
use crate::scalar::fake_glv_selector::{FakeGlvSelectorClaim, FAKE_GLV_SELECTOR_CHUNKS};
use crate::scalar::fake_glv_selector_lookup::Selector16DecodeEntry;
use crate::scalar::prepared_table::{
    prepared_table_ec_point_values, PreparedAffinePoint, PreparedTableClaim,
    PreparedTableEcEvalPoint, PREPARED_TABLE_EC_POINT_COLUMNS,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::types::U256;

relation!(
    FakeGlvSignedSelectorOperandRelation,
    FAKE_GLV_SIGNED_SELECTOR_OPERAND_RELATION_ARITY
);

pub type FakeGlvSignedSelectorOperandProviderComponent =
    FrameworkComponent<FakeGlvSignedSelectorOperandProviderEval>;
pub type FakeGlvSignedSelectorOperandConsumerComponent =
    FrameworkComponent<FakeGlvSignedSelectorOperandConsumerEval>;

pub const FAKE_GLV_SIGNED_SELECTOR_OPERAND_RELATION_ARITY: usize =
    6 + PREPARED_TABLE_EC_POINT_COLUMNS;
pub const FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS: usize =
    1 + FAKE_GLV_SIGNED_SELECTOR_OPERAND_RELATION_ARITY;

const SIGNED_SELECTOR_OPERAND_ZERO_COLUMN: &str = "p256_fake_glv_signed_selector_operand_zero";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvSignedSelectorOperandProofClaim {
    pub provider_log_size: u32,
    pub consumer_log_size: u32,
}

impl FakeGlvSignedSelectorOperandProofClaim {
    pub fn from_claims(selectors: &FakeGlvSelectorClaim, chain: &FakeGlvChainClaim) -> Self {
        let active_selectors = selectors
            .rows
            .iter()
            .filter(|row| row.cert_active.0 == 1)
            .count();
        Self {
            provider_log_size: padded_log_size(active_selectors * (FAKE_GLV_SELECTOR_CHUNKS - 1)),
            consumer_log_size: padded_log_size(chain_step_row_count(chain)),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.provider_log_size as u64);
        channel.mix_u64(self.consumer_log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = FakeGlvSignedSelectorOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvSignedSelectorOperandInteractionClaim::zero(),
            &FakeGlvSignedSelectorOperandRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvSignedSelectorOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvSignedSelectorOperandInteractionClaim::zero(),
            &FakeGlvSignedSelectorOperandRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = FakeGlvSignedSelectorOperandComponents::new(
            &mut allocator,
            *self,
            &FakeGlvSignedSelectorOperandInteractionClaim::zero(),
            &FakeGlvSignedSelectorOperandRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FakeGlvSignedSelectorOperandInteractionClaim {
    pub provider_claimed_sum: SecureField,
    pub consumer_claimed_sum: SecureField,
}

impl FakeGlvSignedSelectorOperandInteractionClaim {
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
pub struct FakeGlvSignedSelectorOperandProof<
    H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted,
> {
    pub claim: FakeGlvSignedSelectorOperandProofClaim,
    pub interaction_claim: FakeGlvSignedSelectorOperandInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

pub struct FakeGlvSignedSelectorOperandComponents {
    pub provider: FakeGlvSignedSelectorOperandProviderComponent,
    pub consumer: FakeGlvSignedSelectorOperandConsumerComponent,
}

impl FakeGlvSignedSelectorOperandComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FakeGlvSignedSelectorOperandProofClaim,
        interaction_claim: &FakeGlvSignedSelectorOperandInteractionClaim,
        relation: &FakeGlvSignedSelectorOperandRelation,
    ) -> Self {
        Self {
            provider: FakeGlvSignedSelectorOperandProviderComponent::new(
                allocator,
                FakeGlvSignedSelectorOperandProviderEval {
                    log_size: claim.provider_log_size,
                    relation: relation.clone(),
                },
                interaction_claim.provider_claimed_sum,
            ),
            consumer: FakeGlvSignedSelectorOperandConsumerComponent::new(
                allocator,
                FakeGlvSignedSelectorOperandConsumerEval {
                    log_size: claim.consumer_log_size,
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
pub struct FakeGlvSignedSelectorOperandProviderEval {
    pub log_size: u32,
    pub relation: FakeGlvSignedSelectorOperandRelation,
}

impl FrameworkEval for FakeGlvSignedSelectorOperandProviderEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let zero = eval.get_preprocessed_column(signed_selector_operand_zero_column_id());
        let instance = SignedSelectorOperandEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(zero * instance.active.clone());
        instance.add_constraints(&mut eval, &one);
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(instance.active.clone()),
            &instance.relation_values(),
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct FakeGlvSignedSelectorOperandConsumerEval {
    pub log_size: u32,
    pub relation: FakeGlvSignedSelectorOperandRelation,
}

impl FrameworkEval for FakeGlvSignedSelectorOperandConsumerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let instance = SignedSelectorOperandEvalInstance::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        instance.add_constraints(&mut eval, &one);
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(instance.active.clone()),
            &instance.relation_values(),
        ));
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
struct SignedSelectorOperandEvalInstance<F> {
    active: F,
    sig_id: F,
    cert_id: F,
    chain_step: F,
    selector: F,
    base_index: F,
    neg_bit: F,
    operand: PreparedTableEcEvalPoint<F>,
}

impl<F> SignedSelectorOperandEvalInstance<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            active: eval.next_trace_mask(),
            sig_id: eval.next_trace_mask(),
            cert_id: eval.next_trace_mask(),
            chain_step: eval.next_trace_mask(),
            selector: eval.next_trace_mask(),
            base_index: eval.next_trace_mask(),
            neg_bit: eval.next_trace_mask(),
            operand: PreparedTableEcEvalPoint::read(eval),
        }
    }
}

impl<F: Clone> SignedSelectorOperandEvalInstance<F> {
    fn relation_values(&self) -> [F; FAKE_GLV_SIGNED_SELECTOR_OPERAND_RELATION_ARITY] {
        signed_selector_operand_relation_values(
            &[
                self.sig_id.clone(),
                self.cert_id.clone(),
                self.chain_step.clone(),
                self.selector.clone(),
                self.base_index.clone(),
                self.neg_bit.clone(),
            ],
            &self.operand.relation_values(),
        )
    }
}

impl<F> SignedSelectorOperandEvalInstance<F>
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
{
    fn add_constraints<E: EvalAtRow<F = F>>(&self, eval: &mut E, one: &F) {
        eval.add_constraint(self.active.clone() * (self.active.clone() - one.clone()));
        eval.add_constraint(self.neg_bit.clone() * (self.neg_bit.clone() - one.clone()));
        for value in [
            self.sig_id.clone(),
            self.cert_id.clone(),
            self.chain_step.clone(),
            self.selector.clone(),
            self.base_index.clone(),
            self.neg_bit.clone(),
        ] {
            eval.add_constraint((one.clone() - self.active.clone()) * value);
        }
        self.operand.add_constraints(eval, &self.active, one);
    }
}

pub fn prove_fake_glv_signed_selector_operand_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
    config: PcsConfig,
) -> Result<FakeGlvSignedSelectorOperandProof<MC::H>, FakeGlvChainError>
where
    SimdBackend: BackendForChannel<MC>,
{
    prepared
        .verify()
        .map_err(FakeGlvChainError::PreparedPoint)?;
    chain.verify()?;
    let claim = FakeGlvSignedSelectorOperandProofClaim::from_claims(selectors, chain);
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

    let preprocessed = gen_signed_selector_operand_preprocessed_trace(&claim, &ids)?;
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let provider_base = gen_signed_selector_operand_provider_base_trace(
        prepared,
        selectors,
        claim.provider_log_size,
    )?;
    let consumer_base =
        gen_signed_selector_operand_consumer_base_trace(selectors, chain, claim.consumer_log_size)?;
    let mut base = provider_base.clone();
    base.extend(consumer_base.clone());
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relation = FakeGlvSignedSelectorOperandRelation::draw(&mut channel);
    let (provider_interaction, provider_claimed_sum) =
        gen_signed_selector_operand_interaction_trace(&provider_base, &relation, true);
    let (consumer_interaction, consumer_claimed_sum) =
        gen_signed_selector_operand_interaction_trace(&consumer_base, &relation, false);
    let interaction_claim = FakeGlvSignedSelectorOperandInteractionClaim {
        provider_claimed_sum,
        consumer_claimed_sum,
    };
    if interaction_claim.total() != secure_zero() {
        return Err(FakeGlvChainError::RelationImbalance {
            relation: "FakeGlvSignedSelectorOperand",
        });
    }
    interaction_claim.mix_into(&mut channel);
    let mut interaction = provider_interaction;
    interaction.extend(consumer_interaction);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = FakeGlvSignedSelectorOperandComponents::new(
        &mut allocator,
        claim,
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

    Ok(FakeGlvSignedSelectorOperandProof {
        claim,
        interaction_claim,
        stark_proof,
    })
}

pub fn verify_fake_glv_signed_selector_operand_proof_slice<
    MC: stwo::core::channel::MerkleChannel,
>(
    proof: FakeGlvSignedSelectorOperandProof<MC::H>,
) -> Result<(), FakeGlvChainError> {
    let FakeGlvSignedSelectorOperandProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;
    if interaction_claim.total() != secure_zero() {
        return Err(FakeGlvChainError::RelationImbalance {
            relation: "FakeGlvSignedSelectorOperand",
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
    let relation = FakeGlvSignedSelectorOperandRelation::draw(&mut channel);
    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = FakeGlvSignedSelectorOperandComponents::new(
        &mut allocator,
        claim,
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

pub(crate) fn gen_signed_selector_operand_preprocessed_trace(
    claim: &FakeGlvSignedSelectorOperandProofClaim,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    ids.iter()
        .map(|id| {
            if id == &signed_selector_operand_zero_column_id() {
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

pub(crate) fn gen_signed_selector_operand_provider_base_trace(
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let rows = signed_selector_operand_providers(prepared, selectors)?;
    rows_to_base_trace(rows, log_size)
}

pub(crate) fn gen_signed_selector_operand_consumer_base_trace(
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, FakeGlvChainError> {
    let rows = signed_selector_operand_consumers(selectors, chain)?;
    rows_to_base_trace(rows, log_size)
}

fn rows_to_base_trace(
    mut rows: Vec<[M31; FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS]>,
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
        [M31::from_u32_unchecked(0); FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn signed_selector_operand_providers(
    prepared: &PreparedTableClaim,
    selectors: &FakeGlvSelectorClaim,
) -> Result<Vec<[M31; FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS]>, FakeGlvChainError> {
    let mut rows = Vec::new();
    for selector_row in selectors.rows.iter().filter(|row| row.cert_active.0 == 1) {
        for chain_step in (1..FAKE_GLV_SELECTOR_CHUNKS).rev() {
            let selector = selector_row.selectors[chain_step];
            let decoded = Selector16DecodeEntry::from_selector(selector).map_err(|_| {
                FakeGlvChainError::InvalidSelector {
                    selector: selector.0,
                }
            })?;
            let base = prepared
                .instance(
                    selector_row.sig_id,
                    selector_row.cert_id,
                    decoded.base_index.0,
                )
                .ok_or(FakeGlvChainError::MissingTablePoint {
                    table_index: decoded.base_index.0,
                })?;
            let operand = apply_selector_sign(&base, decoded.neg_bit)?;
            rows.push(signed_selector_operand_trace_values(
                selector_row.sig_id,
                selector_row.cert_id,
                chain_step as u32,
                decoded,
                &operand,
            ));
        }
    }
    Ok(rows)
}

fn signed_selector_operand_consumers(
    selectors: &FakeGlvSelectorClaim,
    chain: &FakeGlvChainClaim,
) -> Result<Vec<[M31; FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS]>, FakeGlvChainError> {
    if chain.certs.len() != selectors.rows.len() {
        return Err(FakeGlvChainError::RowCountMismatch {
            certs: chain.certs.len(),
            fake_glv: chain.certs.len(),
            selectors: selectors.rows.len(),
            tables: selectors.rows.len(),
        });
    }
    let mut rows = Vec::new();
    for (cert, selector_row) in chain.certs.iter().zip(&selectors.rows) {
        for row in &cert.rows {
            let FakeGlvChainRowKind::ChainStep(chain_step) = row.kind else {
                continue;
            };
            let selector = selector_row.selectors[chain_step as usize];
            let decoded = Selector16DecodeEntry::from_selector(selector).map_err(|_| {
                FakeGlvChainError::InvalidSelector {
                    selector: selector.0,
                }
            })?;
            rows.push(signed_selector_operand_trace_values(
                row.sig_id,
                row.cert_id,
                chain_step,
                decoded,
                &row.operand,
            ));
        }
    }
    Ok(rows)
}

fn signed_selector_operand_trace_values(
    sig_id: M31,
    cert_id: M31,
    chain_step: u32,
    decoded: Selector16DecodeEntry,
    operand: &PreparedAffinePoint,
) -> [M31; FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS];
    values[0] = M31::from_u32_unchecked(1);
    values[1] = sig_id;
    values[2] = cert_id;
    values[3] = M31::from_u32_unchecked(chain_step);
    values[4] = decoded.selector;
    values[5] = decoded.base_index;
    values[6] = decoded.neg_bit;
    values[7..].copy_from_slice(&prepared_table_ec_point_values(operand));
    values
}

fn apply_selector_sign(
    base: &crate::prepared_point::PreparedPointInstance<M31>,
    neg_bit: M31,
) -> Result<PreparedAffinePoint, FakeGlvChainError> {
    let point = PreparedAffinePoint {
        x: base.x.clone(),
        y: base.y.clone(),
        inf: base.inf,
    };
    if point.inf.0 == 1 {
        return Ok(PreparedAffinePoint::infinity());
    }
    match neg_bit.0 {
        0 => Ok(point),
        1 => Ok(PreparedAffinePoint {
            x: point.x,
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
        }),
        actual => Err(FakeGlvChainError::NonBooleanFlag {
            field: "selector.neg_bit",
            actual,
        }),
    }
}

pub(crate) fn gen_signed_selector_operand_interaction_trace(
    base: &[M31ColumnEval],
    relation: &FakeGlvSignedSelectorOperandRelation,
    provider: bool,
) -> (ColumnVec<M31ColumnEval>, SecureField) {
    assert_eq!(base.len(), FAKE_GLV_SIGNED_SELECTOR_OPERAND_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = signed_selector_operand_packed_relation_values(base, vec_row);
        let numerator = PackedQM31::from(base[0].data[vec_row]);
        let numerator = if provider { -numerator } else { numerator };
        col.write_frac(vec_row, numerator, relation.combine(&values));
    }
    col.finalize_col();
    logup.finalize_last()
}

fn signed_selector_operand_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; FAKE_GLV_SIGNED_SELECTOR_OPERAND_RELATION_ARITY] {
    core::array::from_fn(|index| base[index + 1].data[vec_row])
}

fn signed_selector_operand_relation_values<F: Clone>(
    header: &[F; 6],
    operand: &[F; PREPARED_TABLE_EC_POINT_COLUMNS],
) -> [F; FAKE_GLV_SIGNED_SELECTOR_OPERAND_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0..=5 => header[index].clone(),
        6..=46 => operand[index - 6].clone(),
        _ => unreachable!("fake-GLV signed selector operand relation index is in range"),
    })
}

fn chain_step_row_count(chain: &FakeGlvChainClaim) -> usize {
    chain
        .certs
        .iter()
        .flat_map(|cert| cert.rows.iter())
        .filter(|row| matches!(row.kind, FakeGlvChainRowKind::ChainStep(_)))
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

fn signed_selector_operand_zero_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: SIGNED_SELECTOR_OPERAND_ZERO_COLUMN.into(),
    }
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}
