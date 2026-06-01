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
use stwo_p256_utils::constants::N_LIMBS;

use crate::constants::P256_MODULUS;
use crate::curve::{point_add, point_double, scalar_mul};
use crate::field_ops::{add_mod_witness, sub_mod_witness};
use crate::limbs::P256M31BigInt;
use crate::prepared_point::{
    PreparedPointInstance, PreparedPointTraceClaim, PreparedPointUseCountClaim,
    PREPARED_BASE_COUNT, TABLE16_INDEX,
};
use crate::projective::{ProjectiveEcOp, ProjectiveEcTraceClaim};
use crate::types::{AffinePoint, U256};

use super::cert_bind::{CertScalarInputClaim, CertScalarInputRow, CERT_ID_U1_GENERATOR};
use super::fake_glv_scalar::{FakeGlvScalarHintClaim, FakeGlvScalarHintRow};
use super::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorRow};
use super::fake_glv_selector_lookup::Selector16DecodeEntry;
use super::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

relation!(
    PreparedTableEcRowRelation,
    PREPARED_TABLE_EC_ROW_RELATION_ARITY
);

pub type PreparedTableEcRowComponent = FrameworkComponent<PreparedTableEcRowEval>;

pub const PREPARED_TABLE_EC_KIND_FLAGS: usize = 13;
pub const PREPARED_TABLE_EC_KIND_DOUBLE_P: usize = 0;
pub const PREPARED_TABLE_EC_KIND_ADD_P2P: usize = 1;
pub const PREPARED_TABLE_EC_KIND_DOUBLE_R: usize = 2;
pub const PREPARED_TABLE_EC_KIND_ADD_R2R: usize = 3;
pub const PREPARED_TABLE_EC_KIND_BASE_START: usize = 4;
pub const PREPARED_TABLE_EC_KIND_TABLE16: usize = 12;
pub const PREPARED_TABLE_EC_OP_MIXED_ADD: u32 = 0;
pub const PREPARED_TABLE_EC_OP_DOUBLE: u32 = 1;
pub const PREPARED_TABLE_EC_POINT_COLUMNS: usize = 2 * N_LIMBS + 1;
pub const PREPARED_TABLE_EC_ROW_RELATION_ARITY: usize = 5 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;
pub const PREPARED_TABLE_EC_ROW_TRACE_COLUMNS: usize =
    1 + 3 + PREPARED_TABLE_EC_KIND_FLAGS + 2 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;
pub const PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS: usize =
    1 + 5 + 3 * PREPARED_TABLE_EC_POINT_COLUMNS;

const PREPARED_TABLE_EC_ROW_INDEX_COLUMN: &str = "p256_prepared_table_ec_row_index";

pub type PreparedTableProjectiveSourceComponent =
    FrameworkComponent<PreparedTableProjectiveSourceEval>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableClaim {
    pub certs: Vec<PreparedTableCert>,
}

impl PreparedTableClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
        {
            return Err(PreparedTableError::RowCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
            });
        }

        let certs = cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .map(|((cert, fake_glv), selector)| PreparedTableCert::new(cert, fake_glv, selector))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { certs })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for cert in &self.certs {
            cert.verify()?;
        }
        Ok(())
    }

    pub fn prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
    ) -> Result<PreparedPointTraceClaim, PreparedTableError> {
        if self.certs.len() != use_counts.certs.len() {
            return Err(PreparedTableError::UseCountCountMismatch {
                tables: self.certs.len(),
                use_counts: use_counts.certs.len(),
            });
        }

        Ok(PreparedPointTraceClaim::from_use_counts(
            use_counts,
            |sig_id, cert_id, table_index| {
                self.instance(sig_id, cert_id, table_index)
                    .unwrap_or_else(|| PreparedPointInstance::dummy(sig_id, cert_id, table_index))
            },
        ))
    }

    pub fn verify_prepared_point_trace(
        &self,
        use_counts: &PreparedPointUseCountClaim,
        trace: &PreparedPointTraceClaim,
    ) -> Result<(), PreparedTableError> {
        let expected = self.prepared_point_trace(use_counts)?;
        if &expected == trace {
            Ok(())
        } else {
            Err(PreparedTableError::PreparedPointTraceMismatch)
        }
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> Option<PreparedPointInstance<M31>> {
        self.certs
            .iter()
            .find(|cert| cert.sig_id == sig_id && cert.cert_id == cert_id)
            .and_then(|cert| cert.instance(table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcTraceClaim {
    pub rows: Vec<PreparedTableEcRow>,
}

impl PreparedTableEcTraceClaim {
    pub fn from_claims(
        cert_inputs: &CertScalarInputClaim,
        fake_glv_scalars: &FakeGlvScalarHintClaim,
        selectors: &FakeGlvSelectorClaim,
        table: &PreparedTableClaim,
    ) -> Result<Self, PreparedTableError> {
        if cert_inputs.rows.len() != fake_glv_scalars.rows.len()
            || cert_inputs.rows.len() != selectors.rows.len()
            || cert_inputs.rows.len() != table.certs.len()
        {
            return Err(PreparedTableError::EcTraceCountMismatch {
                certs: cert_inputs.rows.len(),
                fake_glv: fake_glv_scalars.rows.len(),
                selectors: selectors.rows.len(),
                tables: table.certs.len(),
            });
        }

        let mut rows = Vec::new();
        for (((cert, fake_glv), selector), table_cert) in cert_inputs
            .rows
            .iter()
            .zip(&fake_glv_scalars.rows)
            .zip(&selectors.rows)
            .zip(&table.certs)
        {
            rows.extend(prepared_table_ec_rows_for_cert(
                cert, fake_glv, selector, table_cert,
            )?);
        }
        let claim = Self { rows };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        for row in &self.rows {
            row.verify()?;
        }
        Ok(())
    }

    pub fn active_row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn verify_against_table(
        &self,
        table: &PreparedTableClaim,
    ) -> Result<(), PreparedTableError> {
        for cert in &table.certs {
            let cert_rows = self
                .rows
                .iter()
                .filter(|row| row.sig_id == cert.sig_id && row.cert_id == cert.cert_id)
                .collect::<Vec<_>>();
            if cert.cert_active.0 == 0 {
                if cert_rows.is_empty() {
                    continue;
                }
                return Err(PreparedTableError::InactiveEcTraceRows {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                });
            }

            let expected_rows = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
                PREPARED_BASE_COUNT + 3
            } else {
                PREPARED_BASE_COUNT + 5
            };
            if cert_rows.len() != expected_rows {
                return Err(PreparedTableError::EcTraceCertRowCountMismatch {
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                    expected: expected_rows,
                    actual: cert_rows.len(),
                });
            }

            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::AddR2R,
                "R3",
                &cert.r3,
            )?;
            for (index, point) in cert.base.iter().enumerate() {
                require_unique_output(
                    &cert_rows,
                    cert.sig_id,
                    cert.cert_id,
                    PreparedTableEcRowKind::Base(index as u32),
                    "Base",
                    point,
                )?;
            }
            require_unique_output(
                &cert_rows,
                cert.sig_id,
                cert.cert_id,
                PreparedTableEcRowKind::Table16,
                "Table16",
                &cert.table16,
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowProofClaim {
    pub log_size: u32,
}

impl PreparedTableEcRowProofClaim {
    pub fn from_trace(trace: &PreparedTableEcTraceClaim) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
            },
            secure_zero(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
            },
            secure_zero(),
        );
        component.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let component = PreparedTableEcRowComponent::new(
            &mut allocator,
            PreparedTableEcRowEval {
                log_size: self.log_size,
                relation: PreparedTableEcRowRelation::dummy(),
            },
            secure_zero(),
        );
        component.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRowInteractionClaim {
    pub claimed_sum: SecureField,
}

impl PreparedTableEcRowInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

#[derive(Clone, Debug)]
pub struct PreparedTableEcRowProof<H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted> {
    pub claim: PreparedTableEcRowProofClaim,
    pub interaction_claim: PreparedTableEcRowInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableProjectiveSourceProofClaim {
    pub log_size: u32,
}

impl PreparedTableProjectiveSourceProofClaim {
    pub fn from_prepared_trace(trace: &PreparedTableEcTraceClaim) -> Self {
        Self {
            log_size: padded_log_size(trace.rows.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut allocator = TraceLocationAllocator::default();
        let _ = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
        );
        allocator.preprocessed_columns().clone()
    }

    pub fn trace_log_degree_bounds(&self, ids: &[PreProcessedColumnId]) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
        );
        components.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = PreparedTableProjectiveSourceComponents::new(
            &mut allocator,
            self.log_size,
            &PreparedTableProjectiveSourceInteractionClaim::zero(),
            &PreparedTableEcRowRelation::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedTableProjectiveSourceInteractionClaim {
    pub provider_claimed_sum: SecureField,
    pub consumer_claimed_sum: SecureField,
}

impl PreparedTableProjectiveSourceInteractionClaim {
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
pub struct PreparedTableProjectiveSourceProof<
    H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted,
> {
    pub claim: PreparedTableProjectiveSourceProofClaim,
    pub interaction_claim: PreparedTableProjectiveSourceInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

pub struct PreparedTableProjectiveSourceComponents {
    pub provider: PreparedTableEcRowComponent,
    pub consumer: PreparedTableProjectiveSourceComponent,
}

impl PreparedTableProjectiveSourceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        interaction_claim: &PreparedTableProjectiveSourceInteractionClaim,
        relation: &PreparedTableEcRowRelation,
    ) -> Self {
        Self {
            provider: PreparedTableEcRowComponent::new(
                allocator,
                PreparedTableEcRowEval {
                    log_size,
                    relation: relation.clone(),
                },
                interaction_claim.provider_claimed_sum,
            ),
            consumer: PreparedTableProjectiveSourceComponent::new(
                allocator,
                PreparedTableProjectiveSourceEval {
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
pub struct PreparedTableEcRowEval {
    pub log_size: u32,
    pub relation: PreparedTableEcRowRelation,
}

impl FrameworkEval for PreparedTableEcRowEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let row_index = eval.get_preprocessed_column(prepared_table_ec_row_index_column_id());
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let kind_flags: [E::F; PREPARED_TABLE_EC_KIND_FLAGS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let op = eval.next_trace_mask();
        let table_index = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(active.clone() * (source_index.clone() - row_index));

        let mut kind_sum = E::F::from(M31::from_u32_unchecked(0));
        for flag in &kind_flags {
            eval.add_constraint(flag.clone() * (flag.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * flag.clone());
            kind_sum += flag.clone();
        }
        eval.add_constraint(active.clone() * (kind_sum - one.clone()));

        let double_flag = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_P].clone()
            + kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
        eval.add_constraint(active.clone() * (op.clone() - double_flag.clone()));

        let mut expected_table_index = E::F::from(M31::from_u32_unchecked(0));
        for base_index in 0..PREPARED_BASE_COUNT {
            expected_table_index += kind_flags[PREPARED_TABLE_EC_KIND_BASE_START + base_index]
                .clone()
                * E::F::from(M31::from_u32_unchecked(base_index as u32));
        }
        expected_table_index += kind_flags[PREPARED_TABLE_EC_KIND_TABLE16].clone()
            * E::F::from(M31::from_u32_unchecked(TABLE16_INDEX));
        eval.add_constraint(active.clone() * (table_index.clone() - expected_table_index));

        eval.add_constraint(double_flag.clone() * (rhs.inf.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
            table_index.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = prepared_table_ec_row_relation_values(
            &[source_index, sig_id, cert_id, op, table_index],
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
pub struct PreparedTableProjectiveSourceEval {
    pub log_size: u32,
    pub relation: PreparedTableEcRowRelation,
}

impl FrameworkEval for PreparedTableProjectiveSourceEval {
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
        let table_index = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
            table_index.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = prepared_table_ec_row_relation_values(
            &[source_index, sig_id, cert_id, op, table_index],
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

#[derive(Clone, Debug)]
struct PreparedTableEcEvalPoint<F> {
    x: [F; N_LIMBS],
    y: [F; N_LIMBS],
    inf: F,
}

impl<F: Clone> PreparedTableEcEvalPoint<F> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS] {
        core::array::from_fn(|index| match index {
            0..=19 => self.x[index].clone(),
            20..=39 => self.y[index - N_LIMBS].clone(),
            40 => self.inf.clone(),
            _ => unreachable!("prepared-table EC point relation index is in range"),
        })
    }
}

impl<F> PreparedTableEcEvalPoint<F> {
    fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            x: core::array::from_fn(|_| eval.next_trace_mask()),
            y: core::array::from_fn(|_| eval.next_trace_mask()),
            inf: eval.next_trace_mask(),
        }
    }
}

impl<F> PreparedTableEcEvalPoint<F>
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
{
    fn add_constraints<E: EvalAtRow<F = F>>(&self, eval: &mut E, active: &F, one: &F) {
        eval.add_constraint(self.inf.clone() * (self.inf.clone() - one.clone()));
        for limb in self.x.iter().chain(self.y.iter()) {
            eval.add_constraint(self.inf.clone() * limb.clone());
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }
        eval.add_constraint((one.clone() - active.clone()) * self.inf.clone());
    }
}

pub fn prove_prepared_table_ec_row_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    trace: &PreparedTableEcTraceClaim,
    config: PcsConfig,
) -> Result<PreparedTableEcRowProof<MC::H>, PreparedTableError>
where
    SimdBackend: BackendForChannel<MC>,
{
    trace.verify()?;
    let claim = PreparedTableEcRowProofClaim::from_trace(trace);
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

    let preprocessed = gen_prepared_table_ec_row_preprocessed_trace(claim.log_size, &ids)?;
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let base = gen_prepared_table_ec_row_base_trace(trace, claim.log_size)?;
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base.clone());
    tree_builder.commit(&mut channel);

    let relation = PreparedTableEcRowRelation::draw(&mut channel);
    let (interaction, interaction_claim) =
        gen_prepared_table_ec_row_interaction_trace(&base, &relation);
    interaction_claim.mix_into(&mut channel);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = PreparedTableEcRowComponent::new(
        &mut allocator,
        PreparedTableEcRowEval {
            log_size: claim.log_size,
            relation,
        },
        interaction_claim.claimed_sum,
    );
    assert_eq!(
        commitment_scheme
            .polynomials()
            .as_cols_ref()
            .map_cols(|column| column.evals.domain.log_size() - config.fri_config.log_blowup_factor)
            .0,
        component.trace_log_degree_bounds().0
    );
    let stark_proof = prove(
        &[&component as &dyn ComponentProver<SimdBackend>],
        &mut channel,
        commitment_scheme,
    )
    .map_err(|_| PreparedTableError::ProofLayer)?;

    Ok(PreparedTableEcRowProof {
        claim,
        interaction_claim,
        stark_proof,
    })
}

pub fn verify_prepared_table_ec_row_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    proof: PreparedTableEcRowProof<MC::H>,
) -> Result<(), PreparedTableError> {
    let PreparedTableEcRowProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;

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

    let relation = PreparedTableEcRowRelation::draw(&mut channel);

    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let component = PreparedTableEcRowComponent::new(
        &mut allocator,
        PreparedTableEcRowEval {
            log_size: claim.log_size,
            relation,
        },
        interaction_claim.claimed_sum,
    );
    verify(
        &[&component as &dyn Component],
        &mut channel,
        commitment_scheme,
        stark_proof,
    )
    .map_err(|_| PreparedTableError::ProofLayer)
}

pub fn prove_prepared_table_projective_source_proof_slice<MC: stwo::core::channel::MerkleChannel>(
    prepared: &PreparedTableEcTraceClaim,
    projective: &ProjectiveEcTraceClaim,
    config: PcsConfig,
) -> Result<PreparedTableProjectiveSourceProof<MC::H>, PreparedTableError>
where
    SimdBackend: BackendForChannel<MC>,
{
    prepared.verify()?;
    projective
        .verify()
        .map_err(|_| PreparedTableError::ProjectiveSourceInvalid)?;
    let claim = PreparedTableProjectiveSourceProofClaim::from_prepared_trace(prepared);
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

    let preprocessed = gen_prepared_table_ec_row_preprocessed_trace(claim.log_size, &ids)?;
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let provider_base = gen_prepared_table_ec_row_base_trace(prepared, claim.log_size)?;
    let consumer_base =
        gen_prepared_table_projective_source_base_trace(prepared, projective, claim.log_size)?;
    let mut base = provider_base.clone();
    base.extend(consumer_base.clone());
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.commit(&mut channel);

    let relation = PreparedTableEcRowRelation::draw(&mut channel);
    let (provider_interaction, provider_claim) =
        gen_prepared_table_ec_row_interaction_trace(&provider_base, &relation);
    let (consumer_interaction, consumer_claim) =
        gen_prepared_table_projective_source_interaction_trace(&consumer_base, &relation);
    let interaction_claim = PreparedTableProjectiveSourceInteractionClaim {
        provider_claimed_sum: provider_claim.claimed_sum,
        consumer_claimed_sum: consumer_claim.claimed_sum,
    };
    if interaction_claim.total() != secure_zero() {
        return Err(PreparedTableError::RelationImbalance {
            relation: "PreparedTableProjectiveSource",
        });
    }
    interaction_claim.mix_into(&mut channel);
    let mut interaction = provider_interaction;
    interaction.extend(consumer_interaction);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(&mut channel);

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = PreparedTableProjectiveSourceComponents::new(
        &mut allocator,
        claim.log_size,
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
    .map_err(|_| PreparedTableError::ProofLayer)?;

    Ok(PreparedTableProjectiveSourceProof {
        claim,
        interaction_claim,
        stark_proof,
    })
}

pub fn verify_prepared_table_projective_source_proof_slice<
    MC: stwo::core::channel::MerkleChannel,
>(
    proof: PreparedTableProjectiveSourceProof<MC::H>,
) -> Result<(), PreparedTableError> {
    let PreparedTableProjectiveSourceProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;

    if interaction_claim.total() != secure_zero() {
        return Err(PreparedTableError::RelationImbalance {
            relation: "PreparedTableProjectiveSource",
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

    let relation = PreparedTableEcRowRelation::draw(&mut channel);

    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components = PreparedTableProjectiveSourceComponents::new(
        &mut allocator,
        claim.log_size,
        &interaction_claim,
        &relation,
    );
    verify(
        &components.components(),
        &mut channel,
        commitment_scheme,
        stark_proof,
    )
    .map_err(|_| PreparedTableError::ProofLayer)
}

fn gen_prepared_table_ec_row_preprocessed_trace(
    log_size: u32,
    ids: &[PreProcessedColumnId],
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    ids.iter()
        .map(|id| {
            if id == &prepared_table_ec_row_index_column_id() {
                Ok(m31_column_eval(
                    log_size,
                    (0..(1usize << log_size))
                        .map(|index| M31::from_u32_unchecked(index as u32))
                        .collect(),
                ))
            } else {
                Err(PreparedTableError::PreprocessedColumnMissing)
            }
        })
        .collect()
}

fn gen_prepared_table_ec_row_base_trace(
    trace: &PreparedTableEcTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let padded_rows = 1usize << log_size;
    if trace.rows.len() > padded_rows {
        return Err(PreparedTableError::EcTraceRowsExceedDomain {
            rows: trace.rows.len(),
            domain: padded_rows,
        });
    }
    let mut rows = trace
        .rows
        .iter()
        .enumerate()
        .map(|(source_index, row)| prepared_table_ec_row_trace_values(source_index, row))
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_ROW_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn gen_prepared_table_projective_source_base_trace(
    prepared: &PreparedTableEcTraceClaim,
    projective: &ProjectiveEcTraceClaim,
    log_size: u32,
) -> Result<ColumnVec<M31ColumnEval>, PreparedTableError> {
    let padded_rows = 1usize << log_size;
    if prepared.rows.len() > padded_rows {
        return Err(PreparedTableError::EcTraceRowsExceedDomain {
            rows: prepared.rows.len(),
            domain: padded_rows,
        });
    }
    if projective.rows.len() < prepared.rows.len() {
        return Err(PreparedTableError::ProjectiveSourcePrefixTooShort {
            prepared: prepared.rows.len(),
            projective: projective.rows.len(),
        });
    }
    let mut rows = prepared
        .rows
        .iter()
        .zip(projective.rows.iter())
        .enumerate()
        .map(|(source_index, (prepared_row, projective_row))| {
            prepared_table_projective_source_trace_values(
                source_index,
                prepared_row,
                projective_row,
            )
        })
        .collect::<Vec<_>>();
    rows.resize(
        padded_rows,
        [M31::from_u32_unchecked(0); PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS],
    );
    Ok(columns_from_rows(log_size, rows))
}

fn gen_prepared_table_ec_row_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_table_ec_row_packed_relation_values(base, vec_row);
        let numerator = -PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, PreparedTableEcRowInteractionClaim { claimed_sum })
}

fn gen_prepared_table_projective_source_interaction_trace(
    base: &[M31ColumnEval],
    relation: &PreparedTableEcRowRelation,
) -> (ColumnVec<M31ColumnEval>, PreparedTableEcRowInteractionClaim) {
    assert_eq!(base.len(), PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values = prepared_table_projective_source_packed_relation_values(base, vec_row);
        let numerator = PackedQM31::from(base[0].data[vec_row]);
        let denominator: PackedQM31 = relation.combine(&values);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, PreparedTableEcRowInteractionClaim { claimed_sum })
}

fn prepared_table_ec_row_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 17,
            4 => 18,
            5..=127 => 19 + (index - 5),
            _ => unreachable!("prepared-table EC packed relation index is in range"),
        };
        base[column].data[vec_row]
    })
}

fn prepared_table_projective_source_packed_relation_values(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    core::array::from_fn(|index| {
        let column = match index {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 4,
            4 => 5,
            5..=127 => 6 + (index - 5),
            _ => unreachable!("prepared-table projective source relation index is in range"),
        };
        base[column].data[vec_row]
    })
}

fn prepared_table_ec_row_index_column_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: PREPARED_TABLE_EC_ROW_INDEX_COLUMN.into(),
    }
}

fn prepared_table_ec_row_trace_values(
    source_index: usize,
    row: &PreparedTableEcRow,
) -> [M31; PREPARED_TABLE_EC_ROW_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_ROW_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = row.sig_id;
    column += 1;
    values[column] = row.cert_id;
    column += 1;
    for flag in kind_flags(row.kind) {
        values[column] = flag;
        column += 1;
    }
    values[column] = prepared_table_ec_op_code(row.kind);
    column += 1;
    values[column] = prepared_table_ec_table_index(row.kind);
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
    debug_assert_eq!(column, PREPARED_TABLE_EC_ROW_TRACE_COLUMNS);
    values
}

fn prepared_table_projective_source_trace_values(
    source_index: usize,
    prepared_row: &PreparedTableEcRow,
    projective_row: &crate::projective::ProjectiveEcRow,
) -> [M31; PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS] {
    let mut values = [M31::from_u32_unchecked(0); PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS];
    let mut column = 0;
    values[column] = M31::from_u32_unchecked(1);
    column += 1;
    values[column] = M31::from_u32_unchecked(source_index as u32);
    column += 1;
    values[column] = projective_row.sig_id;
    column += 1;
    values[column] = projective_row.cert_id;
    column += 1;
    values[column] = projective_ec_op_code(projective_row.op);
    column += 1;
    values[column] = prepared_table_ec_table_index(prepared_row.kind);
    column += 1;
    for value in prepared_table_ec_point_values(&projective_row.lhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&projective_row.rhs_affine) {
        values[column] = value;
        column += 1;
    }
    for value in prepared_table_ec_point_values(&projective_row.output_affine) {
        values[column] = value;
        column += 1;
    }
    debug_assert_eq!(column, PREPARED_TABLE_PROJECTIVE_SOURCE_TRACE_COLUMNS);
    values
}

fn prepared_table_ec_row_relation_values<F: Clone>(
    header: &[F; 5],
    lhs: &impl PreparedTableEcPointLike<F>,
    rhs: &impl PreparedTableEcPointLike<F>,
    output: &impl PreparedTableEcPointLike<F>,
) -> [F; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    let lhs = lhs.relation_values();
    let rhs = rhs.relation_values();
    let output = output.relation_values();
    core::array::from_fn(|index| match index {
        0..=4 => header[index].clone(),
        5..=45 => lhs[index - 5].clone(),
        46..=86 => rhs[index - 46].clone(),
        87..=127 => output[index - 87].clone(),
        _ => unreachable!("prepared-table EC row relation index is in range"),
    })
}

trait PreparedTableEcPointLike<F: Clone> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS];
}

impl<F: Clone> PreparedTableEcPointLike<F> for PreparedTableEcEvalPoint<F> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS] {
        self.relation_values()
    }
}

#[derive(Clone, Debug)]
struct PreparedTableEcPointValues {
    x: [M31; N_LIMBS],
    y: [M31; N_LIMBS],
    inf: M31,
}

impl PreparedTableEcPointValues {
    fn from_prepared(point: &PreparedAffinePoint) -> Self {
        Self {
            x: *point.x.limbs(),
            y: *point.y.limbs(),
            inf: point.inf,
        }
    }
}

impl PreparedTableEcPointLike<M31> for PreparedTableEcPointValues {
    fn relation_values(&self) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
        core::array::from_fn(|index| match index {
            0..=19 => self.x[index],
            20..=39 => self.y[index - N_LIMBS],
            40 => self.inf,
            _ => unreachable!("prepared-table EC point relation index is in range"),
        })
    }
}

fn prepared_table_ec_point_values(
    point: &PreparedAffinePoint,
) -> [M31; PREPARED_TABLE_EC_POINT_COLUMNS] {
    PreparedTableEcPointValues::from_prepared(point).relation_values()
}

fn columns_from_rows<const N: usize>(
    log_size: u32,
    rows: Vec<[M31; N]>,
) -> ColumnVec<M31ColumnEval> {
    (0..N)
        .map(|column| m31_column_eval(log_size, rows.iter().map(|row| row[column]).collect()))
        .collect()
}

fn kind_flags(kind: PreparedTableEcRowKind) -> [M31; PREPARED_TABLE_EC_KIND_FLAGS] {
    let mut flags = [M31::from_u32_unchecked(0); PREPARED_TABLE_EC_KIND_FLAGS];
    flags[prepared_table_ec_kind_flag_index(kind)] = M31::from_u32_unchecked(1);
    flags
}

fn prepared_table_ec_kind_flag_index(kind: PreparedTableEcRowKind) -> usize {
    match kind {
        PreparedTableEcRowKind::DoubleP => PREPARED_TABLE_EC_KIND_DOUBLE_P,
        PreparedTableEcRowKind::AddP2P => PREPARED_TABLE_EC_KIND_ADD_P2P,
        PreparedTableEcRowKind::DoubleR => PREPARED_TABLE_EC_KIND_DOUBLE_R,
        PreparedTableEcRowKind::AddR2R => PREPARED_TABLE_EC_KIND_ADD_R2R,
        PreparedTableEcRowKind::Base(index) => PREPARED_TABLE_EC_KIND_BASE_START + index as usize,
        PreparedTableEcRowKind::Table16 => PREPARED_TABLE_EC_KIND_TABLE16,
    }
}

fn prepared_table_ec_op_code(kind: PreparedTableEcRowKind) -> M31 {
    let code = match kind {
        PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
            PREPARED_TABLE_EC_OP_DOUBLE
        }
        PreparedTableEcRowKind::AddP2P
        | PreparedTableEcRowKind::AddR2R
        | PreparedTableEcRowKind::Base(_)
        | PreparedTableEcRowKind::Table16 => PREPARED_TABLE_EC_OP_MIXED_ADD,
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

fn prepared_table_ec_table_index(kind: PreparedTableEcRowKind) -> M31 {
    let index = match kind {
        PreparedTableEcRowKind::Base(index) => index,
        PreparedTableEcRowKind::Table16 => TABLE16_INDEX,
        PreparedTableEcRowKind::DoubleP
        | PreparedTableEcRowKind::AddP2P
        | PreparedTableEcRowKind::DoubleR
        | PreparedTableEcRowKind::AddR2R => 0,
    };
    M31::from_u32_unchecked(index)
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableEcRow {
    pub sig_id: M31,
    pub cert_id: M31,
    pub kind: PreparedTableEcRowKind,
    pub lhs: PreparedAffinePoint,
    pub rhs: PreparedAffinePoint,
    pub output: PreparedAffinePoint,
}

impl PreparedTableEcRow {
    fn double(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        input: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs: input,
            rhs: PreparedAffinePoint::infinity(),
            output,
        }
    }

    fn add(
        sig_id: M31,
        cert_id: M31,
        kind: PreparedTableEcRowKind,
        lhs: PreparedAffinePoint,
        rhs: PreparedAffinePoint,
        output: PreparedAffinePoint,
    ) -> Self {
        Self {
            sig_id,
            cert_id,
            kind,
            lhs,
            rhs,
            output,
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        self.lhs.verify()?;
        self.rhs.verify()?;
        self.output.verify()?;
        let expected = match self.kind {
            PreparedTableEcRowKind::DoubleP | PreparedTableEcRowKind::DoubleR => {
                double_optional(self.lhs.to_option())
            }
            PreparedTableEcRowKind::AddP2P
            | PreparedTableEcRowKind::AddR2R
            | PreparedTableEcRowKind::Base(_)
            | PreparedTableEcRowKind::Table16 => {
                add_optional_points(self.lhs.to_option(), self.rhs.to_option())
            }
        };
        let expected = prepared(expected);
        if self.output == expected {
            Ok(())
        } else {
            Err(PreparedTableError::EcTraceOutputMismatch {
                sig_id: self.sig_id.0,
                cert_id: self.cert_id.0,
                kind: self.kind,
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableEcRowKind {
    DoubleP,
    AddP2P,
    DoubleR,
    AddR2R,
    Base(u32),
    Table16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedTableCert {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub base: [PreparedAffinePoint; PREPARED_BASE_COUNT],
    pub r3: PreparedAffinePoint,
    pub table16: PreparedAffinePoint,
}

impl PreparedTableCert {
    fn new(
        cert: &CertScalarInputRow,
        fake_glv: &FakeGlvScalarHintRow,
        selector: &FakeGlvSelectorRow,
    ) -> Result<Self, PreparedTableError> {
        require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
        require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;

        if cert.cert_active.0 == 0 {
            return Ok(Self {
                sig_id: cert.sig_id,
                cert_id: cert.cert_id,
                cert_active: cert.cert_active,
                base: core::array::from_fn(|_| PreparedAffinePoint::infinity()),
                r3: PreparedAffinePoint::infinity(),
                table16: PreparedAffinePoint::infinity(),
            });
        }

        let p = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let h =
            scalar_mul(&cert.scalar.to_u256(), &p).ok_or(PreparedTableError::MissingHintPoint {
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            })?;
        let r = signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?;
        let p3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "P",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;
        let r3 = scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &r).ok_or(
            PreparedTableError::MissingTriplePoint {
                point: "R",
                sig_id: cert.sig_id.0,
                cert_id: cert.cert_id.0,
            },
        )?;

        let base = [
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r.clone()))),
            prepared(add_optional_points(
                Some(p3.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(
                Some(p.clone()),
                negate_optional(Some(r3.clone())),
            )),
            prepared(add_optional_points(Some(p.clone()), Some(r3.clone()))),
            prepared(add_optional_points(Some(p3.clone()), Some(r3.clone()))),
        ];

        let selector0 =
            Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
                PreparedTableError::InvalidSelector {
                    selector: selector.selectors[0].0,
                }
            })?;
        let selected = apply_selector(&base, selector0)?;
        let table16 = prepared(add_optional_points(selected.to_option(), Some(r3.clone())));

        Ok(Self {
            sig_id: cert.sig_id,
            cert_id: cert.cert_id,
            cert_active: cert.cert_active,
            base,
            r3: prepared(Some(r3)),
            table16,
        })
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.cert_active.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "cert_active",
                actual: self.cert_active.0,
            });
        }
        for point in &self.base {
            point.verify()?;
        }
        self.r3.verify()?;
        self.table16.verify()?;
        Ok(())
    }

    pub fn instance(&self, table_index: u32) -> Option<PreparedPointInstance<M31>> {
        let point = match table_index {
            0..=7 => self.base[table_index as usize].clone(),
            TABLE16_INDEX => self.table16.clone(),
            _ => return None,
        };
        Some(point.instance(self.sig_id, self.cert_id, table_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedAffinePoint {
    pub x: P256M31BigInt,
    pub y: P256M31BigInt,
    pub inf: M31,
}

impl PreparedAffinePoint {
    pub const fn infinity() -> Self {
        Self {
            x: P256M31BigInt::zero(),
            y: P256M31BigInt::zero(),
            inf: M31::from_u32_unchecked(1),
        }
    }

    pub fn from_affine(point: AffinePoint) -> Self {
        Self {
            x: P256M31BigInt::from_u256(&point.x),
            y: P256M31BigInt::from_u256(&point.y),
            inf: M31::from_u32_unchecked(0),
        }
    }

    pub fn verify(&self) -> Result<(), PreparedTableError> {
        if self.inf.0 > 1 {
            return Err(PreparedTableError::NonBooleanFlag {
                field: "inf",
                actual: self.inf.0,
            });
        }
        if self.inf.0 == 1 && (self.x != P256M31BigInt::zero() || self.y != P256M31BigInt::zero()) {
            return Err(PreparedTableError::NonCanonicalInfinity);
        }
        Ok(())
    }

    pub fn to_option(&self) -> Option<AffinePoint> {
        (self.inf.0 == 0).then(|| AffinePoint {
            x: self.x.to_u256(),
            y: self.y.to_u256(),
        })
    }

    pub fn instance(
        &self,
        sig_id: M31,
        cert_id: M31,
        table_index: u32,
    ) -> PreparedPointInstance<M31> {
        PreparedPointInstance {
            sig_id,
            cert_id,
            table_index: M31::from_u32_unchecked(table_index),
            x: self.x.clone(),
            y: self.y.clone(),
            inf: self.inf,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedTableError {
    RowCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
    },
    UseCountCountMismatch {
        tables: usize,
        use_counts: usize,
    },
    EcTraceCountMismatch {
        certs: usize,
        fake_glv: usize,
        selectors: usize,
        tables: usize,
    },
    IdMismatch {
        source: &'static str,
        cert_sig_id: u32,
        cert_cert_id: u32,
        other_sig_id: u32,
        other_cert_id: u32,
    },
    InvalidSelector {
        selector: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    MissingHintPoint {
        sig_id: u32,
        cert_id: u32,
    },
    MissingTriplePoint {
        point: &'static str,
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        kind: PreparedTableEcRowKind,
    },
    PreparedTableOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        table_index: u32,
    },
    PreparedPointTraceMismatch,
    InactiveEcTraceRows {
        sig_id: u32,
        cert_id: u32,
    },
    EcTraceCertRowCountMismatch {
        sig_id: u32,
        cert_id: u32,
        expected: usize,
        actual: usize,
    },
    EcTraceExpectedOutputMissing {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputDuplicate {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceExpectedOutputMismatch {
        sig_id: u32,
        cert_id: u32,
        label: &'static str,
    },
    EcTraceRowsExceedDomain {
        rows: usize,
        domain: usize,
    },
    ProjectiveSourcePrefixTooShort {
        prepared: usize,
        projective: usize,
    },
    ProjectiveSourceInvalid,
    RelationImbalance {
        relation: &'static str,
    },
    PreprocessedColumnMissing,
    NonCanonicalInfinity,
    ProofLayer,
}

fn require_unique_output(
    rows: &[&PreparedTableEcRow],
    sig_id: M31,
    cert_id: M31,
    kind: PreparedTableEcRowKind,
    label: &'static str,
    expected: &PreparedAffinePoint,
) -> Result<(), PreparedTableError> {
    let matches = rows
        .iter()
        .copied()
        .filter(|row| row.kind == kind)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Err(PreparedTableError::EcTraceExpectedOutputMissing {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        [row] if &row.output == expected => Ok(()),
        [_row] => Err(PreparedTableError::EcTraceExpectedOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
        _ => Err(PreparedTableError::EcTraceExpectedOutputDuplicate {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            label,
        }),
    }
}

fn prepared_table_ec_rows_for_cert(
    cert: &CertScalarInputRow,
    fake_glv: &FakeGlvScalarHintRow,
    selector: &FakeGlvSelectorRow,
    table: &PreparedTableCert,
) -> Result<Vec<PreparedTableEcRow>, PreparedTableError> {
    require_same_id("fake_glv", cert, fake_glv.sig_id, fake_glv.cert_id)?;
    require_same_id("selector", cert, selector.sig_id, selector.cert_id)?;
    if cert.sig_id != table.sig_id || cert.cert_id != table.cert_id {
        return Err(PreparedTableError::IdMismatch {
            source: "prepared_table",
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: table.sig_id.0,
            other_cert_id: table.cert_id.0,
        });
    }
    if cert.cert_active.0 == 0 {
        return Ok(Vec::new());
    }

    let sig_id = cert.sig_id;
    let cert_id = cert.cert_id;
    let p = PreparedAffinePoint::from_affine(AffinePoint {
        x: cert.base_x.to_u256(),
        y: cert.base_y.to_u256(),
    });
    let h = scalar_mul(
        &cert.scalar.to_u256(),
        &p.to_option().expect("base point finite"),
    )
    .ok_or(PreparedTableError::MissingHintPoint {
        sig_id: cert.sig_id.0,
        cert_id: cert.cert_id.0,
    })?;
    let r = PreparedAffinePoint::from_affine(signed_hint_point(&h, fake_glv.hint.s2_sign_bit)?);

    let mut rows = Vec::new();
    let p3 = if cert.cert_id.0 == CERT_ID_U1_GENERATOR {
        PreparedAffinePoint::from_affine(
            scalar_mul(&U256::from_le_u64s(&[3, 0, 0, 0]), &p.to_option().unwrap()).ok_or(
                PreparedTableError::MissingTriplePoint {
                    point: "P",
                    sig_id: cert.sig_id.0,
                    cert_id: cert.cert_id.0,
                },
            )?,
        )
    } else {
        let p2 = prepared(double_optional(p.to_option()));
        rows.push(PreparedTableEcRow::double(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::DoubleP,
            p.clone(),
            p2.clone(),
        ));
        let p3 = prepared(add_optional_points(p2.to_option(), p.to_option()));
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::AddP2P,
            p2,
            p.clone(),
            p3.clone(),
        ));
        p3
    };

    let r2 = prepared(double_optional(r.to_option()));
    rows.push(PreparedTableEcRow::double(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::DoubleR,
        r.clone(),
        r2.clone(),
    ));
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::AddR2R,
        r2.clone(),
        r.clone(),
        table.r3.clone(),
    ));

    let base_operands = [
        (p3.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), prepared(negate_optional(r.to_option()))),
        (p.clone(), r.clone()),
        (p3.clone(), r.clone()),
        (p3.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), prepared(negate_optional(table.r3.to_option()))),
        (p.clone(), table.r3.clone()),
        (p3.clone(), table.r3.clone()),
    ];

    for (index, (lhs, rhs)) in base_operands.into_iter().enumerate() {
        let output = table.base[index].clone();
        rows.push(PreparedTableEcRow::add(
            sig_id,
            cert_id,
            PreparedTableEcRowKind::Base(index as u32),
            lhs.clone(),
            rhs.clone(),
            output.clone(),
        ));
        let expected = prepared(add_optional_points(lhs.to_option(), rhs.to_option()));
        if output != expected {
            return Err(PreparedTableError::PreparedTableOutputMismatch {
                sig_id: sig_id.0,
                cert_id: cert_id.0,
                table_index: index as u32,
            });
        }
    }

    let selector0 = Selector16DecodeEntry::from_selector(selector.selectors[0]).map_err(|_| {
        PreparedTableError::InvalidSelector {
            selector: selector.selectors[0].0,
        }
    })?;
    let selected = apply_selector(&table.base, selector0)?;
    rows.push(PreparedTableEcRow::add(
        sig_id,
        cert_id,
        PreparedTableEcRowKind::Table16,
        selected.clone(),
        table.r3.clone(),
        table.table16.clone(),
    ));
    let expected_table16 = prepared(add_optional_points(
        selected.to_option(),
        table.r3.to_option(),
    ));
    if table.table16 != expected_table16 {
        return Err(PreparedTableError::PreparedTableOutputMismatch {
            sig_id: sig_id.0,
            cert_id: cert_id.0,
            table_index: TABLE16_INDEX,
        });
    }

    Ok(rows)
}

fn require_same_id(
    source: &'static str,
    cert: &CertScalarInputRow,
    other_sig_id: M31,
    other_cert_id: M31,
) -> Result<(), PreparedTableError> {
    if cert.sig_id == other_sig_id && cert.cert_id == other_cert_id {
        Ok(())
    } else {
        Err(PreparedTableError::IdMismatch {
            source,
            cert_sig_id: cert.sig_id.0,
            cert_cert_id: cert.cert_id.0,
            other_sig_id: other_sig_id.0,
            other_cert_id: other_cert_id.0,
        })
    }
}

fn signed_hint_point(h: &AffinePoint, s2_sign_bit: M31) -> Result<AffinePoint, PreparedTableError> {
    match s2_sign_bit.0 {
        0 => Ok(h.clone()),
        1 => Ok(negate_point(h)),
        actual => Err(PreparedTableError::NonBooleanFlag {
            field: "s2_sign_bit",
            actual,
        }),
    }
}

fn apply_selector(
    base: &[PreparedAffinePoint; PREPARED_BASE_COUNT],
    selector: Selector16DecodeEntry,
) -> Result<PreparedAffinePoint, PreparedTableError> {
    let base_index = selector.base_index.0 as usize;
    let point = base
        .get(base_index)
        .cloned()
        .ok_or(PreparedTableError::InvalidSelector {
            selector: selector.selector.0,
        })?;
    if selector.neg_bit.0 == 0 {
        Ok(point)
    } else if selector.neg_bit.0 == 1 {
        Ok(prepared(negate_optional(point.to_option())))
    } else {
        Err(PreparedTableError::NonBooleanFlag {
            field: "selector.neg_bit",
            actual: selector.neg_bit.0,
        })
    }
}

fn prepared(point: Option<AffinePoint>) -> PreparedAffinePoint {
    point.map_or_else(
        PreparedAffinePoint::infinity,
        PreparedAffinePoint::from_affine,
    )
}

fn add_optional_points(lhs: Option<AffinePoint>, rhs: Option<AffinePoint>) -> Option<AffinePoint> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(point), None) | (None, Some(point)) => Some(point),
        (Some(lhs), Some(rhs)) if lhs == rhs => Some(point_double(&lhs).output),
        (Some(lhs), Some(rhs)) if is_additive_inverse(&lhs, &rhs) => None,
        (Some(lhs), Some(rhs)) => Some(point_add(&lhs, &rhs).output),
    }
}

fn double_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| point_double(&point).output)
}

fn negate_optional(point: Option<AffinePoint>) -> Option<AffinePoint> {
    point.map(|point| negate_point(&point))
}

fn negate_point(point: &AffinePoint) -> AffinePoint {
    AffinePoint {
        x: point.x.clone(),
        y: sub_mod_witness(
            &U256::from_le_u64s(&P256_MODULUS),
            &point.y,
            &U256::from_le_u64s(&P256_MODULUS),
        )
        .result
        .to_u256(),
    }
}

fn is_additive_inverse(lhs: &AffinePoint, rhs: &AffinePoint) -> bool {
    lhs.x == rhs.x
        && add_mod_witness(&lhs.y, &rhs.y, &U256::from_le_u64s(&P256_MODULUS))
            .result
            .to_u256()
            == U256::ZERO
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::fake_glv_chain::FakeGlvPrimitiveEcTraceClaim;
    use crate::projective::ProjectiveEcTraceClaim;
    use crate::public_inputs::PublicEcdsaInputClaim;
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
    use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{Signature, U256};
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo_constraint_framework::assert_constraints_on_polys;

    fn test_input(message_hash: u64, r: u64, s: u64) -> crate::types::EcdsaVerifyInput {
        crate::types::EcdsaVerifyInput {
            message_hash: scalar(message_hash),
            signature: Signature {
                r: scalar(r),
                s: scalar(s),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn build_table(
        message_hash: u64,
    ) -> (
        CertScalarInputClaim,
        FakeGlvScalarHintClaim,
        FakeGlvSelectorClaim,
        PreparedTableClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        let table =
            PreparedTableClaim::from_claims(&certs, &fake_glv, &selectors).expect("valid table");
        (certs, fake_glv, selectors, table)
    }

    fn prepared_table_ec_row_low_ram_config(trace: &PreparedTableEcTraceClaim) -> PcsConfig {
        let claim = PreparedTableEcRowProofClaim::from_trace(trace);
        let ids = claim.preprocessed_column_ids();
        let max_constraint_log_degree_bound = claim.max_constraint_log_degree_bound(&ids);
        let fri_config = FriConfig::new(5, 4, 64, 1);
        PcsConfig {
            pow_bits: 0,
            fri_config,
            lifting_log_size: Some(
                (max_constraint_log_degree_bound + fri_config.log_blowup_factor).max(10),
            ),
        }
    }

    fn prepared_table_projective_source_low_ram_config(
        trace: &PreparedTableEcTraceClaim,
    ) -> PcsConfig {
        let claim = PreparedTableProjectiveSourceProofClaim::from_prepared_trace(trace);
        let ids = claim.preprocessed_column_ids();
        let max_constraint_log_degree_bound = claim.max_constraint_log_degree_bound(&ids);
        let fri_config = FriConfig::new(5, 4, 64, 1);
        PcsConfig {
            pow_bits: 0,
            fri_config,
            lifting_log_size: Some(
                (max_constraint_log_degree_bound + fri_config.log_blowup_factor).max(10),
            ),
        }
    }

    #[test]
    fn prepared_table_generates_active_base_and_table16_points() {
        let (_, _, _, table) = build_table(42);

        assert_eq!(table.certs.len(), 2);
        for cert in &table.certs {
            assert_eq!(cert.cert_active.0, 1);
            for point in &cert.base {
                point.verify().expect("base point is canonical");
            }
            assert_eq!(cert.r3.inf.0, 0);
            assert_eq!(cert.table16.inf.0, 0);
        }
    }

    #[test]
    fn prepared_table_table16_matches_selector0_plus_r3() {
        let (_, _, selectors, table) = build_table(42);

        for (selector, cert) in selectors.rows.iter().zip(&table.certs) {
            let decoded = Selector16DecodeEntry::from_selector(selector.selectors[0]).unwrap();
            let selected = apply_selector(&cert.base, decoded).unwrap();
            let expected = prepared(add_optional_points(
                selected.to_option(),
                cert.r3.to_option(),
            ));

            assert_eq!(cert.table16, expected);
        }
    }

    #[test]
    fn prepared_table_inactive_cert_is_canonical_infinity() {
        let (_, _, _, table) = build_table(0);

        assert_eq!(table.certs[0].cert_active.0, 0);
        assert_eq!(
            table.certs[0].base,
            core::array::from_fn(|_| PreparedAffinePoint::infinity())
        );
        assert_eq!(table.certs[0].r3, PreparedAffinePoint::infinity());
        assert_eq!(table.certs[0].table16, PreparedAffinePoint::infinity());
        assert_eq!(table.certs[1].cert_active.0, 1);
    }

    #[test]
    fn prepared_table_ec_trace_records_expected_active_rows() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        trace.verify().expect("ec trace verifies");
        assert_eq!(trace.active_row_count(), 24);
        assert!(trace
            .rows
            .iter()
            .any(|row| row.kind == PreparedTableEcRowKind::Base(0)));
        assert!(trace
            .rows
            .iter()
            .any(|row| row.kind == PreparedTableEcRowKind::Table16));
    }

    #[test]
    fn prepared_table_ec_trace_skips_inactive_zero_branch() {
        let (certs, fake_glv, selectors, table) = build_table(0);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        assert_eq!(table.certs[0].cert_active.0, 0);
        assert_eq!(trace.active_row_count(), 13);
        assert!(trace
            .rows
            .iter()
            .all(|row| row.cert_id == table.certs[1].cert_id));
    }

    #[test]
    fn prepared_table_ec_trace_detects_mutated_output() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let mut trace =
            PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
                .expect("valid ec trace");
        trace.rows[0].output = PreparedAffinePoint::infinity();

        let err = trace.verify().expect_err("mutated output must fail");

        assert!(matches!(
            err,
            PreparedTableError::EcTraceOutputMismatch { .. }
        ));
    }

    #[test]
    fn prepared_table_ec_trace_links_outputs_to_table_points() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");

        trace
            .verify_against_table(&table)
            .expect("ec trace outputs match table points");
    }

    #[test]
    fn prepared_table_ec_row_constraints_pass_for_honest_trace() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        let claim = PreparedTableEcRowProofClaim::from_trace(&trace);
        let ids = claim.preprocessed_column_ids();
        let preprocessed =
            gen_prepared_table_ec_row_preprocessed_trace(claim.log_size, &ids).unwrap();
        let base = gen_prepared_table_ec_row_base_trace(&trace, claim.log_size).unwrap();
        let mut channel = Blake2sChannel::default();
        let relation = PreparedTableEcRowRelation::draw(&mut channel);
        let (interaction, interaction_claim) =
            gen_prepared_table_ec_row_interaction_trace(&base, &relation);
        let trace_polys = TreeVec::new(vec![preprocessed, base, interaction]).map(|trace| {
            trace
                .into_iter()
                .map(|column| column.interpolate())
                .collect::<Vec<_>>()
        });

        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(claim.log_size),
            |eval| {
                PreparedTableEcRowEval {
                    log_size: claim.log_size,
                    relation: relation.clone(),
                }
                .evaluate(eval);
            },
            interaction_claim.claimed_sum,
        );
    }

    #[test]
    fn prepared_table_ec_row_proof_slice_proves_and_verifies() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        let proof = prove_prepared_table_ec_row_proof_slice::<Blake2sMerkleChannel>(
            &trace,
            prepared_table_ec_row_low_ram_config(&trace),
        )
        .expect("prepared-table EC row provider slice proves");

        verify_prepared_table_ec_row_proof_slice::<Blake2sMerkleChannel>(proof)
            .expect("prepared-table EC row provider slice verifies");
    }

    #[test]
    fn prepared_table_projective_source_proof_slice_proves_and_verifies() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let prepared =
            PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
                .expect("valid ec trace");
        let projective = ProjectiveEcTraceClaim::from_native_traces(
            &prepared,
            &FakeGlvPrimitiveEcTraceClaim { rows: vec![] },
        )
        .expect("projective trace builds");
        let proof = prove_prepared_table_projective_source_proof_slice::<Blake2sMerkleChannel>(
            &prepared,
            &projective,
            prepared_table_projective_source_low_ram_config(&prepared),
        )
        .expect("prepared-table projective source link proves");

        verify_prepared_table_projective_source_proof_slice::<Blake2sMerkleChannel>(proof)
            .expect("prepared-table projective source link verifies");
    }

    #[test]
    fn prepared_table_projective_source_proof_slice_rejects_mutated_prefix() {
        let (certs, fake_glv, selectors, table) = build_table(42);
        let prepared =
            PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
                .expect("valid ec trace");
        let mut projective = ProjectiveEcTraceClaim::from_native_traces(
            &prepared,
            &FakeGlvPrimitiveEcTraceClaim { rows: vec![] },
        )
        .expect("projective trace builds");
        projective.rows[0].sig_id += M31::from_u32_unchecked(1);

        let err = prove_prepared_table_projective_source_proof_slice::<Blake2sMerkleChannel>(
            &prepared,
            &projective,
            prepared_table_projective_source_low_ram_config(&prepared),
        )
        .expect_err("mutated projective source tuple must not balance");

        assert!(matches!(
            err,
            PreparedTableError::RelationImbalance {
                relation: "PreparedTableProjectiveSource"
            }
        ));
    }

    #[test]
    fn prepared_table_ec_trace_detects_mutated_table_output_link() {
        let (certs, fake_glv, selectors, mut table) = build_table(42);
        let trace = PreparedTableEcTraceClaim::from_claims(&certs, &fake_glv, &selectors, &table)
            .expect("valid ec trace");
        table.certs[0].base[0] = PreparedAffinePoint::infinity();

        let err = trace
            .verify_against_table(&table)
            .expect_err("mutated table output link must fail");

        assert!(matches!(
            err,
            PreparedTableError::EcTraceExpectedOutputMismatch { label: "Base", .. }
        ));
    }

    #[test]
    fn prepared_table_prepared_point_trace_matches_table_and_use_counts() {
        let (_, _, selectors, table) = build_table(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let prepared_trace = table
            .prepared_point_trace(&use_counts)
            .expect("prepared trace generates");

        table
            .verify_prepared_point_trace(&use_counts, &prepared_trace)
            .expect("prepared providers match table");
    }

    #[test]
    fn prepared_table_prepared_point_trace_detects_mutated_provider() {
        let (_, _, selectors, table) = build_table(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let mut prepared_trace = table
            .prepared_point_trace(&use_counts)
            .expect("prepared trace generates");
        prepared_trace.providers[0].instance.x = P256M31BigInt::zero();

        let err = table
            .verify_prepared_point_trace(&use_counts, &prepared_trace)
            .expect_err("mutated provider must fail");

        assert_eq!(err, PreparedTableError::PreparedPointTraceMismatch);
    }
}
