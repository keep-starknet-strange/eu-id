use stwo::core::{
    air::Component,
    channel::Channel,
    channel::MerkleChannel,
    fields::{m31::M31, qm31::SecureField},
    fri::FriConfig,
    pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec},
    poly::circle::CanonicCoset,
    proof::StarkProof,
    vcs_lifted::merkle_hasher::MerkleHasherLifted,
    verifier::verify,
    ColumnVec,
};
use stwo::prover::{
    backend::{simd::SimdBackend, BackendForChannel},
    poly::circle::PolyOps,
    prove, CommitmentSchemeProver, ComponentProver,
};
use stwo_constraint_framework::{
    preprocessed_columns::PreProcessedColumnId, TraceLocationAllocator,
};

use crate::ecdsa::ecdsa_verify;
use crate::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError, FakeGlvPrimitiveEcTraceClaim};
use crate::fake_glv_chain_continuity::{
    gen_fake_glv_chain_continuity_base_trace, gen_fake_glv_chain_continuity_interaction_trace,
    gen_fake_glv_chain_continuity_preprocessed_trace, prove_fake_glv_chain_continuity_proof_slice,
    verify_fake_glv_chain_continuity_proof_slice, FakeGlvChainAccumulatorRelation,
    FakeGlvChainContinuityComponent, FakeGlvChainContinuityEval,
    FakeGlvChainContinuityInteractionClaim, FakeGlvChainContinuityProof,
    FakeGlvChainContinuityProofClaim,
};
use crate::fake_glv_chain_expansion::{
    gen_fake_glv_chain_expansion_base_trace, gen_fake_glv_chain_expansion_interaction_trace,
    gen_fake_glv_chain_expansion_preprocessed_trace,
    gen_fake_glv_primitive_expansion_consumer_base_trace,
    gen_fake_glv_primitive_expansion_consumer_interaction_trace,
    prove_fake_glv_chain_expansion_proof_slice, verify_fake_glv_chain_expansion_proof_slice,
    FakeGlvChainExpansionComponents, FakeGlvChainExpansionInteractionClaim,
    FakeGlvChainExpansionProof, FakeGlvChainExpansionProofClaim,
    FakeGlvChainPrimitiveExpansionRelation,
};
use crate::fake_glv_chain_schedule::{
    gen_fake_glv_chain_schedule_base_trace, gen_fake_glv_chain_schedule_preprocessed_trace,
    prove_fake_glv_chain_schedule_proof_slice, verify_fake_glv_chain_schedule_proof_slice,
    FakeGlvChainScheduleComponent, FakeGlvChainScheduleEval, FakeGlvChainScheduleProof,
    FakeGlvChainScheduleProofClaim,
};
use crate::fake_glv_direct_prepared_operand::{
    gen_direct_operand_consumer_base_trace, gen_direct_operand_consumer_interaction_trace,
    gen_direct_operand_preprocessed_trace, gen_direct_operand_provider_base_trace,
    gen_direct_operand_provider_interaction_trace,
    prove_fake_glv_direct_prepared_operand_proof_slice,
    verify_fake_glv_direct_prepared_operand_proof_slice, FakeGlvDirectPreparedOperandComponents,
    FakeGlvDirectPreparedOperandInteractionClaim, FakeGlvDirectPreparedOperandProof,
    FakeGlvDirectPreparedOperandProofClaim,
};
use crate::fake_glv_ec_source::{
    gen_fake_glv_primitive_ec_preprocessed_trace, gen_fake_glv_primitive_ec_source_base_trace,
    gen_fake_glv_primitive_ec_source_interaction_trace, gen_fake_glv_projective_source_base_trace,
    prove_fake_glv_projective_source_proof_slice, verify_fake_glv_projective_source_proof_slice,
    FakeGlvPrimitiveEcRowRelation, FakeGlvProjectiveSourceComponents,
    FakeGlvProjectiveSourceInteractionClaim, FakeGlvProjectiveSourceProof,
    FakeGlvProjectiveSourceProofClaim, RelationMultiplicity,
};
use crate::fake_glv_lsb_correction_operand::{
    gen_lsb_correction_operand_consumer_base_trace, gen_lsb_correction_operand_interaction_trace,
    gen_lsb_correction_operand_preprocessed_trace, gen_lsb_correction_operand_provider_base_trace,
    prove_fake_glv_lsb_correction_operand_proof_slice,
    verify_fake_glv_lsb_correction_operand_proof_slice, FakeGlvLsbCorrectionOperandComponents,
    FakeGlvLsbCorrectionOperandInteractionClaim, FakeGlvLsbCorrectionOperandProof,
    FakeGlvLsbCorrectionOperandProofClaim, FakeGlvLsbCorrectionOperandRelation,
};
use crate::fake_glv_prepared_point_source::{
    gen_fake_glv_prepared_point_consumer_base_trace,
    gen_fake_glv_prepared_point_consumer_interaction_trace,
    gen_fake_glv_prepared_point_source_preprocessed_trace, gen_prepared_point_provider_base_trace,
    gen_prepared_point_provider_interaction_trace,
    prove_fake_glv_prepared_point_source_proof_slice,
    verify_fake_glv_prepared_point_source_proof_slice, FakeGlvPreparedPointSourceComponents,
    FakeGlvPreparedPointSourceInteractionClaim, FakeGlvPreparedPointSourceProof,
    FakeGlvPreparedPointSourceProofClaim,
};
use crate::final_check::{FinalEcdsaCheckClaim, FinalEcdsaCheckError};
use crate::prepared_point::{
    prepared_point_provider_claimed_sum, prepared_point_range7_consumer_claimed_sum,
    PreparedPointAudit, PreparedPointError, PreparedPointRelation, PreparedPointTraceClaim,
    PreparedPointUseCountClaim,
};
use crate::prepared_table::{
    gen_prepared_table_ec_row_base_trace, gen_prepared_table_ec_row_interaction_trace,
    gen_prepared_table_ec_row_preprocessed_trace, gen_prepared_table_projective_source_base_trace,
    gen_prepared_table_projective_source_interaction_trace,
    prove_prepared_table_ec_row_proof_slice, prove_prepared_table_projective_source_proof_slice,
    verify_prepared_table_ec_row_proof_slice, verify_prepared_table_projective_source_proof_slice,
    PreparedTableClaim, PreparedTableEcRowProof, PreparedTableEcRowProofClaim,
    PreparedTableEcRowRelation, PreparedTableEcTraceClaim, PreparedTableError,
    PreparedTableProjectiveSourceComponents, PreparedTableProjectiveSourceInteractionClaim,
    PreparedTableProjectiveSourceProof, PreparedTableProjectiveSourceProofClaim,
};
use crate::projective::{ProjectiveEcError, ProjectiveEcTraceClaim};
use crate::projective_air::{
    projective_rcb_signed_carry_log_size, prove_projective_rcb_air_proof_slice,
    verify_projective_rcb_air_proof_slice, ProjectiveRcbAirComponents, ProjectiveRcbAirError,
    ProjectiveRcbAirInteractionClaim, ProjectiveRcbAirProof, ProjectiveRcbAirProofClaim,
    ProjectiveRcbAirProofInteractionClaim, ProjectiveRcbAirTraceClaim,
    ProjectiveRcbMulComponentRelations, PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::public_inputs::{
    public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
};
use crate::public_key_check::{PublicKeyOnCurveClaim, PublicKeyOnCurveError};
use crate::range_checks::{
    range_check_value_column_id, RangeCheckClaim, RangeCheckComponent, RangeCheckEval,
    RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim, RANGE13_BITS,
    RANGE7_BITS,
};
use crate::scalar::cert_bind::{
    gen_cert_scalar_input_air_base_trace, gen_cert_scalar_input_air_interaction_trace,
    CertScalarInputAirComponents, CertScalarInputAirInteractionClaim, CertScalarInputAirProofClaim,
    CertScalarInputClaim, CertScalarInputError, CertScalarInputRelation,
};
use crate::scalar::fake_glv_scalar::{
    gen_fake_glv_scalar_air_base_trace, gen_fake_glv_scalar_air_interaction_trace,
    FakeGlvScalarAirComponents, FakeGlvScalarAirInteractionClaim, FakeGlvScalarAirProofClaim,
    FakeGlvScalarHint, FakeGlvScalarHintClaim, FakeGlvScalarHintError, FakeGlvScalarRelation,
};
use crate::scalar::fake_glv_selector::{
    gen_fake_glv_selector_air_base_trace, gen_fake_glv_selector_air_interaction_trace,
    FakeGlvSelectorAirComponents, FakeGlvSelectorAirInteractionClaim,
    FakeGlvSelectorAirProofClaim, FakeGlvSelectorClaim, FakeGlvSelectorError,
};
use crate::scalar::fake_glv_selector_lookup::{
    prove_selector_lookup_provider_proof_slice, selector_lookup_consumer_claimed_sum,
    verify_selector_lookup_provider_proof_slice, FakeGlvSelectorLookupRelations,
    SelectorLookupAudit, SelectorLookupError, SelectorLookupProviderProof,
    SelectorLookupProviderProofClaim, SelectorLookupRequests, SelectorProviderInteractionClaim,
};
use crate::scalar::fake_glv_signed_selector_operand::{
    gen_signed_selector_operand_consumer_base_trace, gen_signed_selector_operand_interaction_trace,
    gen_signed_selector_operand_preprocessed_trace,
    gen_signed_selector_operand_provider_base_trace,
    prove_fake_glv_signed_selector_operand_proof_slice,
    verify_fake_glv_signed_selector_operand_proof_slice, FakeGlvSignedSelectorOperandComponents,
    FakeGlvSignedSelectorOperandInteractionClaim, FakeGlvSignedSelectorOperandProof,
    FakeGlvSignedSelectorOperandProofClaim, FakeGlvSignedSelectorOperandRelation,
};
use crate::scalar::scalar_mod_mul::claim::{
    gen_base_trace as gen_scalar_mod_mul_base_trace,
    gen_interaction_trace as gen_scalar_mod_mul_interaction_trace,
    gen_preprocessed_trace as gen_scalar_mod_mul_preprocessed_trace,
    preprocessed_column_ids as scalar_mod_mul_preprocessed_column_ids, ScalarModMulComponents,
};
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;
use crate::scalar::scalar_mod_mul::interaction_claim::{
    zero_interaction_claim, ScalarModMulProofSliceInteractionClaim,
};
use crate::scalar::scalar_mod_mul::providers::LookupProviderClaims;
use crate::scalar::scalar_mod_mul::relation::ScalarModMulLookupRelations;
use crate::scalar::scalar_mod_mul::{
    ScalarModMulClaim, ScalarModMulTraceError, ScalarModMulTraceRows,
};
use crate::scalar::setup_air::{
    gen_scalar_setup_air_base_trace, gen_scalar_setup_air_interaction_trace,
    gen_scalar_setup_air_lookup_provider_base_trace, gen_scalar_setup_air_preprocessed_trace,
    scalar_setup_air_preprocessed_column_ids, ScalarSetupAirComponents,
    ScalarSetupAirInteractionClaim, ScalarSetupAirProofClaim, ScalarSetupAirRelations,
    ScalarSetupClaim, ScalarSetupClaimError, ScalarSetupOutputRelation,
};
use crate::types::EcdsaVerifyInput;

#[derive(Clone, Debug)]
pub struct P256ProofClaim {
    pub public_inputs: PublicEcdsaInputClaim,
    pub public_key_check: PublicKeyOnCurveClaim,
    pub scalar_setup: ScalarSetupClaim,
    pub cert_inputs: CertScalarInputClaim,
    pub fake_glv_scalars: FakeGlvScalarHintClaim,
    pub fake_glv_selectors: FakeGlvSelectorClaim,
    pub selector_requests: SelectorLookupRequests,
    pub prepared_table: PreparedTableClaim,
    pub prepared_table_ec_trace: PreparedTableEcTraceClaim,
    pub fake_glv_chain: FakeGlvChainClaim,
    pub fake_glv_ec_trace: FakeGlvPrimitiveEcTraceClaim,
    pub projective_ec_trace: ProjectiveEcTraceClaim,
    pub projective_rcb_air_trace: ProjectiveRcbAirTraceClaim,
    pub final_check: FinalEcdsaCheckClaim,
    pub prepared_use_counts: PreparedPointUseCountClaim,
    pub prepared_trace: PreparedPointTraceClaim,
}

impl P256ProofClaim {
    pub fn from_inputs_with_hints(
        inputs: &[EcdsaVerifyInput],
        fake_glv_hints: Vec<FakeGlvScalarHint>,
    ) -> Result<Self, P256ProofError> {
        let public_inputs = PublicEcdsaInputClaim::from_inputs(inputs);
        let public_key_check = PublicKeyOnCurveClaim::from_public_inputs(&public_inputs)?;
        let scalar_setup = ScalarSetupClaim::from_public_inputs(&public_inputs)?;
        let cert_inputs = CertScalarInputClaim::from_scalar_setup(&scalar_setup)?;
        let fake_glv_scalars =
            FakeGlvScalarHintClaim::from_cert_inputs(&cert_inputs, fake_glv_hints)?;
        let fake_glv_selectors = FakeGlvSelectorClaim::from_scalar_hints(&fake_glv_scalars)?;
        let selector_requests = SelectorLookupRequests::from_selector_claim(&fake_glv_selectors)?;
        let prepared_table =
            PreparedTableClaim::from_claims(&cert_inputs, &fake_glv_scalars, &fake_glv_selectors)?;
        let prepared_table_ec_trace = PreparedTableEcTraceClaim::from_claims(
            &cert_inputs,
            &fake_glv_scalars,
            &fake_glv_selectors,
            &prepared_table,
        )?;
        let fake_glv_chain = FakeGlvChainClaim::from_claims(
            &cert_inputs,
            &fake_glv_scalars,
            &fake_glv_selectors,
            &prepared_table,
        )?;
        let fake_glv_ec_trace = FakeGlvPrimitiveEcTraceClaim::from_chain(&fake_glv_chain)?;
        let projective_ec_trace = ProjectiveEcTraceClaim::from_native_traces(
            &prepared_table_ec_trace,
            &fake_glv_ec_trace,
        )?;
        let projective_rcb_air_trace =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&projective_ec_trace)?;
        let final_check = FinalEcdsaCheckClaim::from_claims(
            &public_inputs,
            &cert_inputs,
            &fake_glv_scalars,
            &fake_glv_chain,
        )?;
        let prepared_use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&fake_glv_selectors)?;
        let prepared_trace = prepared_table.prepared_point_trace(&prepared_use_counts)?;

        Ok(Self {
            public_inputs,
            public_key_check,
            scalar_setup,
            cert_inputs,
            fake_glv_scalars,
            fake_glv_selectors,
            selector_requests,
            prepared_table,
            prepared_table_ec_trace,
            fake_glv_chain,
            fake_glv_ec_trace,
            projective_ec_trace,
            projective_rcb_air_trace,
            final_check,
            prepared_use_counts,
            prepared_trace,
        })
    }

    pub fn from_inputs_with_trivial_fake_glv_hints(
        inputs: &[EcdsaVerifyInput],
    ) -> Result<Self, P256ProofError> {
        let public_inputs = PublicEcdsaInputClaim::from_inputs(inputs);
        let scalar_setup = ScalarSetupClaim::from_public_inputs(&public_inputs)?;
        let cert_inputs = CertScalarInputClaim::from_scalar_setup(&scalar_setup)?;
        let hints = cert_inputs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar))
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_inputs_with_hints(inputs, hints)
    }

    pub fn verify_current_components(&self) -> Result<(), P256ProofError> {
        self.public_key_check.verify()?;
        self.scalar_setup.verify()?;
        self.cert_inputs.verify()?;
        self.fake_glv_scalars.verify()?;
        self.fake_glv_selectors.verify(&self.fake_glv_scalars)?;
        self.selector_requests.verify()?;
        self.prepared_table.verify()?;
        self.prepared_table_ec_trace.verify()?;
        self.prepared_table_ec_trace
            .verify_against_table(&self.prepared_table)?;
        self.fake_glv_chain.verify()?;
        self.fake_glv_chain.verify_against_claims(
            &self.cert_inputs,
            &self.fake_glv_scalars,
            &self.fake_glv_selectors,
            &self.prepared_table,
        )?;
        self.fake_glv_ec_trace
            .verify_against_chain(&self.fake_glv_chain)?;
        self.projective_ec_trace.verify()?;
        self.projective_ec_trace
            .verify_against_native_traces(&self.prepared_table_ec_trace, &self.fake_glv_ec_trace)?;
        self.projective_rcb_air_trace
            .verify_against_projective_trace(&self.projective_ec_trace)?;
        self.projective_rcb_air_trace.verify_preprocessed_trace()?;
        self.projective_rcb_air_trace.verify_base_trace()?;
        self.final_check.verify()?;
        self.prepared_use_counts.verify()?;
        self.prepared_table
            .verify_prepared_point_trace(&self.prepared_use_counts, &self.prepared_trace)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct P256ProofRelations {
    pub public_inputs: PublicEcdsaInstanceRelation,
    pub selector_lookups: FakeGlvSelectorLookupRelations,
    pub prepared_points: PreparedPointRelation,
    pub range7: RangeCheckRelation,
    pub projective_rcb: ProjectiveRcbMulComponentRelations,
}

impl P256ProofRelations {
    pub fn dummy() -> Self {
        Self {
            public_inputs: PublicEcdsaInstanceRelation::dummy(),
            selector_lookups: FakeGlvSelectorLookupRelations::dummy(),
            prepared_points: PreparedPointRelation::dummy(),
            range7: RangeCheckRelation::dummy(),
            projective_rcb: ProjectiveRcbMulComponentRelations::dummy(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct P256ProofInteractionClaim {
    pub public_inputs: RelationBalanceClaim,
    pub selector_lookups: RelationBalanceClaim,
    pub prepared_points: RelationBalanceClaim,
    pub range7: RelationBalanceClaim,
    pub projective_range13: RelationBalanceClaim,
    pub projective_signed_carry: RelationBalanceClaim,
    pub projective_rcb: ProjectiveRcbAirInteractionClaim,
}

impl P256ProofInteractionClaim {
    pub fn from_claim(claim: &P256ProofClaim, relations: &P256ProofRelations) -> Self {
        let public_provider = claim
            .public_inputs
            .initial_logup_claim(&relations.public_inputs)
            .claimed_sum;
        let public_consumer = public_ecdsa_consumer_claimed_sum(
            &claim.scalar_setup.public_consumers(),
            &relations.public_inputs,
        );

        let (_, selector_provider_interaction) =
            SelectorProviderInteractionClaim::gen_interaction_traces(
                &claim.selector_requests,
                &relations.selector_lookups,
            );
        let selector_provider = selector_provider_interaction.claimed_sum();
        let selector_consumer = selector_lookup_consumer_claimed_sum(
            &claim.selector_requests,
            &relations.selector_lookups,
        );

        let prepared_provider = prepared_point_provider_claimed_sum(
            &claim.prepared_trace.providers,
            &relations.prepared_points,
        );
        let prepared_consumer = crate::prepared_point::prepared_point_consumer_claimed_sum(
            &claim.fake_glv_chain.prepared_point_consumers(),
            &relations.prepared_points,
        );

        let range7 = RangeCheckClaim::new(RANGE7_BITS);
        let range7_values = range7.gen_preprocessed_column();
        let range7_multiplicity =
            range7.gen_multiplicity_trace(claim.prepared_use_counts.range7_use_count_values());
        let (_, range7_provider_interaction) = RangeCheckInteractionClaim::gen_interaction_trace(
            &range7_multiplicity,
            &range7_values,
            &relations.range7,
        );
        let range7_consumer = prepared_point_range7_consumer_claimed_sum(
            &claim.prepared_use_counts,
            &relations.range7,
        );
        let projective_range13 = RangeCheckClaim::new(RANGE13_BITS);
        let projective_range13_values = projective_range13.gen_preprocessed_column();
        let projective_range13_multiplicity = projective_range13
            .gen_multiplicity_trace(claim.projective_rcb_air_trace.range13_lookup_values());
        let (_, projective_range13_provider_interaction) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &projective_range13_multiplicity,
                &projective_range13_values,
                &relations.projective_rcb.range13,
            );
        let projective_range13_consumer = claim
            .projective_rcb_air_trace
            .range13_consumer_claimed_sum(&relations.projective_rcb.range13);

        let projective_signed_carry = SignedCarryRangeClaim::new(
            projective_rcb_signed_carry_log_size(),
            PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
            PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
        );
        let projective_signed_carry_values = projective_signed_carry.gen_value_column();
        let projective_signed_carry_multiplicity = projective_signed_carry.gen_multiplicity_trace(
            claim
                .projective_rcb_air_trace
                .signed_carry_lookup_values()
                .expect("verified projective RCB signed carries fit fixed bound"),
        );
        let (_, projective_signed_carry_provider_interaction) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &projective_signed_carry_multiplicity,
                &projective_signed_carry_values,
                &relations.projective_rcb.signed_carry,
            );
        let projective_signed_carry_consumer = claim
            .projective_rcb_air_trace
            .signed_carry_consumer_claimed_sum(&relations.projective_rcb.signed_carry)
            .expect("verified projective RCB signed carries fit fixed bound");
        let projective_rcb = claim
            .projective_rcb_air_trace
            .internal_interaction_claim(&relations.projective_rcb);

        Self {
            public_inputs: RelationBalanceClaim::new(public_provider, public_consumer),
            selector_lookups: RelationBalanceClaim::new(selector_provider, selector_consumer),
            prepared_points: RelationBalanceClaim::new(prepared_provider, prepared_consumer),
            range7: RelationBalanceClaim::new(
                range7_provider_interaction.claimed_sum,
                range7_consumer,
            ),
            projective_range13: RelationBalanceClaim::new(
                projective_range13_provider_interaction.claimed_sum,
                projective_range13_consumer,
            ),
            projective_signed_carry: RelationBalanceClaim::new(
                projective_signed_carry_provider_interaction.claimed_sum,
                projective_signed_carry_consumer,
            ),
            projective_rcb,
        }
    }

    pub fn verify_balanced(&self) -> Result<(), P256ProofError> {
        self.public_inputs.verify("PublicEcdsaInstance")?;
        self.selector_lookups.verify("SelectorLookups")?;
        self.prepared_points.verify("PreparedPoint")?;
        self.range7.verify("Range7")?;
        self.projective_range13.verify("ProjectiveRange13")?;
        self.projective_signed_carry
            .verify("ProjectiveSignedCarry")?;
        self.projective_rcb.verify_balanced()?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationBalanceClaim {
    pub provider_claimed_sum: SecureField,
    pub consumer_claimed_sum: SecureField,
}

impl RelationBalanceClaim {
    pub fn new(provider_claimed_sum: SecureField, consumer_claimed_sum: SecureField) -> Self {
        Self {
            provider_claimed_sum,
            consumer_claimed_sum,
        }
    }

    pub fn total(self) -> SecureField {
        self.provider_claimed_sum + self.consumer_claimed_sum
    }

    fn verify(self, relation: &'static str) -> Result<(), P256ProofError> {
        if self.total() == zero() {
            Ok(())
        } else {
            Err(P256ProofError::RelationImbalance { relation })
        }
    }
}

#[derive(Clone, Debug)]
pub struct P256ProofDraft {
    pub inputs: Vec<EcdsaVerifyInput>,
    pub claim: P256ProofClaim,
    pub relations: P256ProofRelations,
    pub interaction_claim: P256ProofInteractionClaim,
}

#[derive(Clone, Debug)]
pub struct P256StarkProofSlices<H: MerkleHasherLifted> {
    pub selector_lookup: SelectorLookupProviderProof<H>,
    pub prepared_table_ec_rows: PreparedTableEcRowProof<H>,
    pub prepared_table_projective_source: PreparedTableProjectiveSourceProof<H>,
    pub fake_glv_projective_source: FakeGlvProjectiveSourceProof<H>,
    pub fake_glv_chain_expansion: FakeGlvChainExpansionProof<H>,
    pub fake_glv_chain_continuity: FakeGlvChainContinuityProof<H>,
    pub fake_glv_chain_schedule: FakeGlvChainScheduleProof<H>,
    pub fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandProof<H>,
    pub fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandProof<H>,
    pub fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandProof<H>,
    pub fake_glv_prepared_point_source: FakeGlvPreparedPointSourceProof<H>,
    pub projective_rcb_air: ProjectiveRcbAirProof<H>,
}

impl<H: MerkleHasherLifted> P256StarkProofSlices<H> {
    pub fn verify<MC>(self) -> Result<(), P256ProofError>
    where
        MC: MerkleChannel<H = H>,
    {
        let Self {
            selector_lookup,
            prepared_table_ec_rows,
            prepared_table_projective_source,
            fake_glv_projective_source,
            fake_glv_chain_expansion,
            fake_glv_chain_continuity,
            fake_glv_chain_schedule,
            fake_glv_direct_prepared_operand,
            fake_glv_signed_selector_operand,
            fake_glv_lsb_correction_operand,
            fake_glv_prepared_point_source,
            projective_rcb_air,
        } = self;

        verify_selector_lookup_provider_proof_slice::<MC>(selector_lookup)?;
        verify_prepared_table_ec_row_proof_slice::<MC>(prepared_table_ec_rows)?;
        verify_prepared_table_projective_source_proof_slice::<MC>(
            prepared_table_projective_source,
        )?;
        verify_fake_glv_projective_source_proof_slice::<MC>(fake_glv_projective_source)?;
        verify_fake_glv_chain_expansion_proof_slice::<MC>(fake_glv_chain_expansion)?;
        verify_fake_glv_chain_continuity_proof_slice::<MC>(fake_glv_chain_continuity)?;
        verify_fake_glv_chain_schedule_proof_slice::<MC>(fake_glv_chain_schedule)?;
        verify_fake_glv_direct_prepared_operand_proof_slice::<MC>(
            fake_glv_direct_prepared_operand,
        )?;
        verify_fake_glv_signed_selector_operand_proof_slice::<MC>(
            fake_glv_signed_selector_operand,
        )?;
        verify_fake_glv_lsb_correction_operand_proof_slice::<MC>(fake_glv_lsb_correction_operand)?;
        verify_fake_glv_prepared_point_source_proof_slice::<MC>(fake_glv_prepared_point_source)?;
        verify_projective_rcb_air_proof_slice::<MC>(projective_rcb_air)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct P256CurrentAirProof<H: MerkleHasherLifted> {
    pub claim: P256CurrentAirProofClaim,
    pub interaction_claim: P256CurrentAirInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct P256CurrentAirProofClaim {
    pub public_inputs: PublicEcdsaInputClaim,
    pub scalar_setup: ScalarSetupAirProofClaim,
    pub cert_scalar_inputs: CertScalarInputAirProofClaim,
    pub fake_glv_scalar_air: FakeGlvScalarAirProofClaim,
    pub fake_glv_selector_air: FakeGlvSelectorAirProofClaim,
    pub scalar_setup_mod_muls: Vec<ScalarModMulClaim>,
    pub prepared_table_projective_source: PreparedTableProjectiveSourceProofClaim,
    pub fake_glv_projective_source: FakeGlvProjectiveSourceProofClaim,
    pub fake_glv_chain_expansion: FakeGlvChainExpansionProofClaim,
    pub fake_glv_chain_continuity: FakeGlvChainContinuityProofClaim,
    pub fake_glv_chain_schedule: FakeGlvChainScheduleProofClaim,
    pub fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandProofClaim,
    pub fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandProofClaim,
    pub fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandProofClaim,
    pub fake_glv_prepared_point_source: FakeGlvPreparedPointSourceProofClaim,
    pub prepared_point_range7: RangeCheckClaim,
    pub projective_rcb_air: ProjectiveRcbAirProofClaim,
}

impl P256CurrentAirProofClaim {
    fn from_claim(claim: &P256ProofClaim) -> Self {
        let source_offset = claim.prepared_table_ec_trace.active_row_count();
        Self {
            public_inputs: claim.public_inputs.clone(),
            scalar_setup: ScalarSetupAirProofClaim::from_claim(&claim.scalar_setup),
            cert_scalar_inputs: CertScalarInputAirProofClaim::from_claim(&claim.scalar_setup),
            fake_glv_scalar_air: FakeGlvScalarAirProofClaim::from_claim(&claim.fake_glv_scalars),
            fake_glv_selector_air: FakeGlvSelectorAirProofClaim::from_claim(
                &claim.fake_glv_selectors,
            ),
            scalar_setup_mod_muls: scalar_setup_mod_mul_rows(claim)
                .expect("verified scalar setup mod-mul rows generate")
                .iter()
                .map(ScalarModMulClaim::from_rows_with_external_limb_links)
                .collect(),
            prepared_table_projective_source:
                PreparedTableProjectiveSourceProofClaim::from_prepared_trace(
                    &claim.prepared_table_ec_trace,
                ),
            fake_glv_projective_source: FakeGlvProjectiveSourceProofClaim::from_fake_glv_trace(
                &claim.fake_glv_ec_trace,
                source_offset,
            ),
            fake_glv_chain_expansion: FakeGlvChainExpansionProofClaim::from_claims(
                &claim.fake_glv_chain,
                &claim.fake_glv_ec_trace,
                source_offset,
            ),
            fake_glv_chain_continuity: FakeGlvChainContinuityProofClaim::from_chain(
                &claim.fake_glv_chain,
            ),
            fake_glv_chain_schedule: FakeGlvChainScheduleProofClaim::from_chain(
                &claim.fake_glv_chain,
            ),
            fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandProofClaim::from_claims(
                &claim.fake_glv_selectors,
                &claim.fake_glv_chain,
            ),
            fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandProofClaim::from_claims(
                &claim.fake_glv_selectors,
                &claim.fake_glv_chain,
            ),
            fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandProofClaim::from_claims(
                &claim.fake_glv_selectors,
                &claim.fake_glv_chain,
            ),
            fake_glv_prepared_point_source: FakeGlvPreparedPointSourceProofClaim::from_claims(
                &claim.prepared_trace,
                &claim.fake_glv_chain,
            ),
            prepared_point_range7: RangeCheckClaim::new(RANGE7_BITS),
            projective_rcb_air: ProjectiveRcbAirProofClaim::from_trace(
                &claim.projective_rcb_air_trace,
            ),
        }
    }

    fn mix_into(&self, channel: &mut impl Channel) {
        self.public_inputs.mix_into(channel);
        self.scalar_setup.mix_into(channel);
        self.cert_scalar_inputs.mix_into(channel);
        self.fake_glv_scalar_air.mix_into(channel);
        self.fake_glv_selector_air.mix_into(channel);
        channel.mix_u64(self.scalar_setup_mod_muls.len() as u64);
        for claim in &self.scalar_setup_mod_muls {
            claim.mix_into(channel);
        }
        self.prepared_table_projective_source.mix_into(channel);
        self.fake_glv_projective_source.mix_into(channel);
        self.fake_glv_chain_expansion.mix_into(channel);
        self.fake_glv_chain_continuity.mix_into(channel);
        self.fake_glv_chain_schedule.mix_into(channel);
        self.fake_glv_direct_prepared_operand.mix_into(channel);
        self.fake_glv_signed_selector_operand.mix_into(channel);
        self.fake_glv_lsb_correction_operand.mix_into(channel);
        self.fake_glv_prepared_point_source.mix_into(channel);
        self.prepared_point_range7.mix_into(channel);
        self.projective_rcb_air.mix_into(channel);
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut ids = Vec::new();
        append_unique_preprocessed_ids(&mut ids, scalar_setup_air_preprocessed_column_ids());
        let lookup_claims = LookupProviderClaims::scalar_mod_mul();
        for claim in &self.scalar_setup_mod_muls {
            append_unique_preprocessed_ids(
                &mut ids,
                scalar_mod_mul_preprocessed_column_ids(claim, &lookup_claims),
            );
        }
        append_unique_preprocessed_ids(
            &mut ids,
            self.prepared_table_projective_source
                .preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_projective_source.preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_chain_expansion.preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_chain_continuity.preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_chain_schedule.preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_direct_prepared_operand
                .preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_signed_selector_operand
                .preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_lsb_correction_operand
                .preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.fake_glv_prepared_point_source
                .preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(
            &mut ids,
            vec![range_check_value_column_id(self.prepared_point_range7.log_size)],
        );
        append_unique_preprocessed_ids(&mut ids, self.projective_rcb_air.preprocessed_column_ids());
        ids
    }

    fn trace_log_degree_bounds(
        &self,
        ids: &[PreProcessedColumnId],
        interaction_claim: &P256CurrentAirInteractionClaim,
        relations: &P256CurrentAirRelations,
    ) -> TreeVec<ColumnVec<u32>> {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components =
            P256CurrentAirComponents::new(&mut allocator, self, interaction_claim, relations);
        let component_list = components.components();
        let mut bounds = components.trace_log_degree_bounds();
        let mut preprocessed_bounds = vec![0; ids.len()];
        let mut visited = vec![false; ids.len()];

        for component in component_list {
            let component_bounds = component.trace_log_degree_bounds();
            for (&index, &log_size) in std::iter::zip(
                component.preprocessed_column_indices().iter(),
                component_bounds[0].iter(),
            ) {
                if visited[index] {
                    assert_eq!(
                        preprocessed_bounds[index], log_size,
                        "preprocessed column {index} log-size mismatch"
                    );
                } else {
                    preprocessed_bounds[index] = log_size;
                    visited[index] = true;
                }
            }
        }
        assert!(
            visited.iter().all(|&is_visited| is_visited),
            "not all preprocessed columns are used by current-air components"
        );
        bounds[0] = preprocessed_bounds;
        bounds
    }

    fn max_constraint_log_degree_bound(&self, ids: &[PreProcessedColumnId]) -> u32 {
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids);
        let components = P256CurrentAirComponents::new(
            &mut allocator,
            self,
            &P256CurrentAirInteractionClaim::zero_for_claim(self),
            &P256CurrentAirRelations::dummy(),
        );
        components.max_constraint_log_degree_bound()
    }
}

#[derive(Clone, Debug)]
pub struct P256CurrentAirInteractionClaim {
    pub public_inputs: RelationBalanceClaim,
    pub scalar_setup: ScalarSetupAirInteractionClaim,
    pub cert_scalar_inputs: CertScalarInputAirInteractionClaim,
    pub fake_glv_scalar_air: FakeGlvScalarAirInteractionClaim,
    pub fake_glv_selector_air: FakeGlvSelectorAirInteractionClaim,
    pub(crate) scalar_setup_mod_muls: Vec<ScalarModMulProofSliceInteractionClaim>,
    pub prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim,
    pub fake_glv_projective_source: FakeGlvProjectiveSourceInteractionClaim,
    pub fake_glv_chain_expansion: FakeGlvChainExpansionInteractionClaim,
    pub fake_glv_chain_continuity: FakeGlvChainContinuityInteractionClaim,
    pub fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandInteractionClaim,
    pub fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandInteractionClaim,
    pub fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandInteractionClaim,
    pub fake_glv_prepared_point_source: FakeGlvPreparedPointSourceInteractionClaim,
    pub prepared_point_range7: RangeCheckInteractionClaim,
    pub projective_rcb_air: ProjectiveRcbAirProofInteractionClaim,
}

impl P256CurrentAirInteractionClaim {
    fn zero() -> Self {
        Self {
            public_inputs: RelationBalanceClaim {
                provider_claimed_sum: zero(),
                consumer_claimed_sum: zero(),
            },
            scalar_setup: ScalarSetupAirInteractionClaim::zero(),
            cert_scalar_inputs: CertScalarInputAirInteractionClaim::zero(),
            fake_glv_scalar_air: FakeGlvScalarAirInteractionClaim::zero(),
            fake_glv_selector_air: FakeGlvSelectorAirInteractionClaim::zero(),
            scalar_setup_mod_muls: Vec::new(),
            prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim::zero(),
            fake_glv_projective_source: FakeGlvProjectiveSourceInteractionClaim::zero(),
            fake_glv_chain_expansion: FakeGlvChainExpansionInteractionClaim::zero(),
            fake_glv_chain_continuity: FakeGlvChainContinuityInteractionClaim {
                claimed_sum: zero(),
            },
            fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandInteractionClaim::zero(),
            fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandInteractionClaim::zero(),
            fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandInteractionClaim::zero(),
            fake_glv_prepared_point_source: FakeGlvPreparedPointSourceInteractionClaim::zero(),
            prepared_point_range7: RangeCheckInteractionClaim {
                claimed_sum: zero(),
            },
            projective_rcb_air: ProjectiveRcbAirProofInteractionClaim::zero(),
        }
    }

    fn zero_for_claim(claim: &P256CurrentAirProofClaim) -> Self {
        let mut zero = Self::zero();
        zero.scalar_setup_mod_muls = (0..claim.scalar_setup_mod_muls.len())
            .map(|_| zero_interaction_claim())
            .collect();
        zero
    }

    fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.public_inputs.provider_claimed_sum,
            self.public_inputs.consumer_claimed_sum,
        ]);
        self.scalar_setup.mix_into(channel);
        self.cert_scalar_inputs.mix_into(channel);
        self.fake_glv_scalar_air.mix_into(channel);
        self.fake_glv_selector_air.mix_into(channel);
        channel.mix_u64(self.scalar_setup_mod_muls.len() as u64);
        for claim in &self.scalar_setup_mod_muls {
            claim.scalar_mod_mul.mix_into(channel);
            claim.range13.mix_into(channel);
            claim.signed_carry.mix_into(channel);
        }
        self.prepared_table_projective_source.mix_into(channel);
        self.fake_glv_projective_source.mix_into(channel);
        self.fake_glv_chain_expansion.mix_into(channel);
        self.fake_glv_chain_continuity.mix_into(channel);
        self.fake_glv_direct_prepared_operand.mix_into(channel);
        self.fake_glv_signed_selector_operand.mix_into(channel);
        self.fake_glv_lsb_correction_operand.mix_into(channel);
        self.fake_glv_prepared_point_source.mix_into(channel);
        self.prepared_point_range7.mix_into(channel);
        self.projective_rcb_air.mix_into(channel);
    }

    fn verify_balanced(&self) -> Result<(), P256ProofError> {
        self.public_inputs.verify("PublicEcdsaInstance")?;
        verify_current_air_relation_zero(
            "ScalarSetupOutput",
            self.scalar_setup.output_provider_claimed_sum
                + self.cert_scalar_inputs.scalar_setup_consumer_claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "CertScalarInput",
            self.cert_scalar_inputs.cert_provider_claimed_sum
                + self.fake_glv_scalar_air.cert_consumer_claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "FakeGlvScalar",
            self.fake_glv_scalar_air.scalar_provider_claimed_sum
                + self.fake_glv_selector_air.scalar_consumer_claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "ScalarSetupRange13",
            self.scalar_setup.range13_consumer_claimed_sum
                + self.scalar_setup.range13_provider.claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "ScalarSetupRange9",
            self.scalar_setup.range9_consumer_claimed_sum
                + self.scalar_setup.range9_provider.claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "ScalarSetupSignedCarry",
            self.scalar_setup.signed_carry_consumer_claimed_sum
                + self.scalar_setup.signed_carry_provider.claimed_sum,
        )?;
        let scalar_setup_mod_mul_total = self
            .scalar_setup_mod_muls
            .iter()
            .map(ScalarModMulProofSliceInteractionClaim::claimed_sum)
            .sum::<SecureField>()
            + self.scalar_setup.scalar_limb_consumer_claimed_sum;
        verify_current_air_relation_zero("ScalarSetupModMul", scalar_setup_mod_mul_total)?;
        verify_current_air_relation_zero(
            "PreparedTableProjectiveSource",
            self.prepared_table_projective_source.total(),
        )?;
        verify_current_air_relation_zero(
            "FakeGlvProjectiveSource",
            self.fake_glv_projective_source.total(),
        )?;
        verify_current_air_relation_zero(
            "FakeGlvChainExpansion",
            self.fake_glv_chain_expansion.total(),
        )?;
        verify_current_air_relation_zero(
            "FakeGlvChainContinuity",
            self.fake_glv_chain_continuity.claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "FakeGlvDirectPreparedOperand",
            self.fake_glv_direct_prepared_operand.total(),
        )?;
        verify_current_air_relation_zero(
            "FakeGlvSignedSelectorOperand",
            self.fake_glv_signed_selector_operand.total(),
        )?;
        verify_current_air_relation_zero(
            "FakeGlvLsbCorrectionOperand",
            self.fake_glv_lsb_correction_operand.total(),
        )?;
        verify_current_air_relation_zero(
            "FakeGlvPreparedPointSource",
            self.fake_glv_prepared_point_source.total(),
        )?;
        verify_current_air_relation_zero(
            "Range7",
            self.prepared_point_range7.claimed_sum
                + self.fake_glv_prepared_point_source.range7_consumer_claimed_sum,
        )?;
        verify_current_air_relation_zero(
            "ProjectiveRcbAirProofSlice",
            self.projective_rcb_air.total(),
        )
    }
}

#[derive(Clone)]
struct P256CurrentAirRelations {
    public_inputs: PublicEcdsaInstanceRelation,
    scalar_setup_output: ScalarSetupOutputRelation,
    cert_scalar_input: CertScalarInputRelation,
    fake_glv_scalar: FakeGlvScalarRelation,
    scalar_mod_mul: ScalarModMulLookupRelations,
    scalar_setup: ScalarSetupAirRelations,
    prepared_table: PreparedTableEcRowRelation,
    fake_glv_projective_source: FakeGlvPrimitiveEcRowRelation,
    fake_glv_chain_expansion: FakeGlvChainPrimitiveExpansionRelation,
    fake_glv_chain_continuity: FakeGlvChainAccumulatorRelation,
    direct_prepared_operand: PreparedPointRelation,
    signed_selector_operand: FakeGlvSignedSelectorOperandRelation,
    lsb_correction_operand: FakeGlvLsbCorrectionOperandRelation,
    prepared_point_source: PreparedPointRelation,
    range7: RangeCheckRelation,
    projective_rcb_air: ProjectiveRcbMulComponentRelations,
}

impl P256CurrentAirRelations {
    fn dummy() -> Self {
        let public_inputs = PublicEcdsaInstanceRelation::dummy();
        let scalar_setup_output = ScalarSetupOutputRelation::dummy();
        let cert_scalar_input = CertScalarInputRelation::dummy();
        let fake_glv_scalar = FakeGlvScalarRelation::dummy();
        let scalar_mod_mul = ScalarModMulLookupRelations::dummy();
        let scalar_setup = ScalarSetupAirRelations {
            public_inputs: public_inputs.clone(),
            output: scalar_setup_output.clone(),
            scalar_mod_mul: scalar_mod_mul.clone(),
            range13: RangeCheckRelation::dummy(),
            range9: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
        };
        Self {
            public_inputs,
            scalar_setup_output,
            cert_scalar_input,
            fake_glv_scalar,
            scalar_mod_mul,
            scalar_setup,
            prepared_table: PreparedTableEcRowRelation::dummy(),
            fake_glv_projective_source: FakeGlvPrimitiveEcRowRelation::dummy(),
            fake_glv_chain_expansion: FakeGlvChainPrimitiveExpansionRelation::dummy(),
            fake_glv_chain_continuity: FakeGlvChainAccumulatorRelation::dummy(),
            direct_prepared_operand: PreparedPointRelation::dummy(),
            signed_selector_operand: FakeGlvSignedSelectorOperandRelation::dummy(),
            lsb_correction_operand: FakeGlvLsbCorrectionOperandRelation::dummy(),
            prepared_point_source: PreparedPointRelation::dummy(),
            range7: RangeCheckRelation::dummy(),
            projective_rcb_air: ProjectiveRcbMulComponentRelations::dummy(),
        }
    }

    fn draw(channel: &mut impl Channel) -> Self {
        let public_inputs = PublicEcdsaInstanceRelation::draw(channel);
        let scalar_setup_output = ScalarSetupOutputRelation::draw(channel);
        let cert_scalar_input = CertScalarInputRelation::draw(channel);
        let fake_glv_scalar = FakeGlvScalarRelation::draw(channel);
        let scalar_mod_mul = ScalarModMulLookupRelations::draw(channel);
        let scalar_setup = ScalarSetupAirRelations {
            public_inputs: public_inputs.clone(),
            output: scalar_setup_output.clone(),
            scalar_mod_mul: scalar_mod_mul.clone(),
            range13: RangeCheckRelation::draw(channel),
            range9: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
        };
        Self {
            public_inputs,
            scalar_setup_output,
            cert_scalar_input,
            fake_glv_scalar,
            scalar_mod_mul,
            scalar_setup,
            prepared_table: PreparedTableEcRowRelation::draw(channel),
            fake_glv_projective_source: FakeGlvPrimitiveEcRowRelation::draw(channel),
            fake_glv_chain_expansion: FakeGlvChainPrimitiveExpansionRelation::draw(channel),
            fake_glv_chain_continuity: FakeGlvChainAccumulatorRelation::draw(channel),
            direct_prepared_operand: PreparedPointRelation::draw(channel),
            signed_selector_operand: FakeGlvSignedSelectorOperandRelation::draw(channel),
            lsb_correction_operand: FakeGlvLsbCorrectionOperandRelation::draw(channel),
            prepared_point_source: PreparedPointRelation::draw(channel),
            range7: RangeCheckRelation::draw(channel),
            projective_rcb_air: ProjectiveRcbMulComponentRelations::draw(channel),
        }
    }
}

struct P256CurrentAirComponents {
    scalar_setup: ScalarSetupAirComponents,
    cert_scalar_inputs: CertScalarInputAirComponents,
    fake_glv_scalar_air: FakeGlvScalarAirComponents,
    fake_glv_selector_air: FakeGlvSelectorAirComponents,
    scalar_setup_mod_muls: Vec<ScalarModMulComponents>,
    prepared_table_projective_source: PreparedTableProjectiveSourceComponents,
    fake_glv_projective_source: FakeGlvProjectiveSourceComponents,
    fake_glv_chain_expansion: FakeGlvChainExpansionComponents,
    fake_glv_chain_continuity: FakeGlvChainContinuityComponent,
    fake_glv_chain_schedule: FakeGlvChainScheduleComponent,
    fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandComponents,
    fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandComponents,
    fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandComponents,
    fake_glv_prepared_point_source: FakeGlvPreparedPointSourceComponents,
    prepared_point_range7: RangeCheckComponent,
    projective_rcb_air: ProjectiveRcbAirComponents,
}

impl P256CurrentAirComponents {
    fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &P256CurrentAirProofClaim,
        interaction_claim: &P256CurrentAirInteractionClaim,
        relations: &P256CurrentAirRelations,
    ) -> Self {
        let scalar_lookup_claims = LookupProviderClaims::scalar_mod_mul();
        Self {
            scalar_setup: ScalarSetupAirComponents::new(
                allocator,
                claim.scalar_setup,
                &interaction_claim.scalar_setup,
                &relations.scalar_setup,
            ),
            cert_scalar_inputs: CertScalarInputAirComponents::new(
                allocator,
                claim.cert_scalar_inputs,
                &interaction_claim.cert_scalar_inputs,
                &relations.scalar_setup_output,
                &relations.cert_scalar_input,
            ),
            fake_glv_scalar_air: FakeGlvScalarAirComponents::new(
                allocator,
                claim.fake_glv_scalar_air,
                &interaction_claim.fake_glv_scalar_air,
                &relations.cert_scalar_input,
                &relations.fake_glv_scalar,
            ),
            fake_glv_selector_air: FakeGlvSelectorAirComponents::new(
                allocator,
                claim.fake_glv_selector_air,
                &interaction_claim.fake_glv_selector_air,
                &relations.fake_glv_scalar,
            ),
            scalar_setup_mod_muls: claim
                .scalar_setup_mod_muls
                .iter()
                .zip(&interaction_claim.scalar_setup_mod_muls)
                .map(|(claim, interaction_claim)| {
                    ScalarModMulComponents::new(
                        allocator,
                        claim,
                        interaction_claim,
                        &scalar_lookup_claims,
                        &relations.scalar_mod_mul,
                    )
                })
                .collect(),
            prepared_table_projective_source: PreparedTableProjectiveSourceComponents::new(
                allocator,
                claim.prepared_table_projective_source.log_size,
                &interaction_claim.prepared_table_projective_source,
                &relations.prepared_table,
            ),
            fake_glv_projective_source: FakeGlvProjectiveSourceComponents::new(
                allocator,
                claim.fake_glv_projective_source.log_size,
                claim.fake_glv_projective_source.source_offset,
                &interaction_claim.fake_glv_projective_source,
                &relations.fake_glv_projective_source,
            ),
            fake_glv_chain_expansion: FakeGlvChainExpansionComponents::new(
                allocator,
                claim.fake_glv_chain_expansion,
                &interaction_claim.fake_glv_chain_expansion,
                &relations.fake_glv_chain_expansion,
            ),
            fake_glv_chain_continuity: FakeGlvChainContinuityComponent::new(
                allocator,
                FakeGlvChainContinuityEval {
                    log_size: claim.fake_glv_chain_continuity.log_size,
                    relation: relations.fake_glv_chain_continuity.clone(),
                },
                interaction_claim.fake_glv_chain_continuity.claimed_sum,
            ),
            fake_glv_chain_schedule: FakeGlvChainScheduleComponent::new(
                allocator,
                FakeGlvChainScheduleEval {
                    log_size: claim.fake_glv_chain_schedule.log_size,
                },
                zero(),
            ),
            fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandComponents::new(
                allocator,
                claim.fake_glv_direct_prepared_operand,
                &interaction_claim.fake_glv_direct_prepared_operand,
                &relations.direct_prepared_operand,
            ),
            fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandComponents::new(
                allocator,
                claim.fake_glv_signed_selector_operand,
                &interaction_claim.fake_glv_signed_selector_operand,
                &relations.signed_selector_operand,
            ),
            fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandComponents::new(
                allocator,
                claim.fake_glv_lsb_correction_operand,
                &interaction_claim.fake_glv_lsb_correction_operand,
                &relations.lsb_correction_operand,
            ),
            fake_glv_prepared_point_source: FakeGlvPreparedPointSourceComponents::new(
                allocator,
                claim.fake_glv_prepared_point_source,
                &interaction_claim.fake_glv_prepared_point_source,
                &relations.prepared_point_source,
                &relations.range7,
            ),
            prepared_point_range7: RangeCheckComponent::new(
                allocator,
                RangeCheckEval::new(
                    relations.range7.clone(),
                    claim.prepared_point_range7.log_size,
                ),
                interaction_claim.prepared_point_range7.claimed_sum,
            ),
            projective_rcb_air: ProjectiveRcbAirComponents::new_with_log_sizes(
                allocator,
                claim.projective_rcb_air.log_sizes,
                &interaction_claim.projective_rcb_air,
                &relations.projective_rcb_air,
            ),
        }
    }

    fn components(&self) -> Vec<&dyn Component> {
        let mut components = Vec::new();
        components.extend(self.scalar_setup.components());
        components.extend(self.cert_scalar_inputs.components());
        components.extend(self.fake_glv_scalar_air.components());
        components.extend(self.fake_glv_selector_air.components());
        for scalar_setup_mod_mul in &self.scalar_setup_mod_muls {
            components.push(&scalar_setup_mod_mul.canonical as &dyn Component);
            components.push(&scalar_setup_mod_mul.ab_chunks as &dyn Component);
            components.push(&scalar_setup_mod_mul.qn_chunks as &dyn Component);
            components.push(&scalar_setup_mod_mul.accumulators as &dyn Component);
            components.push(&scalar_setup_mod_mul.reduction_digits as &dyn Component);
            components.push(&scalar_setup_mod_mul.range13 as &dyn Component);
            components.push(&scalar_setup_mod_mul.signed_carry as &dyn Component);
        }
        components.extend(self.prepared_table_projective_source.components());
        components.extend(self.fake_glv_projective_source.components());
        components.extend(self.fake_glv_chain_expansion.components());
        components.push(&self.fake_glv_chain_continuity as &dyn Component);
        components.push(&self.fake_glv_chain_schedule as &dyn Component);
        components.extend(self.fake_glv_direct_prepared_operand.components());
        components.extend(self.fake_glv_signed_selector_operand.components());
        components.extend(self.fake_glv_lsb_correction_operand.components());
        components.extend(self.fake_glv_prepared_point_source.components());
        components.push(&self.prepared_point_range7 as &dyn Component);
        components.extend(self.projective_rcb_air.components());
        components
    }

    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut components = Vec::new();
        components.extend(self.scalar_setup.component_provers());
        components.extend(self.cert_scalar_inputs.component_provers());
        components.extend(self.fake_glv_scalar_air.component_provers());
        components.extend(self.fake_glv_selector_air.component_provers());
        for scalar_setup_mod_mul in &self.scalar_setup_mod_muls {
            components.push(&scalar_setup_mod_mul.canonical as &dyn ComponentProver<SimdBackend>);
            components.push(&scalar_setup_mod_mul.ab_chunks as &dyn ComponentProver<SimdBackend>);
            components.push(&scalar_setup_mod_mul.qn_chunks as &dyn ComponentProver<SimdBackend>);
            components
                .push(&scalar_setup_mod_mul.accumulators as &dyn ComponentProver<SimdBackend>);
            components
                .push(&scalar_setup_mod_mul.reduction_digits as &dyn ComponentProver<SimdBackend>);
            components.push(&scalar_setup_mod_mul.range13 as &dyn ComponentProver<SimdBackend>);
            components
                .push(&scalar_setup_mod_mul.signed_carry as &dyn ComponentProver<SimdBackend>);
        }
        components.extend(self.prepared_table_projective_source.component_provers());
        components.extend(self.fake_glv_projective_source.component_provers());
        components.extend(self.fake_glv_chain_expansion.component_provers());
        components.push(&self.fake_glv_chain_continuity as &dyn ComponentProver<SimdBackend>);
        components.push(&self.fake_glv_chain_schedule as &dyn ComponentProver<SimdBackend>);
        components.extend(self.fake_glv_direct_prepared_operand.component_provers());
        components.extend(self.fake_glv_signed_selector_operand.component_provers());
        components.extend(self.fake_glv_lsb_correction_operand.component_provers());
        components.extend(self.fake_glv_prepared_point_source.component_provers());
        components.push(&self.prepared_point_range7 as &dyn ComponentProver<SimdBackend>);
        components.extend(self.projective_rcb_air.component_provers());
        components
    }

    fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            self.components()
                .into_iter()
                .map(|component| component.trace_log_degree_bounds()),
        )
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.components()
            .into_iter()
            .map(|component| component.max_constraint_log_degree_bound())
            .max()
            .unwrap_or(0)
    }
}

fn p256_stark_slice_low_ram_config(max_constraint_log_degree_bound: u32) -> PcsConfig {
    let fri_config = FriConfig::new(5, 4, 64, 1);
    PcsConfig {
        pow_bits: 0,
        fri_config,
        lifting_log_size: Some(
            (max_constraint_log_degree_bound + fri_config.log_blowup_factor).max(10),
        ),
    }
}

fn p256_stark_monolithic_profile_config(_max_constraint_log_degree_bound: u32) -> PcsConfig {
    let fri_config = FriConfig::new(5, 2, 64, 1);
    PcsConfig {
        pow_bits: 0,
        fri_config,
        lifting_log_size: None,
    }
}

impl P256ProofDraft {
    pub fn from_verified_inputs_with_trivial_fake_glv_hints(
        inputs: Vec<EcdsaVerifyInput>,
    ) -> Result<Self, P256ProofError> {
        for (index, input) in inputs.iter().enumerate() {
            if !ecdsa_verify(input) {
                return Err(P256ProofError::InvalidNativeEcdsaInput { index });
            }
        }
        Self::from_inputs_with_trivial_fake_glv_hints(inputs)
    }

    pub fn from_inputs_with_hints(
        inputs: Vec<EcdsaVerifyInput>,
        fake_glv_hints: Vec<FakeGlvScalarHint>,
    ) -> Result<Self, P256ProofError> {
        let claim = P256ProofClaim::from_inputs_with_hints(&inputs, fake_glv_hints)?;
        Self::from_claim(inputs, claim)
    }

    pub fn from_inputs_with_trivial_fake_glv_hints(
        inputs: Vec<EcdsaVerifyInput>,
    ) -> Result<Self, P256ProofError> {
        let claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)?;
        Self::from_claim(inputs, claim)
    }

    pub fn verify_current_e2e(&self) -> Result<(), P256ProofError> {
        self.claim.verify_current_components()?;
        self.claim
            .projective_rcb_air_trace
            .verify_proof_slice_traces(&self.relations.projective_rcb)?;
        self.verify_audits()?;
        self.interaction_claim.verify_balanced()
    }

    pub fn prove_current_air_monolithic<MC>(
        &self,
    ) -> Result<P256CurrentAirProof<MC::H>, P256ProofError>
    where
        MC: MerkleChannel,
        SimdBackend: BackendForChannel<MC>,
    {
        self.verify_current_e2e()?;
        let proof_claim = P256CurrentAirProofClaim::from_claim(&self.claim);
        let ids = proof_claim.preprocessed_column_ids();
        let max_constraint_log_degree_bound = proof_claim.max_constraint_log_degree_bound(&ids);
        let config = p256_stark_monolithic_profile_config(max_constraint_log_degree_bound);
        let twiddles =
            SimdBackend::precompute_twiddles(
                CanonicCoset::new(config.lifting_log_size.unwrap_or(
                    max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
                ))
                .circle_domain()
                .half_coset,
            );

        let mut channel = MC::C::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, MC>::new(config, &twiddles);
        commitment_scheme.set_store_polynomials_coefficients();

        let preprocessed = self.gen_current_air_preprocessed_trace(&proof_claim, &ids)?;
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.commit(&mut channel);

        proof_claim.mix_into(&mut channel);
        let mut base = self.gen_current_air_base_trace(&proof_claim)?;
        let base_columns = std::mem::take(&mut base.columns);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base_columns);
        tree_builder.commit(&mut channel);

        let relations = P256CurrentAirRelations::draw(&mut channel);
        let (interaction, interaction_claim) =
            self.gen_current_air_interaction_trace(&base, &relations)?;
        interaction_claim.verify_balanced()?;
        interaction_claim.mix_into(&mut channel);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.commit(&mut channel);

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = P256CurrentAirComponents::new(
            &mut allocator,
            &proof_claim,
            &interaction_claim,
            &relations,
        );
        let stark_proof = prove(
            &components.component_provers(),
            &mut channel,
            commitment_scheme,
        )
        .map_err(|error| P256ProofError::ProofLayer(error.to_string()))?;

        Ok(P256CurrentAirProof {
            claim: proof_claim,
            interaction_claim,
            stark_proof,
        })
    }

    pub fn prove_current_stark_slices<MC>(
        &self,
    ) -> Result<P256StarkProofSlices<MC::H>, P256ProofError>
    where
        MC: MerkleChannel,
        SimdBackend: BackendForChannel<MC>,
    {
        self.verify_current_e2e()?;
        let source_offset = self.claim.prepared_table_ec_trace.active_row_count();
        let selector_claim = SelectorLookupProviderProofClaim;
        let selector_ids = selector_claim.preprocessed_column_ids();
        let selector_config = p256_stark_slice_low_ram_config(
            selector_claim.max_constraint_log_degree_bound(&selector_ids),
        );
        let prepared_table_ec_claim =
            PreparedTableEcRowProofClaim::from_trace(&self.claim.prepared_table_ec_trace);
        let prepared_table_ec_ids = prepared_table_ec_claim.preprocessed_column_ids();
        let prepared_table_ec_config = p256_stark_slice_low_ram_config(
            prepared_table_ec_claim.max_constraint_log_degree_bound(&prepared_table_ec_ids),
        );
        let prepared_table_source_claim =
            PreparedTableProjectiveSourceProofClaim::from_prepared_trace(
                &self.claim.prepared_table_ec_trace,
            );
        let prepared_table_source_ids = prepared_table_source_claim.preprocessed_column_ids();
        let prepared_table_source_config = p256_stark_slice_low_ram_config(
            prepared_table_source_claim.max_constraint_log_degree_bound(&prepared_table_source_ids),
        );
        let fake_glv_source_claim = FakeGlvProjectiveSourceProofClaim::from_fake_glv_trace(
            &self.claim.fake_glv_ec_trace,
            source_offset,
        );
        let fake_glv_source_ids = fake_glv_source_claim.preprocessed_column_ids();
        let fake_glv_source_config = p256_stark_slice_low_ram_config(
            fake_glv_source_claim.max_constraint_log_degree_bound(&fake_glv_source_ids),
        );
        let expansion_claim = FakeGlvChainExpansionProofClaim::from_claims(
            &self.claim.fake_glv_chain,
            &self.claim.fake_glv_ec_trace,
            source_offset,
        );
        let expansion_ids = expansion_claim.preprocessed_column_ids();
        let expansion_config = p256_stark_slice_low_ram_config(
            expansion_claim.max_constraint_log_degree_bound(&expansion_ids),
        );
        let continuity_claim =
            FakeGlvChainContinuityProofClaim::from_chain(&self.claim.fake_glv_chain);
        let continuity_ids = continuity_claim.preprocessed_column_ids();
        let continuity_config = p256_stark_slice_low_ram_config(
            continuity_claim.max_constraint_log_degree_bound(&continuity_ids),
        );
        let schedule_claim = FakeGlvChainScheduleProofClaim::from_chain(&self.claim.fake_glv_chain);
        let schedule_ids = schedule_claim.preprocessed_column_ids();
        let schedule_config = p256_stark_slice_low_ram_config(
            schedule_claim.max_constraint_log_degree_bound(&schedule_ids),
        );
        let direct_claim = FakeGlvDirectPreparedOperandProofClaim::from_claims(
            &self.claim.fake_glv_selectors,
            &self.claim.fake_glv_chain,
        );
        let direct_ids = direct_claim.preprocessed_column_ids();
        let direct_config = p256_stark_slice_low_ram_config(
            direct_claim.max_constraint_log_degree_bound(&direct_ids),
        );
        let signed_claim = FakeGlvSignedSelectorOperandProofClaim::from_claims(
            &self.claim.fake_glv_selectors,
            &self.claim.fake_glv_chain,
        );
        let signed_ids = signed_claim.preprocessed_column_ids();
        let signed_config = p256_stark_slice_low_ram_config(
            signed_claim.max_constraint_log_degree_bound(&signed_ids),
        );
        let lsb_claim = FakeGlvLsbCorrectionOperandProofClaim::from_claims(
            &self.claim.fake_glv_selectors,
            &self.claim.fake_glv_chain,
        );
        let lsb_ids = lsb_claim.preprocessed_column_ids();
        let lsb_config =
            p256_stark_slice_low_ram_config(lsb_claim.max_constraint_log_degree_bound(&lsb_ids));
        let prepared_point_claim = FakeGlvPreparedPointSourceProofClaim::from_claims(
            &self.claim.prepared_trace,
            &self.claim.fake_glv_chain,
        );
        let prepared_point_ids = prepared_point_claim.preprocessed_column_ids();
        let prepared_point_config = p256_stark_slice_low_ram_config(
            prepared_point_claim.max_constraint_log_degree_bound(&prepared_point_ids),
        );
        let projective_claim =
            ProjectiveRcbAirProofClaim::from_trace(&self.claim.projective_rcb_air_trace);
        let projective_ids = projective_claim.preprocessed_column_ids();
        let projective_config = p256_stark_slice_low_ram_config(
            projective_claim.max_constraint_log_degree_bound(&projective_ids),
        );

        Ok(P256StarkProofSlices {
            selector_lookup: prove_selector_lookup_provider_proof_slice::<MC>(
                &self.claim.selector_requests,
                selector_config,
            )?,
            prepared_table_ec_rows: prove_prepared_table_ec_row_proof_slice::<MC>(
                &self.claim.prepared_table_ec_trace,
                prepared_table_ec_config,
            )?,
            prepared_table_projective_source: prove_prepared_table_projective_source_proof_slice::<
                MC,
            >(
                &self.claim.prepared_table_ec_trace,
                &self.claim.projective_ec_trace,
                prepared_table_source_config,
            )?,
            fake_glv_projective_source: prove_fake_glv_projective_source_proof_slice::<MC>(
                &self.claim.fake_glv_ec_trace,
                &self.claim.projective_ec_trace,
                source_offset,
                fake_glv_source_config,
            )?,
            fake_glv_chain_expansion: prove_fake_glv_chain_expansion_proof_slice::<MC>(
                &self.claim.fake_glv_chain,
                &self.claim.fake_glv_ec_trace,
                source_offset,
                expansion_config,
            )?,
            fake_glv_chain_continuity: prove_fake_glv_chain_continuity_proof_slice::<MC>(
                &self.claim.fake_glv_chain,
                continuity_config,
            )?,
            fake_glv_chain_schedule: prove_fake_glv_chain_schedule_proof_slice::<MC>(
                &self.claim.fake_glv_chain,
                schedule_config,
            )?,
            fake_glv_direct_prepared_operand: prove_fake_glv_direct_prepared_operand_proof_slice::<
                MC,
            >(
                &self.claim.prepared_table,
                &self.claim.fake_glv_selectors,
                &self.claim.fake_glv_chain,
                direct_config,
            )?,
            fake_glv_signed_selector_operand: prove_fake_glv_signed_selector_operand_proof_slice::<
                MC,
            >(
                &self.claim.prepared_table,
                &self.claim.fake_glv_selectors,
                &self.claim.fake_glv_chain,
                signed_config,
            )?,
            fake_glv_lsb_correction_operand: prove_fake_glv_lsb_correction_operand_proof_slice::<MC>(
                &self.claim.cert_inputs,
                &self.claim.fake_glv_scalars,
                &self.claim.prepared_table,
                &self.claim.fake_glv_selectors,
                &self.claim.fake_glv_chain,
                lsb_config,
            )?,
            fake_glv_prepared_point_source: prove_fake_glv_prepared_point_source_proof_slice::<MC>(
                &self.claim.prepared_trace,
                &self.claim.fake_glv_chain,
                prepared_point_config,
            )?,
            projective_rcb_air: prove_projective_rcb_air_proof_slice::<MC>(
                &self.claim.projective_rcb_air_trace,
                projective_config,
            )?,
        })
    }

    fn gen_current_air_preprocessed_trace(
        &self,
        claim: &P256CurrentAirProofClaim,
        global_ids: &[PreProcessedColumnId],
    ) -> Result<ColumnVec<M31ColumnEval>, P256ProofError> {
        let mut ids = Vec::new();
        let mut columns = Vec::new();

        let local_ids = scalar_setup_air_preprocessed_column_ids();
        let local_columns = gen_scalar_setup_air_preprocessed_trace(&local_ids);
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let scalar_lookup_claims = LookupProviderClaims::scalar_mod_mul();
        let scalar_setup_rows = scalar_setup_mod_mul_rows(&self.claim)?;
        for (rows, local_claim) in scalar_setup_rows.iter().zip(&claim.scalar_setup_mod_muls) {
            let local_ids =
                scalar_mod_mul_preprocessed_column_ids(local_claim, &scalar_lookup_claims);
            let local_columns =
                gen_scalar_mod_mul_preprocessed_trace(rows, &scalar_lookup_claims, &local_ids);
            append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);
        }

        let local_ids = claim
            .prepared_table_projective_source
            .preprocessed_column_ids();
        let local_columns = gen_prepared_table_ec_row_preprocessed_trace(
            claim.prepared_table_projective_source.log_size,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim.fake_glv_projective_source.preprocessed_column_ids();
        let local_columns = gen_fake_glv_primitive_ec_preprocessed_trace(
            claim.fake_glv_projective_source.log_size,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim.fake_glv_chain_expansion.preprocessed_column_ids();
        let local_columns = gen_fake_glv_chain_expansion_preprocessed_trace(
            claim.fake_glv_chain_expansion,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim.fake_glv_chain_continuity.preprocessed_column_ids();
        let local_columns = gen_fake_glv_chain_continuity_preprocessed_trace(
            claim.fake_glv_chain_continuity.log_size,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim.fake_glv_chain_schedule.preprocessed_column_ids();
        let local_columns = gen_fake_glv_chain_schedule_preprocessed_trace(
            claim.fake_glv_chain_schedule.log_size,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim
            .fake_glv_direct_prepared_operand
            .preprocessed_column_ids();
        let local_columns = gen_direct_operand_preprocessed_trace(
            &claim.fake_glv_direct_prepared_operand,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim
            .fake_glv_signed_selector_operand
            .preprocessed_column_ids();
        let local_columns = gen_signed_selector_operand_preprocessed_trace(
            &claim.fake_glv_signed_selector_operand,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim
            .fake_glv_lsb_correction_operand
            .preprocessed_column_ids();
        let local_columns = gen_lsb_correction_operand_preprocessed_trace(
            &claim.fake_glv_lsb_correction_operand,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim
            .fake_glv_prepared_point_source
            .preprocessed_column_ids();
        let local_columns = gen_fake_glv_prepared_point_source_preprocessed_trace(
            &claim.fake_glv_prepared_point_source,
            &local_ids,
        )?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let range7_id =
            range_check_value_column_id(claim.prepared_point_range7.log_size);
        let range7_column = claim.prepared_point_range7.gen_preprocessed_column();
        append_unique_preprocessed_columns(
            &mut ids,
            &mut columns,
            vec![range7_id],
            vec![range7_column],
        );

        let local_ids = claim.projective_rcb_air.preprocessed_column_ids();
        let local_columns = self
            .claim
            .projective_rcb_air_trace
            .gen_proof_slice_preprocessed_trace(&local_ids)?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        Ok(global_ids
            .iter()
            .map(|global_id| {
                ids.iter()
                    .zip(&columns)
                    .find_map(|(id, column)| (id == global_id).then(|| column.clone()))
                    .unwrap_or_else(|| {
                        panic!("missing global preprocessed column {}", global_id.id)
                    })
            })
            .collect())
    }

    fn gen_current_air_base_trace(
        &self,
        claim: &P256CurrentAirProofClaim,
    ) -> Result<P256CurrentAirBaseTrace, P256ProofError> {
        let scalar_setup =
            gen_scalar_setup_air_base_trace(&self.claim.scalar_setup, claim.scalar_setup);
        let scalar_setup_lookup_providers =
            gen_scalar_setup_air_lookup_provider_base_trace(&scalar_setup);
        let cert_scalar_inputs = gen_cert_scalar_input_air_base_trace(
            &self.claim.scalar_setup,
            &self.claim.cert_inputs,
            claim.cert_scalar_inputs,
        );
        let fake_glv_scalar_air = gen_fake_glv_scalar_air_base_trace(
            &self.claim.cert_inputs,
            &self.claim.fake_glv_scalars,
            claim.fake_glv_scalar_air,
        );
        let fake_glv_selector_air = gen_fake_glv_selector_air_base_trace(
            &self.claim.fake_glv_scalars,
            &self.claim.fake_glv_selectors,
            claim.fake_glv_selector_air,
        );
        let scalar_lookup_claims = LookupProviderClaims::scalar_mod_mul();
        let scalar_setup_rows = scalar_setup_mod_mul_rows(&self.claim)?;
        let scalar_setup_mod_muls = scalar_setup_rows
            .iter()
            .map(|rows| gen_scalar_mod_mul_base_trace(rows, &scalar_lookup_claims))
            .collect::<Vec<_>>();
        let prepared_table_provider = gen_prepared_table_ec_row_base_trace(
            &self.claim.prepared_table_ec_trace,
            claim.prepared_table_projective_source.log_size,
        )?;
        let prepared_table_consumer = gen_prepared_table_projective_source_base_trace(
            &self.claim.prepared_table_ec_trace,
            &self.claim.projective_ec_trace,
            claim.prepared_table_projective_source.log_size,
        )?;
        let fake_glv_projective_provider = gen_fake_glv_primitive_ec_source_base_trace(
            &self.claim.fake_glv_ec_trace,
            claim.fake_glv_projective_source.source_offset as usize,
            claim.fake_glv_projective_source.log_size,
        )?;
        let fake_glv_projective_consumer = gen_fake_glv_projective_source_base_trace(
            &self.claim.fake_glv_ec_trace,
            &self.claim.projective_ec_trace,
            claim.fake_glv_projective_source.source_offset as usize,
            claim.fake_glv_projective_source.log_size,
        )?;
        let chain_expansion_provider = gen_fake_glv_chain_expansion_base_trace(
            &self.claim.fake_glv_chain,
            &self.claim.fake_glv_ec_trace,
            claim.fake_glv_chain_expansion.source_offset as usize,
            claim.fake_glv_chain_expansion.expansion_log_size,
        )?;
        let chain_expansion_consumer = gen_fake_glv_primitive_expansion_consumer_base_trace(
            &self.claim.fake_glv_ec_trace,
            claim.fake_glv_chain_expansion.source_offset as usize,
            claim.fake_glv_chain_expansion.primitive_log_size,
        )?;
        let chain_continuity = gen_fake_glv_chain_continuity_base_trace(
            &self.claim.fake_glv_chain,
            claim.fake_glv_chain_continuity.log_size,
        )?;
        let chain_schedule = gen_fake_glv_chain_schedule_base_trace(
            &self.claim.fake_glv_chain,
            claim.fake_glv_chain_schedule.log_size,
        )?;
        let direct_provider = gen_direct_operand_provider_base_trace(
            &self.claim.prepared_table,
            &self.claim.fake_glv_selectors,
            claim.fake_glv_direct_prepared_operand.provider_log_size,
        )?;
        let direct_consumer = gen_direct_operand_consumer_base_trace(
            &self.claim.fake_glv_selectors,
            &self.claim.fake_glv_chain,
            claim.fake_glv_direct_prepared_operand.consumer_log_size,
        )?;
        let signed_provider = gen_signed_selector_operand_provider_base_trace(
            &self.claim.prepared_table,
            &self.claim.fake_glv_selectors,
            claim.fake_glv_signed_selector_operand.provider_log_size,
        )?;
        let signed_consumer = gen_signed_selector_operand_consumer_base_trace(
            &self.claim.fake_glv_selectors,
            &self.claim.fake_glv_chain,
            claim.fake_glv_signed_selector_operand.consumer_log_size,
        )?;
        let lsb_provider = gen_lsb_correction_operand_provider_base_trace(
            &self.claim.cert_inputs,
            &self.claim.fake_glv_scalars,
            &self.claim.prepared_table,
            &self.claim.fake_glv_selectors,
            claim.fake_glv_lsb_correction_operand.provider_log_size,
        )?;
        let lsb_consumer = gen_lsb_correction_operand_consumer_base_trace(
            &self.claim.fake_glv_selectors,
            &self.claim.fake_glv_chain,
            claim.fake_glv_lsb_correction_operand.consumer_log_size,
        )?;
        let prepared_point_provider = gen_prepared_point_provider_base_trace(
            &self.claim.prepared_trace,
            claim.fake_glv_prepared_point_source.provider_log_size,
        )?;
        let prepared_point_consumers = self.claim.fake_glv_chain.prepared_point_consumers();
        let prepared_point_consumer = gen_fake_glv_prepared_point_consumer_base_trace(
            &prepared_point_consumers,
            claim.fake_glv_prepared_point_source.consumer_log_size,
        )?;
        let prepared_point_range7_multiplicity =
            claim
                .prepared_point_range7
                .gen_multiplicity_trace(self.claim.prepared_trace.providers.iter().filter_map(
                    |provider| {
                        (provider.use_count.0 != 0).then_some(provider.use_count)
                    },
                ));
        let projective_rcb_air = self
            .claim
            .projective_rcb_air_trace
            .gen_proof_slice_base_trace()?;

        let mut columns = Vec::new();
        columns.extend(scalar_setup.clone());
        columns.extend(scalar_setup_lookup_providers.clone());
        columns.extend(cert_scalar_inputs.clone());
        columns.extend(fake_glv_scalar_air.clone());
        columns.extend(fake_glv_selector_air.clone());
        for scalar_setup_mod_mul in &scalar_setup_mod_muls {
            columns.extend(scalar_setup_mod_mul.clone());
        }
        columns.extend(prepared_table_provider.clone());
        columns.extend(prepared_table_consumer.clone());
        columns.extend(fake_glv_projective_provider.clone());
        columns.extend(fake_glv_projective_consumer.clone());
        columns.extend(chain_expansion_provider.clone());
        columns.extend(chain_expansion_consumer.clone());
        columns.extend(chain_continuity.clone());
        columns.extend(chain_schedule.clone());
        columns.extend(direct_provider.clone());
        columns.extend(direct_consumer.clone());
        columns.extend(signed_provider.clone());
        columns.extend(signed_consumer.clone());
        columns.extend(lsb_provider.clone());
        columns.extend(lsb_consumer.clone());
        columns.extend(prepared_point_provider.clone());
        columns.extend(prepared_point_consumer.clone());
        columns.push(prepared_point_range7_multiplicity.clone());
        columns.extend(projective_rcb_air.clone());

        Ok(P256CurrentAirBaseTrace {
            columns,
            scalar_setup,
            cert_scalar_inputs,
            fake_glv_scalar_air,
            fake_glv_selector_air,
            scalar_setup_mod_muls,
            prepared_table_provider,
            prepared_table_consumer,
            fake_glv_projective_provider,
            fake_glv_projective_consumer,
            chain_expansion_provider,
            chain_expansion_consumer,
            chain_continuity,
            direct_provider,
            direct_consumer,
            signed_provider,
            signed_consumer,
            lsb_provider,
            lsb_consumer,
            prepared_point_provider,
            prepared_point_consumer,
            prepared_point_range7_multiplicity,
        })
    }

    fn gen_current_air_interaction_trace(
        &self,
        base: &P256CurrentAirBaseTrace,
        relations: &P256CurrentAirRelations,
    ) -> Result<(ColumnVec<M31ColumnEval>, P256CurrentAirInteractionClaim), P256ProofError> {
        let (scalar_setup_interaction, scalar_setup_claim) =
            gen_scalar_setup_air_interaction_trace(&base.scalar_setup, &relations.scalar_setup);
        let (cert_scalar_input_interaction, cert_scalar_input_claim) =
            gen_cert_scalar_input_air_interaction_trace(
                &base.cert_scalar_inputs,
                &relations.scalar_setup_output,
                &relations.cert_scalar_input,
            );
        let (fake_glv_scalar_interaction, fake_glv_scalar_claim) =
            gen_fake_glv_scalar_air_interaction_trace(
                &base.fake_glv_scalar_air,
                &relations.cert_scalar_input,
                &relations.fake_glv_scalar,
            );
        let (fake_glv_selector_interaction, fake_glv_selector_claim) =
            gen_fake_glv_selector_air_interaction_trace(
                &base.fake_glv_selector_air,
                &relations.fake_glv_scalar,
            );
        let public_provider_claim = self
            .claim
            .public_inputs
            .initial_logup_claim(&relations.public_inputs);
        let scalar_lookup_claims = LookupProviderClaims::scalar_mod_mul();
        let scalar_setup_rows = scalar_setup_mod_mul_rows(&self.claim)?;
        let scalar_setup_claims = scalar_setup_rows
            .iter()
            .map(ScalarModMulClaim::from_rows_with_external_limb_links)
            .collect::<Vec<_>>();
        debug_assert_eq!(base.scalar_setup_mod_muls.len(), scalar_setup_rows.len());
        let mut scalar_setup_interactions = Vec::with_capacity(scalar_setup_rows.len());
        let mut scalar_setup_interaction_claims = Vec::with_capacity(scalar_setup_rows.len());
        for (rows, claim) in scalar_setup_rows.iter().zip(&scalar_setup_claims) {
            let (interaction, interaction_claim) = gen_scalar_mod_mul_interaction_trace(
                rows,
                claim,
                &scalar_lookup_claims,
                &relations.scalar_mod_mul,
            );
            scalar_setup_interactions.push(interaction);
            scalar_setup_interaction_claims.push(interaction_claim);
        }
        let (prepared_provider_interaction, prepared_provider_claim) =
            gen_prepared_table_ec_row_interaction_trace(
                &base.prepared_table_provider,
                &relations.prepared_table,
            );
        let (prepared_consumer_interaction, prepared_consumer_claim) =
            gen_prepared_table_projective_source_interaction_trace(
                &base.prepared_table_consumer,
                &relations.prepared_table,
            );
        let (fake_glv_provider_interaction, fake_glv_provider_claim) =
            gen_fake_glv_primitive_ec_source_interaction_trace(
                &base.fake_glv_projective_provider,
                &relations.fake_glv_projective_source,
                RelationMultiplicity::Provider,
            );
        let (fake_glv_consumer_interaction, fake_glv_consumer_claim) =
            gen_fake_glv_primitive_ec_source_interaction_trace(
                &base.fake_glv_projective_consumer,
                &relations.fake_glv_projective_source,
                RelationMultiplicity::Consumer,
            );
        let (expansion_provider_interaction, expansion_provider_sum) =
            gen_fake_glv_chain_expansion_interaction_trace(
                &base.chain_expansion_provider,
                &relations.fake_glv_chain_expansion,
            );
        let (expansion_consumer_interaction, expansion_consumer_sum) =
            gen_fake_glv_primitive_expansion_consumer_interaction_trace(
                &base.chain_expansion_consumer,
                &relations.fake_glv_chain_expansion,
            );
        let (continuity_interaction, continuity_claim) =
            gen_fake_glv_chain_continuity_interaction_trace(
                &base.chain_continuity,
                &relations.fake_glv_chain_continuity,
            );
        let (direct_provider_interaction, direct_provider_sum) =
            gen_direct_operand_provider_interaction_trace(
                &base.direct_provider,
                &relations.direct_prepared_operand,
            );
        let (direct_consumer_interaction, direct_consumer_sum) =
            gen_direct_operand_consumer_interaction_trace(
                &base.direct_consumer,
                &relations.direct_prepared_operand,
            );
        let (signed_provider_interaction, signed_provider_sum) =
            gen_signed_selector_operand_interaction_trace(
                &base.signed_provider,
                &relations.signed_selector_operand,
                true,
            );
        let (signed_consumer_interaction, signed_consumer_sum) =
            gen_signed_selector_operand_interaction_trace(
                &base.signed_consumer,
                &relations.signed_selector_operand,
                false,
            );
        let (lsb_provider_interaction, lsb_provider_sum) =
            gen_lsb_correction_operand_interaction_trace(
                &base.lsb_provider,
                &relations.lsb_correction_operand,
                true,
            );
        let (lsb_consumer_interaction, lsb_consumer_sum) =
            gen_lsb_correction_operand_interaction_trace(
                &base.lsb_consumer,
                &relations.lsb_correction_operand,
                false,
            );
        let (
            prepared_point_provider_interaction,
            prepared_point_provider_sum,
            prepared_point_range7_consumer_sum,
        ) = gen_prepared_point_provider_interaction_trace(
            &base.prepared_point_provider,
            &relations.prepared_point_source,
            &relations.range7,
        );
        let (prepared_point_consumer_interaction, prepared_point_consumer_sum) =
            gen_fake_glv_prepared_point_consumer_interaction_trace(
                &base.prepared_point_consumer,
                &relations.prepared_point_source,
            );
        let range7_value_column = RangeCheckClaim::new(RANGE7_BITS).gen_preprocessed_column();
        let (prepared_point_range7_interaction, prepared_point_range7_claim) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &base.prepared_point_range7_multiplicity,
                &range7_value_column,
                &relations.range7,
            );
        let (projective_interaction, projective_claim) = self
            .claim
            .projective_rcb_air_trace
            .gen_proof_slice_interaction_trace(&relations.projective_rcb_air)?;

        let mut columns = Vec::new();
        columns.extend(scalar_setup_interaction);
        columns.extend(cert_scalar_input_interaction);
        columns.extend(fake_glv_scalar_interaction);
        columns.extend(fake_glv_selector_interaction);
        for interaction in scalar_setup_interactions {
            columns.extend(interaction);
        }
        columns.extend(prepared_provider_interaction);
        columns.extend(prepared_consumer_interaction);
        columns.extend(fake_glv_provider_interaction);
        columns.extend(fake_glv_consumer_interaction);
        columns.extend(expansion_provider_interaction);
        columns.extend(expansion_consumer_interaction);
        columns.extend(continuity_interaction);
        columns.extend(direct_provider_interaction);
        columns.extend(direct_consumer_interaction);
        columns.extend(signed_provider_interaction);
        columns.extend(signed_consumer_interaction);
        columns.extend(lsb_provider_interaction);
        columns.extend(lsb_consumer_interaction);
        columns.extend(prepared_point_provider_interaction);
        columns.extend(prepared_point_consumer_interaction);
        columns.extend(prepared_point_range7_interaction);
        columns.extend(projective_interaction);

        Ok((
            columns,
            P256CurrentAirInteractionClaim {
                public_inputs: RelationBalanceClaim::new(
                    public_provider_claim.claimed_sum,
                    scalar_setup_claim.public_consumer_claimed_sum,
                ),
                scalar_setup: scalar_setup_claim,
                cert_scalar_inputs: cert_scalar_input_claim,
                fake_glv_scalar_air: fake_glv_scalar_claim,
                fake_glv_selector_air: fake_glv_selector_claim,
                scalar_setup_mod_muls: scalar_setup_interaction_claims,
                prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim {
                    provider_claimed_sum: prepared_provider_claim.claimed_sum,
                    consumer_claimed_sum: prepared_consumer_claim.claimed_sum,
                },
                fake_glv_projective_source: FakeGlvProjectiveSourceInteractionClaim {
                    provider_claimed_sum: fake_glv_provider_claim.claimed_sum,
                    consumer_claimed_sum: fake_glv_consumer_claim.claimed_sum,
                },
                fake_glv_chain_expansion: FakeGlvChainExpansionInteractionClaim {
                    expansion_claimed_sum: expansion_provider_sum,
                    primitive_claimed_sum: expansion_consumer_sum,
                },
                fake_glv_chain_continuity: FakeGlvChainContinuityInteractionClaim {
                    claimed_sum: continuity_claim.claimed_sum,
                },
                fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandInteractionClaim {
                    provider_claimed_sum: direct_provider_sum,
                    consumer_claimed_sum: direct_consumer_sum,
                },
                fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandInteractionClaim {
                    provider_claimed_sum: signed_provider_sum,
                    consumer_claimed_sum: signed_consumer_sum,
                },
                fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandInteractionClaim {
                    provider_claimed_sum: lsb_provider_sum,
                    consumer_claimed_sum: lsb_consumer_sum,
                },
                fake_glv_prepared_point_source: FakeGlvPreparedPointSourceInteractionClaim {
                    provider_claimed_sum: prepared_point_provider_sum,
                    consumer_claimed_sum: prepared_point_consumer_sum,
                    range7_consumer_claimed_sum: prepared_point_range7_consumer_sum,
                },
                prepared_point_range7: prepared_point_range7_claim,
                projective_rcb_air: projective_claim,
            },
        ))
    }

    fn from_claim(
        inputs: Vec<EcdsaVerifyInput>,
        claim: P256ProofClaim,
    ) -> Result<Self, P256ProofError> {
        let relations = P256ProofRelations::dummy();
        let interaction_claim = P256ProofInteractionClaim::from_claim(&claim, &relations);
        let proof = Self {
            inputs,
            claim,
            relations,
            interaction_claim,
        };
        proof.verify_current_e2e()?;
        Ok(proof)
    }

    fn verify_audits(&self) -> Result<(), P256ProofError> {
        let selector_audit =
            SelectorLookupAudit::balanced_for_requests(&self.claim.selector_requests)?;
        if !selector_audit.is_balanced() {
            return Err(P256ProofError::RelationImbalance {
                relation: "SelectorLookupAudit",
            });
        }

        let mut prepared_audit = PreparedPointAudit::default();
        for provider in &self.claim.prepared_trace.providers {
            prepared_audit.add_provider(provider);
        }
        for consumer in self.claim.fake_glv_chain.prepared_point_consumers() {
            prepared_audit.add_consumer(&consumer);
        }
        if !prepared_audit.is_balanced() {
            return Err(P256ProofError::RelationImbalance {
                relation: "PreparedPointAudit",
            });
        }

        Ok(())
    }
}

struct P256CurrentAirBaseTrace {
    columns: ColumnVec<M31ColumnEval>,
    scalar_setup: ColumnVec<M31ColumnEval>,
    cert_scalar_inputs: ColumnVec<M31ColumnEval>,
    fake_glv_scalar_air: ColumnVec<M31ColumnEval>,
    fake_glv_selector_air: ColumnVec<M31ColumnEval>,
    scalar_setup_mod_muls: Vec<ColumnVec<M31ColumnEval>>,
    prepared_table_provider: ColumnVec<M31ColumnEval>,
    prepared_table_consumer: ColumnVec<M31ColumnEval>,
    fake_glv_projective_provider: ColumnVec<M31ColumnEval>,
    fake_glv_projective_consumer: ColumnVec<M31ColumnEval>,
    chain_expansion_provider: ColumnVec<M31ColumnEval>,
    chain_expansion_consumer: ColumnVec<M31ColumnEval>,
    chain_continuity: ColumnVec<M31ColumnEval>,
    direct_provider: ColumnVec<M31ColumnEval>,
    direct_consumer: ColumnVec<M31ColumnEval>,
    signed_provider: ColumnVec<M31ColumnEval>,
    signed_consumer: ColumnVec<M31ColumnEval>,
    lsb_provider: ColumnVec<M31ColumnEval>,
    lsb_consumer: ColumnVec<M31ColumnEval>,
    prepared_point_provider: ColumnVec<M31ColumnEval>,
    prepared_point_consumer: ColumnVec<M31ColumnEval>,
    prepared_point_range7_multiplicity: M31ColumnEval,
}

fn scalar_setup_mod_mul_rows(
    claim: &P256ProofClaim,
) -> Result<Vec<ScalarModMulTraceRows>, P256ProofError> {
    let mut rows = Vec::with_capacity(2 * claim.scalar_setup.rows.len());
    for (sig_index, row) in claim.scalar_setup.rows.iter().enumerate() {
        rows.push(ScalarModMulTraceRows::new(
            (2 * sig_index) as u32,
            &row.witness.trace.s_u1_eq,
        )?);
        rows.push(ScalarModMulTraceRows::new(
            (2 * sig_index + 1) as u32,
            &row.witness.trace.s_u2_eq,
        )?);
    }
    Ok(rows)
}

pub fn verify_current_air_monolithic<MC>(
    proof: P256CurrentAirProof<MC::H>,
) -> Result<(), P256ProofError>
where
    MC: MerkleChannel,
{
    let P256CurrentAirProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;
    interaction_claim.verify_balanced()?;

    let ids = claim.preprocessed_column_ids();
    let mut channel = MC::C::default();
    let commitment_scheme = &mut CommitmentSchemeVerifier::<MC>::new(stark_proof.config);
    let dummy_log_degree_bounds = claim.trace_log_degree_bounds(
        &ids,
        &P256CurrentAirInteractionClaim::zero_for_claim(&claim),
        &P256CurrentAirRelations::dummy(),
    );

    commitment_scheme.commit(
        stark_proof.commitments[0],
        &dummy_log_degree_bounds[0],
        &mut channel,
    );
    claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[1],
        &dummy_log_degree_bounds[1],
        &mut channel,
    );
    let relations = P256CurrentAirRelations::draw(&mut channel);
    let log_degree_bounds = claim.trace_log_degree_bounds(&ids, &interaction_claim, &relations);

    interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        stark_proof.commitments[2],
        &log_degree_bounds[2],
        &mut channel,
    );

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    let components =
        P256CurrentAirComponents::new(&mut allocator, &claim, &interaction_claim, &relations);
    verify(
        &components.components(),
        &mut channel,
        commitment_scheme,
        stark_proof,
    )
    .map_err(|error| P256ProofError::ProofLayer(error.to_string()))
}

fn append_unique_preprocessed_ids(
    out: &mut Vec<PreProcessedColumnId>,
    ids: Vec<PreProcessedColumnId>,
) {
    for id in ids {
        if !out.iter().any(|existing| existing == &id) {
            out.push(id);
        }
    }
}

fn append_unique_preprocessed_columns(
    out_ids: &mut Vec<PreProcessedColumnId>,
    out_columns: &mut ColumnVec<M31ColumnEval>,
    ids: Vec<PreProcessedColumnId>,
    columns: ColumnVec<M31ColumnEval>,
) {
    for (id, column) in ids.into_iter().zip(columns) {
        if !out_ids.iter().any(|existing| existing == &id) {
            out_ids.push(id);
            out_columns.push(column);
        }
    }
}

fn verify_current_air_relation_zero(
    relation: &'static str,
    total: SecureField,
) -> Result<(), P256ProofError> {
    if total == zero() {
        Ok(())
    } else {
        Err(P256ProofError::RelationImbalance { relation })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P256ProofComponentStatus {
    Implemented,
    Pending,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct P256ProofComponentSlot {
    pub name: &'static str,
    pub status: P256ProofComponentStatus,
    pub note: &'static str,
}

pub const P256_PROOF_COMPONENT_SLOTS: &[P256ProofComponentSlot] = &[
    P256ProofComponentSlot {
        name: "PublicEcdsaInput",
        status: P256ProofComponentStatus::Implemented,
        note: "The monolithic current AIR proof now carries verifier-supplied public ECDSA tuples and consumes them from scalar setup through PublicEcdsaInstance LogUp balance.",
    },
    P256ProofComponentSlot {
        name: "PublicKeyOnCurve",
        status: P256ProofComponentStatus::Pending,
        note: "Currently checked by native Solinas traces; still needs inclusion in the single verifier-facing STARK proof.",
    },
    P256ProofComponentSlot {
        name: "SolinasReductionTraceRows",
        status: P256ProofComponentStatus::Pending,
        note: "Solinas reduction trace/checker exists for public-key checks, but those rows are not yet included in the single STARK proof.",
    },
    P256ProofComponentSlot {
        name: "ScalarSetup",
        status: P256ProofComponentStatus::Implemented,
        note: "Scalar setup consumes public ECDSA tuples, proves r/s canonical nonzero and z mod n reduction, and links s*u1=z_red and s*u2=r scalar-mod-mul rows inside the monolithic STARK proof.",
    },
    P256ProofComponentSlot {
        name: "CertScalarInput",
        status: P256ProofComponentStatus::Implemented,
        note: "Certificate scalar input rows are proven from ScalarSetupOutput inside the monolithic STARK proof, including fixed-generator/public-key base binding and u2 nonzero enforcement.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvScalarHint",
        status: P256ProofComponentStatus::Implemented,
        note: "Fake-GLV scalar rows are proven from CertScalarInput inside the monolithic STARK for the current trivial scalar strategy, including small-limb, active/inactive, sign, and scalar equality constraints.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvSelector",
        status: P256ProofComponentStatus::Implemented,
        note: "Selector reconstruction is proven from FakeGlvScalarRelation inside the monolithic STARK with bit decomposition, limb reconstruction, final-selector/init-base, and inactive/padding zeroing; the separate selector lookup providers retain their proof slices.",
    },
    P256ProofComponentSlot {
        name: "PreparedPointUseCounts",
        status: P256ProofComponentStatus::Implemented,
        note: "PreparedPoint provider rows now consume Range7 on their use_count column, and the Range7 multiplicity provider sits inside the monolithic STARK with its LogUp balance enforced against the provider consumers.",
    },
    P256ProofComponentSlot {
        name: "PreparedTablePoints",
        status: P256ProofComponentStatus::Pending,
        note: "Per-cert base binding (table[0] = G for cert_id=0, Q for cert_id=1) is not yet a verifier-checked AIR consumer of CertScalarInputRelation; correctness currently propagates only through the final ECDSA check (also pending).",
    },
    P256ProofComponentSlot {
        name: "PreparedTableEcTrace",
        status: P256ProofComponentStatus::Implemented,
        note: "Prepared-table EC row shape is proven inside the monolithic STARK by prepared_table_projective_source's provider/consumer pair over PreparedTableEcRowRelation; the legacy standalone slice proof is now redundant under prove_current_air_monolithic.",
    },
    P256ProofComponentSlot {
        name: "PreparedTableEcRows",
        status: P256ProofComponentStatus::Implemented,
        note: "Prepared-table EC row shape is proven and linked into projective RCB source rows; EC arithmetic is discharged by ProjectiveRcbAirRows.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvChainTrace",
        status: P256ProofComponentStatus::Implemented,
        note: "Native chain trace consumes PreparedPoint entries, runs MSB init, 62 selector steps, Table[16], LSB correction, and checks final accumulator equals R3.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvPrimitiveEcTrace",
        status: P256ProofComponentStatus::Implemented,
        note: "Compressed fake-GLV chain steps are expanded into primitive DOUBLE/DOUBLE/ADD rows and verified against native EC formulas.",
    },
    P256ProofComponentSlot {
        name: "ProjectiveRcbEcTrace",
        status: P256ProofComponentStatus::Implemented,
        note: "Prepared-table and fake-GLV primitive EC rows are replayed through homogeneous projective RCB double/mixed-add formulas and exported back to affine outputs.",
    },
    P256ProofComponentSlot {
        name: "ProjectiveRcbAirRows",
        status: P256ProofComponentStatus::Implemented,
        note: "Projective RCB formula multiplications are expanded into AIR-facing Solinas multiplication/reduction rows, raw-product chunks, folded contributions, folded digits, and folded carry links.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvEcChainRows",
        status: P256ProofComponentStatus::Implemented,
        note: "Fake-GLV chain schedule, continuity, operands, primitive expansion, prepared-point source, and projective-source links are proven; EC arithmetic is discharged by ProjectiveRcbAirRows.",
    },
    P256ProofComponentSlot {
        name: "FinalEcdsaCheck",
        status: P256ProofComponentStatus::Pending,
        note: "Native final check links H1/H2, finite R = H1 + H2, and x(R) mod n = r; AIR rows for this final equation are still pending.",
    },
    P256ProofComponentSlot {
        name: "StarkProveVerify",
        status: P256ProofComponentStatus::Implemented,
        note: "The current AIR path commits one global preprocessed tree, one global base tree, one global interaction tree, and verifies one monolithic STARK proof artifact.",
    },
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum P256ProofError {
    ScalarSetup(ScalarSetupClaimError),
    CertScalarInput(CertScalarInputError),
    FakeGlvChain(FakeGlvChainError),
    FakeGlvScalar(FakeGlvScalarHintError),
    FakeGlvSelector(FakeGlvSelectorError),
    FinalEcdsaCheck(FinalEcdsaCheckError),
    SelectorLookup(SelectorLookupError),
    PreparedPoint(PreparedPointError),
    PreparedTable(PreparedTableError),
    ProjectiveEc(ProjectiveEcError),
    ProjectiveRcbAir(ProjectiveRcbAirError),
    PublicKeyOnCurve(PublicKeyOnCurveError),
    ScalarModMulTrace(ScalarModMulTraceError),
    InvalidNativeEcdsaInput { index: usize },
    RelationImbalance { relation: &'static str },
    ProofLayer(String),
}

impl From<ScalarSetupClaimError> for P256ProofError {
    fn from(value: ScalarSetupClaimError) -> Self {
        Self::ScalarSetup(value)
    }
}

impl From<CertScalarInputError> for P256ProofError {
    fn from(value: CertScalarInputError) -> Self {
        Self::CertScalarInput(value)
    }
}

impl From<FakeGlvChainError> for P256ProofError {
    fn from(value: FakeGlvChainError) -> Self {
        Self::FakeGlvChain(value)
    }
}

impl From<FakeGlvScalarHintError> for P256ProofError {
    fn from(value: FakeGlvScalarHintError) -> Self {
        Self::FakeGlvScalar(value)
    }
}

impl From<FakeGlvSelectorError> for P256ProofError {
    fn from(value: FakeGlvSelectorError) -> Self {
        Self::FakeGlvSelector(value)
    }
}

impl From<FinalEcdsaCheckError> for P256ProofError {
    fn from(value: FinalEcdsaCheckError) -> Self {
        Self::FinalEcdsaCheck(value)
    }
}

impl From<SelectorLookupError> for P256ProofError {
    fn from(value: SelectorLookupError) -> Self {
        Self::SelectorLookup(value)
    }
}

impl From<PreparedPointError> for P256ProofError {
    fn from(value: PreparedPointError) -> Self {
        Self::PreparedPoint(value)
    }
}

impl From<PreparedTableError> for P256ProofError {
    fn from(value: PreparedTableError) -> Self {
        Self::PreparedTable(value)
    }
}

impl From<ProjectiveEcError> for P256ProofError {
    fn from(value: ProjectiveEcError) -> Self {
        Self::ProjectiveEc(value)
    }
}

impl From<ProjectiveRcbAirError> for P256ProofError {
    fn from(value: ProjectiveRcbAirError) -> Self {
        Self::ProjectiveRcbAir(value)
    }
}

impl From<PublicKeyOnCurveError> for P256ProofError {
    fn from(value: PublicKeyOnCurveError) -> Self {
        Self::PublicKeyOnCurve(value)
    }
}

impl From<ScalarModMulTraceError> for P256ProofError {
    fn from(value: ScalarModMulTraceError) -> Self {
        Self::ScalarModMulTrace(value)
    }
}

fn zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY, P256_ORDER};
    use crate::curve::{mod_inverse, scalar_mul};
    use crate::debug::MockCommitmentScheme;
    use crate::fake_glv_chain_continuity::{
        prove_fake_glv_chain_continuity_proof_slice, verify_fake_glv_chain_continuity_proof_slice,
        FakeGlvChainContinuityProofClaim,
    };
    use crate::fake_glv_chain_expansion::{
        prove_fake_glv_chain_expansion_proof_slice, verify_fake_glv_chain_expansion_proof_slice,
        FakeGlvChainExpansionProofClaim,
    };
    use crate::fake_glv_chain_schedule::{
        prove_fake_glv_chain_schedule_proof_slice, verify_fake_glv_chain_schedule_proof_slice,
        FakeGlvChainScheduleProofClaim,
    };
    use crate::fake_glv_direct_prepared_operand::{
        prove_fake_glv_direct_prepared_operand_proof_slice,
        verify_fake_glv_direct_prepared_operand_proof_slice,
        FakeGlvDirectPreparedOperandProofClaim,
    };
    use crate::fake_glv_ec_source::{
        prove_fake_glv_projective_source_proof_slice,
        verify_fake_glv_projective_source_proof_slice, FakeGlvProjectiveSourceProofClaim,
    };
    use crate::fake_glv_lsb_correction_operand::{
        prove_fake_glv_lsb_correction_operand_proof_slice,
        verify_fake_glv_lsb_correction_operand_proof_slice, FakeGlvLsbCorrectionOperandProofClaim,
    };
    use crate::fake_glv_prepared_point_source::{
        prove_fake_glv_prepared_point_source_proof_slice,
        verify_fake_glv_prepared_point_source_proof_slice, FakeGlvPreparedPointSourceProofClaim,
    };
    use crate::fake_glv_selector_lookup::{
        prove_selector_lookup_provider_proof_slice, verify_selector_lookup_provider_proof_slice,
        SelectorLookupProviderProofClaim,
    };
    use crate::fake_glv_signed_selector_operand::{
        prove_fake_glv_signed_selector_operand_proof_slice,
        verify_fake_glv_signed_selector_operand_proof_slice,
        FakeGlvSignedSelectorOperandProofClaim,
    };
    use crate::field_ops::mul_mod_witness;
    use crate::fp_solinas_air::FP_SOLINAS_REDUCTION_DIGITS;
    use crate::limbs::P256M31BigInt;
    use crate::prepared_table::{
        prove_prepared_table_ec_row_proof_slice,
        prove_prepared_table_projective_source_proof_slice,
        verify_prepared_table_ec_row_proof_slice,
        verify_prepared_table_projective_source_proof_slice, PreparedAffinePoint,
        PreparedTableEcRowProofClaim, PreparedTableProjectiveSourceProofClaim,
    };
    use crate::projective_air::{
        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS, PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS,
        PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS, PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS,
        PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS, PROJECTIVE_RCB_MUL_TRACE_COLUMNS,
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS, PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS,
        PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS,
    };
    use crate::scalar::scalar_mod_mul::interaction_claim::zero_interaction_claim;
    use crate::scalar::scalar_mod_mul::layout::{
        ScalarModMulFamilyTraces, PRODUCT_METADATA_TRACE_COLUMNS,
    };
    use crate::scalar::scalar_mod_mul::schedule::ScalarModMulFixedSchedule;
    use crate::scalar::scalar_mod_mul::{
        SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS, SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS,
    };
    use crate::types::{AffinePoint, Signature, U256};
    use core::cmp::Ordering;
    use std::collections::BTreeMap;
    use std::ops::Deref;
    use stwo::core::channel::Blake2sM31Channel;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::{
        assert_constraints_on_trace, FrameworkComponent, FrameworkEval, PREPROCESSED_TRACE_IDX,
    };

    fn test_input(message_hash: u64, r: u64, s: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
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

    fn generator_point() -> AffinePoint {
        AffinePoint {
            x: U256::from_le_u64s(&P256_GX),
            y: U256::from_le_u64s(&P256_GY),
        }
    }

    fn valid_real_input_with_small_u_scalars(u1: u64, u2: u64) -> EcdsaVerifyInput {
        assert_ne!(u2, 0, "u2 must use the active fake-GLV branch");
        let n = U256::from_le_u64s(&P256_ORDER);
        let public_key = generator_point();
        let r_point = scalar_mul(&scalar(u1 + u2), &public_key).expect("nonzero R");
        let r = x_mod_order(&r_point.x);
        let u2_inv = mod_inverse(&scalar(u2), &n);
        let s = mul_mod_witness(&r, &u2_inv, &n).result.to_u256();
        let message_hash = mul_mod_witness(&scalar(u1), &s, &n).result.to_u256();

        EcdsaVerifyInput {
            message_hash,
            signature: Signature { r, s },
            public_key,
        }
    }

    fn x_mod_order(x: &U256) -> U256 {
        let n = U256::from_le_u64s(&P256_ORDER);
        if cmp_u256(x, &n).is_lt() {
            return x.clone();
        }
        let x_words = x.to_le_u64s();
        let n_words = P256_ORDER;
        let mut diff = [0u64; 4];
        let mut borrow = 0u64;
        for i in 0..4 {
            let (s1, c1) = x_words[i].overflowing_sub(n_words[i]);
            let (s2, c2) = s1.overflowing_sub(borrow);
            diff[i] = s2;
            borrow = (c1 as u64) + (c2 as u64);
        }
        U256::from_le_u64s(&diff)
    }

    fn cmp_u256(lhs: &U256, rhs: &U256) -> Ordering {
        let lhs = lhs.to_le_u64s();
        let rhs = rhs.to_le_u64s();
        for i in (0..4).rev() {
            match lhs[i].cmp(&rhs[i]) {
                Ordering::Equal => {}
                ordering => return ordering,
            }
        }
        Ordering::Equal
    }

    fn selector_lookup_provider_low_ram_config() -> PcsConfig {
        let claim = SelectorLookupProviderProofClaim;
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

    fn fake_glv_projective_source_low_ram_config(
        trace: &FakeGlvPrimitiveEcTraceClaim,
        source_offset: usize,
    ) -> PcsConfig {
        let claim = FakeGlvProjectiveSourceProofClaim::from_fake_glv_trace(trace, source_offset);
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

    fn fake_glv_chain_expansion_low_ram_config(
        chain: &FakeGlvChainClaim,
        primitive: &FakeGlvPrimitiveEcTraceClaim,
        source_offset: usize,
    ) -> PcsConfig {
        let claim = FakeGlvChainExpansionProofClaim::from_claims(chain, primitive, source_offset);
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

    fn fake_glv_chain_continuity_low_ram_config(chain: &FakeGlvChainClaim) -> PcsConfig {
        let claim = FakeGlvChainContinuityProofClaim::from_chain(chain);
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

    fn fake_glv_chain_schedule_low_ram_config(chain: &FakeGlvChainClaim) -> PcsConfig {
        let claim = FakeGlvChainScheduleProofClaim::from_chain(chain);
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

    fn fake_glv_direct_prepared_operand_low_ram_config(
        selectors: &FakeGlvSelectorClaim,
        chain: &FakeGlvChainClaim,
    ) -> PcsConfig {
        let claim = FakeGlvDirectPreparedOperandProofClaim::from_claims(selectors, chain);
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

    fn fake_glv_signed_selector_operand_low_ram_config(
        selectors: &FakeGlvSelectorClaim,
        chain: &FakeGlvChainClaim,
    ) -> PcsConfig {
        let claim = FakeGlvSignedSelectorOperandProofClaim::from_claims(selectors, chain);
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

    fn fake_glv_lsb_correction_operand_low_ram_config(
        selectors: &FakeGlvSelectorClaim,
        chain: &FakeGlvChainClaim,
    ) -> PcsConfig {
        let claim = FakeGlvLsbCorrectionOperandProofClaim::from_claims(selectors, chain);
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

    fn fake_glv_prepared_point_source_low_ram_config(
        prepared: &PreparedPointTraceClaim,
        chain: &FakeGlvChainClaim,
    ) -> PcsConfig {
        let claim = FakeGlvPreparedPointSourceProofClaim::from_claims(prepared, chain);
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
    fn current_p256_proof_pipeline_links_all_implemented_components() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
            valid_real_input_with_small_u_scalars(13, 17),
        ])
        .expect("current pipeline builds");

        proof.verify_current_e2e().expect("current e2e verifies");
        assert_eq!(proof.claim.public_inputs.instances.len(), 2);
        assert_eq!(proof.claim.public_key_check.rows.len(), 2);
        assert_eq!(
            proof.claim.public_key_check.solinas_reduction_row_count(),
            224
        );
        assert_eq!(proof.claim.scalar_setup.rows.len(), 2);
        assert_eq!(proof.claim.cert_inputs.rows.len(), 4);
        assert_eq!(proof.claim.fake_glv_scalars.rows.len(), 4);
        assert_eq!(proof.claim.fake_glv_selectors.rows.len(), 4);
        assert_eq!(proof.claim.selector_requests.final_selector.len(), 4);
        assert_eq!(proof.claim.prepared_table.certs.len(), 4);
        assert_eq!(proof.claim.prepared_table_ec_trace.active_row_count(), 48);
        assert_eq!(proof.claim.fake_glv_chain.active_row_count(), 260);
        assert_eq!(proof.claim.fake_glv_ec_trace.active_row_count(), 760);
        assert_eq!(proof.claim.projective_ec_trace.active_row_count(), 808);
        assert_eq!(proof.claim.projective_rcb_air_trace.active_row_count(), 808);
        assert_eq!(
            proof.claim.projective_rcb_air_trace.mul_row_count(),
            804 * 13
        );
        assert_eq!(
            proof.claim.projective_rcb_air_trace.reduction_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count() * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            proof
                .claim
                .projective_rcb_air_trace
                .folded_digit_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count() * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            proof
                .claim
                .projective_rcb_air_trace
                .folded_contribution_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count()
                * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS
        );
        assert_eq!(
            proof
                .claim
                .projective_rcb_air_trace
                .raw_product_chunk_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count()
                * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
        );
        let projective_rcb_preprocessed_ids = proof
            .claim
            .projective_rcb_air_trace
            .preprocessed_column_ids();
        let projective_rcb_preprocessed = proof
            .claim
            .projective_rcb_air_trace
            .gen_preprocessed_trace(&projective_rcb_preprocessed_ids)
            .expect("projective RCB schedule preprocessed trace generates");
        assert_eq!(
            projective_rcb_preprocessed_ids.len(),
            (3 + 3 * PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TERMS + 3)
                + (3 + 5 * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TERMS)
                + (2 + 2 * PROJECTIVE_RCB_FOLDED_DIGIT_GROUPS)
        );
        assert_eq!(
            projective_rcb_preprocessed.len(),
            projective_rcb_preprocessed_ids.len()
        );
        let projective_rcb_base = proof
            .claim
            .projective_rcb_air_trace
            .gen_base_trace()
            .expect("projective RCB base trace generates");
        assert_eq!(
            projective_rcb_base.len(),
            PROJECTIVE_RCB_MUL_TRACE_COLUMNS
                + PROJECTIVE_RCB_RAW_PRODUCT_CHUNK_TRACE_COLUMNS
                + PROJECTIVE_RCB_FOLDED_CONTRIBUTION_TRACE_COLUMNS
                + PROJECTIVE_RCB_FOLDED_DIGIT_TRACE_COLUMNS
        );
        assert_eq!(proof.claim.final_check.rows.len(), 2);
        assert_eq!(proof.claim.prepared_use_counts.certs.len(), 4);
        for provider in &proof.claim.prepared_trace.providers {
            assert_eq!(
                Some(provider.instance.clone()),
                proof.claim.prepared_table.instance(
                    provider.instance.sig_id,
                    provider.instance.cert_id,
                    provider.instance.table_index.0,
                )
            );
        }
        assert_eq!(proof.interaction_claim.public_inputs.total(), zero());
        assert_eq!(proof.interaction_claim.selector_lookups.total(), zero());
        assert_eq!(proof.interaction_claim.prepared_points.total(), zero());
        assert_eq!(proof.interaction_claim.range7.total(), zero());
        proof
            .interaction_claim
            .projective_rcb
            .verify_balanced()
            .expect("projective RCB internal relations balance");
    }

    #[test]
    fn current_p256_proof_pipeline_accepts_real_valid_signature_input() {
        let input = valid_real_input_with_small_u_scalars(7, 11);

        assert!(ecdsa_verify(&input));
        let proof = P256ProofDraft::from_verified_inputs_with_trivial_fake_glv_hints(vec![input])
            .expect("real valid input feeds current AIR pipeline");

        proof
            .verify_current_e2e()
            .expect("real input current e2e verifies");
        assert_eq!(
            proof.claim.scalar_setup.rows[0].output.u1,
            P256M31BigInt::from_u256(&scalar(7))
        );
        assert_eq!(
            proof.claim.scalar_setup.rows[0].output.u2,
            P256M31BigInt::from_u256(&scalar(11))
        );
        assert_eq!(proof.claim.fake_glv_chain.active_row_count(), 130);
        assert_eq!(proof.claim.fake_glv_ec_trace.active_row_count(), 380);
        assert_eq!(proof.claim.projective_ec_trace.active_row_count(), 404);
        assert_eq!(proof.claim.projective_rcb_air_trace.active_row_count(), 404);
        assert_eq!(
            proof.claim.projective_rcb_air_trace.mul_row_count(),
            402 * 13
        );
        assert_eq!(
            proof.claim.projective_rcb_air_trace.reduction_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count() * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            proof
                .claim
                .projective_rcb_air_trace
                .folded_digit_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count() * FP_SOLINAS_REDUCTION_DIGITS
        );
        assert_eq!(
            proof
                .claim
                .projective_rcb_air_trace
                .folded_contribution_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count()
                * PROJECTIVE_RCB_FOLDED_CONTRIBUTION_ROWS
        );
        assert_eq!(
            proof
                .claim
                .projective_rcb_air_trace
                .raw_product_chunk_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count()
                * PROJECTIVE_RCB_RAW_PRODUCT_CHUNKS
        );
        assert_eq!(
            proof.claim.public_key_check.solinas_reduction_row_count(),
            112
        );
        assert_eq!(proof.interaction_claim.public_inputs.total(), zero());
        assert_eq!(proof.interaction_claim.selector_lookups.total(), zero());
        assert_eq!(proof.interaction_claim.prepared_points.total(), zero());
        assert_eq!(proof.interaction_claim.range7.total(), zero());
        proof
            .interaction_claim
            .projective_rcb
            .verify_balanced()
            .expect("projective RCB internal relations balance");
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_invalid_real_signature_input() {
        let mut input = valid_real_input_with_small_u_scalars(7, 11);
        input.message_hash = scalar(123);

        assert!(!ecdsa_verify(&input));
        let err = P256ProofDraft::from_verified_inputs_with_trivial_fake_glv_hints(vec![input])
            .expect_err("invalid native signature must not enter current AIR pipeline");

        assert_eq!(err, P256ProofError::InvalidNativeEcdsaInput { index: 0 });
    }

    #[test]
    fn current_p256_monolithic_proof_rejects_mutated_public_input_binding() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.public_inputs.instances[0].r = P256M31BigInt::zero();

        let err = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect_err("public tuple mismatch must reject before proving");

        assert_eq!(
            err,
            P256ProofError::RelationImbalance {
                relation: "PublicEcdsaInstance"
            }
        );
    }

    #[test]
    fn current_p256_monolithic_verifier_rejects_mutated_public_r() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        let mut monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("current AIR monolithic proof proves");
        monolithic.claim.public_inputs.instances[0].r = P256M31BigInt::zero();

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("mutated verifier public r must reject");

        assert!(matches!(err, P256ProofError::ProofLayer(_)));
    }

    #[test]
    fn current_p256_monolithic_proof_rejects_mutated_cert_base() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.cert_inputs.rows[1].base_x.limbs_mut()[0] = M31::from_u32_unchecked(1234);

        let err = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect_err("mutated cert base must reject in the monolithic AIR");

        assert!(matches!(err, P256ProofError::ProofLayer(_)));
    }

    #[test]
    fn current_p256_monolithic_verifier_rejects_mutated_fake_glv_scalar_claim() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        let mut monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("current AIR monolithic proof proves");
        monolithic.claim.fake_glv_scalar_air.log_size += 1;

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("mutated fake-GLV scalar AIR claim must reject");

        assert!(matches!(err, P256ProofError::ProofLayer(_)));
    }

    #[test]
    fn current_p256_monolithic_verifier_rejects_mutated_fake_glv_selector_claim() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        let mut monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("current AIR monolithic proof proves");
        monolithic.claim.fake_glv_selector_air.log_size += 1;

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("mutated fake-GLV selector AIR claim must reject");

        assert!(matches!(err, P256ProofError::ProofLayer(_)));
    }

    #[test]
    fn current_p256_monolithic_verifier_rejects_unbalanced_range7_consumer_sum() {
        use num_traits::One;
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        let mut monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("current AIR monolithic proof proves");
        monolithic
            .interaction_claim
            .fake_glv_prepared_point_source
            .range7_consumer_claimed_sum += SecureField::one();

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("Range7 balance must reject mutated consumer sum");

        assert!(matches!(
            err,
            P256ProofError::RelationImbalance { relation: "Range7" }
        ));
    }

    #[test]
    fn current_p256_monolithic_verifier_rejects_unbalanced_scalar_consumer_sum() {
        use num_traits::One;
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        let mut monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("current AIR monolithic proof proves");
        monolithic
            .interaction_claim
            .fake_glv_selector_air
            .scalar_consumer_claimed_sum += SecureField::one();

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("scalar relation balance must reject mutated consumer sum");

        assert!(matches!(
            err,
            P256ProofError::RelationImbalance {
                relation: "FakeGlvScalar"
            }
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_invalid_final_signature_linkage() {
        let err =
            P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![test_input(42, 77, 1)])
                .expect_err("invalid final signature linkage must fail");

        assert!(matches!(
            err,
            P256ProofError::FinalEcdsaCheck(FinalEcdsaCheckError::SignatureRMismatch { .. })
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_mutated_projective_rcb_air_row() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.projective_rcb_air_trace.rows[0].muls[0]
            .reduction
            .rows[0]
            .folded_digit ^= 1;

        let err = proof
            .verify_current_e2e()
            .expect_err("mutated projective RCB AIR row must fail");

        assert!(matches!(
            err,
            P256ProofError::ProjectiveRcbAir(
                ProjectiveRcbAirError::FpSolinasReduction(
                    crate::fp_solinas_air::FpSolinasReductionTraceError::TraceRowsMismatch
                        | crate::fp_solinas_air::FpSolinasReductionTraceError::ReductionEquationMismatch { .. }
                )
                | ProjectiveRcbAirError::FoldedReductionDigitMismatch { .. }
            )
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_mutated_projective_rcb_raw_product_row() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.projective_rcb_air_trace.rows[0].muls[0].raw_product_chunks[0].digits[0] ^= 1;

        let err = proof
            .verify_current_e2e()
            .expect_err("mutated projective RCB raw product row must fail");

        assert!(matches!(
            err,
            P256ProofError::ProjectiveRcbAir(
                ProjectiveRcbAirError::RawProductChunkDigitMismatch { .. }
                    | ProjectiveRcbAirError::RawProductChunkMismatch { .. }
            )
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_projective_rcb_relation_imbalance() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof
            .interaction_claim
            .projective_rcb
            .raw_product_chunk_digit += SecureField::from(M31::from_u32_unchecked(1));

        let err = proof
            .interaction_claim
            .verify_balanced()
            .expect_err("mutated projective RCB relation sum must fail");

        assert!(matches!(
            err,
            P256ProofError::ProjectiveRcbAir(ProjectiveRcbAirError::RelationImbalance {
                relation: "ProjectiveRcbRawProductChunkDigit"
            })
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_mutated_projective_rcb_folded_row() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.projective_rcb_air_trace.rows[0].muls[0]
            .folded_digits
            .rows[0]
            .folded_digit ^= 1;

        let err = proof
            .verify_current_e2e()
            .expect_err("mutated projective RCB folded row must fail");

        assert!(matches!(
            err,
            P256ProofError::ProjectiveRcbAir(
                ProjectiveRcbAirError::FoldedDigitMismatch
                    | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
                    | ProjectiveRcbAirError::FoldedReductionDigitMismatch { .. }
            )
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_mutated_projective_rcb_folded_digit_group() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.projective_rcb_air_trace.rows[0].muls[0]
            .folded_digits
            .rows[0]
            .contribution_groups[0]
            .contribution_sum += 1;

        let err = proof
            .verify_current_e2e()
            .expect_err("mutated projective RCB folded digit group must fail");

        assert!(matches!(
            err,
            P256ProofError::ProjectiveRcbAir(
                ProjectiveRcbAirError::FoldedDigitContributionSumMismatch { .. }
                    | ProjectiveRcbAirError::FoldedDigitMismatch
            )
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_mutated_projective_rcb_folded_contribution() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.claim.projective_rcb_air_trace.rows[0].muls[0]
            .folded_contributions
            .rows[0]
            .contribution_sum += 1;

        let err = proof
            .verify_current_e2e()
            .expect_err("mutated projective RCB folded contribution must fail");

        assert!(matches!(
            err,
            P256ProofError::ProjectiveRcbAir(
                ProjectiveRcbAirError::FoldedContributionMismatch
                    | ProjectiveRcbAirError::FoldedContributionSumMismatch { .. }
                    | ProjectiveRcbAirError::FoldedDigitMismatch
                    | ProjectiveRcbAirError::FoldedDigitEquationMismatch { .. }
            )
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_public_key_off_curve() {
        let mut input = valid_real_input_with_small_u_scalars(7, 11);
        input.public_key.y = scalar(1);

        let err = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![input])
            .expect_err("off-curve public key must fail");

        assert!(matches!(
            err,
            P256ProofError::PublicKeyOnCurve(PublicKeyOnCurveError::PointOffCurve { .. })
        ));
    }

    #[test]
    fn current_p256_proof_pipeline_allows_zero_u1_branch() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");

        proof.verify_current_e2e().expect("zero branch verifies");
        assert_eq!(proof.claim.cert_inputs.rows[0].cert_active.0, 0);
        assert_eq!(
            proof.claim.prepared_use_counts.certs[0].total_use_count(),
            0
        );
        assert_eq!(
            proof.claim.prepared_use_counts.certs[1].total_use_count(),
            65
        );
        assert_eq!(proof.claim.fake_glv_chain.active_row_count(), 65);
        assert_eq!(proof.claim.fake_glv_ec_trace.active_row_count(), 190);
        assert_eq!(proof.claim.projective_ec_trace.active_row_count(), 203);
        assert_eq!(
            proof.claim.final_check.rows[0].h1,
            PreparedAffinePoint::infinity()
        );
    }

    #[test]
    fn current_p256_proof_pipeline_proves_selector_lookup_provider_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let selector_proof = prove_selector_lookup_provider_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.selector_requests,
            selector_lookup_provider_low_ram_config(),
        )
        .expect("selector lookup provider slice proves");

        verify_selector_lookup_provider_proof_slice::<Blake2sMerkleChannel>(selector_proof)
            .expect("selector lookup provider slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_prepared_table_ec_row_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let prepared_proof = prove_prepared_table_ec_row_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.prepared_table_ec_trace,
            prepared_table_ec_row_low_ram_config(&proof.claim.prepared_table_ec_trace),
        )
        .expect("prepared-table EC row provider slice proves");

        verify_prepared_table_ec_row_proof_slice::<Blake2sMerkleChannel>(prepared_proof)
            .expect("prepared-table EC row provider slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_prepared_table_projective_source_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let source_proof =
            prove_prepared_table_projective_source_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.prepared_table_ec_trace,
                &proof.claim.projective_ec_trace,
                prepared_table_projective_source_low_ram_config(
                    &proof.claim.prepared_table_ec_trace,
                ),
            )
            .expect("prepared-table/projective source slice proves");

        verify_prepared_table_projective_source_proof_slice::<Blake2sMerkleChannel>(source_proof)
            .expect("prepared-table/projective source slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_projective_source_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let source_offset = proof.claim.prepared_table_ec_trace.active_row_count();
        let source_proof = prove_fake_glv_projective_source_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_ec_trace,
            &proof.claim.projective_ec_trace,
            source_offset,
            fake_glv_projective_source_low_ram_config(
                &proof.claim.fake_glv_ec_trace,
                source_offset,
            ),
        )
        .expect("fake-GLV/projective source slice proves");

        verify_fake_glv_projective_source_proof_slice::<Blake2sMerkleChannel>(source_proof)
            .expect("fake-GLV/projective source slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_chain_expansion_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let source_offset = proof.claim.prepared_table_ec_trace.active_row_count();
        let expansion_proof = prove_fake_glv_chain_expansion_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            &proof.claim.fake_glv_ec_trace,
            source_offset,
            fake_glv_chain_expansion_low_ram_config(
                &proof.claim.fake_glv_chain,
                &proof.claim.fake_glv_ec_trace,
                source_offset,
            ),
        )
        .expect("fake-GLV chain expansion slice proves");

        verify_fake_glv_chain_expansion_proof_slice::<Blake2sMerkleChannel>(expansion_proof)
            .expect("fake-GLV chain expansion slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_chain_continuity_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let continuity_proof = prove_fake_glv_chain_continuity_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            fake_glv_chain_continuity_low_ram_config(&proof.claim.fake_glv_chain),
        )
        .expect("fake-GLV chain continuity slice proves");

        verify_fake_glv_chain_continuity_proof_slice::<Blake2sMerkleChannel>(continuity_proof)
            .expect("fake-GLV chain continuity slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_chain_schedule_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let schedule_proof = prove_fake_glv_chain_schedule_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            fake_glv_chain_schedule_low_ram_config(&proof.claim.fake_glv_chain),
        )
        .expect("fake-GLV chain schedule slice proves");

        verify_fake_glv_chain_schedule_proof_slice::<Blake2sMerkleChannel>(schedule_proof)
            .expect("fake-GLV chain schedule slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_direct_prepared_operand_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let operand_proof =
            prove_fake_glv_direct_prepared_operand_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.prepared_table,
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
                fake_glv_direct_prepared_operand_low_ram_config(
                    &proof.claim.fake_glv_selectors,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("fake-GLV direct prepared operand slice proves");

        verify_fake_glv_direct_prepared_operand_proof_slice::<Blake2sMerkleChannel>(operand_proof)
            .expect("fake-GLV direct prepared operand slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_signed_selector_operand_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let operand_proof =
            prove_fake_glv_signed_selector_operand_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.prepared_table,
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
                fake_glv_signed_selector_operand_low_ram_config(
                    &proof.claim.fake_glv_selectors,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("fake-GLV signed selector operand slice proves");

        verify_fake_glv_signed_selector_operand_proof_slice::<Blake2sMerkleChannel>(operand_proof)
            .expect("fake-GLV signed selector operand slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_lsb_correction_operand_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let operand_proof =
            prove_fake_glv_lsb_correction_operand_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.cert_inputs,
                &proof.claim.fake_glv_scalars,
                &proof.claim.prepared_table,
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
                fake_glv_lsb_correction_operand_low_ram_config(
                    &proof.claim.fake_glv_selectors,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("fake-GLV LSB correction operand slice proves");

        verify_fake_glv_lsb_correction_operand_proof_slice::<Blake2sMerkleChannel>(operand_proof)
            .expect("fake-GLV LSB correction operand slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_prepared_point_source_slice() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let prepared_point_proof =
            prove_fake_glv_prepared_point_source_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.prepared_trace,
                &proof.claim.fake_glv_chain,
                fake_glv_prepared_point_source_low_ram_config(
                    &proof.claim.prepared_trace,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("fake-GLV prepared-point source slice proves");

        verify_fake_glv_prepared_point_source_proof_slice::<Blake2sMerkleChannel>(
            prepared_point_proof,
        )
        .expect("fake-GLV prepared-point source slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_and_verifies_stark_slice_bundle() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let stark_slices = proof
            .prove_current_stark_slices::<Blake2sMerkleChannel>()
            .expect("P-256 STARK slice bundle proves");

        stark_slices
            .verify::<Blake2sMerkleChannel>()
            .expect("P-256 STARK slice bundle verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_and_verifies_current_air_monolithic_proof() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("current AIR monolithic proof proves");

        verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect("current AIR monolithic proof verifies");
    }

    #[test]
    #[ignore = "prints and asserts current AIR constraints component by component"]
    fn current_p256_air_constraint_diagnostic() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        assert_current_air_constraints(&proof);
    }

    #[test]
    #[ignore = "proves scalar setup mod-mul rows through PCS for degree/profile diagnostics"]
    fn scalar_setup_mod_mul_pcs_diagnostic() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        let rows = scalar_setup_mod_mul_rows(&proof.claim).expect("scalar mod-mul rows generate");

        for rows in &rows {
            prove_scalar_mod_mul_rows_for_diagnostic(rows);
        }
    }

    #[test]
    #[ignore = "proves fake-GLV scalar and selector AIR rows through PCS for degree/profile diagnostics"]
    fn fake_glv_scalar_selector_pcs_diagnostic() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");

        prove_fake_glv_scalar_air_for_diagnostic(&proof);
        prove_fake_glv_selector_air_for_diagnostic(&proof);
    }

    #[test]
    #[ignore = "checks scalar setup mod-mul AB schedule/base row order"]
    fn scalar_setup_mod_mul_ab_row_order_diagnostic() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        let rows = scalar_setup_mod_mul_rows(&proof.claim).expect("scalar mod-mul rows generate");

        for rows in &rows {
            assert_ab_schedule_base_row_order(rows);
        }
    }

    #[test]
    #[ignore = "checks scalar setup mod-mul AB decomposition in logical and storage order"]
    fn scalar_setup_mod_mul_ab_decomposition_row_order_diagnostic() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        let rows = scalar_setup_mod_mul_rows(&proof.claim).expect("scalar mod-mul rows generate");

        for rows in &rows {
            assert_ab_decomposition_columns(rows);
        }
    }

    fn assert_ab_schedule_base_row_order(rows: &ScalarModMulTraceRows) {
        let traces = ScalarModMulFamilyTraces::from_rows(rows);
        let schedule = ScalarModMulFixedSchedule::from_rows(rows);
        let trace_evals = traces.to_circle_evaluations();
        let schedule_evals = schedule.to_circle_evaluations();

        let terms = SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS;
        let digits = SCALAR_MOD_MUL_SPLIT_CHUNK_DIGITS;
        let mut comparisons = vec![(0, 0, "active"), (1, 1, "coeff"), (2, 2, "chunk")];

        for term in 0..terms {
            comparisons.push((3 + term, 3 + 3 * term, "term_active"));
            comparisons.push((3 + terms + term, 3 + 3 * term + 1, "lhs_index"));
            comparisons.push((3 + 2 * terms + term, 3 + 3 * term + 2, "rhs_index"));
        }
        for offset in 0..digits {
            comparisons.push((
                3 + 3 * terms + offset,
                3 + 3 * terms + offset,
                "digit_active",
            ));
        }
        assert_eq!(comparisons.len(), PRODUCT_METADATA_TRACE_COLUMNS);

        for (base_col, schedule_col, name) in comparisons {
            assert_eq!(
                traces.ab_chunks.columns[base_col], schedule.ab_chunks[schedule_col].values,
                "logical AB {name} column mismatch for mul_id={} base_col={base_col} schedule_col={schedule_col}",
                rows.mul_id,
            );
            assert_eq!(
                trace_evals.ab_chunks[base_col].values.to_cpu(),
                schedule_evals.ab_chunks[schedule_col].values.to_cpu(),
                "storage-order AB {name} column mismatch for mul_id={} base_col={base_col} schedule_col={schedule_col}",
                rows.mul_id,
            );
        }
    }

    fn assert_ab_decomposition_columns(rows: &ScalarModMulTraceRows) {
        let traces = ScalarModMulFamilyTraces::from_rows(rows);
        assert_ab_decomposition_column_set(
            rows.mul_id,
            "logical",
            traces.ab_chunks.columns.iter().map(Vec::as_slice).collect(),
        );

        let evals = traces.to_circle_evaluations();
        let storage_columns = evals
            .ab_chunks
            .iter()
            .map(|column| column.values.to_cpu())
            .collect::<Vec<_>>();
        assert_ab_decomposition_column_set(
            rows.mul_id,
            "storage",
            storage_columns.iter().map(Vec::as_slice).collect(),
        );
    }

    fn assert_ab_decomposition_column_set(mul_id: u32, order: &str, columns: Vec<&[M31]>) {
        let terms = SCALAR_MOD_MUL_SPLIT_CHUNK_TERMS;
        let limb_base = M31::from_u32_unchecked(1u32 << stwo_p256_utils::constants::LIMB_BITS);
        let digit_start = PRODUCT_METADATA_TRACE_COLUMNS + 3 * terms;
        for row in 0..columns[0].len() {
            let mut product_sum = M31::from_u32_unchecked(0);
            for term in 0..terms {
                let term_active = columns[3 + term][row];
                let product = columns[PRODUCT_METADATA_TRACE_COLUMNS + 3 * term + 2][row];
                product_sum += term_active * product;
            }
            let decomposition = product_sum
                - columns[digit_start][row]
                - limb_base * columns[digit_start + 1][row]
                - limb_base * limb_base * columns[digit_start + 2][row];
            assert_eq!(
                columns[0][row] * decomposition,
                M31::from_u32_unchecked(0),
                "AB decomposition mismatch mul_id={mul_id} order={order} row={row}",
            );
        }
    }

    fn prove_scalar_mod_mul_rows_for_diagnostic(rows: &ScalarModMulTraceRows) {
        eprintln!("prove scalar_mod_mul {} aggregate", rows.mul_id);
        let lookup_claims = LookupProviderClaims::scalar_mod_mul();
        let claim = ScalarModMulClaim::from_rows(rows);
        let ids = scalar_mod_mul_preprocessed_column_ids(&claim, &lookup_claims);
        let max_constraint_log_degree_bound = {
            let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
            let components = ScalarModMulComponents::new(
                &mut allocator,
                &claim,
                &zero_interaction_claim(),
                &lookup_claims,
                &ScalarModMulLookupRelations::dummy(),
            );
            scalar_mod_mul_max_constraint_log_degree_bound(&components)
        };
        let config = p256_stark_slice_low_ram_config(max_constraint_log_degree_bound);
        eprintln!(
            "scalar_mod_mul {} pcs max_bound={} blowup={} lifting={:?}",
            rows.mul_id,
            max_constraint_log_degree_bound,
            config.fri_config.log_blowup_factor,
            config.lifting_log_size
        );
        let twiddles =
            SimdBackend::precompute_twiddles(
                CanonicCoset::new(config.lifting_log_size.unwrap_or(
                    max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
                ))
                .circle_domain()
                .half_coset,
            );
        let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
        let preprocessed = gen_scalar_mod_mul_preprocessed_trace(rows, &lookup_claims, &ids);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.commit(&mut channel);

        claim.mix_into(&mut channel);
        let base = gen_scalar_mod_mul_base_trace(rows, &lookup_claims);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base);
        tree_builder.commit(&mut channel);

        let relations = ScalarModMulLookupRelations::draw(&mut channel);
        let claim = ScalarModMulClaim::from_rows(rows);
        let (interaction, interaction_claim) =
            gen_scalar_mod_mul_interaction_trace(rows, &claim, &lookup_claims, &relations);
        interaction_claim.scalar_mod_mul.mix_into(&mut channel);
        interaction_claim.range13.mix_into(&mut channel);
        interaction_claim.signed_carry.mix_into(&mut channel);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.commit(&mut channel);

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = ScalarModMulComponents::new(
            &mut allocator,
            &claim,
            &interaction_claim,
            &lookup_claims,
            &relations,
        );
        let component_provers = scalar_mod_mul_component_provers(&components);
        prove(&component_provers, &mut channel, commitment_scheme)
            .expect("scalar mod-mul PCS proof proves");
    }

    fn prove_fake_glv_scalar_air_for_diagnostic(proof: &P256ProofDraft) {
        eprintln!("prove fake_glv_scalar_air aggregate");
        let claim = FakeGlvScalarAirProofClaim::from_claim(&proof.claim.fake_glv_scalars);
        let max_constraint_log_degree_bound = {
            let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
            let components = FakeGlvScalarAirComponents::new(
                &mut allocator,
                claim,
                &FakeGlvScalarAirInteractionClaim::zero(),
                &CertScalarInputRelation::dummy(),
                &FakeGlvScalarRelation::dummy(),
            );
            components.max_constraint_log_degree_bound()
        };
        let config = p256_stark_slice_low_ram_config(max_constraint_log_degree_bound);
        eprintln!(
            "fake_glv_scalar_air pcs max_bound={} blowup={} lifting={:?}",
            max_constraint_log_degree_bound, config.fri_config.log_blowup_factor, config.lifting_log_size
        );
        let twiddles =
            SimdBackend::precompute_twiddles(
                CanonicCoset::new(config.lifting_log_size.unwrap_or(
                    max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
                ))
                .circle_domain()
                .half_coset,
            );
        let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
        commitment_scheme.set_store_polynomials_coefficients();

        let tree_builder = commitment_scheme.tree_builder();
        tree_builder.commit(&mut channel);

        claim.mix_into(&mut channel);
        let base = gen_fake_glv_scalar_air_base_trace(
            &proof.claim.cert_inputs,
            &proof.claim.fake_glv_scalars,
            claim,
        );
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base.clone());
        tree_builder.commit(&mut channel);

        let cert_relation = CertScalarInputRelation::draw(&mut channel);
        let scalar_relation = FakeGlvScalarRelation::draw(&mut channel);
        let (interaction, interaction_claim) =
            gen_fake_glv_scalar_air_interaction_trace(&base, &cert_relation, &scalar_relation);
        interaction_claim.mix_into(&mut channel);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.commit(&mut channel);

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
        let components = FakeGlvScalarAirComponents::new(
            &mut allocator,
            claim,
            &interaction_claim,
            &cert_relation,
            &scalar_relation,
        );
        prove(
            &components.component_provers(),
            &mut channel,
            commitment_scheme,
        )
        .expect("fake-GLV scalar AIR PCS proof proves");
    }

    fn prove_fake_glv_selector_air_for_diagnostic(proof: &P256ProofDraft) {
        eprintln!("prove fake_glv_selector_air aggregate");
        let claim = FakeGlvSelectorAirProofClaim::from_claim(&proof.claim.fake_glv_selectors);
        let max_constraint_log_degree_bound = {
            let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
            let components = FakeGlvSelectorAirComponents::new(
                &mut allocator,
                claim,
                &FakeGlvSelectorAirInteractionClaim::zero(),
                &FakeGlvScalarRelation::dummy(),
            );
            components.max_constraint_log_degree_bound()
        };
        let config = p256_stark_slice_low_ram_config(max_constraint_log_degree_bound);
        eprintln!(
            "fake_glv_selector_air pcs max_bound={} blowup={} lifting={:?}",
            max_constraint_log_degree_bound,
            config.fri_config.log_blowup_factor,
            config.lifting_log_size
        );
        let twiddles =
            SimdBackend::precompute_twiddles(
                CanonicCoset::new(config.lifting_log_size.unwrap_or(
                    max_constraint_log_degree_bound + config.fri_config.log_blowup_factor,
                ))
                .circle_domain()
                .half_coset,
            );
        let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
        commitment_scheme.set_store_polynomials_coefficients();

        let tree_builder = commitment_scheme.tree_builder();
        tree_builder.commit(&mut channel);

        claim.mix_into(&mut channel);
        let base = gen_fake_glv_selector_air_base_trace(
            &proof.claim.fake_glv_scalars,
            &proof.claim.fake_glv_selectors,
            claim,
        );
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base.clone());
        tree_builder.commit(&mut channel);

        let scalar_relation = FakeGlvScalarRelation::draw(&mut channel);
        let (interaction, interaction_claim) =
            gen_fake_glv_selector_air_interaction_trace(&base, &scalar_relation);
        interaction_claim.mix_into(&mut channel);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.commit(&mut channel);

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&[]);
        let components = FakeGlvSelectorAirComponents::new(
            &mut allocator,
            claim,
            &interaction_claim,
            &scalar_relation,
        );
        prove(
            &components.component_provers(),
            &mut channel,
            commitment_scheme,
        )
        .expect("fake-GLV selector AIR PCS proof proves");
    }

    fn scalar_mod_mul_max_constraint_log_degree_bound(components: &ScalarModMulComponents) -> u32 {
        [
            components.canonical.max_constraint_log_degree_bound(),
            components.ab_chunks.max_constraint_log_degree_bound(),
            components.qn_chunks.max_constraint_log_degree_bound(),
            components.accumulators.max_constraint_log_degree_bound(),
            components
                .reduction_digits
                .max_constraint_log_degree_bound(),
            components.range13.max_constraint_log_degree_bound(),
            components.signed_carry.max_constraint_log_degree_bound(),
        ]
        .into_iter()
        .max()
        .unwrap_or(0)
    }

    fn scalar_mod_mul_component_provers(
        components: &ScalarModMulComponents,
    ) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &components.canonical as &dyn ComponentProver<SimdBackend>,
            &components.ab_chunks as &dyn ComponentProver<SimdBackend>,
            &components.qn_chunks as &dyn ComponentProver<SimdBackend>,
            &components.accumulators as &dyn ComponentProver<SimdBackend>,
            &components.reduction_digits as &dyn ComponentProver<SimdBackend>,
            &components.range13 as &dyn ComponentProver<SimdBackend>,
            &components.signed_carry as &dyn ComponentProver<SimdBackend>,
        ]
    }

    fn assert_current_air_constraints(proof: &P256ProofDraft) {
        let claim = P256CurrentAirProofClaim::from_claim(&proof.claim);
        let ids = claim.preprocessed_column_ids();
        let preprocessed = proof
            .gen_current_air_preprocessed_trace(&claim, &ids)
            .expect("current AIR preprocessed trace generates");
        let base = proof
            .gen_current_air_base_trace(&claim)
            .expect("current AIR base trace generates");
        let mut dummy_channel = Blake2sM31Channel::default();
        let relations = P256CurrentAirRelations::draw(&mut dummy_channel);
        let (interaction, interaction_claim) = proof
            .gen_current_air_interaction_trace(&base, &relations)
            .expect("current AIR interaction trace generates");

        let mut commitment_scheme = MockCommitmentScheme::default();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.finalize_interaction();

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base.columns);
        tree_builder.finalize_interaction();

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.finalize_interaction();

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components =
            P256CurrentAirComponents::new(&mut allocator, &claim, &interaction_claim, &relations);
        let trace = commitment_scheme.trace_domain_evaluations();

        assert_component_named("scalar_setup.setup", &components.scalar_setup.setup, &trace);
        assert_component_named(
            "scalar_setup.range13",
            &components.scalar_setup.range13,
            &trace,
        );
        assert_component_named(
            "scalar_setup.range9",
            &components.scalar_setup.range9,
            &trace,
        );
        assert_component_named(
            "scalar_setup.signed_carry",
            &components.scalar_setup.signed_carry,
            &trace,
        );
        assert_component_named(
            "cert_scalar_inputs",
            &components.cert_scalar_inputs.certs,
            &trace,
        );
        assert_component_named(
            "fake_glv_scalar_air",
            &components.fake_glv_scalar_air.scalar,
            &trace,
        );
        assert_component_named(
            "fake_glv_selector_air",
            &components.fake_glv_selector_air.selector,
            &trace,
        );
        for (index, scalar_mod_mul) in components.scalar_setup_mod_muls.iter().enumerate() {
            assert_scalar_mod_mul_components_named(index, scalar_mod_mul, &trace);
        }
        assert_component_named(
            "prepared_table_projective_source.provider",
            &components.prepared_table_projective_source.provider,
            &trace,
        );
        assert_component_named(
            "prepared_table_projective_source.consumer",
            &components.prepared_table_projective_source.consumer,
            &trace,
        );
        assert_component_named(
            "fake_glv_projective_source.provider",
            &components.fake_glv_projective_source.provider,
            &trace,
        );
        assert_component_named(
            "fake_glv_projective_source.consumer",
            &components.fake_glv_projective_source.consumer,
            &trace,
        );
        assert_component_named(
            "fake_glv_chain_expansion.expansion",
            &components.fake_glv_chain_expansion.expansion,
            &trace,
        );
        assert_component_named(
            "fake_glv_chain_expansion.primitive",
            &components.fake_glv_chain_expansion.primitive,
            &trace,
        );
        assert_component_named(
            "fake_glv_chain_continuity",
            &components.fake_glv_chain_continuity,
            &trace,
        );
        assert_component_named(
            "fake_glv_chain_schedule",
            &components.fake_glv_chain_schedule,
            &trace,
        );
        assert_component_named(
            "fake_glv_direct_prepared_operand.provider",
            &components.fake_glv_direct_prepared_operand.provider,
            &trace,
        );
        assert_component_named(
            "fake_glv_direct_prepared_operand.consumer",
            &components.fake_glv_direct_prepared_operand.consumer,
            &trace,
        );
        assert_component_named(
            "fake_glv_signed_selector_operand.provider",
            &components.fake_glv_signed_selector_operand.provider,
            &trace,
        );
        assert_component_named(
            "fake_glv_signed_selector_operand.consumer",
            &components.fake_glv_signed_selector_operand.consumer,
            &trace,
        );
        assert_component_named(
            "fake_glv_lsb_correction_operand.provider",
            &components.fake_glv_lsb_correction_operand.provider,
            &trace,
        );
        assert_component_named(
            "fake_glv_lsb_correction_operand.consumer",
            &components.fake_glv_lsb_correction_operand.consumer,
            &trace,
        );
        assert_component_named(
            "fake_glv_prepared_point_source.provider",
            &components.fake_glv_prepared_point_source.provider,
            &trace,
        );
        assert_component_named(
            "fake_glv_prepared_point_source.consumer",
            &components.fake_glv_prepared_point_source.consumer,
            &trace,
        );
        assert_component_named(
            "prepared_point_range7",
            &components.prepared_point_range7,
            &trace,
        );
        assert_component_named(
            "projective_rcb_air.mul",
            &components.projective_rcb_air.mul,
            &trace,
        );
        assert_component_named(
            "projective_rcb_air.raw_product_chunk",
            &components.projective_rcb_air.raw_product_chunk,
            &trace,
        );
        assert_component_named(
            "projective_rcb_air.folded_contribution",
            &components.projective_rcb_air.folded_contribution,
            &trace,
        );
        assert_component_named(
            "projective_rcb_air.folded_digit",
            &components.projective_rcb_air.folded_digit,
            &trace,
        );
        assert_component_named(
            "projective_rcb_air.range13",
            &components.projective_rcb_air.range13,
            &trace,
        );
        assert_component_named(
            "projective_rcb_air.signed_carry",
            &components.projective_rcb_air.signed_carry,
            &trace,
        );
    }

    fn assert_scalar_mod_mul_components_named(
        index: usize,
        components: &ScalarModMulComponents,
        trace: &TreeVec<Vec<&Vec<M31>>>,
    ) {
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.canonical"),
            &components.canonical,
            trace,
        );
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.ab_chunks"),
            &components.ab_chunks,
            trace,
        );
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.qn_chunks"),
            &components.qn_chunks,
            trace,
        );
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.accumulators"),
            &components.accumulators,
            trace,
        );
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.reduction_digits"),
            &components.reduction_digits,
            trace,
        );
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.range13"),
            &components.range13,
            trace,
        );
        assert_component_named(
            &format!("scalar_setup_mod_mul_{index}.signed_carry"),
            &components.signed_carry,
            trace,
        );
    }

    fn assert_component_named<E: FrameworkEval + Sync>(
        name: &str,
        component: &FrameworkComponent<E>,
        trace: &TreeVec<Vec<&Vec<M31>>>,
    ) {
        eprintln!("assert {name}");
        let mut component_trace = trace
            .sub_tree(component.trace_locations())
            .map(|tree| tree.into_iter().cloned().collect::<Vec<_>>());
        component_trace[PREPROCESSED_TRACE_IDX] = component
            .preprocessed_column_indices()
            .iter()
            .map(|index| trace[PREPROCESSED_TRACE_IDX][*index])
            .collect();

        let component_eval = component.deref();
        assert_constraints_on_trace(
            &component_trace,
            component.log_size(),
            |eval| {
                let _ = component_eval.evaluate(eval);
            },
            component.claimed_sum(),
        );
    }

    #[test]
    #[ignore = "prints current AIR row/column shape for performance diagnostics"]
    fn current_p256_air_shape_diagnostic() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let claim = P256CurrentAirProofClaim::from_claim(&proof.claim);
        let ids = claim.preprocessed_column_ids();
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = P256CurrentAirComponents::new(
            &mut allocator,
            &claim,
            &P256CurrentAirInteractionClaim::zero(),
            &P256CurrentAirRelations::dummy(),
        );

        eprintln!("current-air unique_preprocessed_columns={}", ids.len());
        eprintln!(
            "current-air max_constraint_log_degree_bound={}",
            claim.max_constraint_log_degree_bound(&ids)
        );
        eprintln!(
            "native rows: prepared_ec={} fake_glv_chain={} fake_glv_primitive_ec={} projective_ec={} projective_rcb_active={} projective_mul={}",
            proof.claim.prepared_table_ec_trace.active_row_count(),
            proof.claim.fake_glv_chain.active_row_count(),
            proof.claim.fake_glv_ec_trace.active_row_count(),
            proof.claim.projective_ec_trace.active_row_count(),
            proof.claim.projective_rcb_air_trace.active_row_count(),
            proof.claim.projective_rcb_air_trace.mul_row_count(),
        );
        eprintln!(
            "projective row families: raw_chunks={} folded_contributions={} folded_digits={} reductions={}",
            proof.claim.projective_rcb_air_trace.raw_product_chunk_count(),
            proof.claim.projective_rcb_air_trace.folded_contribution_row_count(),
            proof.claim.projective_rcb_air_trace.folded_digit_row_count(),
            proof.claim.projective_rcb_air_trace.reduction_row_count(),
        );

        for (index, scalar_mod_mul) in components.scalar_setup_mod_muls.iter().enumerate() {
            print_component_shape(
                &format!("scalar_setup_mod_mul_{index}"),
                scalar_mod_mul_component_bounds(scalar_mod_mul),
            );
        }
        print_component_shape(
            "prepared_table_projective_source",
            components
                .prepared_table_projective_source
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_projective_source",
            components
                .fake_glv_projective_source
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_chain_expansion",
            components
                .fake_glv_chain_expansion
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_chain_continuity",
            components
                .fake_glv_chain_continuity
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_chain_schedule",
            components.fake_glv_chain_schedule.trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_direct_prepared_operand",
            components
                .fake_glv_direct_prepared_operand
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_signed_selector_operand",
            components
                .fake_glv_signed_selector_operand
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_lsb_correction_operand",
            components
                .fake_glv_lsb_correction_operand
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "fake_glv_prepared_point_source",
            components
                .fake_glv_prepared_point_source
                .trace_log_degree_bounds(),
        );
        print_component_shape(
            "projective_rcb_air",
            components.projective_rcb_air.trace_log_degree_bounds(),
        );
        print_component_shape("current_air_total", components.trace_log_degree_bounds());
    }

    fn print_component_shape(name: &str, bounds: TreeVec<ColumnVec<u32>>) {
        let labels = ["preprocessed", "base", "interaction"];
        for (tree, columns) in bounds.0.iter().enumerate() {
            let mut by_log_size = BTreeMap::new();
            for log_size in columns {
                *by_log_size.entry(*log_size).or_insert(0usize) += 1;
            }
            eprintln!(
                "shape {name} {} columns={} by_log_size={:?}",
                labels.get(tree).copied().unwrap_or("extra"),
                columns.len(),
                by_log_size
            );
        }
    }

    fn scalar_mod_mul_component_bounds(
        components: &ScalarModMulComponents,
    ) -> TreeVec<ColumnVec<u32>> {
        TreeVec::concat_cols(
            [
                components.canonical.trace_log_degree_bounds(),
                components.ab_chunks.trace_log_degree_bounds(),
                components.qn_chunks.trace_log_degree_bounds(),
                components.accumulators.trace_log_degree_bounds(),
                components.reduction_digits.trace_log_degree_bounds(),
                components.range13.trace_log_degree_bounds(),
                components.signed_carry.trace_log_degree_bounds(),
            ]
            .into_iter(),
        )
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_prepared_point_source_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");
        let provider = proof
            .claim
            .prepared_trace
            .providers
            .iter_mut()
            .find(|provider| provider.use_count.0 != 0)
            .expect("at least one prepared-point provider is used");
        provider.instance.table_index =
            M31::from_u32_unchecked(provider.instance.table_index.0 + 1);

        let err = prove_fake_glv_prepared_point_source_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.prepared_trace,
            &proof.claim.fake_glv_chain,
            fake_glv_prepared_point_source_low_ram_config(
                &proof.claim.prepared_trace,
                &proof.claim.fake_glv_chain,
            ),
        )
        .expect_err("mutated fake-GLV prepared-point consumer must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvPreparedPointSource",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_chain_expansion_slice_with_zero_branch() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let source_offset = proof.claim.prepared_table_ec_trace.active_row_count();
        let expansion_proof = prove_fake_glv_chain_expansion_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            &proof.claim.fake_glv_ec_trace,
            source_offset,
            fake_glv_chain_expansion_low_ram_config(
                &proof.claim.fake_glv_chain,
                &proof.claim.fake_glv_ec_trace,
                source_offset,
            ),
        )
        .expect("zero-branch fake-GLV chain expansion slice proves");

        verify_fake_glv_chain_expansion_proof_slice::<Blake2sMerkleChannel>(expansion_proof)
            .expect("zero-branch fake-GLV chain expansion slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_chain_continuity_slice_with_zero_branch() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let continuity_proof = prove_fake_glv_chain_continuity_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            fake_glv_chain_continuity_low_ram_config(&proof.claim.fake_glv_chain),
        )
        .expect("zero-branch fake-GLV chain continuity slice proves");

        verify_fake_glv_chain_continuity_proof_slice::<Blake2sMerkleChannel>(continuity_proof)
            .expect("zero-branch fake-GLV chain continuity slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_chain_schedule_slice_with_zero_branch() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let schedule_proof = prove_fake_glv_chain_schedule_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            fake_glv_chain_schedule_low_ram_config(&proof.claim.fake_glv_chain),
        )
        .expect("zero-branch fake-GLV chain schedule slice proves");

        verify_fake_glv_chain_schedule_proof_slice::<Blake2sMerkleChannel>(schedule_proof)
            .expect("zero-branch fake-GLV chain schedule slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_direct_prepared_operand_slice_with_zero_branch()
    {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let operand_proof =
            prove_fake_glv_direct_prepared_operand_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.prepared_table,
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
                fake_glv_direct_prepared_operand_low_ram_config(
                    &proof.claim.fake_glv_selectors,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("zero-branch fake-GLV direct prepared operand slice proves");

        verify_fake_glv_direct_prepared_operand_proof_slice::<Blake2sMerkleChannel>(operand_proof)
            .expect("zero-branch fake-GLV direct prepared operand slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_signed_selector_operand_slice_with_zero_branch()
    {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let operand_proof =
            prove_fake_glv_signed_selector_operand_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.prepared_table,
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
                fake_glv_signed_selector_operand_low_ram_config(
                    &proof.claim.fake_glv_selectors,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("zero-branch fake-GLV signed selector operand slice proves");

        verify_fake_glv_signed_selector_operand_proof_slice::<Blake2sMerkleChannel>(operand_proof)
            .expect("zero-branch fake-GLV signed selector operand slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_proves_fake_glv_lsb_correction_operand_slice_with_zero_branch() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(0, 11),
        ])
        .expect("zero branch pipeline builds");
        proof.verify_current_e2e().expect("zero branch verifies");

        let operand_proof =
            prove_fake_glv_lsb_correction_operand_proof_slice::<Blake2sMerkleChannel>(
                &proof.claim.cert_inputs,
                &proof.claim.fake_glv_scalars,
                &proof.claim.prepared_table,
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
                fake_glv_lsb_correction_operand_low_ram_config(
                    &proof.claim.fake_glv_selectors,
                    &proof.claim.fake_glv_chain,
                ),
            )
            .expect("zero-branch fake-GLV LSB correction operand slice proves");

        verify_fake_glv_lsb_correction_operand_proof_slice::<Blake2sMerkleChannel>(operand_proof)
            .expect("zero-branch fake-GLV LSB correction operand slice verifies");
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_chain_expansion_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let source_offset = proof.claim.prepared_table_ec_trace.active_row_count();
        proof.claim.fake_glv_ec_trace.rows[0].sig_id =
            M31::from_u32_unchecked(proof.claim.fake_glv_ec_trace.rows[0].sig_id.0 + 1);

        let err = prove_fake_glv_chain_expansion_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            &proof.claim.fake_glv_ec_trace,
            source_offset,
            fake_glv_chain_expansion_low_ram_config(
                &proof.claim.fake_glv_chain,
                &proof.claim.fake_glv_ec_trace,
                source_offset,
            ),
        )
        .expect_err("mutated fake-GLV primitive expansion tuple must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvChainExpansion",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_chain_continuity_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let row = proof
            .claim
            .fake_glv_chain
            .certs
            .iter_mut()
            .find_map(|cert| cert.rows.get_mut(1))
            .expect("at least one active certificate has a successor row");
        row.sig_id = M31::from_u32_unchecked(row.sig_id.0 + 1);

        let err = prove_fake_glv_chain_continuity_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            fake_glv_chain_continuity_low_ram_config(&proof.claim.fake_glv_chain),
        )
        .expect_err("mutated fake-GLV chain continuity tuple must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvChainContinuity",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_chain_schedule_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let row = proof
            .claim
            .fake_glv_chain
            .certs
            .iter_mut()
            .find_map(|cert| cert.rows.get_mut(1))
            .expect("at least one active certificate has a successor row");
        row.kind = crate::fake_glv_chain::FakeGlvChainRowKind::Table16Step;

        let err = prove_fake_glv_chain_schedule_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_chain,
            fake_glv_chain_schedule_low_ram_config(&proof.claim.fake_glv_chain),
        )
        .expect_err("mutated fake-GLV chain schedule must reject");

        assert_eq!(err, FakeGlvChainError::ProofLayer);
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_direct_prepared_operand_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let msb = proof
            .claim
            .fake_glv_chain
            .certs
            .iter_mut()
            .find_map(|cert| {
                cert.rows
                    .iter_mut()
                    .find(|row| row.kind == crate::fake_glv_chain::FakeGlvChainRowKind::MsbInit)
            })
            .expect("at least one active certificate has an MSB init row");
        msb.operand.x.limbs_mut()[0] += M31::from_u32_unchecked(1);
        msb.acc_after = msb.operand.clone();

        let err = prove_fake_glv_direct_prepared_operand_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.prepared_table,
            &proof.claim.fake_glv_selectors,
            &proof.claim.fake_glv_chain,
            fake_glv_direct_prepared_operand_low_ram_config(
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
            ),
        )
        .expect_err("mutated fake-GLV direct prepared operand must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvDirectPreparedOperand",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_signed_selector_operand_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let (cert_index, base_index) = proof
            .claim
            .fake_glv_selectors
            .rows
            .iter()
            .enumerate()
            .find_map(|(cert_index, selector_row)| {
                if selector_row.cert_active.0 == 0 {
                    return None;
                }
                (1..crate::scalar::fake_glv_selector::FAKE_GLV_SELECTOR_CHUNKS)
                    .rev()
                    .find_map(|step| {
                        let decoded =
                            crate::scalar::fake_glv_selector_lookup::Selector16DecodeEntry::from_selector(
                                selector_row.selectors[step],
                            )
                            .ok()?;
                        let base_index = decoded.base_index.0 as usize;
                        (proof.claim.prepared_table.certs[cert_index].base[base_index].inf.0 == 0)
                            .then_some((cert_index, base_index))
                    })
            })
            .expect("at least one finite signed selector base point is used");
        proof.claim.prepared_table.certs[cert_index].base[base_index]
            .x
            .limbs_mut()[0] += M31::from_u32_unchecked(1);

        let err = prove_fake_glv_signed_selector_operand_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.prepared_table,
            &proof.claim.fake_glv_selectors,
            &proof.claim.fake_glv_chain,
            fake_glv_signed_selector_operand_low_ram_config(
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
            ),
        )
        .expect_err("mutated fake-GLV signed selector operand must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvSignedSelectorOperand",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_lsb_correction_operand_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(6, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let cert_index = proof
            .claim
            .fake_glv_selectors
            .rows
            .iter()
            .position(|selector| {
                selector.cert_active.0 == 1 && selector.s1_lsb.0 == 0 && selector.s2_lsb.0 == 1
            })
            .expect("at least one active certificate uses the -P LSB correction");
        proof.claim.cert_inputs.rows[cert_index].base_x.limbs_mut()[0] +=
            M31::from_u32_unchecked(1);

        let err = prove_fake_glv_lsb_correction_operand_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.cert_inputs,
            &proof.claim.fake_glv_scalars,
            &proof.claim.prepared_table,
            &proof.claim.fake_glv_selectors,
            &proof.claim.fake_glv_chain,
            fake_glv_lsb_correction_operand_low_ram_config(
                &proof.claim.fake_glv_selectors,
                &proof.claim.fake_glv_chain,
            ),
        )
        .expect_err("mutated fake-GLV LSB correction operand must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvLsbCorrectionOperand",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_rejects_mutated_fake_glv_projective_source_slice() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.verify_current_e2e().expect("current e2e verifies");

        let source_offset = proof.claim.prepared_table_ec_trace.active_row_count();
        proof.claim.projective_ec_trace.rows[source_offset].sig_id = M31::from_u32_unchecked(
            proof.claim.projective_ec_trace.rows[source_offset].sig_id.0 + 1,
        );

        let err = prove_fake_glv_projective_source_proof_slice::<Blake2sMerkleChannel>(
            &proof.claim.fake_glv_ec_trace,
            &proof.claim.projective_ec_trace,
            source_offset,
            fake_glv_projective_source_low_ram_config(
                &proof.claim.fake_glv_ec_trace,
                source_offset,
            ),
        )
        .expect_err("mutated fake-GLV/projective source tuple must reject");

        assert_eq!(
            err,
            FakeGlvChainError::RelationImbalance {
                relation: "FakeGlvProjectiveSource",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_reports_pending_full_proof_slots() {
        let pending = P256_PROOF_COMPONENT_SLOTS
            .iter()
            .filter(|slot| slot.status == P256ProofComponentStatus::Pending)
            .map(|slot| slot.name)
            .collect::<Vec<_>>();
        let implemented = P256_PROOF_COMPONENT_SLOTS
            .iter()
            .filter(|slot| slot.status == P256ProofComponentStatus::Implemented)
            .map(|slot| slot.name)
            .collect::<Vec<_>>();

        assert!(implemented.contains(&"PublicEcdsaInput"));
        assert!(pending.contains(&"PublicKeyOnCurve"));
        assert!(pending.contains(&"SolinasReductionTraceRows"));
        assert!(implemented.contains(&"ScalarSetup"));
        assert!(implemented.contains(&"CertScalarInput"));
        assert!(implemented.contains(&"FakeGlvSelector"));
        assert!(implemented.contains(&"PreparedPointUseCounts"));
        assert!(pending.contains(&"PreparedTablePoints"));
        assert!(implemented.contains(&"PreparedTableEcTrace"));
        assert!(implemented.contains(&"PreparedTableEcRows"));
        assert!(implemented.contains(&"FakeGlvChainTrace"));
        assert!(implemented.contains(&"FakeGlvPrimitiveEcTrace"));
        assert!(implemented.contains(&"FakeGlvEcChainRows"));
        assert!(implemented.contains(&"ProjectiveRcbEcTrace"));
        assert!(implemented.contains(&"ProjectiveRcbAirRows"));
        assert!(pending.contains(&"FinalEcdsaCheck"));
        assert!(implemented.contains(&"StarkProveVerify"));
        assert!(!pending.contains(&"PreparedTableEcRows"));
        assert!(!pending.contains(&"FakeGlvScalarHint"));
        assert!(!pending.contains(&"FakeGlvEcChainRows"));
    }

    #[test]
    #[ignore = "close-out gate: enable when all native-only full-proof slots are AIR-proven"]
    fn full_p256_signature_proof_has_no_pending_component_slots() {
        let pending = P256_PROOF_COMPONENT_SLOTS
            .iter()
            .filter(|slot| slot.status == P256ProofComponentStatus::Pending)
            .map(|slot| slot.name)
            .collect::<Vec<_>>();

        assert!(
            pending.is_empty(),
            "full P-256 signature proof still has pending AIR slots: {pending:?}"
        );
    }

    #[test]
    fn current_p256_proof_pipeline_detects_public_relation_imbalance() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.interaction_claim.public_inputs.consumer_claimed_sum = zero();

        let err = proof
            .interaction_claim
            .verify_balanced()
            .expect_err("mutated public consumer sum must fail");

        assert_eq!(
            err,
            P256ProofError::RelationImbalance {
                relation: "PublicEcdsaInstance",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_detects_selector_lookup_imbalance() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof
            .interaction_claim
            .selector_lookups
            .consumer_claimed_sum = zero();

        let err = proof
            .interaction_claim
            .verify_balanced()
            .expect_err("mutated selector consumer sum must fail");

        assert_eq!(
            err,
            P256ProofError::RelationImbalance {
                relation: "SelectorLookups",
            }
        );
    }

    #[test]
    fn current_p256_proof_pipeline_detects_prepared_point_imbalance() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");
        proof.interaction_claim.prepared_points.consumer_claimed_sum = zero();

        let err = proof
            .interaction_claim
            .verify_balanced()
            .expect_err("mutated prepared consumer sum must fail");

        assert_eq!(
            err,
            P256ProofError::RelationImbalance {
                relation: "PreparedPoint",
            }
        );
    }
}
