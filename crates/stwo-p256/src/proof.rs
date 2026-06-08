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
    gen_fake_glv_chain_continuity_preprocessed_trace, FakeGlvChainAccumulatorRelation,
    FakeGlvChainContinuityComponent, FakeGlvChainContinuityEval,
    FakeGlvChainContinuityInteractionClaim, FakeGlvChainContinuityProofClaim,
};
use crate::fake_glv_chain_expansion::{
    gen_fake_glv_chain_expansion_base_trace, gen_fake_glv_chain_expansion_interaction_trace,
    gen_fake_glv_chain_expansion_preprocessed_trace,
    gen_fake_glv_primitive_expansion_consumer_base_trace,
    gen_fake_glv_primitive_expansion_consumer_interaction_trace,
    FakeGlvChainExpansionComponents, FakeGlvChainExpansionInteractionClaim,
    FakeGlvChainExpansionProofClaim, FakeGlvChainPrimitiveExpansionRelation,
};
use crate::fake_glv_chain_schedule::{
    gen_fake_glv_chain_schedule_base_trace, gen_fake_glv_chain_schedule_preprocessed_trace,
    FakeGlvChainScheduleComponent, FakeGlvChainScheduleEval, FakeGlvChainScheduleProofClaim,
};
use crate::fake_glv_direct_prepared_operand::{
    gen_direct_operand_consumer_base_trace, gen_direct_operand_consumer_interaction_trace,
    gen_direct_operand_preprocessed_trace, gen_direct_operand_provider_base_trace,
    gen_direct_operand_provider_interaction_trace, FakeGlvDirectPreparedOperandComponents,
    FakeGlvDirectPreparedOperandInteractionClaim, FakeGlvDirectPreparedOperandProofClaim,
};
use crate::fake_glv_ec_source::{
    gen_fake_glv_primitive_ec_preprocessed_trace, gen_fake_glv_primitive_ec_source_base_trace,
    gen_fake_glv_primitive_ec_source_interaction_trace, gen_fake_glv_projective_source_base_trace,
    FakeGlvPrimitiveEcRowRelation, FakeGlvProjectiveSourceComponents,
    FakeGlvProjectiveSourceInteractionClaim, FakeGlvProjectiveSourceProofClaim,
    RelationMultiplicity,
};
use crate::fake_glv_lsb_correction_operand::{
    gen_lsb_correction_operand_consumer_base_trace, gen_lsb_correction_operand_interaction_trace,
    gen_lsb_correction_operand_preprocessed_trace, gen_lsb_correction_operand_provider_base_trace,
    FakeGlvLsbCorrectionOperandComponents, FakeGlvLsbCorrectionOperandInteractionClaim,
    FakeGlvLsbCorrectionOperandProofClaim, FakeGlvLsbCorrectionOperandRelation,
};
use crate::fake_glv_prepared_point_source::{
    gen_fake_glv_prepared_point_consumer_base_trace,
    gen_fake_glv_prepared_point_consumer_interaction_trace,
    gen_fake_glv_prepared_point_source_preprocessed_trace, gen_prepared_point_provider_base_trace,
    gen_prepared_point_provider_interaction_trace, FakeGlvPreparedPointSourceComponents,
    FakeGlvPreparedPointSourceInteractionClaim, FakeGlvPreparedPointSourceProofClaim,
};
use crate::final_add_air::{
    final_add_preprocessed_columns, gen_final_add_base_trace, gen_final_add_interaction_trace,
    FinalAddClaim, FinalAddComponents, FinalAddError, FinalAddInteractionClaim,
    FinalAddMulResultRelation, FinalAddOutputRelation, FinalAddProofClaim, FinalAddRelations,
};
use crate::final_check::{FinalEcdsaCheckClaim, FinalEcdsaCheckError};
use crate::final_check_air::{
    ecdsa_result_provider_claimed_sum, gen_final_check_air_base_trace,
    gen_final_check_air_interaction_trace, EcdsaResultRelation, FinalCheckAirComponents,
    FinalCheckAirInteractionClaim, FinalCheckAirProofClaim, FinalCheckAirRelations,
};
use crate::prepared_table::FinalCheckHintRelation;
use crate::prepared_point::{
    prepared_point_provider_claimed_sum, prepared_point_range7_consumer_claimed_sum,
    PreparedPointAudit, PreparedPointError, PreparedPointRelation, PreparedPointTraceClaim,
    PreparedPointUseCountClaim,
};
use crate::prepared_table::{
    gen_prepared_table_ec_row_base_trace,
    gen_prepared_table_ec_row_preprocessed_trace, gen_prepared_table_projective_source_base_trace,
    gen_prepared_table_projective_source_interaction_trace,
    gen_prepared_table_ec_row_pinned_interaction_trace, CertBaseRelation,
    PreparedTableCanonicalRelation, PreparedTableClaim, PreparedTableEcRowPinnedInteractionClaim,
    PreparedTableEcRowRelation, PreparedTableEcTraceClaim, PreparedTableError,
    PreparedTablePinningRelations, PreparedTableProjectiveSourceComponents,
    PreparedTableProjectiveSourceInteractionClaim, PreparedTableProjectiveSourceProofClaim,
};
use crate::projective::{ProjectiveEcError, ProjectiveEcTraceClaim};
use crate::projective_air::{
    projective_rcb_signed_carry_log_size, ProjectiveRcbAirComponents, ProjectiveRcbAirError,
    ProjectiveRcbAirInteractionClaim, ProjectiveRcbAirProofClaim,
    ProjectiveRcbAirProofInteractionClaim, ProjectiveRcbAirTraceClaim,
    ProjectiveRcbMulComponentRelations, PROJECTIVE_RCB_SIGNED_CARRY_BOUND,
    PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::public_inputs::{
    public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
};
use crate::public_key_check::{PublicKeyOnCurveClaim, PublicKeyOnCurveError};
use crate::public_key_curve_air::{
    gen_slice_base_trace as gen_public_key_on_curve_base_trace,
    gen_slice_interaction_trace as gen_public_key_on_curve_interaction_trace,
    gen_slice_preprocessed_trace as gen_public_key_on_curve_preprocessed_trace,
    PublicKeyCurveSliceClaim, PublicKeyCurveSliceComponents, PublicKeyCurveSliceError,
    PublicKeyCurveSliceInteractionClaim, PublicKeyCurveSliceProofClaim,
    PublicKeyCurveSliceRelations, PublicKeyPointRelation,
};
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
    fake_glv_small_to_le_u64s, gen_fake_glv_scalar_air_base_trace,
    gen_fake_glv_scalar_air_interaction_trace, FakeGlvScalarAirComponents,
    FakeGlvScalarAirInteractionClaim, FakeGlvScalarAirProofClaim, FakeGlvScalarHint,
    FakeGlvScalarHintClaim, FakeGlvScalarHintError, FakeGlvScalarRelation,
};
use crate::scalar::fake_glv_selector::{
    gen_fake_glv_selector_air_base_trace, gen_fake_glv_selector_air_interaction_trace,
    FakeGlvSelectorAirComponents, FakeGlvSelectorAirInteractionClaim,
    FakeGlvSelectorAirProofClaim, FakeGlvSelectorClaim, FakeGlvSelectorError,
};
use crate::scalar::fake_glv_selector_lookup::{
    selector_lookup_consumer_claimed_sum, FakeGlvSelectorLookupRelations, SelectorLookupAudit,
    SelectorLookupError, SelectorLookupRequests, SelectorProviderInteractionClaim,
};
use crate::scalar::fake_glv_signed_selector_operand::{
    gen_signed_selector_operand_consumer_base_trace, gen_signed_selector_operand_interaction_trace,
    gen_signed_selector_operand_preprocessed_trace,
    gen_signed_selector_operand_provider_base_trace, FakeGlvSignedSelectorOperandComponents,
    FakeGlvSignedSelectorOperandInteractionClaim, FakeGlvSignedSelectorOperandProofClaim,
    FakeGlvSignedSelectorOperandRelation,
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
    /// In-AIR EC addition `S = R_1 + R_2` binding `r_x = x(S)`. Single signature.
    pub final_add: FinalAddClaim,
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
        let final_add = final_add_claim_from_final_check(&final_check, &fake_glv_scalars)?;
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
            final_add,
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

    /// Production builder: Garaga-style fake-GLV decomposition for any
    /// scalar in `[0, n)`. Used for all real ECDSA signatures.
    ///
    /// Note: the AIR currently enforces the *trivial* fake-GLV constraints
    /// (`s1 = scalar, s2 = 1, q = 0`). Tasks 3–4 of the
    /// `2026-06-05-arbitrary-p256-signature-air.md` plan replace those with
    /// the general `k · s2_abs ≡ ±s1 (mod n)` constraints proved via
    /// `ScalarModMul` external limb links. Until those land, this builder
    /// produces a valid native witness but `prove_current_air_monolithic`
    /// will reject any signature whose `u1`/`u2` exceed `2^128`.
    pub fn from_inputs_with_arbitrary_fake_glv_hints(
        inputs: &[EcdsaVerifyInput],
    ) -> Result<Self, P256ProofError> {
        let public_inputs = PublicEcdsaInputClaim::from_inputs(inputs);
        let scalar_setup = ScalarSetupClaim::from_public_inputs(&public_inputs)?;
        let cert_inputs = CertScalarInputClaim::from_scalar_setup(&scalar_setup)?;
        let hints = cert_inputs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::decompose(&row.scalar))
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_inputs_with_hints(inputs, hints)
    }

    /// Test-only: build a globally-shaped proof claim in which the prepared
    /// table + fake-GLV chain for `override_cert_index` are rebuilt from an
    /// injected hint point `R'` (`!= ±u·base`), with every R-derived artifact
    /// (EC trace, projective trace, rcb-air trace, prepared-point trace)
    /// cascaded consistently from `R'`. The `final_check` is taken from the
    /// true-R build (its `r_x`/`expected_r` columns bind to the public `r`
    /// independently of the chain), so the public-input relation still
    /// balances. The chain's `final_acc == r3` native gate is *not* asserted
    /// during construction — the experiment then asks whether the monolithic
    /// AIR constraints reject this wrong-`R'` witness.
    #[cfg(test)]
    pub(crate) fn from_inputs_with_wrong_r_for_cert(
        inputs: &[EcdsaVerifyInput],
        override_cert_index: usize,
        r_override: crate::types::AffinePoint,
    ) -> Result<Self, P256ProofError> {
        let base = Self::from_inputs_with_trivial_fake_glv_hints(inputs)?;

        let prepared_table = PreparedTableClaim::from_claims_with_r_override(
            &base.cert_inputs,
            &base.fake_glv_scalars,
            &base.fake_glv_selectors,
            override_cert_index,
            r_override.clone(),
        )?;
        let prepared_table_ec_trace = PreparedTableEcTraceClaim::from_claims_with_r_override(
            &base.cert_inputs,
            &base.fake_glv_scalars,
            &base.fake_glv_selectors,
            &prepared_table,
            override_cert_index,
            r_override.clone(),
        )?;
        let fake_glv_chain = FakeGlvChainClaim::from_claims_with_r_override(
            &base.cert_inputs,
            &base.fake_glv_scalars,
            &base.fake_glv_selectors,
            &prepared_table,
            override_cert_index,
            r_override.clone(),
        )?;
        let fake_glv_ec_trace = FakeGlvPrimitiveEcTraceClaim::from_chain(&fake_glv_chain)?;
        let projective_ec_trace = ProjectiveEcTraceClaim::from_native_traces(
            &prepared_table_ec_trace,
            &fake_glv_ec_trace,
        )?;
        let projective_rcb_air_trace =
            ProjectiveRcbAirTraceClaim::from_projective_trace(&projective_ec_trace)?;
        let prepared_trace = prepared_table.prepared_point_trace(&base.prepared_use_counts)?;

        Ok(Self {
            public_inputs: base.public_inputs,
            public_key_check: base.public_key_check,
            scalar_setup: base.scalar_setup,
            cert_inputs: base.cert_inputs,
            fake_glv_scalars: base.fake_glv_scalars,
            fake_glv_selectors: base.fake_glv_selectors,
            selector_requests: base.selector_requests,
            prepared_table,
            prepared_table_ec_trace,
            fake_glv_chain,
            fake_glv_ec_trace,
            projective_ec_trace,
            projective_rcb_air_trace,
            final_check: base.final_check,
            final_add: base.final_add,
            prepared_use_counts: base.prepared_use_counts,
            prepared_trace,
        })
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
    pub fake_glv_scalar_mod_muls: Vec<ScalarModMulClaim>,
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
    pub final_check: FinalCheckAirProofClaim,
    pub public_key_on_curve: PublicKeyCurveSliceProofClaim,
    pub projective_rcb_air: ProjectiveRcbAirProofClaim,
    pub final_add: FinalAddProofClaim,
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
            fake_glv_scalar_mod_muls: fake_glv_scalar_mod_mul_rows(claim)
                .expect("verified fake-GLV scalar mod-mul rows generate")
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
            final_check: FinalCheckAirProofClaim::from_claim(&claim.public_inputs),
            public_key_on_curve: PublicKeyCurveSliceProofClaim::from_claim(
                &public_key_on_curve_slice_claim(claim)
                    .expect("verified public key lies on curve"),
            ),
            projective_rcb_air: ProjectiveRcbAirProofClaim::from_trace(
                &claim.projective_rcb_air_trace,
            ),
            final_add: FinalAddProofClaim::from_claim(&claim.final_add),
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
        channel.mix_u64(self.fake_glv_scalar_mod_muls.len() as u64);
        for claim in &self.fake_glv_scalar_mod_muls {
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
        self.final_check.mix_into(channel);
        self.public_key_on_curve.mix_into(channel);
        self.projective_rcb_air.mix_into(channel);
        self.final_add.mix_into(channel);
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
        for claim in &self.fake_glv_scalar_mod_muls {
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
        append_unique_preprocessed_ids(
            &mut ids,
            self.public_key_on_curve.preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(&mut ids, self.projective_rcb_air.preprocessed_column_ids());
        append_unique_preprocessed_ids(&mut ids, self.final_add.preprocessed_column_ids());
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
    pub(crate) fake_glv_scalar_mod_muls: Vec<ScalarModMulProofSliceInteractionClaim>,
    pub prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim,
    /// Per-relation breakdown of the pinned EC-row provider's logup total
    /// (`prepared_table_projective_source.provider_claimed_sum`), used to verify
    /// the `CertBase` and `PreparedTableCanonical` balances independently.
    pub prepared_table_pinned: PreparedTableEcRowPinnedInteractionClaim,
    pub fake_glv_projective_source: FakeGlvProjectiveSourceInteractionClaim,
    pub fake_glv_chain_expansion: FakeGlvChainExpansionInteractionClaim,
    pub fake_glv_chain_continuity: FakeGlvChainContinuityInteractionClaim,
    pub fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandInteractionClaim,
    pub fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandInteractionClaim,
    pub fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandInteractionClaim,
    pub fake_glv_prepared_point_source: FakeGlvPreparedPointSourceInteractionClaim,
    pub prepared_point_range7: RangeCheckInteractionClaim,
    pub final_check: FinalCheckAirInteractionClaim,
    pub ecdsa_result_provider_claimed_sum: SecureField,
    pub public_key_on_curve: PublicKeyCurveSliceInteractionClaim,
    pub projective_rcb_air: ProjectiveRcbAirProofInteractionClaim,
    pub final_add: FinalAddInteractionClaim,
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
            fake_glv_scalar_mod_muls: Vec::new(),
            prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim::zero(),
            prepared_table_pinned: PreparedTableEcRowPinnedInteractionClaim::zero(),
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
            final_check: FinalCheckAirInteractionClaim::zero(),
            ecdsa_result_provider_claimed_sum: zero(),
            public_key_on_curve: PublicKeyCurveSliceInteractionClaim::zero_claim(),
            projective_rcb_air: ProjectiveRcbAirProofInteractionClaim::zero(),
            final_add: FinalAddInteractionClaim::zero(),
        }
    }

    fn zero_for_claim(claim: &P256CurrentAirProofClaim) -> Self {
        let mut zero = Self::zero();
        zero.scalar_setup_mod_muls = (0..claim.scalar_setup_mod_muls.len())
            .map(|_| zero_interaction_claim())
            .collect();
        zero.fake_glv_scalar_mod_muls = (0..claim.fake_glv_scalar_mod_muls.len())
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
        channel.mix_u64(self.fake_glv_scalar_mod_muls.len() as u64);
        for claim in &self.fake_glv_scalar_mod_muls {
            claim.scalar_mod_mul.mix_into(channel);
            claim.range13.mix_into(channel);
            claim.signed_carry.mix_into(channel);
        }
        self.prepared_table_projective_source.mix_into(channel);
        channel.mix_felts(&[
            self.prepared_table_pinned.prepared_table_provider_claimed_sum,
            self.prepared_table_pinned.cert_base_consumer_claimed_sum,
            self.prepared_table_pinned.canonical_claimed_sum,
        ]);
        self.fake_glv_projective_source.mix_into(channel);
        self.fake_glv_chain_expansion.mix_into(channel);
        self.fake_glv_chain_continuity.mix_into(channel);
        self.fake_glv_direct_prepared_operand.mix_into(channel);
        self.fake_glv_signed_selector_operand.mix_into(channel);
        self.fake_glv_lsb_correction_operand.mix_into(channel);
        self.fake_glv_prepared_point_source.mix_into(channel);
        self.prepared_point_range7.mix_into(channel);
        self.final_check.mix_into(channel);
        channel.mix_felts(&[self.ecdsa_result_provider_claimed_sum]);
        self.public_key_on_curve.mix_into_monolithic(channel);
        self.projective_rcb_air.mix_into(channel);
        self.final_add.mix_into(channel);
    }

    /// Single source of truth for every monolithic relation balance, as
    /// `(name, claimed_sum)` pairs. A sound proof has every sum equal to zero.
    /// Both [`Self::verify_balanced`] and [`Self::relation_audit`] derive from
    /// this list, so a new relation must be added here exactly once.
    ///
    /// Notes on the non-1:1 entries:
    /// - `PreparedTablePinned{Consistency,Breakdown}` bind the pinned EC-row
    ///   provider's committed logup total to its declared sum and per-relation
    ///   breakdown (so the breakdown is anchored to the PCS-verified total).
    /// - `CertBase` / `PreparedTableCanonical` enforce the full table pinning.
    /// - `EcdsaResult` / `PublicKeyPoint` / `FinalCheckHint` / `FinalAddOutput`
    ///   are the boundary-crossing relations that link sub-graphs (see
    ///   [`Self::liveness_witnesses`]).
    fn relation_balances(&self) -> Vec<(&'static str, SecureField)> {
        let scalar_setup_mod_mul_total = self
            .scalar_setup_mod_muls
            .iter()
            .map(ScalarModMulProofSliceInteractionClaim::claimed_sum)
            .sum::<SecureField>()
            + self.scalar_setup.scalar_limb_consumer_claimed_sum;
        let fake_glv_scalar_mod_mul_total = self
            .fake_glv_scalar_mod_muls
            .iter()
            .map(ScalarModMulProofSliceInteractionClaim::claimed_sum)
            .sum::<SecureField>()
            + self.fake_glv_scalar_air.scalar_mod_mul_provider_claimed_sum;
        let pinned = &self.prepared_table_pinned;
        vec![
            ("PublicEcdsaInstance", self.public_inputs.total()),
            (
                "ScalarSetupOutput",
                self.scalar_setup.output_provider_claimed_sum
                    + self.cert_scalar_inputs.scalar_setup_consumer_claimed_sum,
            ),
            (
                "CertScalarInput",
                self.cert_scalar_inputs.cert_provider_claimed_sum
                    + self.fake_glv_scalar_air.cert_consumer_claimed_sum,
            ),
            (
                "FakeGlvScalar",
                self.fake_glv_scalar_air.scalar_provider_claimed_sum
                    + self.fake_glv_selector_air.scalar_consumer_claimed_sum,
            ),
            (
                "ScalarSetupRange13",
                self.scalar_setup.range13_consumer_claimed_sum
                    + self.scalar_setup.range13_provider.claimed_sum
                    + self.final_check.range13_consumer_claimed_sum,
            ),
            (
                "ScalarSetupRange9",
                self.scalar_setup.range9_consumer_claimed_sum
                    + self.scalar_setup.range9_provider.claimed_sum
                    + self.final_check.range9_consumer_claimed_sum,
            ),
            (
                "ScalarSetupSignedCarry",
                self.scalar_setup.signed_carry_consumer_claimed_sum
                    + self.scalar_setup.signed_carry_provider.claimed_sum
                    + self.final_check.signed_carry_consumer_claimed_sum,
            ),
            ("ScalarSetupModMul", scalar_setup_mod_mul_total),
            ("FakeGlvScalarModMul", fake_glv_scalar_mod_mul_total),
            (
                "PreparedTablePinnedConsistency",
                pinned.total_claimed_sum
                    - self.prepared_table_projective_source.provider_claimed_sum,
            ),
            (
                "PreparedTablePinnedBreakdown",
                pinned.total_claimed_sum
                    - pinned.prepared_table_provider_claimed_sum
                    - pinned.cert_base_consumer_claimed_sum
                    - pinned.canonical_claimed_sum
                    - pinned.final_check_hint_claimed_sum,
            ),
            (
                "PreparedTableProjectiveSource",
                pinned.prepared_table_provider_claimed_sum
                    + self.prepared_table_projective_source.consumer_claimed_sum,
            ),
            (
                "CertBase",
                pinned.cert_base_consumer_claimed_sum
                    + self.cert_scalar_inputs.cert_base_provider_claimed_sum,
            ),
            ("PreparedTableCanonical", pinned.canonical_claimed_sum),
            (
                "FakeGlvProjectiveSource",
                self.fake_glv_projective_source.total(),
            ),
            ("FakeGlvChainExpansion", self.fake_glv_chain_expansion.total()),
            (
                "FakeGlvChainContinuity",
                self.fake_glv_chain_continuity.claimed_sum,
            ),
            (
                "FakeGlvDirectPreparedOperand",
                self.fake_glv_direct_prepared_operand.total(),
            ),
            (
                "FakeGlvSignedSelectorOperand",
                self.fake_glv_signed_selector_operand.total(),
            ),
            (
                "FakeGlvLsbCorrectionOperand",
                self.fake_glv_lsb_correction_operand.total(),
            ),
            (
                "FakeGlvPreparedPointSource",
                self.fake_glv_prepared_point_source.total(),
            ),
            (
                "Range7",
                self.prepared_point_range7.claimed_sum
                    + self.fake_glv_prepared_point_source.range7_consumer_claimed_sum,
            ),
            (
                "EcdsaResult",
                self.ecdsa_result_provider_claimed_sum
                    + self.final_check.result_consumer_claimed_sum,
            ),
            (
                "PublicKeyPoint",
                self.public_key_on_curve.total() + self.scalar_setup.point_provider_claimed_sum,
            ),
            ("ProjectiveRcbAirProofSlice", self.projective_rcb_air.total()),
            (
                "FinalCheckHint",
                self.prepared_table_pinned.final_check_hint_claimed_sum
                    + self.final_add.hint_consumer_claimed_sum,
            ),
            ("FinalAddInternal", self.final_add.internal_total()),
            (
                "FinalAddOutput",
                self.final_add.output_provider_claimed_sum
                    + self.final_check.final_add_output_consumer_claimed_sum,
            ),
        ]
    }

    /// Per-relation provider/consumer activity witnesses for the boundary
    /// relations that link otherwise-independent sub-graphs. For an active
    /// proof each entry must be NONZERO — a zero means the link emitted nothing
    /// (the sub-graphs are unconnected), which a balance check alone cannot see
    /// because `0 + 0 == 0` is "balanced". Names mirror [`Self::relation_balances`].
    #[cfg(test)]
    fn liveness_witnesses(&self) -> Vec<(&'static str, SecureField)> {
        vec![
            ("EcdsaResult", self.final_check.result_consumer_claimed_sum),
            ("PublicKeyPoint", self.scalar_setup.point_provider_claimed_sum),
            (
                "CertBase",
                self.cert_scalar_inputs.cert_base_provider_claimed_sum,
            ),
            (
                "FinalCheckHint",
                self.prepared_table_pinned.final_check_hint_claimed_sum,
            ),
            (
                "FinalAddOutput",
                self.final_add.output_provider_claimed_sum,
            ),
        ]
    }

    /// Consolidated relation audit: every monolithic relation balance, plus the
    /// liveness witnesses, in one structure that reports ALL problems at once.
    /// A diagnostic/regression tool — the runtime `verify_balanced` path returns
    /// the first imbalance directly.
    #[cfg(test)]
    pub(crate) fn relation_audit(&self) -> P256CurrentAirRelationAudit {
        P256CurrentAirRelationAudit {
            balances: self.relation_balances(),
            liveness: self.liveness_witnesses(),
        }
    }

    fn verify_balanced(&self) -> Result<(), P256ProofError> {
        match self
            .relation_balances()
            .into_iter()
            .find(|(_, sum)| *sum != zero())
        {
            None => Ok(()),
            Some((relation, _)) => Err(P256ProofError::RelationImbalance { relation }),
        }
    }
}

/// Consolidated view of every monolithic relation balance plus the liveness
/// witnesses for the boundary relations. A sound, fully-linked proof has
/// `is_balanced()` true and `dead_links()` empty.
///
/// Unlike the first-imbalance error returned by `verify_balanced`, this reports
/// ALL problems together — the relation-use accounting lesson borrowed from
/// stwo-cairo. `dead_links` additionally catches the "internally consistent but
/// not linked" case a pure balance check misses (`0 + 0 == 0` is "balanced").
///
/// Diagnostic/regression tool (`#[cfg(test)]`); the runtime `verify_balanced`
/// returns the first imbalance directly from `relation_balances`.
#[cfg(test)]
pub(crate) struct P256CurrentAirRelationAudit {
    balances: Vec<(&'static str, SecureField)>,
    liveness: Vec<(&'static str, SecureField)>,
}

#[cfg(test)]
impl P256CurrentAirRelationAudit {
    /// Names of all relations whose claimed sum is nonzero (unbalanced).
    pub(crate) fn imbalanced(&self) -> Vec<&'static str> {
        self.balances
            .iter()
            .filter(|(_, sum)| *sum != zero())
            .map(|(name, _)| *name)
            .collect()
    }

    /// First unbalanced relation in declaration order (matches the historical
    /// `verify_balanced` error), if any.
    pub(crate) fn first_imbalance(&self) -> Option<&'static str> {
        self.balances
            .iter()
            .find(|(_, sum)| *sum != zero())
            .map(|(name, _)| *name)
    }

    pub(crate) fn is_balanced(&self) -> bool {
        self.balances.iter().all(|(_, sum)| *sum == zero())
    }

    /// All relation names covered by the audit (the completeness surface).
    pub(crate) fn relation_names(&self) -> Vec<&'static str> {
        self.balances.iter().map(|(name, _)| *name).collect()
    }

    /// Boundary relations that emitted nothing (`sum == 0`). For an active proof
    /// each indicates an unlinked sub-graph; empty for a healthy active proof.
    pub(crate) fn dead_links(&self) -> Vec<&'static str> {
        self.liveness
            .iter()
            .filter(|(_, sum)| *sum == zero())
            .map(|(name, _)| *name)
            .collect()
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
    /// Binds prepared-table P-cells to `cert.base` (full table pinning).
    cert_base: CertBaseRelation,
    /// Ties prepared-table `P3/R/R3/±R/±R3/2P/2R` operands to canonical per-cert
    /// values (full table pinning).
    prepared_table_canonical: PreparedTableCanonicalRelation,
    fake_glv_projective_source: FakeGlvPrimitiveEcRowRelation,
    fake_glv_chain_expansion: FakeGlvChainPrimitiveExpansionRelation,
    fake_glv_chain_continuity: FakeGlvChainAccumulatorRelation,
    direct_prepared_operand: PreparedPointRelation,
    signed_selector_operand: FakeGlvSignedSelectorOperandRelation,
    lsb_correction_operand: FakeGlvLsbCorrectionOperandRelation,
    prepared_point_source: PreparedPointRelation,
    range7: RangeCheckRelation,
    ecdsa_result: EcdsaResultRelation,
    /// Forwards the pinned signed hint `R_i` from the prepared table to the
    /// final-add sub-graph (provider: prepared-table `DoubleR` row; consumer:
    /// `FinalAddCheckEval`).
    final_check_hint: FinalCheckHintRelation,
    /// Public-key sub-graph relations. Its `point` field is the shared
    /// `(sig_id, pub_x, pub_y)` binding relation, also held by
    /// `scalar_setup.public_key_point` (the provider).
    public_key_on_curve: PublicKeyCurveSliceRelations,
    projective_rcb_air: ProjectiveRcbMulComponentRelations,
    /// Final EC-addition sub-graph relations (mul engine + result + output).
    /// `hint` is the same `final_check_hint` relation as above.
    final_add: FinalAddRelations,
}

impl P256CurrentAirRelations {
    fn dummy() -> Self {
        let public_inputs = PublicEcdsaInstanceRelation::dummy();
        let scalar_setup_output = ScalarSetupOutputRelation::dummy();
        let cert_scalar_input = CertScalarInputRelation::dummy();
        let fake_glv_scalar = FakeGlvScalarRelation::dummy();
        let scalar_mod_mul = ScalarModMulLookupRelations::dummy();
        let public_key_point = PublicKeyPointRelation::dummy();
        let scalar_setup = ScalarSetupAirRelations {
            public_inputs: public_inputs.clone(),
            output: scalar_setup_output.clone(),
            scalar_mod_mul: scalar_mod_mul.clone(),
            range13: RangeCheckRelation::dummy(),
            range9: RangeCheckRelation::dummy(),
            signed_carry: RangeCheckRelation::dummy(),
            public_key_point: public_key_point.clone(),
        };
        Self {
            public_inputs,
            scalar_setup_output,
            cert_scalar_input,
            fake_glv_scalar,
            scalar_mod_mul,
            scalar_setup,
            prepared_table: PreparedTableEcRowRelation::dummy(),
            cert_base: CertBaseRelation::dummy(),
            prepared_table_canonical: PreparedTableCanonicalRelation::dummy(),
            fake_glv_projective_source: FakeGlvPrimitiveEcRowRelation::dummy(),
            fake_glv_chain_expansion: FakeGlvChainPrimitiveExpansionRelation::dummy(),
            fake_glv_chain_continuity: FakeGlvChainAccumulatorRelation::dummy(),
            direct_prepared_operand: PreparedPointRelation::dummy(),
            signed_selector_operand: FakeGlvSignedSelectorOperandRelation::dummy(),
            lsb_correction_operand: FakeGlvLsbCorrectionOperandRelation::dummy(),
            prepared_point_source: PreparedPointRelation::dummy(),
            range7: RangeCheckRelation::dummy(),
            ecdsa_result: EcdsaResultRelation::dummy(),
            final_check_hint: FinalCheckHintRelation::dummy(),
            public_key_on_curve: PublicKeyCurveSliceRelations::dummy_with_point(public_key_point),
            projective_rcb_air: ProjectiveRcbMulComponentRelations::dummy(),
            final_add: FinalAddRelations {
                mul: ProjectiveRcbMulComponentRelations::dummy(),
                result: FinalAddMulResultRelation::dummy(),
                hint: FinalCheckHintRelation::dummy(),
                output: FinalAddOutputRelation::dummy(),
            },
        }
    }

    fn draw(channel: &mut impl Channel) -> Self {
        let public_inputs = PublicEcdsaInstanceRelation::draw(channel);
        let scalar_setup_output = ScalarSetupOutputRelation::draw(channel);
        let cert_scalar_input = CertScalarInputRelation::draw(channel);
        let fake_glv_scalar = FakeGlvScalarRelation::draw(channel);
        let scalar_mod_mul = ScalarModMulLookupRelations::draw(channel);
        let public_key_point = PublicKeyPointRelation::draw(channel);
        let scalar_setup = ScalarSetupAirRelations {
            public_inputs: public_inputs.clone(),
            output: scalar_setup_output.clone(),
            scalar_mod_mul: scalar_mod_mul.clone(),
            range13: RangeCheckRelation::draw(channel),
            range9: RangeCheckRelation::draw(channel),
            signed_carry: RangeCheckRelation::draw(channel),
            public_key_point: public_key_point.clone(),
        };
        let final_check_hint = FinalCheckHintRelation::draw(channel);
        Self {
            public_inputs,
            scalar_setup_output,
            cert_scalar_input,
            fake_glv_scalar,
            scalar_mod_mul,
            scalar_setup,
            prepared_table: PreparedTableEcRowRelation::draw(channel),
            cert_base: CertBaseRelation::draw(channel),
            prepared_table_canonical: PreparedTableCanonicalRelation::draw(channel),
            fake_glv_projective_source: FakeGlvPrimitiveEcRowRelation::draw(channel),
            fake_glv_chain_expansion: FakeGlvChainPrimitiveExpansionRelation::draw(channel),
            fake_glv_chain_continuity: FakeGlvChainAccumulatorRelation::draw(channel),
            direct_prepared_operand: PreparedPointRelation::draw(channel),
            signed_selector_operand: FakeGlvSignedSelectorOperandRelation::draw(channel),
            lsb_correction_operand: FakeGlvLsbCorrectionOperandRelation::draw(channel),
            prepared_point_source: PreparedPointRelation::draw(channel),
            range7: RangeCheckRelation::draw(channel),
            ecdsa_result: EcdsaResultRelation::draw(channel),
            final_check_hint: final_check_hint.clone(),
            public_key_on_curve: PublicKeyCurveSliceRelations::draw_with_point(
                channel,
                public_key_point,
            ),
            projective_rcb_air: ProjectiveRcbMulComponentRelations::draw(channel),
            final_add: FinalAddRelations {
                mul: ProjectiveRcbMulComponentRelations::draw(channel),
                result: FinalAddMulResultRelation::draw(channel),
                // Shared with the prepared-table provider above.
                hint: final_check_hint,
                output: FinalAddOutputRelation::draw(channel),
            },
        }
    }
}

struct P256CurrentAirComponents {
    scalar_setup: ScalarSetupAirComponents,
    cert_scalar_inputs: CertScalarInputAirComponents,
    fake_glv_scalar_air: FakeGlvScalarAirComponents,
    fake_glv_selector_air: FakeGlvSelectorAirComponents,
    scalar_setup_mod_muls: Vec<ScalarModMulComponents>,
    fake_glv_scalar_mod_muls: Vec<ScalarModMulComponents>,
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
    final_check: FinalCheckAirComponents,
    public_key_on_curve: PublicKeyCurveSliceComponents,
    projective_rcb_air: ProjectiveRcbAirComponents,
    final_add: FinalAddComponents,
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
                Some(&relations.cert_base),
            ),
            fake_glv_scalar_air: FakeGlvScalarAirComponents::new(
                allocator,
                claim.fake_glv_scalar_air,
                &interaction_claim.fake_glv_scalar_air,
                &relations.cert_scalar_input,
                &relations.fake_glv_scalar,
                &relations.scalar_mod_mul.scalar_limb,
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
            fake_glv_scalar_mod_muls: claim
                .fake_glv_scalar_mod_muls
                .iter()
                .zip(&interaction_claim.fake_glv_scalar_mod_muls)
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
            prepared_table_projective_source: PreparedTableProjectiveSourceComponents::new_pinned(
                allocator,
                claim.prepared_table_projective_source.log_size,
                interaction_claim
                    .prepared_table_projective_source
                    .provider_claimed_sum,
                interaction_claim
                    .prepared_table_projective_source
                    .consumer_claimed_sum,
                &relations.prepared_table,
                &PreparedTablePinningRelations {
                    cert_base: relations.cert_base.clone(),
                    canonical: relations.prepared_table_canonical.clone(),
                    final_check_hint: Some(relations.final_check_hint.clone()),
                },
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
            final_check: FinalCheckAirComponents::new(
                allocator,
                claim.final_check,
                &interaction_claim.final_check,
                FinalCheckAirRelations {
                    result: &relations.ecdsa_result,
                    range13: &relations.scalar_setup.range13,
                    range9: &relations.scalar_setup.range9,
                    signed_carry: &relations.scalar_setup.signed_carry,
                    final_add_output: &relations.final_add.output,
                },
            ),
            public_key_on_curve: PublicKeyCurveSliceComponents::new(
                allocator,
                claim.public_key_on_curve.log_sizes(),
                &interaction_claim.public_key_on_curve,
                &relations.public_key_on_curve,
                true,
            ),
            projective_rcb_air: ProjectiveRcbAirComponents::new_with_log_sizes(
                allocator,
                claim.projective_rcb_air.log_sizes,
                &interaction_claim.projective_rcb_air,
                &relations.projective_rcb_air,
            ),
            final_add: FinalAddComponents::new(
                allocator,
                claim.final_add.log_sizes(),
                &interaction_claim.final_add,
                &relations.final_add,
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
        for fake_glv_scalar_mod_mul in &self.fake_glv_scalar_mod_muls {
            components.push(&fake_glv_scalar_mod_mul.canonical as &dyn Component);
            components.push(&fake_glv_scalar_mod_mul.ab_chunks as &dyn Component);
            components.push(&fake_glv_scalar_mod_mul.qn_chunks as &dyn Component);
            components.push(&fake_glv_scalar_mod_mul.accumulators as &dyn Component);
            components.push(&fake_glv_scalar_mod_mul.reduction_digits as &dyn Component);
            components.push(&fake_glv_scalar_mod_mul.range13 as &dyn Component);
            components.push(&fake_glv_scalar_mod_mul.signed_carry as &dyn Component);
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
        components.extend(self.final_check.components());
        components.extend(self.public_key_on_curve.components());
        components.extend(self.projective_rcb_air.components());
        components.extend(self.final_add.components());
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
        for fake_glv_scalar_mod_mul in &self.fake_glv_scalar_mod_muls {
            components
                .push(&fake_glv_scalar_mod_mul.canonical as &dyn ComponentProver<SimdBackend>);
            components
                .push(&fake_glv_scalar_mod_mul.ab_chunks as &dyn ComponentProver<SimdBackend>);
            components
                .push(&fake_glv_scalar_mod_mul.qn_chunks as &dyn ComponentProver<SimdBackend>);
            components
                .push(&fake_glv_scalar_mod_mul.accumulators as &dyn ComponentProver<SimdBackend>);
            components.push(
                &fake_glv_scalar_mod_mul.reduction_digits as &dyn ComponentProver<SimdBackend>,
            );
            components
                .push(&fake_glv_scalar_mod_mul.range13 as &dyn ComponentProver<SimdBackend>);
            components
                .push(&fake_glv_scalar_mod_mul.signed_carry as &dyn ComponentProver<SimdBackend>);
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
        components.extend(self.final_check.component_provers());
        components.extend(self.public_key_on_curve.component_provers());
        components.extend(self.projective_rcb_air.component_provers());
        components.extend(self.final_add.component_provers());
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

    /// Production builder: Garaga-style fake-GLV decomposition for any
    /// scalar in `[0, n)`. See
    /// [`P256ProofClaim::from_inputs_with_arbitrary_fake_glv_hints`] for
    /// the AIR-readiness caveat.
    pub fn from_inputs_with_arbitrary_fake_glv_hints(
        inputs: Vec<EcdsaVerifyInput>,
    ) -> Result<Self, P256ProofError> {
        let claim = P256ProofClaim::from_inputs_with_arbitrary_fake_glv_hints(&inputs)?;
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
        let fake_glv_scalar_rows = fake_glv_scalar_mod_mul_rows(&self.claim)?;
        for (rows, local_claim) in fake_glv_scalar_rows
            .iter()
            .zip(&claim.fake_glv_scalar_mod_muls)
        {
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

        let public_key_slice_claim = public_key_on_curve_slice_claim(&self.claim)?;
        let local_ids = claim.public_key_on_curve.preprocessed_column_ids();
        let local_columns =
            gen_public_key_on_curve_preprocessed_trace(&public_key_slice_claim, &local_ids)?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        let local_ids = claim.projective_rcb_air.preprocessed_column_ids();
        let local_columns = self
            .claim
            .projective_rcb_air_trace
            .gen_proof_slice_preprocessed_trace(&local_ids)?;
        append_unique_preprocessed_columns(&mut ids, &mut columns, local_ids, local_columns);

        // Final EC-addition sub-graph preprocessed columns (FINAL_ADD-namespaced
        // schedule + shared range13 / signed-carry value+active columns).
        let final_add_pairs = final_add_preprocessed_columns(&self.claim.final_add)?;
        let (local_ids, local_columns): (Vec<_>, Vec<_>) = final_add_pairs.into_iter().unzip();
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
        // Generate final_check first so its range checks join the shared
        // scalar_setup providers' multiplicities.
        let final_check =
            gen_final_check_air_base_trace(&self.claim.final_check, claim.final_check);
        // Public-key-on-curve sub-graph base trace (self-contained range13 /
        // signed-carry providers; binds `(x, y)` to the public key).
        let public_key_slice_claim = public_key_on_curve_slice_claim(&self.claim)?;
        let public_key_on_curve = gen_public_key_on_curve_base_trace(&public_key_slice_claim)?;
        let scalar_setup_lookup_providers = gen_scalar_setup_air_lookup_provider_base_trace(
            &scalar_setup,
            crate::final_check_air::final_check_range13_uses_from_base(&final_check),
            crate::final_check_air::final_check_range9_uses_from_base(&final_check),
            crate::final_check_air::final_check_signed_carry_uses_from_base(&final_check),
        );
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
        let fake_glv_scalar_rows = fake_glv_scalar_mod_mul_rows(&self.claim)?;
        let fake_glv_scalar_mod_muls = fake_glv_scalar_rows
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
        let final_add =
            gen_final_add_base_trace(&self.claim.final_add, claim.final_add.log_sizes())?;

        let mut columns = Vec::new();
        columns.extend(scalar_setup.clone());
        columns.extend(scalar_setup_lookup_providers.clone());
        columns.extend(cert_scalar_inputs.clone());
        columns.extend(fake_glv_scalar_air.clone());
        columns.extend(fake_glv_selector_air.clone());
        for scalar_setup_mod_mul in &scalar_setup_mod_muls {
            columns.extend(scalar_setup_mod_mul.clone());
        }
        for fake_glv_scalar_mod_mul in &fake_glv_scalar_mod_muls {
            columns.extend(fake_glv_scalar_mod_mul.clone());
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
        columns.extend(final_check.clone());
        columns.extend(public_key_on_curve.clone());
        columns.extend(projective_rcb_air.clone());
        columns.extend(final_add);

        Ok(P256CurrentAirBaseTrace {
            columns,
            scalar_setup,
            cert_scalar_inputs,
            fake_glv_scalar_air,
            fake_glv_selector_air,
            scalar_setup_mod_muls,
            fake_glv_scalar_mod_muls,
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
            final_check,
            public_key_slice_claim,
        })
    }

    fn gen_current_air_interaction_trace(
        &self,
        base: &P256CurrentAirBaseTrace,
        relations: &P256CurrentAirRelations,
    ) -> Result<(ColumnVec<M31ColumnEval>, P256CurrentAirInteractionClaim), P256ProofError> {
        let (scalar_setup_interaction, scalar_setup_claim) = gen_scalar_setup_air_interaction_trace(
            &base.scalar_setup,
            &relations.scalar_setup,
            crate::final_check_air::final_check_range13_uses_from_base(&base.final_check),
            crate::final_check_air::final_check_range9_uses_from_base(&base.final_check),
            crate::final_check_air::final_check_signed_carry_uses_from_base(&base.final_check),
        );
        let (cert_scalar_input_interaction, cert_scalar_input_claim) =
            gen_cert_scalar_input_air_interaction_trace(
                &base.cert_scalar_inputs,
                &relations.scalar_setup_output,
                &relations.cert_scalar_input,
                Some(&relations.cert_base),
            );
        let (fake_glv_scalar_interaction, fake_glv_scalar_claim) =
            gen_fake_glv_scalar_air_interaction_trace(
                &base.fake_glv_scalar_air,
                &relations.cert_scalar_input,
                &relations.fake_glv_scalar,
                &relations.scalar_mod_mul.scalar_limb,
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
        let fake_glv_scalar_rows = fake_glv_scalar_mod_mul_rows(&self.claim)?;
        let fake_glv_scalar_claims = fake_glv_scalar_rows
            .iter()
            .map(ScalarModMulClaim::from_rows_with_external_limb_links)
            .collect::<Vec<_>>();
        debug_assert_eq!(
            base.fake_glv_scalar_mod_muls.len(),
            fake_glv_scalar_rows.len()
        );
        let mut fake_glv_scalar_interactions = Vec::with_capacity(fake_glv_scalar_rows.len());
        let mut fake_glv_scalar_interaction_claims =
            Vec::with_capacity(fake_glv_scalar_rows.len());
        for (rows, claim) in fake_glv_scalar_rows.iter().zip(&fake_glv_scalar_claims) {
            let (interaction, interaction_claim) = gen_scalar_mod_mul_interaction_trace(
                rows,
                claim,
                &scalar_lookup_claims,
                &relations.scalar_mod_mul,
            );
            fake_glv_scalar_interactions.push(interaction);
            fake_glv_scalar_interaction_claims.push(interaction_claim);
        }
        let (prepared_provider_interaction, prepared_pinned_claim) =
            gen_prepared_table_ec_row_pinned_interaction_trace(
                &base.prepared_table_provider,
                &relations.prepared_table,
                &relations.cert_base,
                &relations.prepared_table_canonical,
                Some(&relations.final_check_hint),
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
        let (final_check_interaction, final_check_claim) = gen_final_check_air_interaction_trace(
            &base.final_check,
            FinalCheckAirRelations {
                result: &relations.ecdsa_result,
                range13: &relations.scalar_setup.range13,
                range9: &relations.scalar_setup.range9,
                signed_carry: &relations.scalar_setup.signed_carry,
                final_add_output: &relations.final_add.output,
            },
        );
        let ecdsa_result_provider_claimed_sum = ecdsa_result_provider_claimed_sum(
            &self.claim.public_inputs.instances,
            &relations.ecdsa_result,
        );
        let (public_key_on_curve_interaction, public_key_on_curve_claim) =
            gen_public_key_on_curve_interaction_trace(
                &base.public_key_slice_claim,
                &relations.public_key_on_curve,
                true,
            )?;
        let (projective_interaction, projective_claim) = self
            .claim
            .projective_rcb_air_trace
            .gen_proof_slice_interaction_trace(&relations.projective_rcb_air)?;
        let (final_add_interaction, final_add_claim) = gen_final_add_interaction_trace(
            &self.claim.final_add,
            &relations.final_add,
            FinalAddProofClaim::from_claim(&self.claim.final_add).log_sizes(),
        )?;

        let mut columns = Vec::new();
        columns.extend(scalar_setup_interaction);
        columns.extend(cert_scalar_input_interaction);
        columns.extend(fake_glv_scalar_interaction);
        columns.extend(fake_glv_selector_interaction);
        for interaction in scalar_setup_interactions {
            columns.extend(interaction);
        }
        for interaction in fake_glv_scalar_interactions {
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
        columns.extend(final_check_interaction);
        columns.extend(public_key_on_curve_interaction);
        columns.extend(projective_interaction);
        columns.extend(final_add_interaction);

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
                fake_glv_scalar_mod_muls: fake_glv_scalar_interaction_claims,
                prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim {
                    provider_claimed_sum: prepared_pinned_claim.total_claimed_sum,
                    consumer_claimed_sum: prepared_consumer_claim.claimed_sum,
                },
                prepared_table_pinned: prepared_pinned_claim,
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
                final_check: final_check_claim,
                ecdsa_result_provider_claimed_sum,
                public_key_on_curve: public_key_on_curve_claim,
                projective_rcb_air: projective_claim,
                final_add: final_add_claim,
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
    fake_glv_scalar_mod_muls: Vec<ColumnVec<M31ColumnEval>>,
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
    final_check: ColumnVec<M31ColumnEval>,
    public_key_slice_claim: PublicKeyCurveSliceClaim,
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

/// Per-certificate `ScalarModMul` trace rows for the fake-GLV scalar equation
/// `k · s2_abs ≡ ±s1 (mod n)`. One row per active certificate (inactive
/// `cert_active == 0` certs contribute no mod-mul row). Mul IDs live in a
/// disjoint range from [`scalar_setup_mod_mul_rows`] (`FAKE_GLV_SCALAR_MUL_ID_BASE`
/// + `2 · sig_id + cert_id`) so the two families never collide in any logup.
///
/// Active half of the Task 4 wiring: the matching AIR-side provider yields
/// (per-(role, limb) `ScalarLimbRelation` tuples gated on `cert_active`) live
/// in `crate::scalar::fake_glv_scalar::FakeGlvScalarAirEval::evaluate`, with
/// the trace-gen provider sum mirrored in
/// `gen_fake_glv_scalar_air_interaction_trace`. Together they close the
/// `FakeGlvScalarModMul` balance entry in
/// `P256CurrentAirInteractionClaim::relation_balances`.
fn fake_glv_scalar_mod_mul_rows(
    claim: &P256ProofClaim,
) -> Result<Vec<ScalarModMulTraceRows>, P256ProofError> {
    use stwo_p256_utils::scalar_arithmetic::{ScalarFieldMulTrace, P256_ORDER};

    let mut rows = Vec::new();
    for fake_glv_row in &claim.fake_glv_scalars.rows {
        if fake_glv_row.cert_active.0 == 0 {
            continue;
        }
        let scalar_u64s = fake_glv_row.scalar.to_u256().to_le_u64s();
        let s2_abs_u64s = fake_glv_small_to_le_u64s(&fake_glv_row.hint.s2_abs);
        let trace = ScalarFieldMulTrace::new(
            "fake_glv_scalar_equation",
            &scalar_u64s,
            &s2_abs_u64s,
            &P256_ORDER,
        )
        .map_err(ScalarModMulTraceError::from)?;
        let mul_id = FAKE_GLV_SCALAR_MUL_ID_BASE
            + 2 * fake_glv_row.sig_id.0
            + fake_glv_row.cert_id.0;
        rows.push(ScalarModMulTraceRows::new(mul_id, &trace)?);
    }
    Ok(rows)
}

/// Base mul-id for the fake-GLV scalar `ScalarModMul` family. Disjoint from
/// the `scalar_setup_mod_mul_rows` range (`0..2·num_sigs`) by a large margin
/// so the two row sets remain distinguishable in lookups.
const FAKE_GLV_SCALAR_MUL_ID_BASE: u32 = 1_000_000;

/// Build the single-public-key on-curve witness for the monolithic current-AIR
/// from the already-verified `public_key_check` claim. The monolithic proof
/// covers exactly one signature, so `from_public_key_claim` requires one row.
fn public_key_on_curve_slice_claim(
    claim: &P256ProofClaim,
) -> Result<PublicKeyCurveSliceClaim, P256ProofError> {
    PublicKeyCurveSliceClaim::from_public_key_claim(&claim.public_key_check)
        .map_err(P256ProofError::from)
}

/// Build the final-add claim `S = R_1 + R_2` from the (single-signature)
/// `FinalEcdsaCheckClaim`. `R_i = signed_hint_point(h_i, s2_sign_bit_i)`:
/// `R_i = -h_i` when `s2_sign_bit == 1` (Garaga negative), `R_i = +h_i` when
/// `s2_sign_bit == 0` (Garaga positive); for the inactive (zero-`u1`)
/// branch `h_i = ∞`, so `R_i = ∞`. Both sign choices are accepted because
/// `x(R_1 + R_2) = x(±(h_1 + h_2))` when both signs agree, which the AIR
/// witness builder enforces upstream (via the per-cert `s2_sign_bit`
/// consistency in `FakeGlvScalarHint::decompose`).
fn final_add_claim_from_final_check(
    final_check: &FinalEcdsaCheckClaim,
    fake_glv_scalars: &FakeGlvScalarHintClaim,
) -> Result<FinalAddClaim, P256ProofError> {
    let row = final_check
        .rows
        .first()
        .ok_or(P256ProofError::FinalAdd(FinalAddError::MulTraceShape))?;
    // Match the two cert hints to the row's sig_id (each cert keyed by
    // (sig_id, cert_id) with cert_id ∈ {0, 1}).
    let bit_for = |cert_id: u32| -> M31 {
        for fake_glv_row in &fake_glv_scalars.rows {
            if fake_glv_row.sig_id == row.sig_id
                && fake_glv_row.cert_id.0 == cert_id
                && fake_glv_row.cert_active.0 == 1
            {
                return fake_glv_row.hint.s2_sign_bit;
            }
        }
        // Inactive cert (zero-`u1` branch): sign is irrelevant because
        // `h_i = ∞`; conventionally treat as `bit = 1`.
        M31::from_u32_unchecked(1)
    };
    let (r1, r1_inf) = signed_prepared(&row.h1, bit_for(0));
    let (r2, r2_inf) = signed_prepared(&row.h2, bit_for(1));
    FinalAddClaim::from_hints(row.sig_id, &r1, r1_inf, &r2, r2_inf).map_err(P256ProofError::FinalAdd)
}

/// `R = signed_hint_point(h, bit)`: returns `h` when `bit == 0` and `-h`
/// when `bit == 1`, matching `signed_hint_point` in
/// [`crate::scalar::prepared_table`]. For an infinity hint both branches
/// collapse to the infinity flag.
fn signed_prepared(
    point: &crate::prepared_table::PreparedAffinePoint,
    s2_sign_bit: M31,
) -> (crate::types::AffinePoint, bool) {
    if s2_sign_bit.0 == 0 {
        return identity_prepared(point);
    }
    negate_prepared(point)
}

fn identity_prepared(
    point: &crate::prepared_table::PreparedAffinePoint,
) -> (crate::types::AffinePoint, bool) {
    use crate::types::{AffinePoint, U256};
    match point.to_option() {
        Some(p) => (AffinePoint { x: p.x, y: p.y }, false),
        None => (AffinePoint { x: U256::ZERO, y: U256::ZERO }, true),
    }
}

/// `(-point, is_infinity)`: `(x, p - y)` for a finite point, or a dummy point
/// flagged infinity.
fn negate_prepared(
    point: &crate::prepared_table::PreparedAffinePoint,
) -> (crate::types::AffinePoint, bool) {
    use crate::types::{AffinePoint, U256};
    match point.to_option() {
        Some(p) => {
            let modulus = U256::from_le_u64s(&crate::constants::P256_MODULUS);
            let neg_y = crate::field_ops::sub_mod_witness(&modulus, &p.y, &modulus)
                .result
                .to_u256();
            (AffinePoint { x: p.x, y: neg_y }, false)
        }
        None => (AffinePoint { x: U256::ZERO, y: U256::ZERO }, true),
    }
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
        status: P256ProofComponentStatus::Implemented,
        note: "The monolithic current AIR proves y^2 + 3x = x^3 + b (mod p) for the public key via four projective-RCB mod-p muls plus a signed-carry curve-identity check, and binds the curve-checked (x, y) to the public input through PublicKeyPointRelation (provided by scalar setup, consumed by the curve check).",
    },
    P256ProofComponentSlot {
        name: "SolinasReductionTraceRows",
        status: P256ProofComponentStatus::Implemented,
        note: "The public-key-on-curve muls prove their Solinas raw-product / matrix-fold / reduction sub-traces in-AIR through the shared projective-RCB raw_product_chunk / folded_contribution / folded_digit families (public-key-namespaced schedule columns).",
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
        note: "Fake-GLV scalar rows are proven for arbitrary nonzero certificate scalars by bounding s1/s2_abs/q to 128 bits, witnessing the sign-selected `selected_s1` (= s1 if s2_sign_bit == 1, else n − s1) with a borrow chain, and linking `scalar · s2_abs ≡ selected_s1 (mod n)` through per-cert ScalarModMul rows that consume external limb tuples (mul_id, role, limb_index, limb_value) yielded by the fake-GLV AIR. Closes the Garaga-style identity in-AIR.",
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
        status: P256ProofComponentStatus::Implemented,
        note: "Full table pinning is enforced in the monolithic STARK: cert_bind yields CertBaseRelation (base = G for cert_id=0, Q for cert_id=1) and the prepared-table EC-row provider consumes it on every P-cell, while PreparedTableCanonicalRelation ties P3=3P (cert0 to constant 3G), R, R3=3R, -R, -R3, 2P, 2R to a single canonical value per (sig,cert,role) with an in-AIR field negation. With output = lhs + rhs already proven, base[] is forced to {P,3P}±{R,3R} for P = cert.base.",
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
        status: P256ProofComponentStatus::Implemented,
        note: "r_x is now bound IN-AIR to x(u1·G + u2·Q). The prepared table forwards the canonically-pinned signed hint R_i (role-R) on FinalCheckHintRelation; the final-add sub-graph (final_add_air.rs) consumes R_1, R_2 and proves S = R_1 + R_2 in affine coordinates via the shared projective-RCB mod-p mul engine. The distinct-x branch uses (lambda·dx ≡ dy, lambda² ≡ x3 + x1 + x2, dx·dx_inv ≡ 1) and the finite-doubling branch (Task 6) uses (lambda·(2·y1) ≡ 3·x1² − 3, lambda² ≡ x3 + 2·x1); branch selectors gate the constraints so the active branch is exactly one of {distinct, double, r1_only, r2_only, inverse}, with `inverse_add` (R_final = ∞) rejected by `active · inverse_add = 0`. Since R_i = -h_i for active certs (s2_sign_bit conventions: bit=1 ⇒ s2_signed = -s2_abs), x(R_1 + R_2) = x(u1·G + u2·Q). x3 = S.x is forwarded on FinalAddOutputRelation and consumed by the final check as r_x; r_check = r_x mod n and EcdsaResultRelation then complete x(u1·G + u2·Q) mod n = r.",
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
    FinalAdd(FinalAddError),
    SelectorLookup(SelectorLookupError),
    PreparedPoint(PreparedPointError),
    PreparedTable(PreparedTableError),
    ProjectiveEc(ProjectiveEcError),
    ProjectiveRcbAir(ProjectiveRcbAirError),
    PublicKeyOnCurve(PublicKeyOnCurveError),
    PublicKeyCurveSlice(PublicKeyCurveSliceError),
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

impl From<FinalAddError> for P256ProofError {
    fn from(value: FinalAddError) -> Self {
        Self::FinalAdd(value)
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

impl From<PublicKeyCurveSliceError> for P256ProofError {
    fn from(value: PublicKeyCurveSliceError) -> Self {
        Self::PublicKeyCurveSlice(value)
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
    use crate::constants::{P256_GX, P256_GY, P256_MODULUS, P256_ORDER};
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
        prove_fake_glv_projective_source_proof_slice, FakeGlvProjectiveSourceProofClaim,
    };
    use crate::fake_glv_lsb_correction_operand::{
        prove_fake_glv_lsb_correction_operand_proof_slice,
        verify_fake_glv_lsb_correction_operand_proof_slice, FakeGlvLsbCorrectionOperandProofClaim,
    };
    use crate::fake_glv_prepared_point_source::{
        prove_fake_glv_prepared_point_source_proof_slice, FakeGlvPreparedPointSourceProofClaim,
    };
    use crate::fake_glv_selector_lookup::SelectorLookupProviderProofClaim;
    use crate::fake_glv_signed_selector_operand::{
        prove_fake_glv_signed_selector_operand_proof_slice,
        verify_fake_glv_signed_selector_operand_proof_slice,
        FakeGlvSignedSelectorOperandProofClaim,
    };
    use crate::field_ops::mul_mod_witness;
    use crate::fp_solinas_air::FP_SOLINAS_REDUCTION_DIGITS;
    use crate::limbs::P256M31BigInt;
    use crate::fake_glv_chain::FakeGlvChainCert;
    use crate::prepared_table::{
        PreparedAffinePoint, PreparedTableCert, PreparedTableEcRowProofClaim,
        PreparedTableProjectiveSourceProofClaim,
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

    /// Like `valid_real_input_with_small_u_scalars`, but builds a real ECDSA
    /// statement for arbitrary full-width `u1`, `u2 ∈ [1, n)`. This stresses
    /// the fake-GLV scalar AIR with scalars that do not fit a trivial hint.
    fn valid_real_input_with_u_scalars(u1: U256, u2: U256) -> EcdsaVerifyInput {
        assert_ne!(u2, U256::ZERO, "u2 must be nonzero for ECDSA setup");
        let n = U256::from_le_u64s(&P256_ORDER);
        let public_key = generator_point();
        let u_sum = add_mod_u256(&u1, &u2, &n);
        let r_point = scalar_mul(&u_sum, &public_key).expect("nonzero R");
        let r = x_mod_order(&r_point.x);
        let u2_inv = mod_inverse(&u2, &n);
        let s = mul_mod_witness(&r, &u2_inv, &n).result.to_u256();
        let message_hash = mul_mod_witness(&u1, &s, &n).result.to_u256();

        EcdsaVerifyInput {
            message_hash,
            signature: Signature { r, s },
            public_key,
        }
    }

    /// Returns `n - delta` as a full-width 256-bit scalar — convenient for
    /// generating arbitrary scalars that live in the upper end of `[0, n)`
    /// and therefore cannot satisfy the trivial fake-GLV hint.
    fn scalar_near_order(delta: u64) -> U256 {
        let n = U256::from_le_u64s(&P256_ORDER);
        sub_mod_u256(&n, &U256::from_le_u64s(&[delta, 0, 0, 0]), &n)
    }

    fn add_mod_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
        crate::field_ops::add_mod_witness(a, b, modulus).result.to_u256()
    }

    fn sub_mod_u256(a: &U256, b: &U256, modulus: &U256) -> U256 {
        crate::field_ops::sub_mod_witness(a, b, modulus).result.to_u256()
    }

    /// Deterministic real-world ECDSA fixture from the `p256` crate. Signs
    /// a known message with a fixed signing key, runs the result through
    /// SHA-256 for the message hash, and returns an `EcdsaVerifyInput`
    /// laid out for the monolithic AIR. This exercises the production
    /// arbitrary-fake-GLV path with a signature that wasn't constructed
    /// to fit the trivial hint.
    fn p256_crate_signed_input() -> EcdsaVerifyInput {
        use ::ecdsa::signature::Signer;
        use p256::ecdsa::{Signature as P256Signature, SigningKey};
        use sha2::{Digest, Sha256};

        let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
        let verifying_key = signing_key.verifying_key();
        let message = b"stwo-p256 arbitrary signature air fixture";
        let digest = Sha256::digest(message);
        let signature: P256Signature = signing_key.sign(message);
        let encoded = verifying_key.to_encoded_point(false);

        let r_bytes: [u8; 32] = signature.r().to_bytes().into();
        let s_bytes: [u8; 32] = signature.s().to_bytes().into();
        let x_bytes: [u8; 32] = encoded.x().expect("x").as_slice().try_into().expect("x len");
        let y_bytes: [u8; 32] = encoded.y().expect("y").as_slice().try_into().expect("y len");

        EcdsaVerifyInput {
            message_hash: U256(digest.into()),
            signature: Signature {
                r: U256(r_bytes),
                s: U256(s_bytes),
            },
            public_key: AffinePoint {
                x: U256(x_bytes),
                y: U256(y_bytes),
            },
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

    /// RED TEST (Task 1, Step 2): expected to fail until `Task 5` adds the
    /// `from_inputs_with_arbitrary_fake_glv_hints` builder backed by the
    /// Garaga-style decomposer (Task 2) and the general AIR (Tasks 3–4).
    ///
    /// Today this fails with either:
    ///   - a missing-method compile error on `from_inputs_with_arbitrary_fake_glv_hints`,
    ///     or once the method exists,
    ///   - `FakeGlvScalarHintError::ScalarDoesNotFitTrivialHint`, because
    ///     `scalar_near_order(123)` is full-width and the trivial hint
    ///     forces `s1 = scalar < 2^128`.
    #[test]
    fn arbitrary_full_width_u_scalars_build_a_current_air_claim() {
        let input = valid_real_input_with_u_scalars(scalar_near_order(123), scalar_near_order(456));
        assert!(
            ecdsa_verify(&input),
            "synthetic arbitrary-width input must be valid",
        );

        P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
            .expect("arbitrary full-width valid signature should build a proof draft");
    }

    /// Task 7 end-to-end: prove + verify a real `p256`-crate signature.
    /// Marked `#[ignore]` while the `fake_glv_selector` AIR still hard-codes
    /// `s2_abs = 1` and `s2_sign_bit = 1` (see
    /// `constrain_selector_from_trivial_scalar`: the constraints forcing
    /// `scalar[S2_START] = cert_active`, `s2_lsb = 1`, `s2_msb = 0`,
    /// `sign = cert_active` reject every non-trivial decomposition).
    /// Promoting the selector AIR to a general arbitrary-`s2_abs` /
    /// arbitrary-sign reconstruction is a follow-up ("Task 3 for the
    /// selector AIR"); once that lands the fixture should verify
    /// end-to-end via the production arbitrary-fake-GLV path.
    #[test]
    #[ignore = "fake_glv_selector AIR still has trivial-only s2/sign constraints"]
    fn current_p256_monolithic_proves_real_p256_crate_signature() {
        let input = p256_crate_signed_input();
        assert!(ecdsa_verify(&input), "native verifier must accept the fixture");
        let proof = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![input])
            .expect("real p256-crate signature builds a proof draft")
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("real p256-crate signature proof generates");
        verify_current_air_monolithic::<Blake2sMerkleChannel>(proof)
            .expect("real p256-crate signature proof verifies");
    }

    /// Task 6 end-to-end: force `u1 == u2` so `R_1 = R_2` and the
    /// FinalAdd AIR's finite-doubling branch is exercised inside the
    /// monolithic proof.
    #[test]
    fn current_p256_monolithic_proves_arbitrary_doubling_final_add() {
        let input = valid_real_input_with_small_u_scalars(99, 99);
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![input])
            .expect("u1 == u2 doubling draft builds")
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("u1 == u2 doubling proof generates");
        verify_current_air_monolithic::<Blake2sMerkleChannel>(proof)
            .expect("u1 == u2 doubling proof verifies");
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

        // Phase 2's prepared-table base pinning now catches a wrong cert base at
        // the interaction-balance check: cert_bind yields the mutated base on
        // CertBaseRelation while the prepared-table provider still consumes the
        // bound G/Q, so the relation no longer balances (a stronger, earlier
        // rejection than the previous PCS-layer ConstraintsNotSatisfied).
        assert!(
            matches!(err, P256ProofError::RelationImbalance { relation: "CertBase" }),
            "expected CertBase imbalance, got {err:?}"
        );
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
    fn current_p256_monolithic_verifier_rejects_unbalanced_ecdsa_result_sum() {
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
            .ecdsa_result_provider_claimed_sum += SecureField::one();

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("EcdsaResult balance must reject mutated provider sum");

        assert!(matches!(
            err,
            P256ProofError::RelationImbalance {
                relation: "EcdsaResult"
            }
        ));
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

    /// In-AIR public-key-on-curve binding: the monolithic STARK proves the
    /// public key lies on the curve via a dedicated curve-check component whose
    /// witnessed `(x, y)` is LogUp-bound to the public input through
    /// `PublicKeyPointRelation` (provided by scalar_setup, consumed by the
    /// curve-check). Mutating the public-input `pub_y` after the draft is built
    /// makes the scalar_setup provider emit a `pub_y'` that no longer matches
    /// the curve-check's witnessed `y`, so the regenerated prover-side
    /// `PublicKeyPoint` balance is non-zero and proving is rejected. Per
    /// lessons.md #18 the rejection oracle is the relation-balance audit
    /// (`RelationImbalance`), not `assert_constraints`.
    #[test]
    fn current_p256_proof_pipeline_rejects_public_key_off_curve_in_air() {
        let mut proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("current pipeline builds");

        // Swap the curve-check witness to a *different* valid on-curve public
        // key (2*G) while leaving scalar_setup and the public input bound to the
        // real key (G). Everything else still balances; only the
        // `PublicKeyPoint` binding tuple drifts: the curve check now consumes
        // (sig_id, 2G_x, 2G_y) while scalar_setup provides (sig_id, G_x, G_y).
        // This is exactly the soundness property the binding enforces - the
        // curve-checked point must equal the public key - and it is caught by
        // the relation-balance audit (lessons.md #18), not assert_constraints.
        let two_g = scalar_mul(&scalar(2), &generator_point()).expect("2*G is finite");
        let other_inputs = PublicEcdsaInputClaim::from_inputs(&[EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(77),
                s: scalar(11),
            },
            public_key: two_g,
        }]);
        proof.claim.public_key_check =
            PublicKeyOnCurveClaim::from_public_inputs(&other_inputs).expect("2*G is on curve");

        let err = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect_err("curve-check (x,y) unbound from public key must reject in the AIR");

        assert_eq!(
            err,
            P256ProofError::RelationImbalance {
                relation: "PublicKeyPoint"
            }
        );
    }

    /// The verifier independently enforces the `PublicKeyPoint` binding balance:
    /// tampering with the scalar_setup provider's claimed sum on a fully valid
    /// monolithic proof is rejected by `verify_current_air_monolithic`.
    #[test]
    fn current_p256_monolithic_verifier_rejects_unbalanced_public_key_point_sum() {
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
            .scalar_setup
            .point_provider_claimed_sum += SecureField::one();

        let err = verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect_err("PublicKeyPoint balance must reject a mutated provider sum");

        assert!(matches!(
            err,
            P256ProofError::RelationImbalance {
                relation: "PublicKeyPoint"
            }
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

    /// Full monolithic prove/verify on the DISTINCT-finite-points branch
    /// `(u1, u2) = (7, 11)` (both `h1, h2` finite, `x1 != x2`). This exercises
    /// the final-add chord-addition identities with `both_finite = 1` through
    /// the full PCS/OODS composition (the primary gate uses the zero-`u1`
    /// branch where `both_finite = 0`), confirming the witnessed
    /// `dx_inv_result` LogUp tuple matches off-domain.
    #[test]
    fn current_p256_proof_pipeline_proves_and_verifies_monolithic_distinct_branch() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            valid_real_input_with_small_u_scalars(7, 11),
        ])
        .expect("distinct branch pipeline builds");
        proof.verify_current_e2e().expect("distinct branch verifies");

        let monolithic = proof
            .prove_current_air_monolithic::<Blake2sMerkleChannel>()
            .expect("distinct branch monolithic proof proves");

        verify_current_air_monolithic::<Blake2sMerkleChannel>(monolithic)
            .expect("distinct branch monolithic proof verifies");
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
    #[ignore = "diagnostic: pinpoints the trivial-only selector AIR constraint #243 \
        that rejects arbitrary s2_abs / sign (see \
        `current_p256_monolithic_proves_real_p256_crate_signature` note)"]
    fn current_p256_air_constraint_diagnostic_real_p256() {
        let proof = P256ProofDraft::from_inputs_with_arbitrary_fake_glv_hints(vec![
            p256_crate_signed_input(),
        ])
        .expect("real p256 pipeline builds");
        proof.verify_current_e2e().expect("real p256 e2e verifies");

        assert_current_air_constraints(&proof);
    }

    /// EXPERIMENT (Phase A — feasibility probe): for ONE active cert, rebuild
    /// the prepared table and fake-GLV chain from a WRONG hint point
    /// `R' != ±u·base` (a valid curve point) while keeping `u`, the public
    /// input and the selectors (= digits of `u`) UNCHANGED. Report whether the
    /// chain's internal `final_acc == r3` gate holds for the wrong `R'`. If it
    /// FAILS, no globally consistent wrong-`R` chain exists (the windowed
    /// accumulation itself binds `R`). If it HOLDS, the accumulation does not
    /// bind `R` and the full prove/verify experiment is worth running.
    #[test]
    fn wrong_r_chain_feasibility_probe() {
        let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
        let claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
            .expect("valid claim builds");

        for cert_index in 0..claim.cert_inputs.rows.len() {
            let cert = &claim.cert_inputs.rows[cert_index];
            if cert.cert_active.0 == 0 {
                eprintln!("cert {cert_index}: inactive, skipping");
                continue;
            }
            let fake_glv = &claim.fake_glv_scalars.rows[cert_index];
            let selector = &claim.fake_glv_selectors.rows[cert_index];

            // Sanity: reconstruct the TRUE R the production pipeline used.
            let base = AffinePoint {
                x: cert.base_x.to_u256(),
                y: cert.base_y.to_u256(),
            };
            let u = cert.scalar.to_u256();
            let h = scalar_mul(&u, &base).expect("u*base finite");
            let true_r = match fake_glv.hint.s2_sign_bit.0 {
                0 => h.clone(),
                1 => negate_affine(&h),
                _ => panic!("bad sign bit"),
            };

            // Pick a WRONG R' that is a valid curve point but != ±u·base:
            // R' = (u+1)*base.
            let u_plus_1 = add_u256(&u, &U256::from_le_u64s(&[1, 0, 0, 0]));
            let wrong_r = scalar_mul(&u_plus_1, &base).expect("(u+1)*base finite");
            assert_ne!(wrong_r, true_r, "R' must differ from the true R");
            assert_ne!(wrong_r, negate_affine(&true_r), "R' must differ from -R");

            // Rebuild table + chain from R' using the production algorithm.
            let wrong_table =
                PreparedTableCert::new_with_r_override(cert, fake_glv, selector, wrong_r.clone())
                    .expect("override table builds");
            let wrong_chain = FakeGlvChainCert::from_claims_with_r_override(
                cert,
                selector,
                &wrong_table,
                wrong_r.clone(),
            )
            .expect("override chain builds");

            let gate_holds = wrong_chain.final_acc == wrong_chain.r3;
            let verify_result = wrong_chain.verify();
            eprintln!(
                "cert {cert_index} (cert_id={}): WRONG-R final_acc==r3 gate holds = {gate_holds}; chain.verify() = {:?}",
                cert.cert_id.0, verify_result
            );

            // Cross-check: the SAME rebuild with the TRUE R must satisfy the gate.
            let true_table =
                PreparedTableCert::new_with_r_override(cert, fake_glv, selector, true_r.clone())
                    .expect("true override table builds");
            let true_chain = FakeGlvChainCert::from_claims_with_r_override(
                cert,
                selector,
                &true_table,
                true_r.clone(),
            )
            .expect("true override chain builds");
            assert_eq!(
                true_chain.final_acc, true_chain.r3,
                "sanity: the TRUE R rebuild must satisfy final_acc==r3 (override harness fidelity)"
            );
            assert!(
                true_chain.verify().is_ok(),
                "sanity: TRUE R chain verifies"
            );
        }
    }

    fn true_r_for_cert(claim: &P256ProofClaim, cert_index: usize) -> AffinePoint {
        let cert = &claim.cert_inputs.rows[cert_index];
        let fake_glv = &claim.fake_glv_scalars.rows[cert_index];
        let base = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let h = scalar_mul(&cert.scalar.to_u256(), &base).expect("u*base finite");
        match fake_glv.hint.s2_sign_bit.0 {
            0 => h,
            1 => negate_affine(&h),
            _ => panic!("bad sign bit"),
        }
    }

    /// FIDELITY CONTROL for the wrong-R AIR oracle: drive the *same* override
    /// build path with the TRUE `R`. If `assert_current_air_constraints`
    /// passes cleanly here, the override harness is faithful and the Phase C
    /// constraint violation is attributable to the wrong `R'`, not to the
    /// harness.
    #[test]
    fn wrong_r_harness_fidelity_true_r_air_constraints_pass() {
        let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
        let base_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
            .expect("valid claim builds");
        let true_r = true_r_for_cert(&base_claim, 0);

        let rebuilt =
            P256ProofClaim::from_inputs_with_wrong_r_for_cert(&inputs, 0, true_r.clone())
                .expect("true-R rebuild via override path assembles");
        // The override path must reproduce the production claim exactly.
        assert_eq!(
            rebuilt.prepared_table, base_claim.prepared_table,
            "override prepared_table with TRUE R must equal production"
        );
        assert_eq!(
            rebuilt.fake_glv_chain, base_claim.fake_glv_chain,
            "override chain with TRUE R must equal production"
        );

        let relations = P256ProofRelations::dummy();
        let interaction_claim = P256ProofInteractionClaim::from_claim(&rebuilt, &relations);
        let draft = P256ProofDraft {
            inputs,
            claim: rebuilt,
            relations,
            interaction_claim,
        };
        assert_current_air_constraints(&draft);
        eprintln!("FIDELITY: TRUE-R override path passes assert_current_air_constraints cleanly.");
    }

    fn wrong_r_for_cert(claim: &P256ProofClaim, cert_index: usize) -> AffinePoint {
        let cert = &claim.cert_inputs.rows[cert_index];
        let base = AffinePoint {
            x: cert.base_x.to_u256(),
            y: cert.base_y.to_u256(),
        };
        let u = cert.scalar.to_u256();
        let u_plus_1 = add_u256(&u, &U256::from_le_u64s(&[1, 0, 0, 0]));
        scalar_mul(&u_plus_1, &base).expect("(u+1)*base finite")
    }

    /// EXPERIMENT (Phase B — full monolithic pipeline on a wrong-`R` witness).
    /// Builds a globally consistent claim whose cert-0 prepared table + chain
    /// use `R' = (u+1)*base != ±u*base`, then drives
    /// `prove_current_air_monolithic`. Reports the exact observed outcome.
    #[test]
    fn wrong_r_monolithic_prove_outcome() {
        let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
        let base_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
            .expect("valid claim builds");
        let r_prime = wrong_r_for_cert(&base_claim, 0);

        let wrong_claim =
            P256ProofClaim::from_inputs_with_wrong_r_for_cert(&inputs, 0, r_prime.clone())
                .expect("wrong-R claim assembles (no native gate in override builders)");

        // Build a draft WITHOUT verify_current_e2e (which would itself reject).
        let relations = P256ProofRelations::dummy();
        let interaction_claim = P256ProofInteractionClaim::from_claim(&wrong_claim, &relations);
        let draft = P256ProofDraft {
            inputs: inputs.clone(),
            claim: wrong_claim,
            relations,
            interaction_claim,
        };

        // (1) Does the native pre-check inside prove reject?
        match draft.prove_current_air_monolithic::<Blake2sMerkleChannel>() {
            Ok(_) => eprintln!(
                "PHASE B: prove_current_air_monolithic SUCCEEDED on wrong-R witness (UNEXPECTED — would indicate acceptance)"
            ),
            Err(e) => eprintln!("PHASE B: prove_current_air_monolithic REJECTED wrong-R: {e:?}"),
        }
    }

    /// EXPERIMENT (Phase C — DECISIVE AIR oracle). Runs `assert_constraints`
    /// directly on the wrong-`R` trace, bypassing every native shape check.
    /// A clean return == AIR ACCEPTS (soundness gap). A panic/abort == AIR
    /// REJECTS (sound). This isolates whether the monolithic AIR *constraints*
    /// bind `R` to `u*base`, independent of native validation.
    #[test]
    #[ignore = "decisive manual wrong-R AIR oracle: assert_current_air_constraints \
                panics (clean single polynomial-constraint panic at \
                fake_glv_chain_continuity final_acc==r3) when the AIR correctly \
                rejects a wrong R (sound). Run with --ignored. Not auto-run to avoid \
                the lessons.md #18 double-panic/SIGABRT risk in the shared suite."]
    fn wrong_r_air_constraints_oracle() {
        let inputs = vec![valid_real_input_with_small_u_scalars(7, 11)];
        let base_claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&inputs)
            .expect("valid claim builds");
        let r_prime = wrong_r_for_cert(&base_claim, 0);

        let wrong_claim =
            P256ProofClaim::from_inputs_with_wrong_r_for_cert(&inputs, 0, r_prime.clone())
                .expect("wrong-R claim assembles");
        let relations = P256ProofRelations::dummy();
        let interaction_claim = P256ProofInteractionClaim::from_claim(&wrong_claim, &relations);
        let draft = P256ProofDraft {
            inputs,
            claim: wrong_claim,
            relations,
            interaction_claim,
        };

        eprintln!(
            "PHASE C: running assert_current_air_constraints on wrong-R trace; \
             a clean PASS == AIR accepts (gap), a panic/abort == AIR rejects (sound)."
        );
        assert_current_air_constraints(&draft);
        eprintln!(
            "PHASE C: assert_current_air_constraints RETURNED CLEANLY on wrong-R trace \
             => AIR ACCEPTED the wrong R (soundness gap confirmed)."
        );
    }

    fn negate_affine(p: &AffinePoint) -> AffinePoint {
        let m = U256::from_le_u64s(&P256_MODULUS);
        AffinePoint {
            x: p.x.clone(),
            y: crate::field_ops::sub_mod_witness(&m, &p.y, &m).result.to_u256(),
        }
    }

    fn add_u256(a: &U256, b: &U256) -> U256 {
        let a = a.to_le_u64s();
        let b = b.to_le_u64s();
        let mut out = [0u64; 4];
        let mut carry = 0u128;
        for i in 0..4 {
            let sum = a[i] as u128 + b[i] as u128 + carry;
            out[i] = sum as u64;
            carry = sum >> 64;
        }
        U256::from_le_u64s(&out)
    }

    /// Re-run the monolithic interaction-trace generation for `draft` and return
    /// the resulting interaction claim, with relations drawn from the real
    /// transcript. The per-relation LogUp balance it carries is the in-AIR
    /// rejection oracle (lessons.md #18); a tampered witness that unbalances any
    /// relation is caught by `verify_balanced` (first imbalance) or surfaced in
    /// full by `relation_audit`.
    fn monolithic_interaction_claim(draft: &P256ProofDraft) -> P256CurrentAirInteractionClaim {
        let proof_claim = P256CurrentAirProofClaim::from_claim(&draft.claim);
        let ids = proof_claim.preprocessed_column_ids();
        let max_bound = proof_claim.max_constraint_log_degree_bound(&ids);
        let config = p256_stark_monolithic_profile_config(max_bound);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(config.lifting_log_size.unwrap_or(
                max_bound + config.fri_config.log_blowup_factor,
            ))
            .circle_domain()
            .half_coset,
        );
        let mut channel = <Blake2sMerkleChannel as MerkleChannel>::C::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);
        let preprocessed = draft
            .gen_current_air_preprocessed_trace(&proof_claim, &ids)
            .expect("preprocessed trace");
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.commit(&mut channel);
        proof_claim.mix_into(&mut channel);
        let mut base = draft.gen_current_air_base_trace(&proof_claim).expect("base trace");
        let base_columns = std::mem::take(&mut base.columns);
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base_columns);
        tree_builder.commit(&mut channel);
        let relations = P256CurrentAirRelations::draw(&mut channel);
        let (_, interaction_claim) = draft
            .gen_current_air_interaction_trace(&base, &relations)
            .expect("interaction trace");
        interaction_claim
    }

    /// The per-relation balance result for `draft` (the first-imbalance oracle
    /// the adversarial tests assert on).
    fn monolithic_balance_outcome(draft: &P256ProofDraft) -> Result<(), P256ProofError> {
        monolithic_interaction_claim(draft).verify_balanced()
    }

    #[test]
    fn relation_audit_lists_all_imbalances_and_dead_links() {
        let nonzero = SecureField::from(M31::from_u32_unchecked(1));
        let audit = P256CurrentAirRelationAudit {
            balances: vec![
                ("Alpha", zero()),
                ("Beta", nonzero),
                ("Gamma", zero()),
                ("Delta", nonzero),
            ],
            liveness: vec![("LiveOk", nonzero), ("DeadLink", zero())],
        };
        // Reports ALL imbalances at once, not just the first.
        assert_eq!(audit.imbalanced(), vec!["Beta", "Delta"]);
        assert_eq!(audit.first_imbalance(), Some("Beta"));
        assert!(!audit.is_balanced());
        // A boundary relation that emitted nothing is flagged even though it
        // "balances" (0 + 0 == 0) — the unlinked-sub-graph case.
        assert_eq!(audit.dead_links(), vec!["DeadLink"]);
        assert_eq!(audit.relation_names(), vec!["Alpha", "Beta", "Gamma", "Delta"]);

        let healthy = P256CurrentAirRelationAudit {
            balances: vec![("A", zero())],
            liveness: vec![("L", nonzero)],
        };
        assert!(healthy.is_balanced());
        assert!(healthy.imbalanced().is_empty());
        assert!(healthy.dead_links().is_empty());
    }

    #[test]
    fn monolithic_relation_audit_is_balanced_and_fully_linked() {
        // Both certs active (u1, u2 != 0), so every boundary relation must be live.
        let draft = valid_draft_for_balance(7, 11);
        let audit = monolithic_interaction_claim(&draft).relation_audit();
        assert!(
            audit.is_balanced(),
            "honest proof has unbalanced relations: {:?}",
            audit.imbalanced()
        );
        assert!(
            audit.dead_links().is_empty(),
            "honest active proof has unlinked boundary relations: {:?}",
            audit.dead_links()
        );
        // The audit covers the full relation surface, including the four
        // verifier-facing ECDSA bindings.
        let names = audit.relation_names();
        assert_eq!(names.len(), 27, "relation audit must cover every relation");
        for required in [
            "EcdsaResult",
            "PublicKeyPoint",
            "FinalCheckHint",
            "FinalAddOutput",
            "CertBase",
        ] {
            assert!(names.contains(&required), "audit missing relation: {required}");
        }
    }

    /// Build a valid single-signature draft for the in-AIR adversarial tests.
    fn valid_draft_for_balance(u1: u64, u2: u64) -> P256ProofDraft {
        let relations = P256ProofRelations::dummy();
        let claim = P256ProofClaim::from_inputs_with_trivial_fake_glv_hints(&[
            valid_real_input_with_small_u_scalars(u1, u2),
        ])
        .expect("valid claim");
        let interaction_claim = P256ProofInteractionClaim::from_claim(&claim, &relations);
        P256ProofDraft {
            inputs: vec![valid_real_input_with_small_u_scalars(u1, u2)],
            claim,
            relations,
            interaction_claim,
        }
    }

    fn bump_limb0(value: &crate::limbs::P256M31BigInt) -> crate::limbs::P256M31BigInt {
        let mut limbs = *value.limbs();
        limbs[0] = limbs[0] + M31::from_u32_unchecked(1);
        crate::limbs::P256M31BigInt::from_limbs(limbs)
    }

    /// IN-AIR oracle: mutating the proven final-add output `x3` (= `R_final.x`)
    /// away from the value the final check consumes as `r_x` unbalances the
    /// `FinalAddOutput` relation, so `verify_balanced` rejects.
    #[test]
    fn monolithic_rejects_mutated_final_add_x3() {
        let mut draft = valid_draft_for_balance(7, 11);
        monolithic_balance_outcome(&draft).expect("honest draft balances");
        draft.claim.final_add.x3 = bump_limb0(&draft.claim.final_add.x3);
        let err = monolithic_balance_outcome(&draft).expect_err("mutated x3 must reject");
        assert!(
            matches!(err, P256ProofError::RelationImbalance { relation: "FinalAddOutput" }),
            "expected FinalAddOutput imbalance, got {err:?}"
        );
    }

    /// IN-AIR oracle: mutating a consumed hint point `R_1` unbalances the
    /// `FinalCheckHint` relation (the prepared table still yields the true,
    /// pinned `R_1`), so `verify_balanced` rejects.
    #[test]
    fn monolithic_rejects_mutated_consumed_hint() {
        let mut draft = valid_draft_for_balance(7, 11);
        monolithic_balance_outcome(&draft).expect("honest draft balances");
        let new_x = bump_limb0(&draft.claim.final_add.r1.x);
        draft.claim.final_add.r1.x = new_x;
        let err = monolithic_balance_outcome(&draft).expect_err("mutated R_1 must reject");
        assert!(
            matches!(err, P256ProofError::RelationImbalance { relation: "FinalCheckHint" }),
            "expected FinalCheckHint imbalance, got {err:?}"
        );
    }

    /// IN-AIR oracle: mutating the public signature `r` unbalances the public
    /// relations binding `r`. The public `r` is provided on BOTH
    /// `PublicEcdsaInstance` (the full instance tuple) and `EcdsaResult` (the
    /// write-back the final check consumes as `r_check = r_x mod n`). Either
    /// imbalance proves the public `r` is bound to the proven computation;
    /// `verify_balanced` reports whichever it checks first.
    #[test]
    fn monolithic_rejects_mutated_public_r() {
        let mut draft = valid_draft_for_balance(7, 11);
        monolithic_balance_outcome(&draft).expect("honest draft balances");
        draft.claim.public_inputs.instances[0].r =
            bump_limb0(&draft.claim.public_inputs.instances[0].r);
        let err = monolithic_balance_outcome(&draft).expect_err("mutated public r must reject");
        assert!(
            matches!(
                err,
                P256ProofError::RelationImbalance {
                    relation: "EcdsaResult" | "PublicEcdsaInstance"
                }
            ),
            "expected EcdsaResult/PublicEcdsaInstance imbalance, got {err:?}"
        );
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
                &crate::scalar::scalar_mod_mul::relation::ScalarLimbRelation::dummy(),
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
        let scalar_limb_relation =
            crate::scalar::scalar_mod_mul::relation::ScalarLimbRelation::dummy();
        let (interaction, interaction_claim) = gen_fake_glv_scalar_air_interaction_trace(
            &base,
            &cert_relation,
            &scalar_relation,
            &scalar_limb_relation,
        );
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
            &scalar_limb_relation,
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
            "fake_glv_final_check",
            &components.final_check.check,
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
        assert!(implemented.contains(&"PublicKeyOnCurve"));
        assert!(implemented.contains(&"SolinasReductionTraceRows"));
        assert!(!pending.contains(&"PublicKeyOnCurve"));
        assert!(!pending.contains(&"SolinasReductionTraceRows"));
        assert!(implemented.contains(&"ScalarSetup"));
        assert!(implemented.contains(&"CertScalarInput"));
        assert!(implemented.contains(&"FakeGlvSelector"));
        assert!(implemented.contains(&"PreparedPointUseCounts"));
        assert!(implemented.contains(&"PreparedTablePoints"));
        assert!(!pending.contains(&"PreparedTablePoints"));
        assert!(implemented.contains(&"PreparedTableEcTrace"));
        assert!(implemented.contains(&"PreparedTableEcRows"));
        assert!(implemented.contains(&"FakeGlvChainTrace"));
        assert!(implemented.contains(&"FakeGlvPrimitiveEcTrace"));
        assert!(implemented.contains(&"FakeGlvEcChainRows"));
        assert!(implemented.contains(&"ProjectiveRcbEcTrace"));
        assert!(implemented.contains(&"ProjectiveRcbAirRows"));
        // FinalEcdsaCheck is now AIR-proven: `r_x` is bound in-AIR to
        // x(u1·G + u2·Q) via the FinalCheckHint forward + final-add sub-graph.
        assert!(implemented.contains(&"FinalEcdsaCheck"));
        assert!(!pending.contains(&"FinalEcdsaCheck"));
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
