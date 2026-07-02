use serde::{Deserialize, Serialize};
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

use crate::components::final_add::final_add_gamma_max_padded_values;
use crate::components::gamma_digest::{GammaChallenge, GammaDigestRelation};
use crate::components::public_key_curve::air::pkc_gamma_max_padded_values;
use crate::components::hinted_mul::air::{
    gen_hinted_mul_slice_preprocessed_trace, hinted_mul_signed_table_claim, HintedMulChallenge,
    HintedMulProofClaim, HintedMulProofInteractionClaim, HintedMulSliceClaimedSums,
    HintedMulSliceComponents,
};
use crate::components::hinted_mul::trace::{
    gen_hinted_mul_base_trace, gen_hinted_mul_interaction_trace, gen_hinted_mul_schedule_columns,
    hinted_mul_gamma_instances, hinted_mul_gamma_max_padded_values, hinted_mul_range13_uses,
    hinted_mul_signed_uses, HintedMulRelations, HintedMulTraceClaim,
};
use crate::components::hinted_mul::witness::HintedMulWitnessError;
use crate::components::hinted_mul::EcOpHeaderRelation;
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
    gen_fake_glv_primitive_expansion_consumer_interaction_trace, FakeGlvChainExpansionComponents,
    FakeGlvChainExpansionInteractionClaim, FakeGlvChainExpansionProofClaim,
    FakeGlvChainPrimitiveExpansionRelation,
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
    gen_fake_glv_projective_source_consumer_interaction_trace, FakeGlvPrimitiveEcRowRelation,
    FakeGlvProjectiveSourceComponents, FakeGlvProjectiveSourceInteractionClaim,
    FakeGlvProjectiveSourceProofClaim,
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
    FinalAddOutputRelation, FinalAddProofClaim, FinalAddRelations, FinalAddSignRelation,
};
use crate::final_check::{FinalEcdsaCheckClaim, FinalEcdsaCheckError};
use crate::final_check_air::{
    ecdsa_result_provider_claimed_sum, gen_final_check_air_base_trace,
    gen_final_check_air_interaction_trace, EcdsaResultRelation, FinalCheckAirComponents,
    FinalCheckAirInteractionClaim, FinalCheckAirProofClaim, FinalCheckAirRelations,
};
use crate::prepared_point::{
    prepared_point_provider_claimed_sum, prepared_point_range7_consumer_claimed_sum,
    PreparedPointAudit, PreparedPointError, PreparedPointRelation, PreparedPointTraceClaim,
    PreparedPointUseCountClaim,
};
use crate::prepared_table::FinalCheckHintRelation;
use crate::prepared_table::{
    gen_prepared_table_ec_row_base_trace, gen_prepared_table_ec_row_pinned_interaction_trace,
    gen_prepared_table_ec_row_preprocessed_trace, gen_prepared_table_projective_source_base_trace,
    gen_prepared_table_projective_source_consumer_interaction_trace, CertBaseRelation,
    PreparedTableCanonicalRelation, PreparedTableClaim, PreparedTableEcRowPinnedInteractionClaim,
    PreparedTableEcRowRelation, PreparedTableEcTraceClaim, PreparedTableError,
    PreparedTablePinningRelations, PreparedTableProjectiveSourceComponents,
    PreparedTableProjectiveSourceInteractionClaim, PreparedTableProjectiveSourceProofClaim,
};
use crate::projective::{ProjectiveEcError, ProjectiveEcTraceClaim};
use crate::projective_air::{
    ProjectiveRcbAirError, ProjectiveRcbAirTraceClaim, ProjectiveRcbMulComponentRelations,
};
use crate::public_inputs::{
    public_ecdsa_consumer_claimed_sum, public_ecdsa_provider_claimed_sum, PublicEcdsaInputClaim,
    PublicEcdsaInstance, PublicEcdsaInstanceRelation,
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
    RangeCheckInteractionClaim, RangeCheckRelation, RANGE13_BITS, RANGE7_BITS,
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
    FakeGlvSelectorAirComponents, FakeGlvSelectorAirInteractionClaim, FakeGlvSelectorAirProofClaim,
    FakeGlvSelectorClaim, FakeGlvSelectorError,
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
    ScalarModMulClaim, ScalarModMulMergedRows, ScalarModMulTraceError, ScalarModMulTraceRows,
};
use crate::scalar::setup_air::{
    gen_scalar_setup_air_base_trace, gen_scalar_setup_air_interaction_trace,
    gen_scalar_setup_air_lookup_provider_base_trace, gen_scalar_setup_air_preprocessed_trace,
    scalar_setup_air_preprocessed_column_ids, ScalarSetupAirComponents,
    ScalarSetupAirInteractionClaim, ScalarSetupAirProofClaim, ScalarSetupAirRelations,
    ScalarSetupClaim, ScalarSetupClaimError, ScalarSetupOutputRelation,
};
use crate::types::EcdsaVerifyInput;

pub mod air;
pub mod balances;
pub use balances::*;

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
    pub hinted_mul_trace: HintedMulTraceClaim,
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
            ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&projective_ec_trace)?;
        let final_check = FinalEcdsaCheckClaim::from_claims(
            &public_inputs,
            &cert_inputs,
            &fake_glv_scalars,
            &fake_glv_chain,
        )?;
        // Final-add's four muls ride the hinted provider on source indices
        // just past the ladder ops.
        let hinted_source_offset = projective_rcb_air_trace.rows.len() as u32;
        let final_add = final_add_claim_from_final_check(
            &final_check,
            &fake_glv_scalars,
            hinted_source_offset,
        )?;
        let mut hinted_mul_trace =
            HintedMulTraceClaim::from_projective_rcb(&projective_rcb_air_trace)?;
        hinted_mul_trace.extend_from_projective_rcb(
            &final_add.mul_trace,
            final_add.hinted_source_offset,
            false,
        )?;
        // Public-key curve-check muls ride the hinted provider right after.
        let public_key_curve_slice = public_key_slice_from_check(
            &public_key_check,
            hinted_source_offset + final_add.mul_trace.rows.len() as u32,
        )?;
        hinted_mul_trace.extend_from_projective_rcb(
            &public_key_curve_slice.mul_trace,
            public_key_curve_slice.hinted_source_offset,
            false,
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
            hinted_mul_trace,
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
    /// The AIR enforces the *general* fake-GLV constraints — `k · s2_abs ≡
    /// ±s1 (mod n)` proved via `ScalarModMul` external limb links
    /// (`constrain_fake_glv_scalar_general`) — so this builder produces a
    /// witness `prove_current_air_monolithic` accepts for any signature,
    /// including full-width `u1`/`u2`. Real `p256`-crate signatures prove and
    /// verify end-to-end (`air_core_p256_proves_and_verifies_real_signature`).
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
            ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&projective_ec_trace)?;
        let mut hinted_mul_trace =
            HintedMulTraceClaim::from_projective_rcb(&projective_rcb_air_trace)?;
        hinted_mul_trace.extend_from_projective_rcb(
            &base.final_add.mul_trace,
            base.final_add.hinted_source_offset,
            false,
        )?;
        let public_key_curve_slice = public_key_slice_from_check(
            &base.public_key_check,
            projective_rcb_air_trace.rows.len() as u32 + base.final_add.mul_trace.rows.len() as u32,
        )?;
        hinted_mul_trace.extend_from_projective_rcb(
            &public_key_curve_slice.mul_trace,
            public_key_curve_slice.hinted_source_offset,
            false,
        )?;
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
            hinted_mul_trace,
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

        self.hinted_mul_trace.verify()?;
        self.final_check.verify()?;
        self.prepared_use_counts.verify()?;
        self.prepared_table
            .verify_prepared_point_trace(&self.prepared_use_counts, &self.prepared_trace)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct P256ProofDraft {
    pub inputs: Vec<EcdsaVerifyInput>,
    pub claim: P256ProofClaim,
    pub relations: P256ProofRelations,
}

#[derive(Clone, Debug)]
pub struct P256CurrentAirProof<H: MerkleHasherLifted> {
    pub claim: P256CurrentAirProofClaim,
    pub interaction_claim: P256CurrentAirInteractionClaim,
    pub stark_proof: StarkProof<H>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct P256CurrentAirProofClaim {
    pub public_inputs: PublicEcdsaInputClaim,
    pub scalar_setup: ScalarSetupAirProofClaim,
    pub cert_scalar_inputs: CertScalarInputAirProofClaim,
    pub fake_glv_scalar_air: FakeGlvScalarAirProofClaim,
    pub fake_glv_selector_air: FakeGlvSelectorAirProofClaim,
    pub scalar_mod_muls: ScalarModMulClaim,
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
    pub hinted_mul: HintedMulProofClaim,
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
            scalar_mod_muls: ScalarModMulClaim::from_rows_with_external_limb_links(
                &merged_scalar_mod_mul_rows(claim)
                    .expect("verified scalar mod-mul rows generate"),
            ),
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
                &public_key_on_curve_slice_claim(claim).expect("verified public key lies on curve"),
            ),
            hinted_mul: HintedMulProofClaim::from_trace(&claim.hinted_mul_trace),
            final_add: FinalAddProofClaim::from_claim(&claim.final_add),
        }
    }

    fn mix_into(&self, channel: &mut impl Channel) {
        self.public_inputs.mix_into(channel);
        self.scalar_setup.mix_into(channel);
        self.cert_scalar_inputs.mix_into(channel);
        self.fake_glv_scalar_air.mix_into(channel);
        self.fake_glv_selector_air.mix_into(channel);
        self.scalar_mod_muls.mix_into(channel);
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
        self.hinted_mul.mix_into(channel);
        self.final_add.mix_into(channel);
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut ids = Vec::new();
        append_unique_preprocessed_ids(&mut ids, scalar_setup_air_preprocessed_column_ids());
        let lookup_claims = LookupProviderClaims::scalar_mod_mul();
        append_unique_preprocessed_ids(
            &mut ids,
            scalar_mod_mul_preprocessed_column_ids(&self.scalar_mod_muls, &lookup_claims),
        );
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
            vec![range_check_value_column_id(
                self.prepared_point_range7.log_size,
            )],
        );
        append_unique_preprocessed_ids(
            &mut ids,
            self.public_key_on_curve.preprocessed_column_ids(),
        );
        append_unique_preprocessed_ids(&mut ids, self.hinted_mul.preprocessed_column_ids());
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct P256CurrentAirInteractionClaim {
    pub scalar_setup: ScalarSetupAirInteractionClaim,
    pub cert_scalar_inputs: CertScalarInputAirInteractionClaim,
    pub fake_glv_scalar_air: FakeGlvScalarAirInteractionClaim,
    pub fake_glv_selector_air: FakeGlvSelectorAirInteractionClaim,
    pub(crate) scalar_mod_muls: ScalarModMulProofSliceInteractionClaim,
    pub prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim,
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
    pub public_key_on_curve: PublicKeyCurveSliceInteractionClaim,
    pub hinted_mul: HintedMulProofInteractionClaim,
    pub final_add: FinalAddInteractionClaim,
}

impl P256CurrentAirInteractionClaim {
    fn zero() -> Self {
        Self {
            scalar_setup: ScalarSetupAirInteractionClaim::zero(),
            cert_scalar_inputs: CertScalarInputAirInteractionClaim::zero(),
            fake_glv_scalar_air: FakeGlvScalarAirInteractionClaim::zero(),
            fake_glv_selector_air: FakeGlvSelectorAirInteractionClaim::zero(),
            scalar_mod_muls: zero_interaction_claim(),
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
            public_key_on_curve: PublicKeyCurveSliceInteractionClaim::zero_claim(),
            hinted_mul: HintedMulProofInteractionClaim::zero(),
            final_add: FinalAddInteractionClaim::zero(),
        }
    }

    fn zero_for_claim(_claim: &P256CurrentAirProofClaim) -> Self {
        Self::zero()
    }

    fn mix_into(&self, channel: &mut impl Channel) {
        self.scalar_setup.mix_into(channel);
        self.cert_scalar_inputs.mix_into(channel);
        self.fake_glv_scalar_air.mix_into(channel);
        self.fake_glv_selector_air.mix_into(channel);
        self.scalar_mod_muls.scalar_mod_mul.mix_into(channel);
        self.scalar_mod_muls.range13.mix_into(channel);
        self.scalar_mod_muls.signed_carry.mix_into(channel);
        self.prepared_table_projective_source.mix_into(channel);
        self.fake_glv_projective_source.mix_into(channel);
        self.fake_glv_chain_expansion.mix_into(channel);
        self.fake_glv_chain_continuity.mix_into(channel);
        self.fake_glv_direct_prepared_operand.mix_into(channel);
        self.fake_glv_signed_selector_operand.mix_into(channel);
        self.fake_glv_lsb_correction_operand.mix_into(channel);
        self.fake_glv_prepared_point_source.mix_into(channel);
        self.prepared_point_range7.mix_into(channel);
        self.final_check.mix_into(channel);
        self.public_key_on_curve.mix_into_monolithic(channel);
        self.hinted_mul.mix_into(channel);
        self.final_add.mix_into(channel);
    }

    fn lookup_sum(
        &self,
        public_instances: &[PublicEcdsaInstance<M31>],
        relations: &P256CurrentAirRelations,
    ) -> SecureField {
        public_ecdsa_provider_claimed_sum(public_instances, &relations.public_inputs)
            + ecdsa_result_provider_claimed_sum(public_instances, &relations.ecdsa_result)
            + self.scalar_setup.total()
            + self.cert_scalar_inputs.claimed_sum
            + self.fake_glv_scalar_air.claimed_sum
            + self.fake_glv_selector_air.claimed_sum
            + self.scalar_mod_muls.claimed_sum()
            + self
                .prepared_table_projective_source
                .component_claimed_sum()
            + self.fake_glv_projective_source.component_claimed_sum()
            + self.fake_glv_chain_expansion.total()
            + self.fake_glv_chain_continuity.claimed_sum
            + self.fake_glv_direct_prepared_operand.total()
            + self.fake_glv_signed_selector_operand.total()
            + self.fake_glv_lsb_correction_operand.total()
            + self.fake_glv_prepared_point_source.component_claimed_sum()
            + self.prepared_point_range7.claimed_sum
            + self.final_check.claimed_sum
            + self.public_key_on_curve.total()
            + self.hinted_mul.total()
            + self.final_add.total()
    }

    /// Stwo-cairo-style aggregate interaction balance. Component claims expose
    /// their declared LogUp sums; semantic provider/consumer splits stay out of
    /// production claims and are checked by AIR constraints plus this aggregate.
    fn relation_balances(
        &self,
        public_instances: &[PublicEcdsaInstance<M31>],
        relations: &P256CurrentAirRelations,
    ) -> Vec<(&'static str, SecureField)> {
        vec![("LookupSum", self.lookup_sum(public_instances, relations))]
    }

    /// Per-relation provider/consumer activity witnesses for the boundary
    /// relations that link otherwise-independent sub-graphs. For an active
    /// proof each entry must be NONZERO — a zero means the link emitted nothing
    /// (the sub-graphs are unconnected), which a balance check alone cannot see
    /// because `0 + 0 == 0` is "balanced". Names mirror [`Self::relation_balances`].
    #[cfg(test)]
    fn liveness_witnesses(&self) -> Vec<(&'static str, SecureField)> {
        vec![
            ("ScalarSetup", self.scalar_setup.total()),
            ("CertScalarInputs", self.cert_scalar_inputs.claimed_sum),
            (
                "PreparedTablePinned",
                self.prepared_table_pinned.claimed_sum,
            ),
            (
                "PreparedTableFinalCheckHint",
                self.prepared_table_pinned.final_check_hint.claimed_sum,
            ),
            (
                "PreparedTableProjectiveSourceProvider",
                self.prepared_table_projective_source.provider.claimed_sum,
            ),
            (
                "PreparedTableProjectiveSourceConsumer",
                self.prepared_table_projective_source.consumer.claimed_sum,
            ),
            (
                "FakeGlvProjectiveSourceProvider",
                self.fake_glv_projective_source.provider.claimed_sum,
            ),
            (
                "FakeGlvProjectiveSourceConsumer",
                self.fake_glv_projective_source.consumer.claimed_sum,
            ),
            (
                "FakeGlvDirectPreparedOperandProvider",
                self.fake_glv_direct_prepared_operand.provider.claimed_sum,
            ),
            (
                "FakeGlvDirectPreparedOperandConsumer",
                self.fake_glv_direct_prepared_operand.consumer.claimed_sum,
            ),
            (
                "FakeGlvSignedSelectorOperandProvider",
                self.fake_glv_signed_selector_operand.provider.claimed_sum,
            ),
            (
                "FakeGlvSignedSelectorOperandConsumer",
                self.fake_glv_signed_selector_operand.consumer.claimed_sum,
            ),
            (
                "FakeGlvLsbCorrectionOperandProvider",
                self.fake_glv_lsb_correction_operand.provider.claimed_sum,
            ),
            (
                "FakeGlvLsbCorrectionOperandConsumer",
                self.fake_glv_lsb_correction_operand.consumer.claimed_sum,
            ),
            (
                "FakeGlvPreparedPointSourceProvider",
                self.fake_glv_prepared_point_source.provider.claimed_sum,
            ),
            (
                "FakeGlvPreparedPointSourceConsumer",
                self.fake_glv_prepared_point_source.consumer.claimed_sum,
            ),
            ("FinalCheck", self.final_check.claimed_sum),
            ("PublicKeyCurve", self.public_key_on_curve.total()),
            ("HintedMul", self.hinted_mul.total()),
            ("FinalAdd", self.final_add.total()),
        ]
    }

    /// Consolidated relation audit: every monolithic relation balance, plus the
    /// liveness witnesses, in one structure that reports ALL problems at once.
    /// A diagnostic/regression tool — the runtime `verify_balanced` path returns
    /// the first imbalance directly.
    #[cfg(test)]
    fn relation_audit(
        &self,
        public_instances: &[PublicEcdsaInstance<M31>],
        relations: &P256CurrentAirRelations,
    ) -> P256CurrentAirRelationAudit {
        P256CurrentAirRelationAudit {
            balances: self.relation_balances(public_instances, relations),
            liveness: self.liveness_witnesses(),
        }
    }

    fn verify_balanced(
        &self,
        public_instances: &[PublicEcdsaInstance<M31>],
        relations: &P256CurrentAirRelations,
    ) -> Result<(), P256ProofError> {
        match self
            .relation_balances(public_instances, relations)
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
    hinted_signed_h: RangeCheckRelation,
    /// Phase-2: silo formula reduction carries, signed table at the projective
    /// bound. A distinct relation instance from the (still-live) consumer
    /// signed-carry providers; dedups only the preprocessed value/active columns
    /// by equation name.
    hinted_signed_formula: RangeCheckRelation,
    hinted_challenge: HintedMulChallenge,
    /// Per-cert proven `s2_sign_bit` provided by `fake_glv_scalar`, consumed by
    /// `final_add` to orient `R_2`. Shared into `final_add.sign`.
    final_add_sign: FinalAddSignRelation,
    /// Final EC-addition sub-graph relations (mul engine + result + output).
    /// `hint` is the same `final_check_hint` relation as above.
    final_add: FinalAddRelations,
    /// EC-op header link: silo (hinted_mul) consumes the header tuple on each
    /// proj group header row; the projective-source consumers (fake_glv
    /// ec_source + prepared_table) provide it. Placed OUTSIDE the
    /// scalar_mod_mul-related fields; drawn LAST to minimize transcript churn.
    ec_op_header: EcOpHeaderRelation,
}

fn p256_gamma_max_padded_values() -> usize {
    fake_glv_gamma_max_padded_values().max(hinted_mul_gamma_max_padded_values())
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
            public_key_on_curve: PublicKeyCurveSliceRelations::dummy_with_point(
                public_key_point,
                ProjectiveRcbMulComponentRelations::dummy().mul_result,
                GammaDigestRelation::dummy(),
                GammaChallenge::from_gamma(
                    SecureField::from(M31::from_u32_unchecked(2)),
                    remaining_gamma_max_padded_values(),
                ),
            ),
            projective_rcb_air: ProjectiveRcbMulComponentRelations::dummy(),
            hinted_signed_h: RangeCheckRelation::dummy(),
            hinted_signed_formula: RangeCheckRelation::dummy(),
            hinted_challenge: HintedMulChallenge::from_z(SecureField::from(
                M31::from_u32_unchecked(2),
            )),
            final_add_sign: FinalAddSignRelation::dummy(),
            final_add: FinalAddRelations {
                // SHARED with the hinted-mul provider relation above (dummy
                // instances are value-identical, mirroring the draw path).
                mul_result: ProjectiveRcbMulComponentRelations::dummy().mul_result,
                range13: RangeCheckRelation::dummy(),
                signed_carry: RangeCheckRelation::dummy(),
                hint: FinalCheckHintRelation::dummy(),
                output: FinalAddOutputRelation::dummy(),
                sign: FinalAddSignRelation::dummy(),
                gamma_digest: GammaDigestRelation::dummy(),
                gamma_challenge: GammaChallenge::from_gamma(
                    SecureField::from(M31::from_u32_unchecked(2)),
                    remaining_gamma_max_padded_values(),
                ),
            },
            ec_op_header: EcOpHeaderRelation::dummy(),
        }
    }

    fn draw(channel: &mut impl Channel) -> Self {
        let projective_rcb_air_relations = ProjectiveRcbMulComponentRelations::draw(channel);
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
        let final_add_sign = FinalAddSignRelation::draw(channel);
        let gamma_digest = GammaDigestRelation::draw(channel);
        let gamma_challenge = GammaChallenge::draw(channel, remaining_gamma_max_padded_values());
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
                projective_rcb_air_relations.mul_result.clone(),
                gamma_digest.clone(),
                gamma_challenge.clone(),
            ),
            projective_rcb_air: projective_rcb_air_relations.clone(),
            hinted_signed_h: RangeCheckRelation::draw(channel),
            hinted_challenge: HintedMulChallenge::draw(channel),
            final_add_sign: final_add_sign.clone(),
            final_add: FinalAddRelations {
                // SHARED with the hinted-mul provider: final-add's muls are
                // hinted rows, so the consumer must use the same instance.
                mul_result: projective_rcb_air_relations.mul_result.clone(),
                range13: RangeCheckRelation::draw(channel),
                signed_carry: RangeCheckRelation::draw(channel),
                // Shared with the prepared-table provider above.
                hint: final_check_hint,
                output: FinalAddOutputRelation::draw(channel),
                // Shared with the fake_glv_scalar provider.
                sign: final_add_sign,
                gamma_digest: gamma_digest.clone(),
                gamma_challenge: gamma_challenge.clone(),
            },
            // Drawn LAST (after all scalar_mod_mul + final_add relations).
            ec_op_header: EcOpHeaderRelation::draw(channel),
            // Phase-2 silo formula signed-carry relation, appended after the
            // header relation (the very end of the draw order).
            hinted_signed_formula: RangeCheckRelation::draw(channel),
        }
    }
}


/// γ-power table size for the SHARED gamma challenge: the max over the
/// REMAINING γ-digest users (final_add + public_key_curve) now that the two
/// projective-source consumers' talls are gone (Phase 3).
fn remaining_gamma_max_padded_values() -> usize {
    final_add_gamma_max_padded_values().max(pkc_gamma_max_padded_values())
}

struct P256CurrentAirComponents {
    scalar_setup: ScalarSetupAirComponents,
    cert_scalar_inputs: CertScalarInputAirComponents,
    fake_glv_scalar_air: FakeGlvScalarAirComponents,
    fake_glv_selector_air: FakeGlvSelectorAirComponents,
    scalar_mod_muls: ScalarModMulComponents,
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
    hinted_mul: HintedMulSliceComponents,
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
                &relations.final_add_sign,
            ),
            fake_glv_selector_air: FakeGlvSelectorAirComponents::new(
                allocator,
                claim.fake_glv_selector_air,
                &interaction_claim.fake_glv_selector_air,
                &relations.fake_glv_scalar,
            ),
            scalar_mod_muls: ScalarModMulComponents::new(
                allocator,
                &claim.scalar_mod_muls,
                &interaction_claim.scalar_mod_muls,
                &scalar_lookup_claims,
                &relations.scalar_mod_mul,
            ),
            prepared_table_projective_source: PreparedTableProjectiveSourceComponents::new_pinned(
                allocator,
                claim.prepared_table_projective_source.log_size,
                interaction_claim
                    .prepared_table_projective_source
                    .provider
                    .claimed_sum,
                &interaction_claim.prepared_table_projective_source,
                &relations.prepared_table,
                &PreparedTablePinningRelations {
                    cert_base: relations.cert_base.clone(),
                    canonical: relations.prepared_table_canonical.clone(),
                    final_check_hint: Some(relations.final_check_hint.clone()),
                },
                &relations.projective_rcb_air,
                &relations.ec_op_header,
            ),
            fake_glv_projective_source: FakeGlvProjectiveSourceComponents::new(
                allocator,
                claim.fake_glv_projective_source.log_size,
                claim.fake_glv_projective_source.source_offset,
                &interaction_claim.fake_glv_projective_source,
                &relations.fake_glv_projective_source,
                &relations.projective_rcb_air,
                &relations.ec_op_header,
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
            hinted_mul: HintedMulSliceComponents::new(
                allocator,
                claim.hinted_mul,
                &HintedMulSliceClaimedSums {
                    check: interaction_claim.hinted_mul.claimed_sum,
                    gamma_range13: interaction_claim.hinted_mul.gamma_range13,
                    gamma_signed: interaction_claim.hinted_mul.gamma_signed,
                    range13: interaction_claim.hinted_mul.range13,
                    signed_h: interaction_claim.hinted_mul.signed_h,
                    signed_formula: interaction_claim.hinted_mul.signed_formula,
                },
                &relations.hinted_challenge,
                &HintedMulRelations {
                    range13: relations.projective_rcb_air.range13.clone(),
                    signed_h: relations.hinted_signed_h.clone(),
                    mul_result: relations.projective_rcb_air.mul_result.clone(),
                    header: relations.ec_op_header.clone(),
                    signed_formula: relations.hinted_signed_formula.clone(),
                },
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
        components.push(&self.scalar_mod_muls.canonical as &dyn Component);
        components.push(&self.scalar_mod_muls.ab_chunks as &dyn Component);
        components.push(&self.scalar_mod_muls.qn_chunks as &dyn Component);
        components.push(&self.scalar_mod_muls.accumulators as &dyn Component);
        components.push(&self.scalar_mod_muls.reduction_digits as &dyn Component);
        components.push(&self.scalar_mod_muls.range13 as &dyn Component);
        components.push(&self.scalar_mod_muls.signed_carry as &dyn Component);
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
        components.extend(self.hinted_mul.components());
        components.extend(self.final_add.components());
        components
    }

    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut components = Vec::new();
        components.extend(self.scalar_setup.component_provers());
        components.extend(self.cert_scalar_inputs.component_provers());
        components.extend(self.fake_glv_scalar_air.component_provers());
        components.extend(self.fake_glv_selector_air.component_provers());
        components.push(&self.scalar_mod_muls.canonical as &dyn ComponentProver<SimdBackend>);
        components.push(&self.scalar_mod_muls.ab_chunks as &dyn ComponentProver<SimdBackend>);
        components.push(&self.scalar_mod_muls.qn_chunks as &dyn ComponentProver<SimdBackend>);
        components.push(&self.scalar_mod_muls.accumulators as &dyn ComponentProver<SimdBackend>);
        components
            .push(&self.scalar_mod_muls.reduction_digits as &dyn ComponentProver<SimdBackend>);
        components.push(&self.scalar_mod_muls.range13 as &dyn ComponentProver<SimdBackend>);
        components.push(&self.scalar_mod_muls.signed_carry as &dyn ComponentProver<SimdBackend>);
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
        components.extend(self.hinted_mul.component_provers());
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

#[cfg(test)]
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
    // 96-bit conjectured target: pow_bits + log_blowup * n_queries = 20 + 2*38 = 96.
    // Re-targeted from 128-bit (n_queries = 54) to match StarkWare's production
    // Cairo security level. Proof size is ~linear in n_queries (every query opens
    // every committed column across all modules), so 54 -> 38 trims ~30% of the
    // query-linear proof mass at no AIR cost. log_blowup is held at 2 so
    // commitment/FFT memory is unchanged from the calibrated on-device baseline
    // (raising it is the axis that made SHA W=7 OOM). Grinding trades a one-off
    // ~2^20 prover hash search for 10 fewer FRI queries; queries dominate proof
    // size.
    let fri_config = FriConfig::new(5, 2, 38, 1);
    PcsConfig {
        pow_bits: 20,
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

    /// Analytic interaction claim, derived on demand from the draft's `claim`
    /// and (dummy) `relations`. This is *not* stored on the draft: recomputing
    /// it costs ~2.4s for a single signature, and the proving path never needs
    /// it (it builds its own fresh interaction claim from the committed trace).
    /// Tests and debug tooling that inspect the analytic per-relation balances
    /// call this explicitly.
    pub fn interaction_claim(&self) -> P256ProofInteractionClaim {
        P256ProofInteractionClaim::from_claim(&self.claim, &self.relations)
    }

    pub fn verify_current_e2e(&self) -> Result<(), P256ProofError> {
        self.claim.verify_current_components()?;
        self.verify_audits()?;
        self.interaction_claim().verify_balanced()
    }

    pub fn prove_current_air_monolithic<MC>(
        &self,
    ) -> Result<P256CurrentAirProof<MC::H>, P256ProofError>
    where
        MC: MerkleChannel,
        SimdBackend: BackendForChannel<MC>,
    {
        // No pre-prove `verify_current_e2e()` here: it natively re-verifies the
        // entire witness, which is fully redundant with (a) the authoritative
        // balance check run below on the *fresh* interaction claim derived from
        // the committed trace (`interaction_claim.verify_balanced()` after
        // interaction-trace generation), and (b) the STARK verifier, which
        // enforces every AIR constraint. Skipping it roughly halves single-proof
        // wall time. `verify_current_e2e` remains a public method for
        // tests/debug that want the native cross-check explicitly.
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
        interaction_claim.verify_balanced(&self.claim.public_inputs.instances, &relations)?;
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
        let scalar_mod_mul_rows = merged_scalar_mod_mul_rows(&self.claim)?;
        {
            let local_ids = scalar_mod_mul_preprocessed_column_ids(
                &claim.scalar_mod_muls,
                &scalar_lookup_claims,
            );
            let local_columns = gen_scalar_mod_mul_preprocessed_trace(
                &scalar_mod_mul_rows,
                &scalar_lookup_claims,
                &local_ids,
            );
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

        let range7_id = range_check_value_column_id(claim.prepared_point_range7.log_size);
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

        let local_ids = claim.hinted_mul.preprocessed_column_ids();
        let local_columns = gen_hinted_mul_slice_preprocessed_trace(&self.claim.hinted_mul_trace);
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
        let scalar_mod_mul_rows = merged_scalar_mod_mul_rows(&self.claim)?;
        let scalar_mod_muls =
            gen_scalar_mod_mul_base_trace(&scalar_mod_mul_rows, &scalar_lookup_claims);
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
            claim.prepared_point_range7.gen_multiplicity_trace(
                self.claim
                    .prepared_trace
                    .providers
                    .iter()
                    .filter_map(|provider| {
                        (provider.use_count.0 != 0).then_some(provider.use_count)
                    }),
            );
        let hinted_mul_base = gen_hinted_mul_base_trace(&self.claim.hinted_mul_trace);
        let [hinted_gamma_range13_instance, hinted_gamma_signed_instance] =
            hinted_mul_gamma_instances(&self.claim.hinted_mul_trace);
        let hinted_gamma_range13_base = gen_gamma_tall_base_trace(&hinted_gamma_range13_instance);
        let hinted_gamma_signed_base = gen_gamma_tall_base_trace(&hinted_gamma_signed_instance);
        let hinted_range13_multiplicity = RangeCheckClaim::new(RANGE13_BITS)
            .gen_multiplicity_trace(hinted_mul_range13_uses(&self.claim.hinted_mul_trace));
        let hinted_signed_h_multiplicity = hinted_mul_signed_table_claim()
            .gen_multiplicity_trace(hinted_mul_signed_uses(&self.claim.hinted_mul_trace));
        // Phase-2 formula signed-carry provider multiplicity (projective bound).
        let hinted_signed_formula_multiplicity =
            crate::projective_air::projective_rcb_signed_carry_claim().gen_multiplicity_trace(
                crate::components::hinted_mul::trace::hinted_mul_formula_signed_uses(
                    &self.claim.hinted_mul_trace,
                ),
            );
        let final_add =
            gen_final_add_base_trace(&self.claim.final_add, claim.final_add.log_sizes())?;

        let mut columns = Vec::new();
        columns.extend(scalar_setup.clone());
        columns.extend(scalar_setup_lookup_providers.clone());
        columns.extend(cert_scalar_inputs.clone());
        columns.extend(fake_glv_scalar_air.clone());
        columns.extend(fake_glv_selector_air.clone());
        columns.extend(scalar_mod_muls);
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
        columns.extend(hinted_mul_base.clone());
        columns.extend(hinted_gamma_range13_base.clone());
        columns.extend(hinted_gamma_signed_base.clone());
        columns.push(hinted_range13_multiplicity.clone());
        columns.push(hinted_signed_h_multiplicity.clone());
        columns.push(hinted_signed_formula_multiplicity.clone());
        columns.extend(final_add);

        Ok(P256CurrentAirBaseTrace {
            columns,
            scalar_setup,
            cert_scalar_inputs,
            fake_glv_scalar_air,
            fake_glv_selector_air,
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
            hinted_mul_base,
            hinted_range13_multiplicity,
            hinted_signed_h_multiplicity,
            hinted_signed_formula_multiplicity,
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
                &relations.final_add_sign,
            );
        let (fake_glv_selector_interaction, fake_glv_selector_claim) =
            gen_fake_glv_selector_air_interaction_trace(
                &base.fake_glv_selector_air,
                &relations.fake_glv_scalar,
            );
        let scalar_lookup_claims = LookupProviderClaims::scalar_mod_mul();
        let scalar_mod_mul_rows = merged_scalar_mod_mul_rows(&self.claim)?;
        let scalar_mod_mul_claim =
            ScalarModMulClaim::from_rows_with_external_limb_links(&scalar_mod_mul_rows);
        let (scalar_mod_mul_interaction, scalar_mod_mul_interaction_claim) =
            gen_scalar_mod_mul_interaction_trace(
                &scalar_mod_mul_rows,
                &scalar_mod_mul_claim,
                &scalar_lookup_claims,
                &relations.scalar_mod_mul,
            );
        let (prepared_provider_interaction, prepared_pinned_claim) =
            gen_prepared_table_ec_row_pinned_interaction_trace(
                &base.prepared_table_provider,
                &relations.prepared_table,
                &relations.cert_base,
                &relations.prepared_table_canonical,
                Some(&relations.final_check_hint),
            );
        // Phase 3: the consumers emit their EC-row consume, the 6 narrow
        // `ProjectiveRcbMulResultRelation` consumes, and the EC-op header
        // yield, so they use the dedicated consumer interaction generators.
        let prepared_consumer = gen_prepared_table_projective_source_consumer_interaction_trace(
            &base.prepared_table_consumer,
            &relations.prepared_table,
            &relations.projective_rcb_air.mul_result,
            &relations.ec_op_header,
        );
        let (fake_glv_provider_interaction, fake_glv_provider_claim) =
            gen_fake_glv_primitive_ec_source_interaction_trace(
                &base.fake_glv_projective_provider,
                &relations.fake_glv_projective_source,
            );
        let fake_glv_consumer = gen_fake_glv_projective_source_consumer_interaction_trace(
            &base.fake_glv_projective_consumer,
            &relations.fake_glv_projective_source,
            &relations.projective_rcb_air.mul_result,
            &relations.ec_op_header,
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
        let (public_key_on_curve_interaction, public_key_on_curve_claim) =
            gen_public_key_on_curve_interaction_trace(
                &base.public_key_slice_claim,
                &relations.public_key_on_curve,
                true,
            )?;
        let hinted_schedule = gen_hinted_mul_schedule_columns(&self.claim.hinted_mul_trace);
        let (hinted_interaction, hinted_claim) = gen_hinted_mul_interaction_trace(
            &self.claim.hinted_mul_trace,
            &base.hinted_mul_base,
            &hinted_schedule,
            &HintedMulRelations {
                range13: relations.projective_rcb_air.range13.clone(),
                signed_h: relations.hinted_signed_h.clone(),
                mul_result: relations.projective_rcb_air.mul_result.clone(),
                header: relations.ec_op_header.clone(),
                signed_formula: relations.hinted_signed_formula.clone(),
            },
        );
        let (hinted_range13_interaction, hinted_range13_provider) =
            crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
                &base.hinted_range13_multiplicity,
                &RangeCheckClaim::new(RANGE13_BITS).gen_preprocessed_column(),
                &relations.projective_rcb_air.range13,
            );
        let (hinted_signed_h_interaction, hinted_signed_h_provider) =
            crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
                &base.hinted_signed_h_multiplicity,
                &hinted_mul_signed_table_claim().gen_value_column(),
                &relations.hinted_signed_h,
            );
        let (hinted_signed_formula_interaction, hinted_signed_formula_provider) =
            crate::range_checks::RangeCheckInteractionClaim::gen_interaction_trace(
                &base.hinted_signed_formula_multiplicity,
                &crate::projective_air::projective_rcb_signed_carry_claim().gen_value_column(),
                &relations.hinted_signed_formula,
            );
        let (final_add_interaction, final_add_claim) = gen_final_add_interaction_trace(
            &self.claim.final_add,
            &relations.final_add,
            FinalAddProofClaim::from_claim(&self.claim.final_add).log_sizes(),
        )?;
        let prepared_consumer_claimed_sum = prepared_consumer.ec_row_sum
            + prepared_consumer.mul_result_sum
            + prepared_consumer.gamma_yield_sum;
        let prepared_consumer_columns = prepared_consumer.columns;
        let fake_glv_consumer_claimed_sum = fake_glv_consumer.ec_row_sum
            + fake_glv_consumer.mul_result_sum
            + fake_glv_consumer.gamma_yield_sum;
        let fake_glv_consumer_columns = fake_glv_consumer.columns;

        let mut columns = Vec::new();
        columns.extend(scalar_setup_interaction);
        columns.extend(cert_scalar_input_interaction);
        columns.extend(fake_glv_scalar_interaction);
        columns.extend(fake_glv_selector_interaction);
        columns.extend(scalar_mod_mul_interaction);
        columns.extend(prepared_provider_interaction);
        columns.extend(prepared_consumer.columns.clone());
        columns.extend(fake_glv_provider_interaction);
        columns.extend(fake_glv_consumer.columns.clone());
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
        columns.extend(hinted_interaction);
        columns.extend(hinted_gamma_range13_interaction);
        columns.extend(hinted_gamma_signed_interaction);
        columns.extend(hinted_range13_interaction);
        columns.extend(hinted_signed_h_interaction);
        columns.extend(hinted_signed_formula_interaction);
        columns.extend(final_add_interaction);

        Ok((
            columns,
            P256CurrentAirInteractionClaim {
                scalar_setup: scalar_setup_claim,
                cert_scalar_inputs: cert_scalar_input_claim,
                fake_glv_scalar_air: fake_glv_scalar_claim,
                fake_glv_selector_air: fake_glv_selector_claim,
                scalar_mod_muls: scalar_mod_mul_interaction_claim,
                prepared_table_projective_source: PreparedTableProjectiveSourceInteractionClaim {
                    provider: crate::components::ComponentInteractionClaim {
                        claimed_sum: prepared_pinned_claim.claimed_sum,
                    },
                    consumer: crate::components::ComponentInteractionClaim {
                        claimed_sum: prepared_consumer.ec_row_sum
                            + prepared_consumer.mul_result_sum
                            + prepared_consumer.header_yield_sum,
                    },
                },
                prepared_table_pinned: prepared_pinned_claim,
                fake_glv_projective_source: FakeGlvProjectiveSourceInteractionClaim {
                    provider: crate::components::ComponentInteractionClaim {
                        claimed_sum: fake_glv_provider_claim.claimed_sum,
                    },
                    consumer: crate::components::ComponentInteractionClaim {
                        claimed_sum: fake_glv_consumer.ec_row_sum
                            + fake_glv_consumer.mul_result_sum
                            + fake_glv_consumer.header_yield_sum,
                    },
                },
                fake_glv_chain_expansion: FakeGlvChainExpansionInteractionClaim {
                    expansion_claimed_sum: expansion_provider_sum,
                    primitive_claimed_sum: expansion_consumer_sum,
                },
                fake_glv_chain_continuity: FakeGlvChainContinuityInteractionClaim {
                    claimed_sum: continuity_claim.claimed_sum,
                },
                fake_glv_direct_prepared_operand: FakeGlvDirectPreparedOperandInteractionClaim {
                    provider: crate::components::ComponentInteractionClaim {
                        claimed_sum: direct_provider_sum,
                    },
                    consumer: crate::components::ComponentInteractionClaim {
                        claimed_sum: direct_consumer_sum,
                    },
                },
                fake_glv_signed_selector_operand: FakeGlvSignedSelectorOperandInteractionClaim {
                    provider: crate::components::ComponentInteractionClaim {
                        claimed_sum: signed_provider_sum,
                    },
                    consumer: crate::components::ComponentInteractionClaim {
                        claimed_sum: signed_consumer_sum,
                    },
                },
                fake_glv_lsb_correction_operand: FakeGlvLsbCorrectionOperandInteractionClaim {
                    provider: crate::components::ComponentInteractionClaim {
                        claimed_sum: lsb_provider_sum,
                    },
                    consumer: crate::components::ComponentInteractionClaim {
                        claimed_sum: lsb_consumer_sum,
                    },
                },
                fake_glv_prepared_point_source: FakeGlvPreparedPointSourceInteractionClaim {
                    provider: crate::components::ComponentInteractionClaim {
                        claimed_sum: prepared_point_provider_sum
                            + prepared_point_range7_consumer_sum,
                    },
                    consumer: crate::components::ComponentInteractionClaim {
                        claimed_sum: prepared_point_consumer_sum,
                    },
                },
                prepared_point_range7: prepared_point_range7_claim,
                final_check: final_check_claim,
                public_key_on_curve: public_key_on_curve_claim,
                hinted_mul: HintedMulProofInteractionClaim {
                    claimed_sum: hinted_claim.claimed_sum,
                    gamma_range13: hinted_gamma_range13_claim,
                    gamma_signed: hinted_gamma_signed_claim,
                    range13: hinted_range13_provider.claimed_sum,
                    signed_h: hinted_signed_h_provider.claimed_sum,
                    signed_formula: hinted_signed_formula_provider.claimed_sum,
                },
                final_add: final_add_claim,
            },
        ))
    }

    fn from_claim(
        inputs: Vec<EcdsaVerifyInput>,
        claim: P256ProofClaim,
    ) -> Result<Self, P256ProofError> {
        let relations = P256ProofRelations::dummy();
        // The analytic interaction claim is *derived* from `claim` + `relations`
        // (see `interaction_claim()`), and recomputing it costs ~2.4s for a
        // single signature. The proving path computes its own fresh interaction
        // claim from the committed trace and balance-checks that, and the STARK
        // verifier enforces every constraint — so the draft does not eagerly
        // compute or balance-check it at build time. Tests/debug that want the
        // analytic per-relation balances call `interaction_claim()` explicitly.
        Ok(Self {
            inputs,
            claim,
            relations,
        })
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
    hinted_mul_base: ColumnVec<M31ColumnEval>,
    hinted_range13_multiplicity: M31ColumnEval,
    hinted_signed_h_multiplicity: M31ColumnEval,
    hinted_signed_formula_multiplicity: M31ColumnEval,
}

/// All `ScalarModMul` instances merged into a single component set, block-major
/// in the fixed order: every scalar_setup instance first, then every fake_glv
/// instance. Each instance keeps its own `mul_id` (now a base trace column), so
/// the merged LogUp tuples stay keyed per instance and the external
/// scalar_setup / fake_glv AIR providers still balance against them.
fn merged_scalar_mod_mul_rows(
    claim: &P256ProofClaim,
) -> Result<ScalarModMulMergedRows, P256ProofError> {
    let mut instances = scalar_setup_mod_mul_rows(claim)?;
    instances.extend(fake_glv_scalar_mod_mul_rows(claim)?);
    Ok(ScalarModMulMergedRows::new(instances))
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
        let mul_id =
            FAKE_GLV_SCALAR_MUL_ID_BASE + 2 * fake_glv_row.sig_id.0 + fake_glv_row.cert_id.0;
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
/// covers exactly one signature, so the slice is built from the FIRST
/// public-key row (mirroring [`final_add_claim_from_final_check`]).
fn public_key_on_curve_slice_claim(
    claim: &P256ProofClaim,
) -> Result<PublicKeyCurveSliceClaim, P256ProofError> {
    // The curve-check muls ride the hinted provider on source indices just
    // past the ladder ops and final-add (one source row per signature each).
    let hinted_source_offset = claim.projective_rcb_air_trace.rows.len() as u32
        + claim.final_add.mul_trace.rows.len() as u32;
    public_key_slice_from_check(&claim.public_key_check, hinted_source_offset)
}

/// Build the (single-signature) curve-check slice claim from the FIRST
/// public-key row: multi-signature claim *construction* stays available
/// (`links_all_implemented_components`), while the monolithic prove path
/// remains single-signature, exactly like `final_add_claim_from_final_check`.
fn public_key_slice_from_check(
    public_key_check: &PublicKeyOnCurveClaim,
    hinted_source_offset: u32,
) -> Result<PublicKeyCurveSliceClaim, P256ProofError> {
    let first = public_key_check
        .rows
        .first()
        .ok_or(P256ProofError::PublicKeyCurveSlice(
            PublicKeyCurveSliceError::UnsupportedRowCount { actual: 0 },
        ))?;
    let single = PublicKeyOnCurveClaim {
        rows: vec![first.clone()],
    };
    PublicKeyCurveSliceClaim::from_public_key_claim(&single, hinted_source_offset)
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
    hinted_source_offset: u32,
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
    let b1 = bit_for(0);
    let b2 = bit_for(1);
    let (r1, r1_inf) = signed_prepared(&row.h1, b1);
    let (r2, r2_inf) = signed_prepared(&row.h2, b2);
    // Pass the proven per-cert sign bits: `from_hints` orients `R_2` by
    // `d = b1 ⊕ b2` so the bound x-coordinate is `x(h_1 + h_2)`, and the AIR
    // binds `b1`/`b2` to these same values via `FinalAddSignRelation`.
    FinalAddClaim::from_hints(
        row.sig_id,
        &r1,
        r1_inf,
        b1,
        &r2,
        r2_inf,
        b2,
        hinted_source_offset,
    )
    .map_err(P256ProofError::FinalAdd)
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
        None => (
            AffinePoint {
                x: U256::ZERO,
                y: U256::ZERO,
            },
            true,
        ),
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
        None => (
            AffinePoint {
                x: U256::ZERO,
                y: U256::ZERO,
            },
            true,
        ),
    }
}

pub fn verify_current_air_monolithic<MC>(
    proof: P256CurrentAirProof<MC::H>,
    expected_instances: &[PublicEcdsaInstance<M31>],
) -> Result<(), P256ProofError>
where
    MC: MerkleChannel,
{
    let P256CurrentAirProof {
        claim,
        interaction_claim,
        stark_proof,
    } = proof;
    // Caller-argument binding. The O1 fix below ties the proof to its OWN
    // embedded `claim.public_inputs.instances` (recomputed provider sums against
    // STARK-bound consumers), but this function returns only `Result<(), _>`: a
    // relying party that trusts `Ok(())` would otherwise accept a valid proof of
    // ANY signature the prover embedded, not the `(z, r, s, pub_x, pub_y)` the
    // caller intended to verify. Compare the embedded instances against the
    // caller's expected statement first — cheap, and fail-closed on any mismatch.
    if claim.public_inputs.instances.as_slice() != expected_instances {
        return Err(P256ProofError::PublicInstanceMismatch);
    }
    // Public-key canonicality gate. The AIR range-checks the limbs and binds
    // them to the curve equation, but the curve check works mod p, so a
    // non-canonical representative (`x + p`) of a valid point would otherwise
    // verify. ECDSA public keys are defined over canonical field elements;
    // reject non-canonical coordinates before any proof work.
    for (index, instance) in claim.public_inputs.instances.iter().enumerate() {
        if let Some(field) = instance.non_canonical_public_key_field() {
            return Err(P256ProofError::NonCanonicalPublicKey { index, field });
        }
    }
    let ids = claim.preprocessed_column_ids();
    // Pin the PCS config: `stark_proof.config` is prover-supplied, and the
    // verifier must not inherit a weakened FRI/grinding setting from it (a
    // 1-query proof would otherwise verify at ~2-bit security).
    let expected_config =
        p256_stark_monolithic_profile_config(claim.max_constraint_log_degree_bound(&ids));
    if stark_proof.config != expected_config {
        return Err(P256ProofError::ProofLayer(format!(
            "proof PCS config {:?} does not match the pinned verifier config {:?}",
            stark_proof.config, expected_config
        )));
    }
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

    if interaction_claim.lookup_sum(&claim.public_inputs.instances, &relations) != zero() {
        return Err(P256ProofError::RelationImbalance {
            relation: "LookupSum",
        });
    }

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
        note: "Selector reconstruction is proven from FakeGlvScalarRelation inside the monolithic STARK for ARBITRARY decompositions: each 4-bit selector splits into boolean-constrained 2-bit s1/s2 chunks (selector = s1c + 4*s2c) and two symmetric 13-bit carry chains bind the reconstructed s1 AND s2_abs to the relation's limbs (s2_lsb/s2_msb/sign witnessed free, not hard-coded), plus final-selector/init-base and inactive/padding zeroing; the separate selector lookup providers retain their proof slices. Real full-width signatures prove via from_inputs_with_arbitrary_fake_glv_hints.",
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
        note: "Prepared-table EC row shape is proven and linked into projective RCB source rows. EC arithmetic is constrained in-AIR (C5-2): the prepared-table projective source binds the Double/MixedAdd coordinate formulas (bind_double_formula/bind_mixed_add_formula) on the consumed silo muls — output = double(lhs) / lhs+rhs incl. projective->affine normalization — with self-contained Range13/signed-carry providers, so the table multiples {P,3P}±{R,3R}, 2P, 2R are forced to correct EC results rather than free witnesses.",
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
    HintedMul(HintedMulWitnessError),
    PublicKeyOnCurve(PublicKeyOnCurveError),
    PublicKeyCurveSlice(PublicKeyCurveSliceError),
    ScalarModMulTrace(ScalarModMulTraceError),
    InvalidNativeEcdsaInput {
        index: usize,
    },
    NonCanonicalPublicKey {
        index: usize,
        field: &'static str,
    },
    RelationImbalance {
        relation: &'static str,
    },
    /// The verified proof's embedded public instances do not match the
    /// statement the caller asked to verify. Without this check, a relying
    /// party that trusts `Ok(())` would accept a valid proof of ANY signature
    /// the prover chose, not the one the caller intended.
    PublicInstanceMismatch,
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

impl From<HintedMulWitnessError> for P256ProofError {
    fn from(value: HintedMulWitnessError) -> Self {
        Self::HintedMul(value)
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
mod tests;
