use stwo::core::fields::{m31::M31, qm31::SecureField};

use crate::ecdsa::ecdsa_verify;
use crate::fake_glv_chain::{FakeGlvChainClaim, FakeGlvChainError, FakeGlvPrimitiveEcTraceClaim};
use crate::final_check::{FinalEcdsaCheckClaim, FinalEcdsaCheckError};
use crate::prepared_point::{
    prepared_point_provider_claimed_sum, prepared_point_range7_consumer_claimed_sum,
    PreparedPointAudit, PreparedPointError, PreparedPointRelation, PreparedPointTraceClaim,
    PreparedPointUseCountClaim,
};
use crate::prepared_table::{PreparedTableClaim, PreparedTableEcTraceClaim, PreparedTableError};
use crate::projective::{ProjectiveEcError, ProjectiveEcTraceClaim};
use crate::projective_air::{
    projective_rcb_signed_carry_log_size, ProjectiveRcbAirError, ProjectiveRcbAirInteractionClaim,
    ProjectiveRcbAirTraceClaim, ProjectiveRcbMulComponentRelations,
    PROJECTIVE_RCB_SIGNED_CARRY_BOUND, PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
};
use crate::public_inputs::{
    public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
};
use crate::public_key_check::{PublicKeyOnCurveClaim, PublicKeyOnCurveError};
use crate::range_checks::{
    RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation, SignedCarryRangeClaim,
    RANGE13_BITS, RANGE7_BITS,
};
use crate::scalar::cert_bind::{CertScalarInputClaim, CertScalarInputError};
use crate::scalar::fake_glv_scalar::{
    FakeGlvScalarHint, FakeGlvScalarHintClaim, FakeGlvScalarHintError,
};
use crate::scalar::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorError};
use crate::scalar::fake_glv_selector_lookup::{
    selector_lookup_consumer_claimed_sum, FakeGlvSelectorLookupRelations, SelectorLookupAudit,
    SelectorLookupError, SelectorLookupRequests, SelectorProviderInteractionClaim,
};
use crate::scalar::setup_air::{ScalarSetupClaim, ScalarSetupClaimError};
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
        note: "Public relation provider and scalar-setup consumer are linked.",
    },
    P256ProofComponentSlot {
        name: "PublicKeyOnCurve",
        status: P256ProofComponentStatus::Implemented,
        note: "Public key curve equation is checked with Solinas base-field multiplication traces.",
    },
    P256ProofComponentSlot {
        name: "SolinasReductionTraceRows",
        status: P256ProofComponentStatus::Implemented,
        note: "Public-key on-curve field multiplications include split Solinas reduction rows tied back to each multiplication trace.",
    },
    P256ProofComponentSlot {
        name: "ScalarSetup",
        status: P256ProofComponentStatus::Implemented,
        note: "Native witness and AIR-facing scalar setup claim are linked.",
    },
    P256ProofComponentSlot {
        name: "CertScalarInput",
        status: P256ProofComponentStatus::Implemented,
        note: "Two fake-GLV certificate rows are derived from scalar setup.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvScalarHint",
        status: P256ProofComponentStatus::Implemented,
        note: "Scalar decomposition hints are checked against certificate scalars.",
    },
    P256ProofComponentSlot {
        name: "FakeGlvSelector",
        status: P256ProofComponentStatus::Implemented,
        note: "Selector reconstruction and selector lookup requests are linked.",
    },
    P256ProofComponentSlot {
        name: "PreparedPointUseCounts",
        status: P256ProofComponentStatus::Implemented,
        note: "PreparedPoint copy-bus counts and Range7 use-count bounds are linked.",
    },
    P256ProofComponentSlot {
        name: "PreparedTablePoints",
        status: P256ProofComponentStatus::Implemented,
        note: "Native prepared-table point generation feeds real Base[0..7] and Table[16] coordinates into PreparedPoint providers.",
    },
    P256ProofComponentSlot {
        name: "PreparedTableEcTrace",
        status: P256ProofComponentStatus::Implemented,
        note: "Native row-level DOUBLE/ADD trace verifies P3, R3, Base[0..7], and Table[16] production against prepared-table points.",
    },
    P256ProofComponentSlot {
        name: "PreparedTableEcRows",
        status: P256ProofComponentStatus::Pending,
        note: "AIR constraints for STATE_LOAD, table construction EC rows, R3 fixed-offset use, and AFFINE_EXPORT are not implemented yet.",
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
        status: P256ProofComponentStatus::Pending,
        note: "Stwo AIR constraints for MSB init, primitive chain DOUBLE/ADD rows, Table[16] final step, and LSB correction are not implemented yet.",
    },
    P256ProofComponentSlot {
        name: "FinalEcdsaCheck",
        status: P256ProofComponentStatus::Implemented,
        note: "Native final check links H1/H2 to fake-GLV chain R3 values, enforces finite R = H1 + H2, and checks x(R) mod n = r.",
    },
    P256ProofComponentSlot {
        name: "StarkProveVerify",
        status: P256ProofComponentStatus::Pending,
        note: "Top-level preprocessed/base/interaction trace commitment and STARK prove/verify wrapper are pending.",
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
    InvalidNativeEcdsaInput { index: usize },
    RelationImbalance { relation: &'static str },
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

fn zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY, P256_ORDER};
    use crate::curve::{mod_inverse, scalar_mul};
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
    use crate::fake_glv_prepared_point_source::{
        prove_fake_glv_prepared_point_source_proof_slice,
        verify_fake_glv_prepared_point_source_proof_slice, FakeGlvPreparedPointSourceProofClaim,
    };
    use crate::fake_glv_selector_lookup::{
        prove_selector_lookup_provider_proof_slice, verify_selector_lookup_provider_proof_slice,
        SelectorLookupProviderProofClaim,
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
    use crate::types::{AffinePoint, Signature, U256};
    use core::cmp::Ordering;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;

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

        assert!(implemented.contains(&"PublicKeyOnCurve"));
        assert!(implemented.contains(&"SolinasReductionTraceRows"));
        assert!(implemented.contains(&"PreparedTablePoints"));
        assert!(implemented.contains(&"PreparedTableEcTrace"));
        assert!(implemented.contains(&"FakeGlvChainTrace"));
        assert!(implemented.contains(&"FakeGlvPrimitiveEcTrace"));
        assert!(implemented.contains(&"ProjectiveRcbEcTrace"));
        assert!(implemented.contains(&"ProjectiveRcbAirRows"));
        assert!(implemented.contains(&"FinalEcdsaCheck"));
        assert!(pending.contains(&"PreparedTableEcRows"));
        assert!(pending.contains(&"FakeGlvEcChainRows"));
        assert!(pending.contains(&"StarkProveVerify"));
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
