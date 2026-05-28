use stwo::core::fields::{m31::M31, qm31::SecureField};

use crate::ecdsa::ecdsa_verify;
use crate::prepared_point::{
    prepared_point_consumer_claimed_sum, prepared_point_provider_claimed_sum,
    prepared_point_range7_consumer_claimed_sum, PreparedPointAudit, PreparedPointError,
    PreparedPointRelation, PreparedPointTraceClaim, PreparedPointUseCountClaim,
};
use crate::prepared_table::{PreparedTableClaim, PreparedTableEcTraceClaim, PreparedTableError};
use crate::public_inputs::{
    public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
};
use crate::range_checks::{
    RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation, RANGE7_BITS,
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
    pub scalar_setup: ScalarSetupClaim,
    pub cert_inputs: CertScalarInputClaim,
    pub fake_glv_scalars: FakeGlvScalarHintClaim,
    pub fake_glv_selectors: FakeGlvSelectorClaim,
    pub selector_requests: SelectorLookupRequests,
    pub prepared_table: PreparedTableClaim,
    pub prepared_table_ec_trace: PreparedTableEcTraceClaim,
    pub prepared_use_counts: PreparedPointUseCountClaim,
    pub prepared_trace: PreparedPointTraceClaim,
}

impl P256ProofClaim {
    pub fn from_inputs_with_hints(
        inputs: &[EcdsaVerifyInput],
        fake_glv_hints: Vec<FakeGlvScalarHint>,
    ) -> Result<Self, P256ProofError> {
        let public_inputs = PublicEcdsaInputClaim::from_inputs(inputs);
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
        let prepared_use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&fake_glv_selectors)?;
        let prepared_trace = prepared_table.prepared_point_trace(&prepared_use_counts)?;

        Ok(Self {
            public_inputs,
            scalar_setup,
            cert_inputs,
            fake_glv_scalars,
            fake_glv_selectors,
            selector_requests,
            prepared_table,
            prepared_table_ec_trace,
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
        self.scalar_setup.verify()?;
        self.cert_inputs.verify()?;
        self.fake_glv_scalars.verify()?;
        self.fake_glv_selectors.verify(&self.fake_glv_scalars)?;
        self.selector_requests.verify()?;
        self.prepared_table.verify()?;
        self.prepared_table_ec_trace.verify()?;
        self.prepared_use_counts.verify()?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct P256ProofRelations {
    pub public_inputs: PublicEcdsaInstanceRelation,
    pub selector_lookups: FakeGlvSelectorLookupRelations,
    pub prepared_points: PreparedPointRelation,
    pub range7: RangeCheckRelation,
}

impl P256ProofRelations {
    pub fn dummy() -> Self {
        Self {
            public_inputs: PublicEcdsaInstanceRelation::dummy(),
            selector_lookups: FakeGlvSelectorLookupRelations::dummy(),
            prepared_points: PreparedPointRelation::dummy(),
            range7: RangeCheckRelation::dummy(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct P256ProofInteractionClaim {
    pub public_inputs: RelationBalanceClaim,
    pub selector_lookups: RelationBalanceClaim,
    pub prepared_points: RelationBalanceClaim,
    pub range7: RelationBalanceClaim,
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
        let prepared_consumer = prepared_point_consumer_claimed_sum(
            &claim.prepared_trace.consumer_instances(),
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

        Self {
            public_inputs: RelationBalanceClaim::new(public_provider, public_consumer),
            selector_lookups: RelationBalanceClaim::new(selector_provider, selector_consumer),
            prepared_points: RelationBalanceClaim::new(prepared_provider, prepared_consumer),
            range7: RelationBalanceClaim::new(
                range7_provider_interaction.claimed_sum,
                range7_consumer,
            ),
        }
    }

    pub fn verify_balanced(&self) -> Result<(), P256ProofError> {
        self.public_inputs.verify("PublicEcdsaInstance")?;
        self.selector_lookups.verify("SelectorLookups")?;
        self.prepared_points.verify("PreparedPoint")?;
        self.range7.verify("Range7")?;
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

        let prepared_audit = PreparedPointAudit::balanced_for_claim(&self.claim.prepared_trace);
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
        name: "FakeGlvEcChainRows",
        status: P256ProofComponentStatus::Pending,
        note: "MSB init, chain ADD rows, Table[16] final step, and LSB correction EC constraints are not implemented yet.",
    },
    P256ProofComponentSlot {
        name: "FinalEcdsaCheck",
        status: P256ProofComponentStatus::Pending,
        note: "H1+H2, R != infinity, x(R) mod n = r, and optional recovery checks are not implemented yet.",
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
    FakeGlvScalar(FakeGlvScalarHintError),
    FakeGlvSelector(FakeGlvSelectorError),
    SelectorLookup(SelectorLookupError),
    PreparedPoint(PreparedPointError),
    PreparedTable(PreparedTableError),
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

fn zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY, P256_ORDER};
    use crate::curve::{mod_inverse, scalar_mul};
    use crate::field_ops::mul_mod_witness;
    use crate::limbs::P256M31BigInt;
    use crate::types::{AffinePoint, Signature, U256};
    use core::cmp::Ordering;

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
        assert_ne!(u1, 0, "u1 must use the active fake-GLV branch");
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

    #[test]
    fn current_p256_proof_pipeline_links_all_implemented_components() {
        let proof = P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![
            test_input(42, 77, 1),
            test_input(43, 78, 1),
        ])
        .expect("current pipeline builds");

        proof.verify_current_e2e().expect("current e2e verifies");
        assert_eq!(proof.claim.public_inputs.instances.len(), 2);
        assert_eq!(proof.claim.scalar_setup.rows.len(), 2);
        assert_eq!(proof.claim.cert_inputs.rows.len(), 4);
        assert_eq!(proof.claim.fake_glv_scalars.rows.len(), 4);
        assert_eq!(proof.claim.fake_glv_selectors.rows.len(), 4);
        assert_eq!(proof.claim.selector_requests.final_selector.len(), 4);
        assert_eq!(proof.claim.prepared_table.certs.len(), 4);
        assert_eq!(proof.claim.prepared_table_ec_trace.active_row_count(), 48);
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
        assert_eq!(proof.interaction_claim.public_inputs.total(), zero());
        assert_eq!(proof.interaction_claim.selector_lookups.total(), zero());
        assert_eq!(proof.interaction_claim.prepared_points.total(), zero());
        assert_eq!(proof.interaction_claim.range7.total(), zero());
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
    fn current_p256_proof_pipeline_allows_zero_u1_branch() {
        let proof =
            P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![test_input(0, 77, 1)])
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

        assert!(implemented.contains(&"PreparedTablePoints"));
        assert!(implemented.contains(&"PreparedTableEcTrace"));
        assert!(pending.contains(&"PreparedTableEcRows"));
        assert!(pending.contains(&"FakeGlvEcChainRows"));
        assert!(pending.contains(&"FinalEcdsaCheck"));
        assert!(pending.contains(&"StarkProveVerify"));
    }

    #[test]
    fn current_p256_proof_pipeline_detects_public_relation_imbalance() {
        let mut proof =
            P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![test_input(42, 77, 1)])
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
        let mut proof =
            P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![test_input(42, 77, 1)])
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
        let mut proof =
            P256ProofDraft::from_inputs_with_trivial_fake_glv_hints(vec![test_input(42, 77, 1)])
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
