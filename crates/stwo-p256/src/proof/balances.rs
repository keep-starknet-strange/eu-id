//! Relation-balance accounting for the monolithic P-256 proof.
//!
//! Holds the per-relation provider/consumer claimed-sum bookkeeping
//! ([`RelationBalanceClaim`], [`P256ProofRelations`], [`P256ProofInteractionClaim`])
//! split out of [`super`] verbatim; the prove/verify orchestration that consumes
//! these stays in [`super`].

use super::*;

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
