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
