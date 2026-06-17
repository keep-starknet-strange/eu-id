pub mod air;
pub mod components;
pub mod eval;
pub mod interaction;
pub mod lookup_elements;
pub mod preprocessed;
pub mod witness;

use crate::age::predicate::AgePredicate;
use crate::age::strategy::range_check::air::{RangeCheckProver, RangeCheckVerifier};
use crate::age::types::{AgeRangeCheckProof, DateOfBirth, Error, PublicInput};
use crate::predicate::{PredicateProver, PredicateVerifier};
use air_core::{prove, verify, Air};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;

pub struct AgeRangeCheck(AgePredicate);

impl AgeRangeCheck {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self(AgePredicate::new(pcs_config))
    }

    #[cfg(test)]
    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self(AgePredicate::new_with_input_validation(
            pcs_config,
            validate_input,
        ))
    }

    /// Prove this strategy on its own and pack the result into a proof.
    pub fn prove(
        &self,
        public: &PublicInput,
        private: &DateOfBirth,
    ) -> Result<AgeRangeCheckProof, Error> {
        let mut prover = self.prover(public, private)?;
        let stark_proof = prove(&mut [&mut prover], self.0.pcs_config)?;

        let s = prover.claimed_sums();
        Ok(AgeRangeCheckProof {
            public: *public,
            age_claimed_sum: s[0],
            calendar_table_claimed_sum: s[1],
            valid_day_table_claimed_sum: s[2],
            day_delta_claimed_sum: s[3],
            month_delta_claimed_sum: s[4],
            year_delta_claimed_sum: s[5],
            stark_proof,
        })
    }

    /// Verify a standalone proof of this strategy.
    pub fn verify(&self, proof: &AgeRangeCheckProof) -> Result<(), Error> {
        let mut verifier = self.verifier(
            &proof.public,
            &[
                proof.age_claimed_sum,
                proof.calendar_table_claimed_sum,
                proof.valid_day_table_claimed_sum,
                proof.day_delta_claimed_sum,
                proof.month_delta_claimed_sum,
                proof.year_delta_claimed_sum,
            ],
        )?;
        verify(&mut [&mut verifier], &proof.stark_proof)?;

        Ok(())
    }
}

impl PredicateProver for AgeRangeCheck {
    type PublicInput = PublicInput;
    type PrivateInput = DateOfBirth;
    type Error = Error;
    type Prover = RangeCheckProver;

    fn prover(
        &self,
        public: &PublicInput,
        private: &DateOfBirth,
    ) -> Result<RangeCheckProver, Error> {
        self.0.validate(public)?;
        let witness = self.0.witness(public, private)?;
        Ok(RangeCheckProver::new(public, &witness))
    }
}

impl PredicateVerifier for AgeRangeCheck {
    type PublicInput = PublicInput;
    type Error = Error;
    type Verifier = RangeCheckVerifier;

    fn verifier(
        &self,
        public: &PublicInput,
        claimed_sums: &[QM31],
    ) -> Result<RangeCheckVerifier, Error> {
        self.0.validate(public)?;
        Ok(RangeCheckVerifier::new(public, claimed_sums.to_vec()))
    }
}
