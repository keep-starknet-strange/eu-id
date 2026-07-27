pub mod air;
pub mod components;
pub mod eval;
pub mod interaction;
pub mod lookup_elements;
pub mod preprocessed;
pub mod witness;

use crate::age::predicate::AgePredicate;
use crate::age::strategy::bit_decomposition::air::{
    BitDecompositionProver, BitDecompositionVerifier, BIT_DECOMPOSITION_CLAIM_COUNT,
};
use crate::age::types::{AgeBitDecompositionProof, AgeInputError, DateOfBirth, Error, PublicInput};
use crate::predicate::{PredicateProver, PredicateVerifier};
use air_core::{prove, verify, Air};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;

pub struct AgeBitDecomposition(AgePredicate);

impl AgeBitDecomposition {
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
    ) -> Result<AgeBitDecompositionProof, Error> {
        let mut prover = self.prover(public, private)?;
        let stark_proof = prove(&mut [&mut prover], self.0.pcs_config)?;

        let s = prover.claimed_sums();
        Ok(AgeBitDecompositionProof {
            public: *public,
            age_claimed_sum: s[0],
            calendar_table_claimed_sum: s[1],
            valid_day_table_claimed_sum: s[2],
            stark_proof,
        })
    }

    /// Verify a standalone proof of this strategy.
    pub fn verify(&self, proof: &AgeBitDecompositionProof) -> Result<(), Error> {
        let mut verifier = self.verifier(
            &proof.public,
            &[
                proof.age_claimed_sum,
                proof.calendar_table_claimed_sum,
                proof.valid_day_table_claimed_sum,
            ],
        )?;
        verify(&mut [&mut verifier], &proof.stark_proof)?;

        Ok(())
    }
}

impl PredicateProver for AgeBitDecomposition {
    type PublicInput = PublicInput;
    type PrivateInput = DateOfBirth;
    type Error = Error;
    type Prover = BitDecompositionProver;

    fn prover(
        &self,
        public: &PublicInput,
        private: &DateOfBirth,
    ) -> Result<BitDecompositionProver, Error> {
        self.0.validate(public)?;
        let witness = self.0.witness(public, private)?;
        Ok(BitDecompositionProver::new(public, &witness))
    }
}

impl PredicateVerifier for AgeBitDecomposition {
    type PublicInput = PublicInput;
    type Error = Error;
    type Verifier = BitDecompositionVerifier;

    fn verifier(
        &self,
        public: &PublicInput,
        claimed_sums: &[QM31],
    ) -> Result<BitDecompositionVerifier, Error> {
        self.0.validate(public)?;
        if claimed_sums.len() != BIT_DECOMPOSITION_CLAIM_COUNT {
            return Err(AgeInputError::Invalid(format!(
                "age bit-decomposition proof carries {} claimed sums; expected {}",
                claimed_sums.len(),
                BIT_DECOMPOSITION_CLAIM_COUNT,
            ))
            .into());
        }
        Ok(BitDecompositionVerifier::new(public, claimed_sums.to_vec()))
    }
}
