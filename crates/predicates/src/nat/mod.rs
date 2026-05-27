mod components;
mod eval;
mod interaction;
pub mod nationalities;
pub mod predicate;
mod preprocessed;
pub mod table;
pub mod types;
mod witness;

use components::components;
use interaction::InteractionTraces;
use predicate::NationalityPredicate;
use preprocessed::Preprocessed;
use table::{table_log_size, NatTableElements};
use types::{Error, InputError, PrivateInput, Proof, PublicInput, Witness};
use witness::WitnessData;

use crate::predicate::{Predicate, StandalonePredicate};
use num_traits::Zero;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::verify;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};

impl Predicate for NationalityPredicate {
    type PublicInput = PublicInput;
    type PrivateInput = PrivateInput;
    type Witness = Witness;
    type Error = Error;

    fn validate(&self, public: &PublicInput) -> Result<(), Error> {
        NationalityPredicate::validate(self, public)
    }

    fn witness(&self, public: &PublicInput, private: &PrivateInput) -> Result<Witness, Error> {
        NationalityPredicate::witness(self, public, private)
    }
}

impl StandalonePredicate for NationalityPredicate {
    type Proof = Proof;

    fn prove(&self, public: &PublicInput, private: &PrivateInput) -> Result<Proof, Error> {
        self.validate(public)?;
        let witness = self.witness(public, private)?;

        let t_log_size = table_log_size(&public.acceptable);
        let preprocessed = Preprocessed::new(public);

        let max_log_size = WitnessData::log_size().max(t_log_size);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                max_log_size + 1 + self.pcs_config.fri_config.log_blowup_factor,
            )
            .circle_domain()
            .half_coset,
        );

        let channel = &mut Blake2sChannel::default();
        self.pcs_config.mix_into(channel);

        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(
                self.pcs_config,
                &twiddles,
            );

        // Tree 0: acceptable nationality table (1 column).
        let mut tb = commitment_scheme.tree_builder();
        preprocessed.extend_evals(&mut tb);
        tb.commit(channel);

        public.mix_into(channel);

        // Tree 1: nationality witness (1 col) + table multiplicity (1 col).
        let witness_data = WitnessData::new(&witness, public);
        let mut tb = commitment_scheme.tree_builder();
        witness_data.extend_evals(&mut tb);
        tb.commit(channel);

        let lookup_elements = NatTableElements::draw(channel);

        // Tree 2: interaction traces (1 logup fraction per component = 4 M31 cols each).
        let interaction = InteractionTraces::new(&witness_data, &preprocessed, &lookup_elements);
        interaction.mix_into(channel);

        let mut tb = commitment_scheme.tree_builder();
        interaction.extend_evals(&mut tb);
        tb.commit(channel);

        let (nat_component, table_component) = components(
            public,
            lookup_elements,
            interaction.nat_claimed_sum,
            interaction.table_claimed_sum,
        );

        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            &[
                &nat_component as &dyn ComponentProver<SimdBackend>,
                &table_component,
            ],
            channel,
            commitment_scheme,
        )?;

        Ok(Proof {
            public: public.clone(),
            nat_claimed_sum: interaction.nat_claimed_sum,
            table_claimed_sum: interaction.table_claimed_sum,
            stark_proof,
        })
    }

    fn verify(&self, proof: &Proof) -> Result<(), Error> {
        self.validate(&proof.public)?;

        let t_log_size = table_log_size(&proof.public.acceptable);
        let nat_log_size = WitnessData::log_size();

        let config = proof.stark_proof.config;
        let channel = &mut Blake2sChannel::default();
        config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);

        // Tree 0: acceptable nationality table (1 column).
        commitment_scheme.commit(
            proof.stark_proof.commitments[0],
            &[t_log_size],
            channel,
        );

        proof.public.mix_into(channel);

        // Tree 1: nationality witness (1 col) + table multiplicity (1 col).
        commitment_scheme.commit(
            proof.stark_proof.commitments[1],
            &[nat_log_size, t_log_size],
            channel,
        );

        let lookup_elements = NatTableElements::draw(channel);

        channel.mix_felts(&[proof.nat_claimed_sum, proof.table_claimed_sum]);

        if proof.nat_claimed_sum + proof.table_claimed_sum != QM31::zero() {
            return Err(InputError::InvalidProof.into());
        }

        // Tree 2: nat interaction (4 M31) + table interaction (4 M31).
        commitment_scheme.commit(
            proof.stark_proof.commitments[2],
            &std::iter::repeat_n(nat_log_size, 4)
                .chain(std::iter::repeat_n(t_log_size, 4))
                .collect::<Vec<_>>(),
            channel,
        );

        let (nat_component, table_component) = components(
            &proof.public,
            lookup_elements,
            proof.nat_claimed_sum,
            proof.table_claimed_sum,
        );

        verify(
            &[&nat_component, &table_component],
            channel,
            commitment_scheme,
            proof.stark_proof.clone(),
        )?;

        Ok(())
    }
}

pub fn prove_nationality(public: &PublicInput, private: &PrivateInput) -> Result<Proof, Error> {
    NationalityPredicate::new(PcsConfig::default()).prove(public, private)
}

pub fn verify_nationality(proof: &Proof) -> Result<(), Error> {
    NationalityPredicate::new(PcsConfig::default()).verify(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nat::types::InputError;

    fn predicate() -> NationalityPredicate {
        NationalityPredicate::new(PcsConfig::default())
    }

    // DE=276, FR=250, GR=300, US=840
    fn eu_set() -> PublicInput {
        PublicInput::new(vec![276, 250, 300])
    }

    fn private(codes: &[u32]) -> PrivateInput {
        PrivateInput { nationalities: codes.to_vec() }
    }

    // --- Happy paths ---

    #[test]
    fn proves_and_verifies_single_nationality_in_set() {
        let p = predicate();
        let proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_first_matching_nationality_chosen() {
        // prover holds FR and DE; both are acceptable; FR appears first
        let p = predicate();
        let proof = p.prove(&eu_set(), &private(&[250, 276])).unwrap();
        p.verify(&proof).unwrap();
        assert_eq!(proof.public.acceptable, eu_set().acceptable);
    }

    #[test]
    fn proves_and_verifies_last_nationality_matches() {
        // only the last nationality is in the acceptable set
        let p = predicate();
        let proof = p.prove(&eu_set(), &private(&[840, 276])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_two_entry_acceptable_set() {
        let p = predicate();
        let public = PublicInput::new(vec![276, 300]);
        let proof = p.prove(&public, &private(&[276])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_large_acceptable_set() {
        // 249 ISO codes — exercises log_size=8 table
        use crate::nat::nationalities::Nationality;
        use strum::IntoEnumIterator;
        let p = predicate();
        let all: Vec<u32> = Nationality::iter().map(|n| n as u32).collect();
        let public = PublicInput::new(all);
        let proof = p.prove(&public, &private(&[276])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn public_input_new_sorts_and_deduplicates() {
        let public = PublicInput::new(vec![300, 276, 250, 276]);
        assert_eq!(public.acceptable, vec![250, 276, 300]);
    }

    // --- Error cases ---

    #[test]
    fn validate_rejects_singleton_acceptable_set() {
        let p = predicate();
        let err = p.prove(&PublicInput::new(vec![276]), &private(&[276])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::AcceptableSetTooSmall)));
    }

    #[test]
    fn validate_rejects_empty_acceptable_set() {
        let p = predicate();
        let err = p.prove(&PublicInput::new(vec![]), &private(&[276])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::AcceptableSetTooSmall)));
    }

    #[test]
    fn validate_rejects_non_iso_code_in_acceptable_set() {
        let p = predicate();
        // 1 is not an assigned ISO 3166-1 numeric code
        let err = p.prove(&PublicInput::new(vec![276, 1]), &private(&[276])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::InvalidNationalityCode(1))));
    }

    #[test]
    fn witness_rejects_no_matching_nationality() {
        let p = predicate();
        // US (840) is not in the EU set
        let err = p.prove(&eu_set(), &private(&[840])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::NoMatch)));
    }

    #[test]
    fn witness_rejects_empty_private_nationalities() {
        let p = predicate();
        let err = p.prove(&eu_set(), &private(&[])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::NoMatch)));
    }

    // --- Proof mutation ---

    #[test]
    fn verification_fails_on_mutated_nat_claimed_sum() {
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        proof.nat_claimed_sum = -proof.nat_claimed_sum;
        assert!(matches!(p.verify(&proof), Err(_)));
    }

    #[test]
    fn verification_fails_on_mutated_table_claimed_sum() {
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        proof.table_claimed_sum = -proof.table_claimed_sum;
        assert!(matches!(p.verify(&proof), Err(_)));
    }

    #[test]
    fn verification_fails_on_mutated_acceptable_set() {
        // Replacing one code changes the preprocessed column commitment
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        proof.public.acceptable[0] = 840; // swap FR(250) → US(840)
        assert!(matches!(p.verify(&proof), Err(_)));
    }
}