pub mod air;
pub mod components;
pub mod eval;
pub mod interaction;
pub mod lookup_elements;
pub mod nationalities;
pub mod preprocessed;
pub mod table;
pub mod types;
pub mod witness;

use air::{NatProver, NatVerifier};
use types::{Error, InputError, PrivateInput, Proof, PublicInput, Witness};

use crate::air::{prove, verify, Air};
use crate::nat::nationalities::Nationality;
use crate::predicate::{PredicateProver, PredicateVerifier};
use strum::IntoEnumIterator;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;

pub struct NationalityPredicate {
    pub pcs_config: PcsConfig,
}

impl NationalityPredicate {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self { pcs_config }
    }
}

impl NationalityPredicate {
    /// Check the acceptable set is well-formed.
    fn validate(&self, public: &PublicInput) -> Result<(), Error> {
        if public.acceptable.len() < 2 {
            return Err(InputError::AcceptableSetTooSmall.into());
        }
        // Nationality enum variants are ordered by numeric code (iso-preset sorts by code).
        let valid_codes: Vec<u32> = Nationality::iter().map(|n| n as u32).collect();
        for &code in &public.acceptable {
            if valid_codes.binary_search(&code).is_err() {
                return Err(InputError::InvalidNationalityCode(code).into());
            }
        }
        Ok(())
    }

    /// Find the first private nationality that is in the acceptable set.
    fn witness(&self, public: &PublicInput, private: &PrivateInput) -> Result<Witness, Error> {
        for &nat in &private.nationalities {
            if let Ok(row_index) = public.acceptable.binary_search(&nat) {
                return Ok(Witness {
                    public: public.clone(),
                    nationality: nat,
                    nat_index: row_index,
                });
            }
        }
        Err(InputError::NoMatch.into())
    }

    /// Prove this predicate on its own and pack the result into a [`Proof`].
    pub fn prove(&self, public: &PublicInput, private: &PrivateInput) -> Result<Proof, Error> {
        let mut prover = self.prover(public, private)?;
        let stark_proof = prove(&mut [&mut prover], self.pcs_config)?;

        let claimed_sums = prover.claimed_sums();
        Ok(Proof {
            public: public.clone(),
            nat_claimed_sum: claimed_sums[0],
            table_claimed_sum: claimed_sums[1],
            stark_proof,
        })
    }

    /// Verify a standalone [`Proof`] of this predicate.
    pub fn verify(&self, proof: &Proof) -> Result<(), Error> {
        let mut verifier = self.verifier(
            &proof.public,
            &[proof.nat_claimed_sum, proof.table_claimed_sum],
        )?;
        verify(&mut [&mut verifier], &proof.stark_proof)?;

        Ok(())
    }
}

impl PredicateProver for NationalityPredicate {
    type PublicInput = PublicInput;
    type PrivateInput = PrivateInput;
    type Error = Error;
    type Prover = NatProver;

    fn prover(&self, public: &PublicInput, private: &PrivateInput) -> Result<NatProver, Error> {
        self.validate(public)?;
        let witness = self.witness(public, private)?;
        Ok(NatProver::new(public, &witness))
    }
}

impl PredicateVerifier for NationalityPredicate {
    type PublicInput = PublicInput;
    type Error = Error;
    type Verifier = NatVerifier;

    fn verifier(&self, public: &PublicInput, claimed_sums: &[QM31]) -> Result<NatVerifier, Error> {
        self.validate(public)?;
        Ok(NatVerifier::new(public, claimed_sums[0], claimed_sums[1]))
    }
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
        PrivateInput {
            nationalities: codes.to_vec(),
        }
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
        let err = p
            .prove(&PublicInput::new(vec![276]), &private(&[276]))
            .unwrap_err();
        assert!(matches!(
            err,
            Error::Input(InputError::AcceptableSetTooSmall)
        ));
    }

    #[test]
    fn validate_rejects_empty_acceptable_set() {
        let p = predicate();
        let err = p
            .prove(&PublicInput::new(vec![]), &private(&[276]))
            .unwrap_err();
        assert!(matches!(
            err,
            Error::Input(InputError::AcceptableSetTooSmall)
        ));
    }

    #[test]
    fn validate_rejects_non_iso_code_in_acceptable_set() {
        let p = predicate();
        // 1 is not an assigned ISO 3166-1 numeric code
        let err = p
            .prove(&PublicInput::new(vec![276, 1]), &private(&[276]))
            .unwrap_err();
        assert!(matches!(
            err,
            Error::Input(InputError::InvalidNationalityCode(1))
        ));
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
        assert!(p.verify(&proof).is_err());
    }

    #[test]
    fn verification_fails_on_mutated_table_claimed_sum() {
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        proof.table_claimed_sum = -proof.table_claimed_sum;
        assert!(p.verify(&proof).is_err());
    }

    #[test]
    fn verification_fails_on_mutated_acceptable_set() {
        // Replacing one code changes the preprocessed column commitment
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        proof.public.acceptable[0] = 840; // swap FR(250) → US(840)
        assert!(p.verify(&proof).is_err());
    }
}
