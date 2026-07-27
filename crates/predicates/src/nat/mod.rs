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
use types::{
    Error, InputError, PrivateInput, Proof, PublicInput, PublicInputKind, Witness,
    MAX_PRESENTED_NATIONALITIES,
};

use crate::nat::nationalities::Nationality;
use crate::predicate::{PredicateProver, PredicateVerifier};
use air_core::{prove, verify, Air};
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
        if public.acceptable.is_empty() {
            return Err(InputError::AcceptableSetTooSmall.into());
        }
        match public.kind {
            PublicInputKind::IsoNumeric => {
                // Nationality enum variants are ordered by numeric code (iso-preset sorts by code).
                let valid_codes: Vec<u32> = Nationality::iter().map(|n| n as u32).collect();
                for &code in &public.acceptable {
                    if valid_codes.binary_search(&code).is_err() {
                        return Err(InputError::InvalidNationalityCode(code).into());
                    }
                }
            }
            PublicInputKind::Alpha2 => {
                // Each code is two uppercase ASCII letters packed as `256*b0 + b1`.
                for &code in &public.acceptable {
                    let [first, second] = u16::try_from(code)
                        .map(u16::to_be_bytes)
                        .map_err(|_| InputError::InvalidNationalityCode(code))?;
                    if !first.is_ascii_uppercase() || !second.is_ascii_uppercase() {
                        return Err(InputError::InvalidNationalityCode(code).into());
                    }
                }
            }
        }
        Ok(())
    }

    /// Build the complete signed-array witness and mark every accepted entry.
    fn witness(&self, public: &PublicInput, private: &PrivateInput) -> Result<Witness, Error> {
        if private.nationalities.is_empty() {
            return Err(InputError::NoMatch.into());
        }
        if private.nationalities.len() > MAX_PRESENTED_NATIONALITIES {
            return Err(InputError::TooManyNationalities {
                count: private.nationalities.len(),
                max: MAX_PRESENTED_NATIONALITIES,
            }
            .into());
        }
        let accepted_rows: Vec<_> = private
            .nationalities
            .iter()
            .map(|nationality| public.acceptable.binary_search(nationality).ok())
            .collect();
        if accepted_rows.iter().all(Option::is_none) {
            return Err(InputError::NoMatch.into());
        }
        Ok(Witness {
            public: public.clone(),
            nationalities: private.nationalities.clone(),
            accepted: accepted_rows.iter().map(Option::is_some).collect(),
            accepted_rows,
        })
    }

    /// Prove this predicate on its own and pack the result into a [`Proof`].
    pub fn prove(&self, public: &PublicInput, private: &PrivateInput) -> Result<Proof, Error> {
        let mut prover = self.prover(public, private)?;
        let stark_proof = prove(&mut [&mut prover], self.pcs_config)?;

        let claimed_sums = prover.claimed_sums();
        Ok(Proof {
            public: public.clone(),
            nationality_count: u16::try_from(private.nationalities.len())
                .expect("validated nationality count fits u16"),
            nat_claimed_sum: claimed_sums[0],
            table_claimed_sum: claimed_sums[1],
            stark_proof,
        })
    }

    /// Verify a standalone [`Proof`] of this predicate.
    pub fn verify(&self, proof: &Proof) -> Result<(), Error> {
        let mut verifier = self.verifier_with_count(
            &proof.public,
            usize::from(proof.nationality_count),
            &[proof.nat_claimed_sum, proof.table_claimed_sum],
        )?;
        verify(&mut [&mut verifier], &proof.stark_proof)?;

        Ok(())
    }

    /// Construct a verifier for a complete signed nationality array.
    ///
    /// The count is proof metadata, mixed into the transcript and capped here;
    /// when credential binding is enabled, relation balance forces it to equal
    /// the number of entries emitted by the semantic mdoc scope.
    pub fn verifier_with_count(
        &self,
        public: &PublicInput,
        nationality_count: usize,
        claimed_sums: &[QM31],
    ) -> Result<NatVerifier, Error> {
        self.validate(public)?;
        if nationality_count == 0 {
            return Err(InputError::NoMatch.into());
        }
        if nationality_count > MAX_PRESENTED_NATIONALITIES {
            return Err(InputError::TooManyNationalities {
                count: nationality_count,
                max: MAX_PRESENTED_NATIONALITIES,
            }
            .into());
        }
        if claimed_sums.len() != 2 {
            return Err(InputError::InvalidProof.into());
        }
        Ok(NatVerifier::new(
            public,
            nationality_count,
            claimed_sums[0],
            claimed_sums[1],
        ))
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
        // The generic trait predates multi-entry presentations. Standalone and
        // mdoc callers that carry a count use `verifier_with_count`.
        self.verifier_with_count(public, 1, claimed_sums)
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

    // --- Alpha-2 (mdoc) path ---

    fn alpha2(code: &[u8; 2]) -> u32 {
        u32::from(u16::from_be_bytes(*code))
    }

    #[test]
    fn proves_and_verifies_alpha2_public_input() {
        let p = predicate();
        let public = PublicInput::new_alpha2(vec![alpha2(b"FR"), alpha2(b"DE")]);

        let proof = p.prove(&public, &private(&[alpha2(b"DE")])).unwrap();

        p.verify(&proof).unwrap();
        assert_eq!(proof.public.acceptable, vec![alpha2(b"DE"), alpha2(b"FR")]);
    }

    #[test]
    fn alpha2_rejects_nationality_not_in_acceptable_set() {
        let p = predicate();
        let public = PublicInput::new_alpha2(vec![alpha2(b"FR"), alpha2(b"DE")]);
        // Prover holds US, which is a valid alpha-2 code but not accepted.
        let err = p.prove(&public, &private(&[alpha2(b"US")])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::NoMatch)));
    }

    #[test]
    fn validate_rejects_non_alpha2_code_in_alpha2_mode() {
        let p = predicate();
        let invalid = alpha2(b"D1");
        let err = p
            .prove(
                &PublicInput::new_alpha2(vec![alpha2(b"DE"), invalid]),
                &private(&[alpha2(b"DE")]),
            )
            .unwrap_err();

        assert!(matches!(
            err,
            Error::Input(InputError::InvalidNationalityCode(code)) if code == invalid
        ));
    }

    // --- Error cases ---

    #[test]
    fn proves_and_verifies_singleton_acceptable_set() {
        let p = predicate();
        let public = PublicInput::new(vec![276]);
        let proof = p.prove(&public, &private(&[276])).unwrap();
        p.verify(&proof).unwrap();
        assert_eq!(proof.public.acceptable, vec![276]);
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
    fn verification_fails_on_mutated_nationality_count() {
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[840, 276])).unwrap();
        proof.nationality_count = 1;
        assert!(
            p.verify(&proof).is_err(),
            "the complete signed-array length is transcript-bound"
        );
    }

    /// Class-D balance-tamper (Q-015 §4b): the blinded accepted-set table's
    /// contribution to the global LogUp balance is load-bearing. A round-trip
    /// through the blinded table verifies; shifting the blinded table's claimed
    /// sum by any nonzero amount breaks the balance and the verifier rejects.
    /// This proves the dummy-region cancelling twin holds the balance rather than
    /// leaving free slack a prover could exploit.
    #[test]
    fn class_d_blinded_table_balance_tamper_is_rejected() {
        use stwo::core::fields::qm31::QM31;
        let p = predicate();
        // Round-trip through the Class-D blinded NatTable.
        let proof = p.prove(&eu_set(), &private(&[276])).unwrap();
        p.verify(&proof).expect("blinded-table round-trip verifies");

        // Shift the blinded table's claimed sum by a nonzero delta.
        let mut tampered = proof;
        tampered.table_claimed_sum += QM31::from_u32_unchecked(1, 0, 0, 0);
        assert!(
            p.verify(&tampered).is_err(),
            "a shifted blinded-table claimed sum must break the balance"
        );
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
