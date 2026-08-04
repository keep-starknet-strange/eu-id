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
    Error, InputError, PrivateInput, Proof, PublicInput, Witness, MAX_PRESENTED_NATIONALITIES,
};

use crate::nat::nationalities::{is_assigned_iso_alpha2, is_valid_signed_alpha2};
use crate::predicate::{PredicateProver, PredicateVerifier};
use air_core::{prove, verify, Air};
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
        for &code in &public.acceptable {
            if !is_assigned_iso_alpha2(code) {
                return Err(InputError::InvalidNationalityCode(code).into());
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
        for &code in &private.nationalities {
            if !is_valid_signed_alpha2(code) {
                return Err(InputError::InvalidNationalityCode(code).into());
            }
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
            nat_claimed_sum: claimed_sums[0],
            table_claimed_sum: claimed_sums[1],
            stark_proof,
        })
    }

    /// Verify a standalone [`Proof`] of this predicate.
    pub fn verify(&self, proof: &Proof) -> Result<(), Error> {
        let mut verifier = self.verifier_for_private_prefix(
            &proof.public,
            &[proof.nat_claimed_sum, proof.table_claimed_sum],
        )?;
        verify(&mut [&mut verifier], &proof.stark_proof)?;

        Ok(())
    }

    /// Construct a verifier for a private, nonempty signed nationality prefix.
    /// Credential relation balance fixes the private prefix to the signed mdoc
    /// entries without exposing their count as proof metadata.
    pub fn verifier_for_private_prefix(
        &self,
        public: &PublicInput,
        claimed_sums: &[QM31],
    ) -> Result<NatVerifier, Error> {
        self.validate(public)?;
        if claimed_sums.len() != 2 {
            return Err(InputError::InvalidProof.into());
        }
        Ok(NatVerifier::new(public, claimed_sums[0], claimed_sums[1]))
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
        self.verifier_for_private_prefix(public, claimed_sums)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nat::types::InputError;

    fn predicate() -> NationalityPredicate {
        NationalityPredicate::new(PcsConfig::default())
    }

    fn alpha2(code: &[u8; 2]) -> u32 {
        crate::nat::nationalities::pack_alpha2(*code)
    }

    fn eu_set() -> PublicInput {
        PublicInput::new(vec![alpha2(b"DE"), alpha2(b"FR"), alpha2(b"GR")])
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
        let proof = p.prove(&eu_set(), &private(&[alpha2(b"DE")])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_first_matching_nationality_chosen() {
        // prover holds FR and DE. Both are acceptable. FR appears first
        let p = predicate();
        let proof = p
            .prove(&eu_set(), &private(&[alpha2(b"FR"), alpha2(b"DE")]))
            .unwrap();
        p.verify(&proof).unwrap();
        assert_eq!(proof.public.acceptable, eu_set().acceptable);
    }

    #[test]
    fn proves_and_verifies_last_nationality_matches() {
        // only the last nationality is in the acceptable set
        let p = predicate();
        let proof = p
            .prove(&eu_set(), &private(&[alpha2(b"US"), alpha2(b"DE")]))
            .unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_two_entry_acceptable_set() {
        let p = predicate();
        let public = PublicInput::new(vec![alpha2(b"DE"), alpha2(b"GR")]);
        let proof = p.prove(&public, &private(&[alpha2(b"DE")])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_large_acceptable_set() {
        // 249 ISO codes — exercises log_size=8 table
        let p = predicate();
        let all = crate::nat::nationalities::assigned_iso_alpha2_codes()
            .iter()
            .copied()
            .map(crate::nat::nationalities::pack_alpha2)
            .collect();
        let public = PublicInput::new(all);
        let proof = p.prove(&public, &private(&[alpha2(b"DE")])).unwrap();
        p.verify(&proof).unwrap();
    }

    #[test]
    fn public_input_new_sorts_and_deduplicates() {
        let public = PublicInput::new(vec![
            alpha2(b"GR"),
            alpha2(b"DE"),
            alpha2(b"FR"),
            alpha2(b"DE"),
        ]);
        assert_eq!(
            public.acceptable,
            vec![alpha2(b"DE"), alpha2(b"FR"), alpha2(b"GR")]
        );
    }

    #[test]
    fn proves_and_verifies_alpha2_public_input() {
        let p = predicate();
        let public = PublicInput::new(vec![alpha2(b"FR"), alpha2(b"DE")]);

        let proof = p.prove(&public, &private(&[alpha2(b"DE")])).unwrap();

        p.verify(&proof).unwrap();
        assert_eq!(proof.public.acceptable, vec![alpha2(b"DE"), alpha2(b"FR")]);
    }

    #[test]
    fn alpha2_rejects_nationality_not_in_acceptable_set() {
        let p = predicate();
        let public = PublicInput::new(vec![alpha2(b"FR"), alpha2(b"DE")]);
        // Prover holds US, which is a valid alpha-2 code but not accepted.
        let err = p.prove(&public, &private(&[alpha2(b"US")])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::NoMatch)));
    }

    #[test]
    fn validate_rejects_unassigned_public_code() {
        let p = predicate();
        let invalid = alpha2(b"D1");
        let err = p
            .prove(
                &PublicInput::new(vec![alpha2(b"DE"), invalid]),
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
        let public = PublicInput::new(vec![alpha2(b"DE")]);
        let proof = p.prove(&public, &private(&[alpha2(b"DE")])).unwrap();
        p.verify(&proof).unwrap();
        assert_eq!(proof.public.acceptable, vec![alpha2(b"DE")]);
    }

    #[test]
    fn validate_rejects_empty_acceptable_set() {
        let p = predicate();
        let err = p
            .prove(&PublicInput::new(vec![]), &private(&[alpha2(b"DE")]))
            .unwrap_err();
        assert!(matches!(
            err,
            Error::Input(InputError::AcceptableSetTooSmall)
        ));
    }

    #[test]
    fn public_policy_rejects_private_only_and_unassigned_codes() {
        let p = predicate();
        for invalid in [alpha2(b"QU"), alpha2(b"QS"), alpha2(b"XK"), alpha2(b"ZZ")] {
            let err = p
                .prove(
                    &PublicInput::new(vec![alpha2(b"DE"), invalid]),
                    &private(&[alpha2(b"DE")]),
                )
                .unwrap_err();
            assert!(matches!(
                err,
                Error::Input(InputError::InvalidNationalityCode(code)) if code == invalid
            ));
        }
    }

    #[test]
    fn witness_rejects_no_matching_nationality() {
        let p = predicate();
        // US is valid but not in the EU set.
        let err = p.prove(&eu_set(), &private(&[alpha2(b"US")])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::NoMatch)));
    }

    #[test]
    fn witness_rejects_empty_private_nationalities() {
        let p = predicate();
        let err = p.prove(&eu_set(), &private(&[])).unwrap_err();
        assert!(matches!(err, Error::Input(InputError::NoMatch)));
    }

    #[test]
    fn private_user_assigned_codes_are_valid_but_not_policy_members() {
        let p = predicate();
        for signed in [
            vec![alpha2(b"DE"), alpha2(b"QU")],
            vec![alpha2(b"QS"), alpha2(b"DE")],
        ] {
            let proof = p.prove(&eu_set(), &private(&signed)).unwrap();
            p.verify(&proof).unwrap();
        }
    }

    #[test]
    fn fixed_signed_domain_rejects_every_invalid_active_extra() {
        let p = predicate();
        let public = PublicInput::new(vec![alpha2(b"DE")]);
        for invalid in [alpha2(b"zz"), alpha2(b"De"), alpha2(b"ZZ"), alpha2(b"XK")] {
            let forged = Witness {
                public: public.clone(),
                nationalities: vec![alpha2(b"DE"), invalid],
                accepted: vec![true, false],
                accepted_rows: vec![Some(0), None],
            };
            let mut prover = NatProver::new(&public, &forged);
            let stark_proof = prove(&mut [&mut prover], p.pcs_config).unwrap();
            let claimed_sums = prover.claimed_sums();
            let mut verifier = p
                .verifier_for_private_prefix(&public, &claimed_sums)
                .unwrap();
            assert!(
                verify(&mut [&mut verifier], &stark_proof).is_err(),
                "invalid active code {invalid:#06x} must leave the fixed lookup unbalanced"
            );
        }
    }

    // --- Proof mutation ---

    #[test]
    fn verification_fails_on_mutated_nat_claimed_sum() {
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[alpha2(b"DE")])).unwrap();
        proof.nat_claimed_sum = -proof.nat_claimed_sum;
        assert!(p.verify(&proof).is_err());
    }

    #[test]
    fn verification_fails_on_mutated_table_claimed_sum() {
        let p = predicate();
        let mut proof = p.prove(&eu_set(), &private(&[alpha2(b"DE")])).unwrap();
        proof.table_claimed_sum = -proof.table_claimed_sum;
        assert!(p.verify(&proof).is_err());
    }

    #[test]
    fn non_power_of_two_padding_row_cannot_accept_zero() {
        let p = predicate();
        let public = eu_set();
        assert_eq!(public.acceptable.len(), 3);
        let forged = Witness {
            public: public.clone(),
            nationalities: vec![alpha2(b"ZZ")],
            accepted: vec![true],
            accepted_rows: vec![Some(public.acceptable.len())],
        };
        let mut prover = NatProver::new(&public, &forged);
        let stark_proof = prove(&mut [&mut prover], p.pcs_config).unwrap();
        let claimed_sums = prover.claimed_sums();
        let mut verifier = p
            .verifier_for_private_prefix(&public, &claimed_sums)
            .unwrap();
        assert!(
            verify(&mut [&mut verifier], &stark_proof).is_err(),
            "a power-of-two padding row must never act as an accepted nationality"
        );
    }

    /// Confirms that a changed Class-D claimed sum fails verification.
    ///
    /// The claimed sum must match the committed real-row multiplicities.
    #[test]
    fn class_d_blinded_table_balance_tamper_is_rejected() {
        use stwo::core::fields::qm31::QM31;
        let p = predicate();
        // Round-trip through the Class-D blinded NatTable.
        let proof = p.prove(&eu_set(), &private(&[alpha2(b"DE")])).unwrap();
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
        let mut proof = p.prove(&eu_set(), &private(&[alpha2(b"DE")])).unwrap();
        proof.public.acceptable[0] = alpha2(b"US");
        assert!(p.verify(&proof).is_err());
    }
}
