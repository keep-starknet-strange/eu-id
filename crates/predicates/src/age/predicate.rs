use crate::age::types::{
    AgeClaim, AgeInputError, AgeProof, AgeWitness, DateOfBirth, Error, Setup,
    AGE_CONSTRAINT_LOG_DEGREE, DAY_OFFSET_BITS, MONTH_OFFSET_BITS,
};
use crate::predicate::{Predicate, StarkPredicate};
use crate::utils::{push_repeated_bits, push_repeated_column};
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::M31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::verify;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};

pub struct AgePredicate {
    pub pcs_config: PcsConfig,
    pub validate_input: bool,
}

impl AgePredicate {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self {
            pcs_config,
            validate_input: true,
        }
    }

    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self {
            pcs_config,
            validate_input,
        }
    }
}

impl Predicate for AgePredicate {
    type PublicInput = Setup;
    type PrivateInput = DateOfBirth;
    type Witness = AgeWitness;
    type Proof = AgeProof;
    type Error = Error;

    fn validate(&self, public: &Self::PublicInput) -> Result<(), Self::Error> {
        public.bounds.validate()?;

        if !self.validate_input {
            return Ok(());
        }

        public.current.validate(&public.bounds)?;

        if public.min_age_years > public.bounds.max_supported_age_years {
            return Err(AgeInputError::Invalid(format!(
                "age check cannot be for people over {} years old",
                public.bounds.max_supported_age_years
            ))
            .into());
        }

        let cutoff_year = public
            .current
            .year
            .checked_sub(public.min_age_years)
            .ok_or(AgeInputError::Invalid(String::from(
                "current year is smaller than minimum age",
            )))?;

        if cutoff_year < public.bounds.min_supported_year {
            return Err(AgeInputError::Invalid(format!(
                "age check cannot apply to people born before {}",
                public.bounds.min_supported_year
            ))
            .into());
        }

        Ok(())
    }

    fn witness(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Witness, Self::Error> {
        let dob = private.0;

        if self.validate_input {
            dob.validate(&public.bounds)?;
        }

        let cutoff = public.cutoff_date();
        let cutoff_num = cutoff.key();
        let dob_num = dob.key();

        if self.validate_input && dob_num > cutoff_num {
            return Err(AgeInputError::UnderAge.into());
        }

        let slack = cutoff_num - dob_num;
        // Needs to always be validated
        let slack_capacity = 1u64
            .checked_shl(public.bounds.age_slack_bits() as u32)
            .ok_or(AgeInputError::Invalid(String::from(
                "date difference bit-width exceeds supported range",
            )))?;
        if u64::from(slack) >= slack_capacity {
            return Err(AgeInputError::Invalid(String::from(
                "date difference exceeds supported range",
            ))
            .into());
        }

        Ok(AgeWitness {
            setup: public.clone(),
            dob,
            cutoff,
            age_slack: slack,
        })
    }

    fn trace(
        &self,
        witness: &Self::Witness,
    ) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        let bounds = witness.setup.bounds;
        let trace_log_size = bounds.trace_log_size();
        let mut columns = Vec::with_capacity(bounds.trace_columns());

        push_repeated_column(&mut columns, witness.dob.year, trace_log_size);
        push_repeated_column(&mut columns, witness.dob.month, trace_log_size);
        push_repeated_column(&mut columns, witness.dob.day, trace_log_size);
        push_repeated_column(&mut columns, witness.age_slack, trace_log_size);

        let year_offset = witness.dob.year.wrapping_sub(bounds.min_supported_year);
        push_repeated_bits(
            &mut columns,
            year_offset,
            trace_log_size,
            bounds.year_offset_bits(),
        );
        push_repeated_bits(
            &mut columns,
            bounds.year_span().wrapping_sub(year_offset),
            trace_log_size,
            bounds.year_offset_bits(),
        );
        push_repeated_bits(
            &mut columns,
            witness.dob.month.wrapping_sub(1),
            trace_log_size,
            MONTH_OFFSET_BITS,
        );
        push_repeated_bits(
            &mut columns,
            12u32.wrapping_sub(witness.dob.month),
            trace_log_size,
            MONTH_OFFSET_BITS,
        );
        push_repeated_bits(
            &mut columns,
            witness.dob.day.wrapping_sub(1),
            trace_log_size,
            DAY_OFFSET_BITS,
        );
        push_repeated_bits(
            &mut columns,
            31u32.wrapping_sub(witness.dob.day),
            trace_log_size,
            DAY_OFFSET_BITS,
        );
        push_repeated_bits(
            &mut columns,
            witness.age_slack,
            trace_log_size,
            bounds.age_slack_bits(),
        );

        debug_assert_eq!(columns.len(), bounds.trace_columns());

        columns
    }
}

impl StarkPredicate for AgePredicate {
    fn prove(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Proof, Self::Error> {
        self.validate(public)?;

        let witness = self.witness(&public, &private)?;
        let trace = self.trace(&witness);
        let statement = AgeClaim::new(public.clone());

        let channel = &mut Blake2sChannel::default();
        self.pcs_config.mix_into(channel);

        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                public.bounds.trace_log_size()
                    + AGE_CONSTRAINT_LOG_DEGREE
                    + self.pcs_config.fri_config.log_blowup_factor,
            )
            .circle_domain()
            .half_coset,
        );

        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(
                self.pcs_config,
                &twiddles,
            );

        let preprocessed_tree_builder = commitment_scheme.tree_builder();
        preprocessed_tree_builder.commit(channel);

        statement.mix_into(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(trace);
        tree_builder.commit(channel);

        let component = statement.into_component();
        let components: Vec<&dyn ComponentProver<SimdBackend>> = vec![&component];
        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            components.as_slice(),
            channel,
            commitment_scheme,
        )?;

        Ok(AgeProof {
            setup: public.clone(),
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.setup)?;

        let pcs_config = proof.stark_proof.config;
        let claim = AgeClaim::new(proof.setup.clone());
        let channel = &mut Blake2sChannel::default();
        pcs_config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

        commitment_scheme.commit(proof.stark_proof.commitments[0], &[], channel);

        claim.mix_into(channel);
        commitment_scheme.commit(
            proof.stark_proof.commitments[1],
            &vec![claim.log_size; proof.setup.bounds.trace_columns()],
            channel,
        );

        let component = claim.into_component();
        verify(
            &[&component],
            channel,
            commitment_scheme,
            proof.stark_proof.clone(),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::age::types::{AgeBounds, Date, MIN_AGE_TRACE_LOG_SIZE};
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::ProvingError;

    fn setup_today(min_age_years: u32) -> Setup {
        Setup::new(
            Date {
                year: 2026,
                month: 5,
                day: 19,
            },
            min_age_years,
        )
    }

    fn setup_today_with_bounds(min_age_years: u32, bounds: AgeBounds) -> Setup {
        Setup::new_with_bounds(
            Date {
                year: 2026,
                month: 5,
                day: 19,
            },
            min_age_years,
            bounds,
        )
    }

    fn dob(year: u32, month: u32, day: u32) -> DateOfBirth {
        DateOfBirth(Date { year, month, day })
    }

    fn validating_predicate() -> AgePredicate {
        AgePredicate::new(PcsConfig::default())
    }

    fn non_validating_predicate() -> AgePredicate {
        AgePredicate::new_with_input_validation(PcsConfig::default(), false)
    }

    fn assert_input_error(error: Error, expected: impl FnOnce(AgeInputError) -> bool) {
        match error {
            Error::Input(input_error) => assert!(expected(input_error)),
            other => panic!("expected input error, got {other:?}"),
        }
    }

    fn assert_proving_constraints_error(error: Error) {
        match error {
            Error::Proving(ProvingError::ConstraintsNotSatisfied) => {}
            other => panic!("expected proving constraint failure, got {other:?}"),
        }
    }

    #[test]
    fn validate_input_rejects_invalid_current_month() {
        let predicate = validating_predicate();
        let setup = Setup {
            current: Date {
                year: 2026,
                month: 13,
                day: 19,
            },
            min_age_years: 18,
            bounds: Default::default(),
        };

        let error = predicate.prove(&setup, &dob(2000, 1, 1)).unwrap_err();

        assert_input_error(error, |input_error| {
            matches!(input_error, AgeInputError::InvalidMonth(13))
        });
    }

    #[test]
    fn validate_input_rejects_min_age_above_supported_bound() {
        let predicate = validating_predicate();
        let setup = setup_today(AgeBounds::default().max_supported_age_years + 1);

        let error = predicate.prove(&setup, &dob(2000, 1, 1)).unwrap_err();

        assert_input_error(
            error,
            |input_error| matches!(input_error, AgeInputError::Invalid(message) if message.contains("over 150")),
        );
    }

    #[test]
    fn bounds_derive_air_width_from_supported_year_range() {
        let bounds = AgeBounds {
            min_supported_year: 2000,
            max_supported_year: 2031,
            max_supported_age_years: 31,
        };

        assert_eq!(bounds.year_offset_bits(), 5);
        assert_eq!(bounds.age_slack_bits(), 14);
        assert_eq!(bounds.trace_columns(), 46);
        assert_eq!(bounds.trace_log_size(), MIN_AGE_TRACE_LOG_SIZE);
    }

    #[test]
    fn proves_and_verifies_with_custom_supported_bounds() {
        let predicate = validating_predicate();
        let bounds = AgeBounds {
            min_supported_year: 1990,
            max_supported_year: 2030,
            max_supported_age_years: 40,
        };

        let proof = predicate
            .prove(&setup_today_with_bounds(18, bounds), &dob(2008, 5, 19))
            .unwrap();

        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn validate_input_rejects_invalid_supported_bounds() {
        let predicate = validating_predicate();
        let bounds = AgeBounds {
            min_supported_year: 2030,
            max_supported_year: 2020,
            max_supported_age_years: 18,
        };

        let error = predicate
            .prove(&setup_today_with_bounds(18, bounds), &dob(2000, 1, 1))
            .unwrap_err();

        assert_input_error(
            error,
            |input_error| matches!(input_error, AgeInputError::Invalid(message) if message.contains("exceeds max")),
        );
    }

    #[test]
    fn validate_input_rejects_invalid_private_day() {
        let predicate = validating_predicate();

        let error = predicate
            .prove(&setup_today(18), &dob(2000, 1, 32))
            .unwrap_err();

        assert_input_error(error, |input_error| {
            matches!(input_error, AgeInputError::InvalidDay(32))
        });
    }

    #[test]
    fn proves_and_verifies_exactly_minimum_age_today_with_validation() {
        let predicate = validating_predicate();
        let proof = predicate
            .prove(&setup_today(18), &dob(2008, 5, 19))
            .unwrap();

        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_older_than_minimum_age_today_with_validation() {
        let predicate = validating_predicate();
        let proof = predicate
            .prove(&setup_today(18), &dob(2008, 5, 18))
            .unwrap();

        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn validate_input_rejects_under_minimum_age_today() {
        let predicate = validating_predicate();

        let error = predicate
            .prove(&setup_today(18), &dob(2008, 5, 20))
            .unwrap_err();

        assert_input_error(error, |input_error| {
            matches!(input_error, AgeInputError::UnderAge)
        });
    }

    #[test]
    fn no_validation_invalid_month_reaches_prover_and_fails_constraints() {
        let predicate = non_validating_predicate();

        let error = predicate
            .prove(&setup_today(18), &dob(2000, 13, 1))
            .unwrap_err();

        assert_proving_constraints_error(error);
    }

    #[test]
    fn no_validation_invalid_day_reaches_prover_and_fails_constraints() {
        let predicate = non_validating_predicate();

        let error = predicate
            .prove(&setup_today(18), &dob(2000, 1, 32))
            .unwrap_err();

        assert_proving_constraints_error(error);
    }

    #[test]
    fn verification_fails_when_public_input_is_mutated() {
        let predicate = validating_predicate();
        let mut proof = predicate.prove(&setup_today(18), &dob(2000, 1, 1)).unwrap();
        proof.setup.min_age_years = 21;

        let error = predicate.verify(&proof).unwrap_err();

        assert!(matches!(error, Error::Verification(_)));
    }
}
