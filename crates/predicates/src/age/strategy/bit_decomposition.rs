use crate::age::predicate::AgePredicate;
use crate::age::types::{
    AgeBounds, AgeProof, AgeWitness, DateOfBirth, Error, Setup,
    DATE_MONTH_BASE, DATE_YEAR_BASE,
};
use crate::predicate::{Predicate, StarkPredicate};
use crate::utils::{
    bit_sum, constrain_bits, field_const, push_repeated_bits, push_repeated_column, read_bits,
    read_bits_dynamic,
};
use num_traits::Zero;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::verify;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator};

pub(crate) const MONTH_OFFSET_BITS: usize = 4;
pub(crate) const DAY_OFFSET_BITS: usize = 5;
pub(crate) const DATE_VALUE_COLUMNS: usize = 4;
pub(crate) const AGE_CONSTRAINT_LOG_DEGREE: u32 = 1;
pub(crate) const MIN_AGE_TRACE_LOG_SIZE: u32 = 5;

pub(crate) fn trace_columns(bounds: &AgeBounds) -> usize {
    DATE_VALUE_COLUMNS
        + bounds.year_offset_bits()
        + bounds.year_offset_bits()
        + MONTH_OFFSET_BITS
        + MONTH_OFFSET_BITS
        + DAY_OFFSET_BITS
        + DAY_OFFSET_BITS
        + bounds.age_slack_bits()
}

pub(crate) fn trace_log_size() -> u32 {
    MIN_AGE_TRACE_LOG_SIZE
}

// ---------------------------------------------------------------------------
// AgeClaim — the AIR component for bit-decomposition age proofs
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub(crate) struct AgeClaim {
    pub(crate) setup: Setup,
    pub(crate) log_size: u32,
}

impl AgeClaim {
    pub(crate) fn new(setup: Setup) -> Self {
        Self {
            log_size: trace_log_size(),
            setup,
        }
    }

    pub(crate) fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.setup.current.year as u64);
        channel.mix_u64(self.setup.current.month as u64);
        channel.mix_u64(self.setup.current.day as u64);
        channel.mix_u64(self.setup.min_age_years as u64);
        channel.mix_u64(self.setup.bounds.min_supported_year as u64);
        channel.mix_u64(self.setup.bounds.max_supported_year as u64);
        channel.mix_u64(self.setup.bounds.max_supported_age_years as u64);
        channel.mix_u64(self.log_size as u64);
    }

    pub(crate) fn into_component(self) -> AgeComponent {
        AgeComponent::new(
            &mut TraceLocationAllocator::default(),
            self.clone(),
            QM31::zero(),
        )
    }
}

impl FrameworkEval for AgeClaim {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + AGE_CONSTRAINT_LOG_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let dob_year = eval.next_trace_mask();
        let dob_month = eval.next_trace_mask();
        let dob_day = eval.next_trace_mask();
        let age_slack = eval.next_trace_mask();

        let bounds = self.setup.bounds;
        let year_offset_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let year_bound_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let month_offset_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let month_bound_slack_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let day_offset_bits = read_bits::<E, DAY_OFFSET_BITS>(&mut eval);
        let day_bound_slack_bits = read_bits::<E, DAY_OFFSET_BITS>(&mut eval);
        let age_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.age_slack_bits());

        constrain_bits(&mut eval, &year_offset_bits);
        constrain_bits(&mut eval, &year_bound_slack_bits);
        constrain_bits(&mut eval, &month_offset_bits);
        constrain_bits(&mut eval, &month_bound_slack_bits);
        constrain_bits(&mut eval, &day_offset_bits);
        constrain_bits(&mut eval, &day_bound_slack_bits);
        constrain_bits(&mut eval, &age_slack_bits);

        let year_offset = bit_sum::<E>(&year_offset_bits);
        let year_bound_slack = bit_sum::<E>(&year_bound_slack_bits);
        let month_offset = bit_sum::<E>(&month_offset_bits);
        let month_bound_slack = bit_sum::<E>(&month_bound_slack_bits);
        let day_offset = bit_sum::<E>(&day_offset_bits);
        let day_bound_slack = bit_sum::<E>(&day_bound_slack_bits);
        let age_slack_from_bits = bit_sum::<E>(&age_slack_bits);

        eval.add_constraint(
            dob_year.clone() - field_const::<E>(bounds.min_supported_year) - year_offset.clone(),
        );
        eval.add_constraint(field_const::<E>(bounds.year_span()) - year_offset - year_bound_slack);
        eval.add_constraint(dob_month.clone() - field_const::<E>(1) - month_offset.clone());
        eval.add_constraint(field_const::<E>(11) - month_offset - month_bound_slack);
        eval.add_constraint(dob_day.clone() - field_const::<E>(1) - day_offset.clone());
        eval.add_constraint(field_const::<E>(30) - day_offset - day_bound_slack);
        eval.add_constraint(age_slack.clone() - age_slack_from_bits);

        let cutoff_key = self.setup.cutoff_date().key();
        let dob_key = dob_year * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
            + dob_month * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
            + dob_day;

        eval.add_constraint(field_const::<E>(cutoff_key) - dob_key - age_slack);

        eval
    }
}

type AgeComponent = FrameworkComponent<AgeClaim>;

pub struct AgeBitDecomposition(pub AgePredicate);

impl AgeBitDecomposition {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self(AgePredicate::new(pcs_config))
    }

    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self(AgePredicate::new_with_input_validation(pcs_config, validate_input))
    }
}

impl Predicate for AgeBitDecomposition {
    type PublicInput = Setup;
    type PrivateInput = DateOfBirth;
    type Witness = AgeWitness;
    type Error = Error;

    fn validate(&self, public: &Self::PublicInput) -> Result<(), Self::Error> {
        self.0.validate(public)
    }

    fn witness(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Witness, Self::Error> {
        self.0.witness(public, private)
    }
}

impl StarkPredicate for AgeBitDecomposition {
    type Proof = AgeProof;

    fn trace(
        &self,
        witness: &Self::Witness,
    ) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        let bounds = witness.setup.bounds;
        let log_size = trace_log_size();
        let mut columns = Vec::with_capacity(trace_columns(&bounds));

        push_repeated_column(&mut columns, witness.dob.year, log_size);
        push_repeated_column(&mut columns, witness.dob.month, log_size);
        push_repeated_column(&mut columns, witness.dob.day, log_size);
        push_repeated_column(&mut columns, witness.age_slack, log_size);

        let year_offset = witness.dob.year.wrapping_sub(bounds.min_supported_year);
        push_repeated_bits(&mut columns, year_offset, log_size, bounds.year_offset_bits());
        push_repeated_bits(
            &mut columns,
            bounds.year_span().wrapping_sub(year_offset),
            log_size,
            bounds.year_offset_bits(),
        );
        push_repeated_bits(&mut columns, witness.dob.month.wrapping_sub(1), log_size, MONTH_OFFSET_BITS);
        push_repeated_bits(&mut columns, 12u32.wrapping_sub(witness.dob.month), log_size, MONTH_OFFSET_BITS);
        push_repeated_bits(&mut columns, witness.dob.day.wrapping_sub(1), log_size, DAY_OFFSET_BITS);
        push_repeated_bits(&mut columns, 31u32.wrapping_sub(witness.dob.day), log_size, DAY_OFFSET_BITS);
        push_repeated_bits(&mut columns, witness.age_slack, log_size, bounds.age_slack_bits());

        debug_assert_eq!(columns.len(), trace_columns(&bounds));

        columns
    }

    fn prove(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Proof, Self::Error> {
        self.validate(public)?;

        let witness = self.witness(public, private)?;
        let trace = self.trace(&witness);
        let statement = AgeClaim::new(public.clone());

        let channel = &mut Blake2sChannel::default();
        self.0.pcs_config.mix_into(channel);

        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                trace_log_size()
                    + AGE_CONSTRAINT_LOG_DEGREE
                    + self.0.pcs_config.fri_config.log_blowup_factor,
            )
            .circle_domain()
            .half_coset,
        );

        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(
                self.0.pcs_config,
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
            &vec![claim.log_size; trace_columns(&proof.setup.bounds)],
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
    use crate::age::types::{AgeBounds, Date};
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::ProvingError;
    use crate::AgeInputError;

    fn setup_today(min_age_years: u32) -> Setup {
        Setup::new(
            Date { year: 2026, month: 5, day: 19 },
            min_age_years,
        )
    }

    fn setup_today_with_bounds(min_age_years: u32, bounds: AgeBounds) -> Setup {
        Setup::new_with_bounds(
            Date { year: 2026, month: 5, day: 19 },
            min_age_years,
            bounds,
        )
    }

    fn dob(year: u32, month: u32, day: u32) -> DateOfBirth {
        DateOfBirth(Date { year, month, day })
    }

    fn validating_predicate() -> AgeBitDecomposition {
        AgeBitDecomposition::new(PcsConfig::default())
    }

    fn non_validating_predicate() -> AgeBitDecomposition {
        AgeBitDecomposition::new_with_input_validation(PcsConfig::default(), false)
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
        let setup = Setup::new(Date { year: 2026, month: 13, day: 19 }, 18);

        let error = predicate.prove(&setup, &dob(2000, 1, 1)).unwrap_err();

        assert_input_error(error, |e| matches!(e, AgeInputError::InvalidMonth(13)));
    }

    #[test]
    fn validate_input_rejects_min_age_above_supported_bound() {
        let predicate = validating_predicate();
        let bounds = AgeBounds::new(Date { year: 2026, month: 12, day: 19 }, 18);
        let setup = Setup::new_with_bounds(
            Date { year: 2026, month: 5, day: 19 },
            bounds.max_supported_age_years + 1,
            bounds,
        );

        let error = predicate.prove(&setup, &dob(2000, 1, 1)).unwrap_err();

        assert_input_error(
            error,
            |e| matches!(e, AgeInputError::Invalid(m) if m.contains("over 18")),
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
        assert_eq!(trace_columns(&bounds), 46);
        assert_eq!(trace_log_size(), MIN_AGE_TRACE_LOG_SIZE);
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
            |e| matches!(e, AgeInputError::Invalid(m) if m.contains("exceeds max")),
        );
    }

    #[test]
    fn validate_input_rejects_invalid_private_day() {
        let predicate = validating_predicate();

        let error = predicate.prove(&setup_today(18), &dob(2000, 1, 32)).unwrap_err();

        assert_input_error(error, |e| matches!(e, AgeInputError::InvalidDay(32)));
    }

    #[test]
    fn proves_and_verifies_exactly_minimum_age_today_with_validation() {
        let predicate = validating_predicate();
        let proof = predicate.prove(&setup_today(18), &dob(2008, 5, 19)).unwrap();
        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_older_than_minimum_age_today_with_validation() {
        let predicate = validating_predicate();
        let proof = predicate.prove(&setup_today(18), &dob(2008, 5, 18)).unwrap();
        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn validate_input_rejects_under_minimum_age_today() {
        let predicate = validating_predicate();

        let error = predicate.prove(&setup_today(18), &dob(2008, 5, 20)).unwrap_err();

        assert_input_error(error, |e| matches!(e, AgeInputError::UnderAge));
    }

    #[test]
    fn no_validation_invalid_month_reaches_prover_and_fails_constraints() {
        let predicate = non_validating_predicate();

        let error = predicate.prove(&setup_today(18), &dob(2000, 13, 1)).unwrap_err();

        assert_proving_constraints_error(error);
    }

    #[test]
    fn no_validation_invalid_day_reaches_prover_and_fails_constraints() {
        let predicate = non_validating_predicate();

        let error = predicate.prove(&setup_today(18), &dob(2000, 1, 32)).unwrap_err();

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
