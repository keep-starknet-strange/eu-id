pub mod components;
pub mod eval;
pub mod interaction;
pub mod lookup_elements;
pub mod preprocessed;
pub mod witness;

use crate::age::calendar::{calendar_log_size, valid_date_ranges};
use crate::age::predicate::AgePredicate;
use crate::age::strategy::range_check::components::components;
use crate::age::strategy::range_check::interaction::InteractionTraces;
use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::age::strategy::range_check::witness::WitnessData;
use crate::age::types::{AgeRangeCheckProof, DateOfBirth, Error, PublicInput, Witness};
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
}

impl Predicate for AgeRangeCheck {
    type PublicInput = PublicInput;
    type PrivateInput = DateOfBirth;
    type Witness = Witness;
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

impl StandalonePredicate for AgeRangeCheck {
    type Proof = AgeRangeCheckProof;

    fn prove(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Proof, Self::Error> {
        self.validate(public)?;

        let witness = self.witness(public, private)?;
        let bounds = public.bounds;

        let day_delta_range_check = Preprocessed::day_range();
        let month_delta_range_check = Preprocessed::month_range();
        let year_delta_range_check = Preprocessed::year_range(&bounds);

        // Phase 1: preprocessed tables
        let preprocessed = Preprocessed::new(&bounds);
        let cal_log_size = preprocessed.cal_trace[0].domain.log_size();

        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(cal_log_size + 1 + self.0.pcs_config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );

        let channel = &mut Blake2sChannel::default();
        self.0.pcs_config.mix_into(channel);

        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(
                self.0.pcs_config,
                &twiddles,
            );

        // Tree 0: calendar (2), valid-day (2), day_delta (1), month_delta (1), year_delta (1)
        let mut tb = commitment_scheme.tree_builder();
        preprocessed.extend_evals(&mut tb);
        tb.commit(channel);

        public.mix_into(channel);
        day_delta_range_check.claim().mix_into(channel);
        month_delta_range_check.claim().mix_into(channel);
        year_delta_range_check.claim().mix_into(channel);

        // Phase 2: witness + multiplicity columns
        let witness_data = WitnessData::new(&witness, &preprocessed);

        // Tree 1: 9 witness + 5 multiplicity columns
        let mut tb = commitment_scheme.tree_builder();
        witness_data.extend_evals(&mut tb);
        tb.commit(channel);

        let lookup_elements = LookupElements::draw(channel);

        // Phase 3: interaction traces
        let interaction = InteractionTraces::new(&witness_data, &preprocessed, &lookup_elements);

        interaction.mix_into(channel);

        // Tree 2: age (5 logup cols = 20 M31) + cal (4) + valid_day (4) + day_delta (4) + month_delta (4) + year_delta (4)
        let mut tb = commitment_scheme.tree_builder();
        interaction.extend_evals(&mut tb);
        tb.commit(channel);

        // Phase 4: component assembly
        let (
            age_component,
            cal_component,
            valid_day_component,
            day_delta_component,
            month_delta_component,
            year_delta_component,
        ) = components(
            public,
            lookup_elements,
            interaction.age_claimed_sum,
            interaction.cal_claimed_sum,
            interaction.valid_day_claimed_sum,
            interaction.day_delta_claimed_sum,
            interaction.month_delta_claimed_sum,
            interaction.year_delta_claimed_sum,
        );

        let components: Vec<&dyn ComponentProver<SimdBackend>> = vec![
            &age_component,
            &cal_component,
            &valid_day_component,
            &day_delta_component,
            &month_delta_component,
            &year_delta_component,
        ];
        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            components.as_slice(),
            channel,
            commitment_scheme,
        )?;

        Ok(AgeRangeCheckProof {
            public: *public,
            age_claimed_sum: interaction.age_claimed_sum,
            calendar_table_claimed_sum: interaction.cal_claimed_sum,
            valid_day_table_claimed_sum: interaction.valid_day_claimed_sum,
            day_delta_claimed_sum: interaction.day_delta_claimed_sum,
            month_delta_claimed_sum: interaction.month_delta_claimed_sum,
            year_delta_claimed_sum: interaction.year_delta_claimed_sum,
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.public)?;

        let bounds = proof.public.bounds;
        let day_delta_range_check = Preprocessed::day_range();
        let month_delta_range_check = Preprocessed::month_range();
        let year_delta_range_check = Preprocessed::year_range(&bounds);

        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_date_ranges()[0].domain.log_size();

        let pcs_config = proof.stark_proof.config;
        let channel = &mut Blake2sChannel::default();
        pcs_config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

        // Tree 0: calendar (2), valid-day (2), day_delta (1), month_delta (1), year_delta (1)
        commitment_scheme.commit(
            proof.stark_proof.commitments[0],
            &[
                cal_log_size,
                cal_log_size,
                valid_day_log_size,
                valid_day_log_size,
                day_delta_range_check.log_size(),
                month_delta_range_check.log_size(),
                year_delta_range_check.log_size(),
            ],
            channel,
        );

        proof.public.mix_into(channel);
        day_delta_range_check.claim().mix_into(channel);
        month_delta_range_check.claim().mix_into(channel);
        year_delta_range_check.claim().mix_into(channel);

        // Tree 1: 9 witness + 5 multiplicity columns
        let main_sizes: Vec<u32> = std::iter::repeat_n(WitnessData::log_size(), 9)
            .chain([
                cal_log_size,
                valid_day_log_size,
                day_delta_range_check.log_size(),
                month_delta_range_check.log_size(),
                year_delta_range_check.log_size(),
            ])
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[1], &main_sizes, channel);

        let lookup_elements = LookupElements::draw(channel);

        channel.mix_felts(&[
            proof.age_claimed_sum,
            proof.calendar_table_claimed_sum,
            proof.valid_day_table_claimed_sum,
            proof.day_delta_claimed_sum,
            proof.month_delta_claimed_sum,
            proof.year_delta_claimed_sum,
        ]);

        if proof.age_claimed_sum
            + proof.calendar_table_claimed_sum
            + proof.valid_day_table_claimed_sum
            + proof.day_delta_claimed_sum
            + proof.month_delta_claimed_sum
            + proof.year_delta_claimed_sum
            != QM31::zero()
        {
            return Err(Error::Input(crate::age::types::AgeInputError::Invalid(
                "LogUp claimed sums do not cancel".into(),
            )));
        }

        // Tree 2: age (5 logup cols = 20 M31) + cal (4) + valid_day (4) + day_delta (4) + month_delta (4) + year_delta (4)
        let tree2_sizes: Vec<u32> = std::iter::repeat_n(WitnessData::log_size(), 20)
            .chain(std::iter::repeat_n(cal_log_size, 4))
            .chain(std::iter::repeat_n(valid_day_log_size, 4))
            .chain(std::iter::repeat_n(day_delta_range_check.log_size(), 4))
            .chain(std::iter::repeat_n(month_delta_range_check.log_size(), 4))
            .chain(std::iter::repeat_n(year_delta_range_check.log_size(), 4))
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[2], &tree2_sizes, channel);

        let (
            age_component,
            cal_component,
            valid_day_component,
            day_delta_component,
            month_delta_component,
            year_delta_component,
        ) = components(
            &proof.public,
            lookup_elements,
            proof.age_claimed_sum,
            proof.calendar_table_claimed_sum,
            proof.valid_day_table_claimed_sum,
            proof.day_delta_claimed_sum,
            proof.month_delta_claimed_sum,
            proof.year_delta_claimed_sum,
        );

        verify(
            &[
                &age_component,
                &cal_component,
                &valid_day_component,
                &day_delta_component,
                &month_delta_component,
                &year_delta_component,
            ],
            channel,
            commitment_scheme,
            proof.stark_proof.clone(),
        )?;

        Ok(())
    }
}
