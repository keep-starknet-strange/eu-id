use crate::age::predicate::AgePredicate;
use crate::age::types::{AgeBounds, AgeBitDecompositionProof, Witness, DateOfBirth, Error, PublicInput, Trace, DATE_MONTH_BASE, DATE_YEAR_BASE};
use crate::predicate::{Predicate, StarkPredicate};
use crate::utils::{bit_sum, constrain_bits, field_const, push_repeated_bits, push_repeated_column, read_bits, read_bits_dynamic};
use num_traits::Zero;
use stwo::core::channel::Blake2sChannel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::verify;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator};

pub(crate) const MONTH_OFFSET_BITS: usize = 4;
pub(crate) const DAY_OFFSET_BITS: usize = 5;
pub(crate) const DATE_VALUE_COLUMNS: usize = 4;
pub(crate) const AGE_CONSTRAINT_LOG_DEGREE: u32 = 1;
pub(crate) const LOG_SIZE: u32 = LOG_N_LANES;

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

struct BitDecompositionEval {
    public: PublicInput,
}

impl FrameworkEval for BitDecompositionEval {
    fn log_size(&self) -> u32 {
            LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_SIZE + AGE_CONSTRAINT_LOG_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let dob_year = eval.next_trace_mask();
        let dob_month = eval.next_trace_mask();
        let dob_day = eval.next_trace_mask();
        let age_slack = eval.next_trace_mask();

        let bounds = self.public.bounds;
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

        let cutoff_key = self.public.cutoff_date().key();
        let dob_key = dob_year * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
            + dob_month * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
            + dob_day;

        eval.add_constraint(field_const::<E>(cutoff_key) - dob_key - age_slack);

        eval
    }
}

type AgeComponent = FrameworkComponent<BitDecompositionEval>;

pub struct AgeBitDecomposition(pub AgePredicate);

impl AgeBitDecomposition {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self(AgePredicate::new(pcs_config))
    }

    #[cfg(test)]
    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self(AgePredicate::new_with_input_validation(pcs_config, validate_input))
    }
}

impl Predicate for AgeBitDecomposition {
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

impl StarkPredicate for AgeBitDecomposition {
    type Proof = AgeBitDecompositionProof;

    fn trace(
        &self,
        witness: &Self::Witness,
    ) -> Trace {
        let bounds = witness.public.bounds;
        let log_size = LOG_SIZE;
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

        let channel = &mut Blake2sChannel::default();
        self.0.pcs_config.mix_into(channel);

        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                LOG_SIZE
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

        public.mix_into(channel);

        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(trace);
        tree_builder.commit(channel);

        let component = AgeComponent::new(
            &mut TraceLocationAllocator::default(),
            BitDecompositionEval { public: public.clone() },
            QM31::zero(),
        );
        let components: Vec<&dyn ComponentProver<SimdBackend>> = vec![&component];
        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            components.as_slice(),
            channel,
            commitment_scheme,
        )?;

        Ok(AgeBitDecompositionProof {
            public: public.clone(),
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.public)?;

        let pcs_config = proof.stark_proof.config;
        let channel = &mut Blake2sChannel::default();
        pcs_config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

        commitment_scheme.commit(proof.stark_proof.commitments[0], &[], channel);

        proof.public.mix_into(channel);

        commitment_scheme.commit(
            proof.stark_proof.commitments[1],
            &vec![LOG_SIZE; trace_columns(&proof.public.bounds)],
            channel,
        );

        let component = AgeComponent::new(
            &mut TraceLocationAllocator::default(),
            BitDecompositionEval { public: proof.public.clone() },
            QM31::zero(),
        );
        verify(
            &[&component],
            channel,
            commitment_scheme,
            proof.stark_proof.clone(),
        )?;

        Ok(())
    }
}
