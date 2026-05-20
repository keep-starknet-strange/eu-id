use crate::age::predicate::AgePredicate;
use crate::age::types::{
    AgeBounds, AgeRangeCheckProof, AgeWitness, DateOfBirth, Error, Setup, DATE_MONTH_BASE,
    DATE_YEAR_BASE,
};
use crate::predicate::{Predicate, StarkPredicate};
use crate::utils::{field_const, push_repeated_column};
use num_traits::{One, Zero};
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::verify;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{prove, CommitmentSchemeProver, ComponentProver};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

const AGE_LOG_SIZE: u32 = 5;
const CONSTRAINT_LOG_DEGREE: u32 = 1;

relation!(SlackRangeElements, 1);

fn slack_log_size(bounds: &AgeBounds) -> u32 {
    (bounds.age_slack_bits() as u32).max(LOG_N_LANES)
}

fn slack_range_col_id(bounds: &AgeBounds) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "age_range_check/slack/{}/{}/{}",
            bounds.min_supported_year, bounds.max_supported_year, bounds.max_supported_age_years
        ),
    }
}

fn mix_setup(setup: &Setup, channel: &mut impl Channel) {
    channel.mix_u64(setup.current.year as u64);
    channel.mix_u64(setup.current.month as u64);
    channel.mix_u64(setup.current.day as u64);
    channel.mix_u64(setup.min_age_years as u64);
    channel.mix_u64(setup.bounds.min_supported_year as u64);
    channel.mix_u64(setup.bounds.max_supported_year as u64);
    channel.mix_u64(setup.bounds.max_supported_age_years as u64);
}

fn gen_preprocessed_trace(
    bounds: &AgeBounds,
) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
    let log_size = slack_log_size(bounds);
    let domain = CanonicCoset::new(log_size).circle_domain();
    let col = BaseColumn::from_iter((0u32..1 << log_size).map(M31::from_u32_unchecked));
    vec![CircleEvaluation::new(domain, col)]
}

fn gen_table_trace(
    witness: &AgeWitness,
) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
    let log_size = slack_log_size(&witness.setup.bounds);
    let n_rows = 1usize << log_size;
    let mut mult = vec![M31::zero(); n_rows];
    mult[witness.age_slack as usize] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
    let domain = CanonicCoset::new(log_size).circle_domain();
    vec![CircleEvaluation::new(
        domain,
        BaseColumn::from_iter(mult.into_iter()),
    )]
}

fn gen_age_interaction_trace(
    age_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
    lookup_elements: &SlackRangeElements,
) -> (Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>, QM31) {
    let log_size = AGE_LOG_SIZE;
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();
    let slack_col = &age_trace[4];
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let slack_val: PackedM31 = slack_col.values.data[vec_row];
        let denom: PackedQM31 = lookup_elements.combine(&[slack_val]);
        col_gen.write_frac(vec_row, PackedQM31::one(), denom);
    }
    col_gen.finalize_col();
    logup_gen.finalize_last()
}

fn gen_table_interaction_trace(
    preproc: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
    table_trace: &[CircleEvaluation<SimdBackend, M31, BitReversedOrder>],
    bounds: &AgeBounds,
    lookup_elements: &SlackRangeElements,
) -> (Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>, QM31) {
    let log_size = slack_log_size(bounds);
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();
    let value_col = &preproc[0];
    let mult_col = &table_trace[0];
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let value: PackedM31 = value_col.values.data[vec_row];
        let mult: PackedM31 = mult_col.values.data[vec_row];
        let denom: PackedQM31 = lookup_elements.combine(&[value]);
        col_gen.write_frac(vec_row, PackedQM31::from(-mult), denom);
    }
    col_gen.finalize_col();
    logup_gen.finalize_last()
}

#[derive(Clone)]
struct SlackRangeTableEval {
    bounds: AgeBounds,
    lookup_elements: SlackRangeElements,
}

impl FrameworkEval for SlackRangeTableEval {
    fn log_size(&self) -> u32 {
        slack_log_size(&self.bounds)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + CONSTRAINT_LOG_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(slack_range_col_id(&self.bounds));
        let mult = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(mult),
            &[value],
        ));
        eval.finalize_logup();
        eval
    }
}

type SlackRangeTableComponent = FrameworkComponent<SlackRangeTableEval>;

#[derive(Clone)]
struct AgeRangeCheckEval {
    setup: Setup,
    lookup_elements: SlackRangeElements,
}

impl FrameworkEval for AgeRangeCheckEval {
    fn log_size(&self) -> u32 {
        AGE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        AGE_LOG_SIZE + CONSTRAINT_LOG_DEGREE
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let birth_day = eval.next_trace_mask();
        let birth_month = eval.next_trace_mask();
        let birth_year = eval.next_trace_mask();
        let birth_packed = eval.next_trace_mask();
        let slack = eval.next_trace_mask();

        eval.add_constraint(
            birth_packed.clone()
                - birth_year.clone() * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
                - birth_month.clone() * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
                - birth_day.clone(),
        );

        let cutoff_key = self.setup.cutoff_date().key();
        eval.add_constraint(slack.clone() - (field_const::<E>(cutoff_key) - birth_packed));

        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[slack],
        ));
        eval.finalize_logup();
        eval
    }
}

type AgeRangeCheckComponent = FrameworkComponent<AgeRangeCheckEval>;

fn make_allocator(bounds: &AgeBounds) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[slack_range_col_id(bounds)])
}

fn make_components(
    allocator: &mut TraceLocationAllocator,
    setup: &Setup,
    lookup_elements: SlackRangeElements,
    age_claimed_sum: QM31,
    table_claimed_sum: QM31,
) -> (AgeRangeCheckComponent, SlackRangeTableComponent) {
    let age_component = AgeRangeCheckComponent::new(
        allocator,
        AgeRangeCheckEval {
            setup: *setup,
            lookup_elements: lookup_elements.clone(),
        },
        age_claimed_sum,
    );
    let table_component = SlackRangeTableComponent::new(
        allocator,
        SlackRangeTableEval {
            bounds: setup.bounds,
            lookup_elements,
        },
        table_claimed_sum,
    );
    (age_component, table_component)
}

pub struct AgeRangeCheck(pub AgePredicate);

impl AgeRangeCheck {
    pub fn new(pcs_config: PcsConfig) -> Self {
        Self(AgePredicate::new(pcs_config))
    }

    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self(AgePredicate::new_with_input_validation(pcs_config, validate_input))
    }
}

impl Predicate for AgeRangeCheck {
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

impl StarkPredicate for AgeRangeCheck {
    type Proof = AgeRangeCheckProof;

    fn trace(
        &self,
        witness: &Self::Witness,
    ) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
        let mut cols = Vec::with_capacity(5);
        push_repeated_column(&mut cols, witness.dob.day, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.month, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.year, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.key(), AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.age_slack, AGE_LOG_SIZE);
        cols
    }

    fn prove(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Proof, Self::Error> {
        self.validate(public)?;
        let witness = self.witness(public, private)?;
        let preproc = gen_preprocessed_trace(&public.bounds);
        let age_trace = self.trace(&witness);
        let table_trace = gen_table_trace(&witness);

        let tbl_log_size = slack_log_size(&public.bounds);
        let max_log_size = tbl_log_size.max(AGE_LOG_SIZE);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                max_log_size
                    + CONSTRAINT_LOG_DEGREE
                    + self.0.pcs_config.fri_config.log_blowup_factor,
            )
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

        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(preproc.clone());
        tb.commit(channel);

        mix_setup(public, channel);

        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(age_trace.clone());
        tb.extend_evals(table_trace.clone());
        tb.commit(channel);

        let lookup_elements = SlackRangeElements::draw(channel);

        let (age_interaction, age_claimed_sum) =
            gen_age_interaction_trace(&age_trace, &lookup_elements);
        let (table_interaction, table_claimed_sum) =
            gen_table_interaction_trace(&preproc, &table_trace, &public.bounds, &lookup_elements);

        channel.mix_felts(&[age_claimed_sum, table_claimed_sum]);

        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(age_interaction);
        tb.extend_evals(table_interaction);
        tb.commit(channel);

        let mut allocator = make_allocator(&public.bounds);
        let (age_component, table_component) = make_components(
            &mut allocator,
            public,
            lookup_elements,
            age_claimed_sum,
            table_claimed_sum,
        );

        let components: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&age_component, &table_component];
        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            components.as_slice(),
            channel,
            commitment_scheme,
        )?;

        Ok(AgeRangeCheckProof {
            setup: *public,
            age_claimed_sum,
            table_claimed_sum,
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.setup)?;

        let pcs_config = proof.stark_proof.config;
        let channel = &mut Blake2sChannel::default();
        pcs_config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

        let tbl_log_size = slack_log_size(&proof.setup.bounds);

        commitment_scheme.commit(proof.stark_proof.commitments[0], &[tbl_log_size], channel);

        mix_setup(&proof.setup, channel);

        let main_sizes: Vec<u32> = std::iter::repeat(AGE_LOG_SIZE)
            .take(5)
            .chain(std::iter::once(tbl_log_size))
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[1], &main_sizes, channel);

        let lookup_elements = SlackRangeElements::draw(channel);

        channel.mix_felts(&[proof.age_claimed_sum, proof.table_claimed_sum]);

        if proof.age_claimed_sum + proof.table_claimed_sum != QM31::zero() {
            return Err(Error::Input(crate::age::types::AgeInputError::Invalid(
                "LogUp claimed sums do not cancel".into(),
            )));
        }

        let tree2_sizes: Vec<u32> = std::iter::repeat(AGE_LOG_SIZE)
            .take(4)
            .chain(std::iter::repeat(tbl_log_size).take(4))
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[2], &tree2_sizes, channel);

        let mut allocator = make_allocator(&proof.setup.bounds);
        let (age_component, table_component) = make_components(
            &mut allocator,
            &proof.setup,
            lookup_elements,
            proof.age_claimed_sum,
            proof.table_claimed_sum,
        );

        verify(
            &[&age_component, &table_component],
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
    use crate::AgeInputError;
    use stwo::core::pcs::PcsConfig;

    fn setup_today(min_age_years: u32) -> Setup {
        Setup::new(Date { year: 2026, month: 5, day: 19 }, min_age_years)
    }

    fn dob(year: u32, month: u32, day: u32) -> DateOfBirth {
        DateOfBirth(Date { year, month, day })
    }

    fn validating_predicate() -> AgeRangeCheck {
        AgeRangeCheck::new(PcsConfig::default())
    }

    fn non_validating_predicate() -> AgeRangeCheck {
        AgeRangeCheck::new_with_input_validation(PcsConfig::default(), false)
    }

    #[test]
    fn proves_and_verifies_exactly_minimum_age() {
        let predicate = validating_predicate();
        let proof = predicate.prove(&setup_today(18), &dob(2008, 5, 19)).unwrap();
        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_older_than_minimum_age() {
        let predicate = validating_predicate();
        let proof = predicate.prove(&setup_today(18), &dob(2008, 5, 18)).unwrap();
        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn proves_and_verifies_with_custom_bounds() {
        let predicate = validating_predicate();
        let bounds = AgeBounds {
            min_supported_year: 1990,
            max_supported_year: 2030,
            max_supported_age_years: 40,
        };
        let proof = predicate
            .prove(
                &Setup::new_with_bounds(
                    Date { year: 2026, month: 5, day: 19 },
                    18,
                    bounds,
                ),
                &dob(2008, 5, 19),
            )
            .unwrap();
        predicate.verify(&proof).unwrap();
    }

    #[test]
    fn validate_rejects_underage() {
        let predicate = validating_predicate();
        let error = predicate.prove(&setup_today(18), &dob(2008, 5, 20)).unwrap_err();
        assert!(matches!(error, Error::Input(AgeInputError::UnderAge)));
    }

    #[test]
    fn no_validation_underage_always_fails_capacity_check() {
        let predicate = non_validating_predicate();
        let error = predicate.prove(&setup_today(18), &dob(2008, 5, 20)).unwrap_err();
        assert!(matches!(error, Error::Input(AgeInputError::Invalid(_))));
    }

    #[test]
    fn verification_fails_on_mutated_setup() {
        let predicate = validating_predicate();
        let mut proof = predicate.prove(&setup_today(18), &dob(2000, 1, 1)).unwrap();
        proof.setup.min_age_years = 21;
        assert!(matches!(predicate.verify(&proof), Err(Error::Verification(_))));
    }
}
