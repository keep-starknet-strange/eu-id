use crate::age::calendar::{calendar_log_size, generate_max_days_per_month, valid_date_ranges};
use crate::age::predicate::AgePredicate;
use crate::age::types::{AgeBounds, AgeRangeCheckProof, DateOfBirth, Error, PublicInput, Trace, Witness, DATE_MONTH_BASE, DATE_YEAR_BASE};
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
    public: PublicInput,
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

        let cutoff_key = self.public.cutoff_date().key();
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
    public: &PublicInput,
    lookup_elements: SlackRangeElements,
    age_claimed_sum: QM31,
    table_claimed_sum: QM31,
) -> (AgeRangeCheckComponent, SlackRangeTableComponent) {
    let age_component = AgeRangeCheckComponent::new(
        allocator,
        AgeRangeCheckEval {
            public: *public,
            lookup_elements: lookup_elements.clone(),
        },
        age_claimed_sum,
    );
    let table_component = SlackRangeTableComponent::new(
        allocator,
        SlackRangeTableEval {
            bounds: public.bounds,
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

    #[cfg(test)]
    pub(crate) fn new_with_input_validation(pcs_config: PcsConfig, validate_input: bool) -> Self {
        Self(AgePredicate::new_with_input_validation(pcs_config, validate_input))
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

impl StarkPredicate for AgeRangeCheck {
    type Proof = AgeRangeCheckProof;

    fn trace(
        &self,
        witness: &Self::Witness,
    ) -> Trace {
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

        // Organize the witness from public and private inputs
        let witness = self.witness(public, private)?;
        let slack_possible_values_log_size = slack_log_size(&witness.public.bounds);
        let slack_rows = 1 << slack_possible_values_log_size;

        // Generate all possible slack values [0, 2^age_slack_log_size) in a trace col
        let domain = CanonicCoset::new(slack_possible_values_log_size).circle_domain();
        let col = BaseColumn::from_iter((0..slack_rows).map(M31::from_u32_unchecked));
        let slack_values_trace: Trace = vec![CircleEvaluation::new(domain, col)];

        // Accumulate all original witness trace (In this case every row is the same)
        let witness_trace: Trace = self.trace(&witness);

        // Multiplicity table. Since witness trace is repeated over AGE_TRACE_SIZE (32) rows, then slack
        // is "multiplied" 32 times. Thus, mult[slack] = 32; where `mult` is a column of size `slack_rows`
        let mut mult = vec![M31::zero(); slack_rows as usize];
        mult[witness.age_slack as usize] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let domain = CanonicCoset::new(slack_possible_values_log_size).circle_domain();
        let slack_multiplicity_trace: Trace = vec![CircleEvaluation::new(
            domain,
            BaseColumn::from_iter(mult.into_iter()),
        )];

        let cal_log_size = calendar_log_size(&public.bounds);
        let max_log_size = slack_possible_values_log_size.max(AGE_LOG_SIZE).max(cal_log_size);
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

        // 1. Commit the preprocessed table of all possible slack values + calendar tables
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(slack_values_trace.clone());
        tb.extend_evals(generate_max_days_per_month(public.bounds));
        tb.extend_evals(valid_date_ranges());
        tb.commit(channel);

        // 2. Mix public input
        public.mix_into(channel);

        // 3. Commit the witness and slack multiplicity traces
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(witness_trace.clone());
        tb.extend_evals(slack_multiplicity_trace.clone());
        tb.commit(channel);

        // 4. Interaction traces
        let lookup_elements = SlackRangeElements::draw(channel);

        // - Interaction for slack appearing once in all trace rows
        let mut logup_gen = LogupTraceGenerator::new(AGE_LOG_SIZE);
        let mut col_gen = logup_gen.new_col();
        let slack_col = &witness_trace[4]; // Get the slack column
        for packed_row_index in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) { // Iterate over 2 packed fields of slack witness
            let slack_val: PackedM31 = slack_col.values.data[packed_row_index];
            col_gen.write_frac(
                packed_row_index,
                PackedQM31::one(),
                lookup_elements.combine(&[slack_val])
            );
        }
        col_gen.finalize_col();
        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

        // - Interaction of what slack appearing in the range of possible values
        let mut logup_gen = LogupTraceGenerator::new(slack_possible_values_log_size);
        let mut col_gen = logup_gen.new_col();
        let value_col = &slack_values_trace[0];
        let mult_col = &slack_multiplicity_trace[0];
        for vec_row in 0..(1 << (slack_possible_values_log_size - LOG_N_LANES)) {
            let value: PackedM31 = value_col.values.data[vec_row];
            let mult: PackedM31 = mult_col.values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                lookup_elements.combine(&[value])
            );
        }
        col_gen.finalize_col();
        let (table_interaction, table_claimed_sum) = logup_gen.finalize_last();

        channel.mix_felts(&[age_claimed_sum, table_claimed_sum]);

        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(age_interaction);
        tb.extend_evals(table_interaction);
        tb.commit(channel);

        // 5. Prove
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
            public: *public,
            age_claimed_sum,
            table_claimed_sum,
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

        let tbl_log_size = slack_log_size(&proof.public.bounds);

        let cal_log_size = calendar_log_size(&proof.public.bounds);
        let vdr_log_size = valid_date_ranges()[0].domain.log_size();
        commitment_scheme.commit(
            proof.stark_proof.commitments[0],
            &[tbl_log_size, cal_log_size, vdr_log_size, vdr_log_size],
            channel,
        );

        proof.public.mix_into(channel);

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

        let mut allocator = make_allocator(&proof.public.bounds);
        let (age_component, table_component) = make_components(
            &mut allocator,
            &proof.public,
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
