use crate::age::calendar::{
    calendar_index_col_id, calendar_log_size, calendar_max_days_col_id, generate_max_days_per_month,
    max_days_at, valid_date_ranges, valid_day_day_col_id, valid_day_max_days_col_id,
    valid_day_row_index, CalendarElements, CalendarTableEval, ValidDayElements, ValidDayTableEval,
};
use crate::age::predicate::AgePredicate;
use crate::age::types::{
    AgeBounds, AgeRangeCheckProof, DateOfBirth, Error, PublicInput, Trace, Witness,
    DATE_MONTH_BASE, DATE_YEAR_BASE,
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
type CalendarTableComponent = FrameworkComponent<CalendarTableEval>;
type ValidDayTableComponent = FrameworkComponent<ValidDayTableEval>;

#[derive(Clone)]
struct AgeRangeCheckEval {
    public: PublicInput,
    slack_elements: SlackRangeElements,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
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
        let max_days = eval.next_trace_mask();

        eval.add_constraint(
            birth_packed.clone()
                - birth_year.clone() * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
                - birth_month.clone() * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
                - birth_day.clone(),
        );

        let cutoff_key = self.public.cutoff_date().key();
        eval.add_constraint(slack.clone() - (field_const::<E>(cutoff_key) - birth_packed));

        eval.add_to_relation(RelationEntry::new(
            &self.slack_elements,
            E::EF::one(),
            &[slack],
        ));

        let bounds = self.public.bounds;
        let table_index = (birth_year - field_const::<E>(bounds.min_supported_year))
            * BaseField::from_u32_unchecked(12)
            + birth_month
            - field_const::<E>(1);
        eval.add_to_relation(RelationEntry::new(
            &self.calendar_elements,
            E::EF::one(),
            &[table_index, max_days.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.valid_day_elements,
            E::EF::one(),
            &[max_days, birth_day],
        ));

        eval.finalize_logup();
        eval
    }
}

type AgeRangeCheckComponent = FrameworkComponent<AgeRangeCheckEval>;

fn make_allocator(bounds: &AgeBounds) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[
        slack_range_col_id(bounds),
        calendar_max_days_col_id(bounds),
        calendar_index_col_id(bounds),
        valid_day_max_days_col_id(),
        valid_day_day_col_id(),
    ])
}

fn make_components(
    allocator: &mut TraceLocationAllocator,
    public: &PublicInput,
    slack_elements: SlackRangeElements,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
    age_claimed_sum: QM31,
    slack_claimed_sum: QM31,
    cal_claimed_sum: QM31,
    valid_day_claimed_sum: QM31,
) -> (AgeRangeCheckComponent, SlackRangeTableComponent, CalendarTableComponent, ValidDayTableComponent) {
    let age_component = AgeRangeCheckComponent::new(
        allocator,
        AgeRangeCheckEval {
            public: *public,
            slack_elements: slack_elements.clone(),
            calendar_elements: calendar_elements.clone(),
            valid_day_elements: valid_day_elements.clone(),
        },
        age_claimed_sum,
    );
    let slack_component = SlackRangeTableComponent::new(
        allocator,
        SlackRangeTableEval { bounds: public.bounds, lookup_elements: slack_elements },
        slack_claimed_sum,
    );
    let cal_component = CalendarTableComponent::new(
        allocator,
        CalendarTableEval { bounds: public.bounds, lookup_elements: calendar_elements },
        cal_claimed_sum,
    );
    let valid_day_component = ValidDayTableComponent::new(
        allocator,
        ValidDayTableEval { lookup_elements: valid_day_elements },
        valid_day_claimed_sum,
    );
    (age_component, slack_component, cal_component, valid_day_component)
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

    fn trace(&self, witness: &Self::Witness) -> Trace {
        let mut cols = Vec::with_capacity(6);
        push_repeated_column(&mut cols, witness.dob.day, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.month, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.year, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.key(), AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.age_slack, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, max_days_at(witness.dob.month, witness.dob.year), AGE_LOG_SIZE);
        cols
    }

    fn prove(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Proof, Self::Error> {
        self.validate(public)?;

        let witness = self.witness(public, private)?;
        let bounds = public.bounds;

        let dob_max_days = max_days_at(witness.dob.month, witness.dob.year);
        let table_index = (witness.dob.year - bounds.min_supported_year) * 12 + witness.dob.month - 1;
        let valid_day_row = valid_day_row_index(dob_max_days, witness.dob.day);

        let slack_log_size = slack_log_size(&bounds);
        let slack_rows = 1 << slack_log_size;
        let cal_trace = generate_max_days_per_month(bounds);
        let valid_day_trace = valid_date_ranges();
        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_day_trace[0].domain.log_size();

        // All possible slack values
        let domain = CanonicCoset::new(slack_log_size).circle_domain();
        let slack_values_trace: Trace = vec![CircleEvaluation::new(
            domain,
            BaseColumn::from_iter((0..slack_rows).map(M31::from_u32_unchecked)),
        )];

        let witness_trace = self.trace(&witness);

        // Multiplicity for slack table
        let mut slack_mult = vec![M31::zero(); slack_rows as usize];
        slack_mult[witness.age_slack as usize] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let slack_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(slack_log_size).circle_domain(),
            BaseColumn::from_iter(slack_mult.into_iter()),
        )];

        // Multiplicity for calendar table
        let cal_total = 1 << cal_log_size;
        let mut cal_mult_data = vec![M31::zero(); cal_total];
        cal_mult_data[table_index as usize] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let cal_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(cal_log_size).circle_domain(),
            BaseColumn::from_iter(cal_mult_data.into_iter()),
        )];

        // Multiplicity for valid-day table
        let valid_day_total = 1 << valid_day_log_size;
        let mut valid_day_mult_data = vec![M31::zero(); valid_day_total];
        valid_day_mult_data[valid_day_row] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let valid_day_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(valid_day_log_size).circle_domain(),
            BaseColumn::from_iter(valid_day_mult_data.into_iter()),
        )];

        let max_log_size = slack_log_size.max(AGE_LOG_SIZE).max(cal_log_size);
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

        // Preprocessed (slack values, calendar (2 cols), valid-day (2 cols))
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(slack_values_trace.clone());
        tb.extend_evals(cal_trace.clone());
        tb.extend_evals(valid_day_trace.clone());
        tb.commit(channel);

        public.mix_into(channel);

        // Witness (Original + multiplicity cols for slack, calendar, valid day)
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(witness_trace.clone());
        tb.extend_evals(slack_mult_trace.clone());
        tb.extend_evals(cal_mult_trace.clone());
        tb.extend_evals(valid_day_mult_trace.clone());
        tb.commit(channel);

        let slack_elements = SlackRangeElements::draw(channel);
        let calendar_elements = CalendarElements::draw(channel);
        let valid_day_elements = ValidDayElements::draw(channel);

        // Age component interaction: 3 logup fractions (slack, calendar, valid-day)
        let mut logup_gen = LogupTraceGenerator::new(AGE_LOG_SIZE);

        let mut col_gen = logup_gen.new_col();
        let slack_col = &witness_trace[4];
        for packed_row in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) {
            let slack_val: PackedM31 = slack_col.values.data[packed_row];
            col_gen.write_frac(packed_row, PackedQM31::one(), slack_elements.combine(&[slack_val]));
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                calendar_elements.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(table_index)),
                    PackedM31::broadcast(M31::from_u32_unchecked(dob_max_days)),
                ]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                valid_day_elements.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(dob_max_days)),
                    PackedM31::broadcast(M31::from_u32_unchecked(witness.dob.day)),
                ]),
            );
        }
        col_gen.finalize_col();
        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

        // Slack table interaction
        let mut logup_gen = LogupTraceGenerator::new(slack_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (slack_log_size - LOG_N_LANES)) {
            let value: PackedM31 = slack_values_trace[0].values.data[vec_row];
            let mult: PackedM31 = slack_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(vec_row, PackedQM31::from(-mult), slack_elements.combine(&[value]));
        }
        col_gen.finalize_col();
        let (slack_interaction, slack_claimed_sum) = logup_gen.finalize_last();

        // Calendar table interaction
        let mut logup_gen = LogupTraceGenerator::new(cal_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (cal_log_size - LOG_N_LANES)) {
            let max_days_val: PackedM31 = cal_trace[0].values.data[vec_row];
            let index_val: PackedM31 = cal_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = cal_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                calendar_elements.combine(&[index_val, max_days_val]),
            );
        }
        col_gen.finalize_col();
        let (cal_interaction, cal_claimed_sum) = logup_gen.finalize_last();

        // Valid-day table interaction
        let mut logup_gen = LogupTraceGenerator::new(valid_day_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (valid_day_log_size - LOG_N_LANES)) {
            let max_days_val: PackedM31 = valid_day_trace[0].values.data[vec_row];
            let day_val: PackedM31 = valid_day_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = valid_day_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                valid_day_elements.combine(&[max_days_val, day_val]),
            );
        }
        col_gen.finalize_col();
        let (valid_day_interaction, valid_day_claimed_sum) = logup_gen.finalize_last();

        channel.mix_felts(&[age_claimed_sum, slack_claimed_sum, cal_claimed_sum, valid_day_claimed_sum]);

        // Interaction traces
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(age_interaction);
        tb.extend_evals(slack_interaction);
        tb.extend_evals(cal_interaction);
        tb.extend_evals(valid_day_interaction);
        tb.commit(channel);

        let mut allocator = make_allocator(&bounds);
        let (age_component, slack_component, cal_component, valid_day_component) = make_components(
            &mut allocator,
            public,
            slack_elements,
            calendar_elements,
            valid_day_elements,
            age_claimed_sum,
            slack_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
        );

        let components: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&age_component, &slack_component, &cal_component, &valid_day_component];
        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            components.as_slice(),
            channel,
            commitment_scheme,
        )?;

        Ok(AgeRangeCheckProof {
            public: *public,
            age_claimed_sum,
            slack_table_claimed_sum: slack_claimed_sum,
            calendar_table_claimed_sum: cal_claimed_sum,
            valid_day_table_claimed_sum: valid_day_claimed_sum,
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.public)?;

        let bounds = proof.public.bounds;
        let tbl_log_size = slack_log_size(&bounds);
        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_date_ranges()[0].domain.log_size();

        let pcs_config = proof.stark_proof.config;
        let channel = &mut Blake2sChannel::default();
        pcs_config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

        // Tree 0: slack values (1), calendar (2), valid-day (2)
        commitment_scheme.commit(
            proof.stark_proof.commitments[0],
            &[tbl_log_size, cal_log_size, cal_log_size, valid_day_log_size, valid_day_log_size],
            channel,
        );

        proof.public.mix_into(channel);

        // Tree 1: 6 witness cols + slack mult + cal mult + vdr mult
        let main_sizes: Vec<u32> = std::iter::repeat(AGE_LOG_SIZE)
            .take(6)
            .chain([tbl_log_size, cal_log_size, valid_day_log_size])
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[1], &main_sizes, channel);

        let slack_elements = SlackRangeElements::draw(channel);
        let calendar_elements = CalendarElements::draw(channel);
        let valid_day_elements = ValidDayElements::draw(channel);

        channel.mix_felts(&[
            proof.age_claimed_sum,
            proof.slack_table_claimed_sum,
            proof.calendar_table_claimed_sum,
            proof.valid_day_table_claimed_sum,
        ]);

        if proof.age_claimed_sum
            + proof.slack_table_claimed_sum
            + proof.calendar_table_claimed_sum
            + proof.valid_day_table_claimed_sum
            != QM31::zero()
        {
            return Err(Error::Input(crate::age::types::AgeInputError::Invalid(
                "LogUp claimed sums do not cancel".into(),
            )));
        }

        // Tree 2: age (3 logup cols = 12 M31) + slack table (1 col = 4 M31) + cal (1 col = 4 M31) + vdr (1 col = 4 M31)
        let tree2_sizes: Vec<u32> = std::iter::repeat(AGE_LOG_SIZE)
            .take(12)
            .chain(std::iter::repeat(tbl_log_size).take(4))
            .chain(std::iter::repeat(cal_log_size).take(4))
            .chain(std::iter::repeat(valid_day_log_size).take(4))
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[2], &tree2_sizes, channel);

        let mut allocator = make_allocator(&bounds);
        let (age_component, slack_component, cal_component, valid_day_component) = make_components(
            &mut allocator,
            &proof.public,
            slack_elements,
            calendar_elements,
            valid_day_elements,
            proof.age_claimed_sum,
            proof.slack_table_claimed_sum,
            proof.calendar_table_claimed_sum,
            proof.valid_day_table_claimed_sum,
        );

        verify(
            &[&age_component, &slack_component, &cal_component, &valid_day_component],
            channel,
            commitment_scheme,
            proof.stark_proof.clone(),
        )?;

        Ok(())
    }
}
