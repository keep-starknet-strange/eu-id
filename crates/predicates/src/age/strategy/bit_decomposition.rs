use crate::age::calendar::{
    calendar_index_col_id, calendar_log_size, calendar_max_days_col_id, generate_max_days_per_month,
    max_days_at, valid_date_ranges, valid_day_day_col_id, valid_day_max_days_col_id,
    valid_day_row_index, CalendarElements, CalendarTableEval, ValidDayElements, ValidDayTableEval,
};
use crate::age::predicate::AgePredicate;
use crate::age::types::{
    AgeBitDecompositionProof, AgeBounds, DateOfBirth, Error, PublicInput, Trace, Witness,
    DATE_MONTH_BASE, DATE_YEAR_BASE,
};
use crate::predicate::{Predicate, StarkPredicate};
use crate::utils::{bit_sum, constrain_bits, field_const, push_repeated_bits, push_repeated_column, read_bits, read_bits_dynamic};
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
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

pub(crate) const MONTH_OFFSET_BITS: usize = 4;
pub(crate) const DAY_OFFSET_BITS: usize = 5;
pub(crate) const DATE_VALUE_COLUMNS: usize = 4;
pub(crate) const AGE_CONSTRAINT_LOG_DEGREE: u32 = 1;
pub(crate) const LOG_SIZE: u32 = LOG_N_LANES;

type CalendarTableComponent = FrameworkComponent<CalendarTableEval>;
type ValidDayTableComponent = FrameworkComponent<ValidDayTableEval>;

pub(crate) fn trace_columns(bounds: &AgeBounds) -> usize {
    DATE_VALUE_COLUMNS + 1 // +1 for max_days witness column
        + bounds.year_offset_bits()
        + bounds.year_offset_bits()
        + MONTH_OFFSET_BITS
        + MONTH_OFFSET_BITS
        + DAY_OFFSET_BITS
        + bounds.age_slack_bits()
}

fn make_allocator(bounds: &AgeBounds) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[
        calendar_max_days_col_id(bounds),
        calendar_index_col_id(bounds),
        valid_day_max_days_col_id(),
        valid_day_day_col_id(),
    ])
}

struct BitDecompositionEval {
    public: PublicInput,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
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
        let max_days = eval.next_trace_mask();

        let bounds = self.public.bounds;
        let year_offset_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let year_bound_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let month_offset_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let month_bound_slack_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let day_offset_bits = read_bits::<E, DAY_OFFSET_BITS>(&mut eval);
        let age_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.age_slack_bits());

        constrain_bits(&mut eval, &year_offset_bits);
        constrain_bits(&mut eval, &year_bound_slack_bits);
        constrain_bits(&mut eval, &month_offset_bits);
        constrain_bits(&mut eval, &month_bound_slack_bits);
        constrain_bits(&mut eval, &day_offset_bits);
        constrain_bits(&mut eval, &age_slack_bits);

        let year_offset = bit_sum::<E>(&year_offset_bits);
        let year_bound_slack = bit_sum::<E>(&year_bound_slack_bits);
        let month_offset = bit_sum::<E>(&month_offset_bits);
        let month_bound_slack = bit_sum::<E>(&month_bound_slack_bits);
        let day_offset = bit_sum::<E>(&day_offset_bits);
        let age_slack_from_bits = bit_sum::<E>(&age_slack_bits);

        eval.add_constraint(
            dob_year.clone() - field_const::<E>(bounds.min_supported_year) - year_offset.clone(),
        );
        eval.add_constraint(field_const::<E>(bounds.year_span()) - year_offset - year_bound_slack);
        eval.add_constraint(dob_month.clone() - field_const::<E>(1) - month_offset.clone());
        eval.add_constraint(field_const::<E>(11) - month_offset - month_bound_slack);
        eval.add_constraint(dob_day.clone() - field_const::<E>(1) - day_offset);
        eval.add_constraint(age_slack.clone() - age_slack_from_bits);

        let cutoff_key = self.public.cutoff_date().key();
        let dob_key = dob_year.clone() * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
            + dob_month.clone() * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
            + dob_day.clone();
        eval.add_constraint(field_const::<E>(cutoff_key) - dob_key - age_slack);

        let table_index = (dob_year - field_const::<E>(bounds.min_supported_year))
            * BaseField::from_u32_unchecked(12)
            + dob_month
            - field_const::<E>(1);
        eval.add_to_relation(RelationEntry::new(
            &self.calendar_elements,
            E::EF::one(),
            &[table_index, max_days.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.valid_day_elements,
            E::EF::one(),
            &[max_days, dob_day],
        ));

        eval.finalize_logup();
        eval
    }
}

type AgeComponent = FrameworkComponent<BitDecompositionEval>;

fn make_components(
    allocator: &mut TraceLocationAllocator,
    public: &PublicInput,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
    age_claimed_sum: QM31,
    cal_claimed_sum: QM31,
    valid_day_claimed_sum: QM31,
) -> (AgeComponent, CalendarTableComponent, ValidDayTableComponent) {
    let age_component = AgeComponent::new(
        allocator,
        BitDecompositionEval {
            public: *public,
            calendar_elements: calendar_elements.clone(),
            valid_day_elements: valid_day_elements.clone(),
        },
        age_claimed_sum,
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
    (age_component, cal_component, valid_day_component)
}

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

    fn trace(&self, witness: &Self::Witness) -> Trace {
        let bounds = witness.public.bounds;
        let log_size = LOG_SIZE;
        let mut columns = Vec::with_capacity(trace_columns(&bounds));

        push_repeated_column(&mut columns, witness.dob.year, log_size);
        push_repeated_column(&mut columns, witness.dob.month, log_size);
        push_repeated_column(&mut columns, witness.dob.day, log_size);
        push_repeated_column(&mut columns, witness.age_slack, log_size);
        push_repeated_column(&mut columns, max_days_at(witness.dob.month, witness.dob.year), log_size);

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
        let bounds = public.bounds;

        let dob_max_days = max_days_at(witness.dob.month, witness.dob.year);
        let table_index = (witness.dob.year - bounds.min_supported_year) * 12 + witness.dob.month - 1;
        let valid_day_row = valid_day_row_index(dob_max_days, witness.dob.day);

        let cal_trace = generate_max_days_per_month(bounds);
        let valid_day_trace = valid_date_ranges();
        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_day_trace[0].domain.log_size();

        let cal_total = 1 << cal_log_size;
        let mut cal_mult_data = vec![M31::zero(); cal_total];
        cal_mult_data[table_index as usize] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let cal_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(cal_log_size).circle_domain(),
            BaseColumn::from_iter(cal_mult_data.into_iter()),
        )];

        let valid_day_total = 1 << valid_day_log_size;
        let mut valid_day_mult_data = vec![M31::zero(); valid_day_total];
        valid_day_mult_data[valid_day_row] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let valid_day_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(valid_day_log_size).circle_domain(),
            BaseColumn::from_iter(valid_day_mult_data.into_iter()),
        )];

        let witness_trace = self.trace(&witness);

        let max_log_size = LOG_SIZE.max(cal_log_size);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                max_log_size
                    + AGE_CONSTRAINT_LOG_DEGREE
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
        tb.extend_evals(cal_trace.clone());
        tb.extend_evals(valid_day_trace.clone());
        tb.commit(channel);

        public.mix_into(channel);

        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(witness_trace.clone());
        tb.extend_evals(cal_mult_trace.clone());
        tb.extend_evals(valid_day_mult_trace.clone());
        tb.commit(channel);

        let calendar_elements = CalendarElements::draw(channel);
        let valid_day_elements = ValidDayElements::draw(channel);

        let mut logup_gen = LogupTraceGenerator::new(LOG_SIZE);
        let mut col_gen = logup_gen.new_col();
        col_gen.write_frac(
            0,
            PackedQM31::one(),
            calendar_elements.combine(&[
                PackedM31::broadcast(M31::from_u32_unchecked(table_index)),
                PackedM31::broadcast(M31::from_u32_unchecked(dob_max_days)),
            ]),
        );
        col_gen.finalize_col();
        let mut col_gen = logup_gen.new_col();
        col_gen.write_frac(
            0,
            PackedQM31::one(),
            valid_day_elements.combine(&[
                PackedM31::broadcast(M31::from_u32_unchecked(dob_max_days)),
                PackedM31::broadcast(M31::from_u32_unchecked(witness.dob.day)),
            ]),
        );
        col_gen.finalize_col();
        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

        let cal_packed_rows = 1 << (cal_log_size - LOG_N_LANES);
        let mut logup_gen = LogupTraceGenerator::new(cal_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..cal_packed_rows {
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

        let valid_day_packed_rows = 1 << (valid_day_log_size - LOG_N_LANES);
        let mut logup_gen = LogupTraceGenerator::new(valid_day_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..valid_day_packed_rows {
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

        channel.mix_felts(&[age_claimed_sum, cal_claimed_sum, valid_day_claimed_sum]);

        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(age_interaction);
        tb.extend_evals(cal_interaction);
        tb.extend_evals(valid_day_interaction);
        tb.commit(channel);

        let mut allocator = make_allocator(&bounds);
        let (age_component, cal_component, valid_day_component) = make_components(
            &mut allocator,
            public,
            calendar_elements,
            valid_day_elements,
            age_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
        );
        let components: Vec<&dyn ComponentProver<SimdBackend>> =
            vec![&age_component, &cal_component, &valid_day_component];
        let stark_proof = prove::<SimdBackend, Blake2sMerkleChannel>(
            components.as_slice(),
            channel,
            commitment_scheme,
        )?;

        Ok(AgeBitDecompositionProof {
            public: *public,
            age_claimed_sum,
            calendar_table_claimed_sum: cal_claimed_sum,
            valid_day_table_claimed_sum: valid_day_claimed_sum,
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.public)?;

        let bounds = proof.public.bounds;
        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_date_ranges()[0].domain.log_size();

        let pcs_config = proof.stark_proof.config;
        let channel = &mut Blake2sChannel::default();
        pcs_config.mix_into(channel);

        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(pcs_config);

        commitment_scheme.commit(
            proof.stark_proof.commitments[0],
            &[cal_log_size, cal_log_size, valid_day_log_size, valid_day_log_size],
            channel,
        );

        proof.public.mix_into(channel);

        let main_sizes: Vec<u32> = std::iter::repeat(LOG_SIZE)
            .take(trace_columns(&bounds))
            .chain([cal_log_size, valid_day_log_size])
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[1], &main_sizes, channel);

        let calendar_elements = CalendarElements::draw(channel);
        let valid_day_elements = ValidDayElements::draw(channel);

        channel.mix_felts(&[
            proof.age_claimed_sum,
            proof.calendar_table_claimed_sum,
            proof.valid_day_table_claimed_sum,
        ]);

        if proof.age_claimed_sum + proof.calendar_table_claimed_sum + proof.valid_day_table_claimed_sum != QM31::zero() {
            return Err(Error::Input(crate::age::types::AgeInputError::Invalid(
                "LogUp claimed sums do not cancel".into(),
            )));
        }

        let tree2_sizes: Vec<u32> = std::iter::repeat(LOG_SIZE)
            .take(8)
            .chain(std::iter::repeat(cal_log_size).take(4))
            .chain(std::iter::repeat(valid_day_log_size).take(4))
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[2], &tree2_sizes, channel);

        let mut allocator = make_allocator(&bounds);
        let (age_component, cal_component, valid_day_component) = make_components(
            &mut allocator,
            &proof.public,
            calendar_elements,
            valid_day_elements,
            proof.age_claimed_sum,
            proof.calendar_table_claimed_sum,
            proof.valid_day_table_claimed_sum,
        );
        verify(
            &[&age_component, &cal_component, &valid_day_component],
            channel,
            commitment_scheme,
            proof.stark_proof.clone(),
        )?;

        Ok(())
    }
}
