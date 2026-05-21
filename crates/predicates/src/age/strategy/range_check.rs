use crate::age::calendar::{
    calendar_index_col_id, calendar_log_size, calendar_max_days_col_id, generate_max_days_per_month,
    max_days_at, valid_date_ranges, valid_day_day_col_id, valid_day_max_days_col_id,
    valid_day_row_index, CalendarElements, CalendarTableEval, ValidDayElements, ValidDayTableEval,
};
use crate::age::predicate::AgePredicate;
use crate::age::types::{
    AgeBounds, AgeRangeCheckProof, DateOfBirth, Error, PublicInput, Trace, Witness,
};
use crate::predicate::{Predicate, StarkPredicate};
use crate::utils::{bits_needed, field_const, push_repeated_column};
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

// day_delta ∈ [0, 31] → 32 rows
const DAY_DELTA_LOG_SIZE: u32 = 5;
// month_delta ∈ [0, 15] → 16 rows
const MONTH_DELTA_LOG_SIZE: u32 = 4;

fn year_delta_log_size(bounds: &AgeBounds) -> u32 {
    bits_needed(bounds.max_supported_age_years + 1) as u32
}

relation!(DayDeltaElements, 1);
relation!(MonthDeltaElements, 1);
relation!(YearDeltaElements, 1);

fn generate_day_delta_table() -> Trace {
    let total = 1u32 << DAY_DELTA_LOG_SIZE;
    let domain = CanonicCoset::new(DAY_DELTA_LOG_SIZE).circle_domain();
    let col = BaseColumn::from_iter((0..total).map(M31::from_u32_unchecked));
    vec![CircleEvaluation::new(domain, col)]
}

fn generate_month_delta_table() -> Trace {
    let total = 1u32 << MONTH_DELTA_LOG_SIZE;
    let domain = CanonicCoset::new(MONTH_DELTA_LOG_SIZE).circle_domain();
    let col = BaseColumn::from_iter((0..total).map(M31::from_u32_unchecked));
    vec![CircleEvaluation::new(domain, col)]
}

fn generate_year_delta_table(bounds: &AgeBounds) -> Trace {
    let log_size = year_delta_log_size(bounds);
    let total = 1u32 << log_size;
    let domain = CanonicCoset::new(log_size).circle_domain();
    let col = BaseColumn::from_iter((0..total).map(M31::from_u32_unchecked));
    vec![CircleEvaluation::new(domain, col)]
}

fn day_delta_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId { id: "age/borrow/day_delta".to_string() }
}

fn month_delta_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId { id: "age/borrow/month_delta".to_string() }
}

fn year_delta_col_id(bounds: &AgeBounds) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "age/borrow/year_delta/{}/{}",
            bounds.min_supported_year, bounds.max_supported_age_years
        ),
    }
}

#[derive(Clone)]
struct DayDeltaTableEval {
    lookup_elements: DayDeltaElements,
}

impl FrameworkEval for DayDeltaTableEval {
    fn log_size(&self) -> u32 {
        DAY_DELTA_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(day_delta_col_id());
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

#[derive(Clone)]
struct MonthDeltaTableEval {
    lookup_elements: MonthDeltaElements,
}

impl FrameworkEval for MonthDeltaTableEval {
    fn log_size(&self) -> u32 {
        MONTH_DELTA_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(month_delta_col_id());
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

#[derive(Clone)]
struct YearDeltaTableEval {
    bounds: AgeBounds,
    lookup_elements: YearDeltaElements,
}

impl FrameworkEval for YearDeltaTableEval {
    fn log_size(&self) -> u32 {
        year_delta_log_size(&self.bounds)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(year_delta_col_id(&self.bounds));
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

type CalendarTableComponent = FrameworkComponent<CalendarTableEval>;
type ValidDayTableComponent = FrameworkComponent<ValidDayTableEval>;
type DayDeltaTableComponent = FrameworkComponent<DayDeltaTableEval>;
type MonthDeltaTableComponent = FrameworkComponent<MonthDeltaTableEval>;
type YearDeltaTableComponent = FrameworkComponent<YearDeltaTableEval>;

#[derive(Clone)]
struct AgeRangeCheckEval {
    public: PublicInput,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
    day_delta_elements: DayDeltaElements,
    month_delta_elements: MonthDeltaElements,
    year_delta_elements: YearDeltaElements,
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
        let max_days = eval.next_trace_mask();

        let day_delta = eval.next_trace_mask();
        let month_delta = eval.next_trace_mask();
        let year_delta = eval.next_trace_mask();
        let day_borrow = eval.next_trace_mask();
        let month_borrow = eval.next_trace_mask();

        eval.add_constraint(day_borrow.clone() * (field_const::<E>(1) - day_borrow.clone()));
        eval.add_constraint(month_borrow.clone() * (field_const::<E>(1) - month_borrow.clone()));

        let cutoff = self.public.cutoff_date();

        eval.add_constraint(
            field_const::<E>(cutoff.day) - birth_day.clone()
                + field_const::<E>(32) * day_borrow.clone()
                - day_delta.clone(),
        );
        eval.add_constraint(
            field_const::<E>(cutoff.month) - birth_month.clone()
                - day_borrow.clone()
                + field_const::<E>(16) * month_borrow.clone()
                - month_delta.clone(),
        );
        eval.add_constraint(
            field_const::<E>(cutoff.year) - birth_year.clone()
                - month_borrow.clone()
                - year_delta.clone(),
        );

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
        eval.add_to_relation(RelationEntry::new(
            &self.day_delta_elements,
            E::EF::one(),
            &[day_delta],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.month_delta_elements,
            E::EF::one(),
            &[month_delta],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.year_delta_elements,
            E::EF::one(),
            &[year_delta],
        ));

        eval.finalize_logup();
        eval
    }
}

type AgeRangeCheckComponent = FrameworkComponent<AgeRangeCheckEval>;

fn make_allocator(bounds: &AgeBounds) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[
        calendar_max_days_col_id(bounds),
        calendar_index_col_id(bounds),
        valid_day_max_days_col_id(),
        valid_day_day_col_id(),
        day_delta_col_id(),
        month_delta_col_id(),
        year_delta_col_id(bounds),
    ])
}

#[allow(clippy::too_many_arguments)]
fn make_components(
    allocator: &mut TraceLocationAllocator,
    public: &PublicInput,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
    day_delta_elements: DayDeltaElements,
    month_delta_elements: MonthDeltaElements,
    year_delta_elements: YearDeltaElements,
    age_claimed_sum: QM31,
    cal_claimed_sum: QM31,
    valid_day_claimed_sum: QM31,
    day_delta_claimed_sum: QM31,
    month_delta_claimed_sum: QM31,
    year_delta_claimed_sum: QM31,
) -> (
    AgeRangeCheckComponent,
    CalendarTableComponent,
    ValidDayTableComponent,
    DayDeltaTableComponent,
    MonthDeltaTableComponent,
    YearDeltaTableComponent,
) {
    let age_component = AgeRangeCheckComponent::new(
        allocator,
        AgeRangeCheckEval {
            public: *public,
            calendar_elements: calendar_elements.clone(),
            valid_day_elements: valid_day_elements.clone(),
            day_delta_elements: day_delta_elements.clone(),
            month_delta_elements: month_delta_elements.clone(),
            year_delta_elements: year_delta_elements.clone(),
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
    let day_delta_component = DayDeltaTableComponent::new(
        allocator,
        DayDeltaTableEval { lookup_elements: day_delta_elements },
        day_delta_claimed_sum,
    );
    let month_delta_component = MonthDeltaTableComponent::new(
        allocator,
        MonthDeltaTableEval { lookup_elements: month_delta_elements },
        month_delta_claimed_sum,
    );
    let year_delta_component = YearDeltaTableComponent::new(
        allocator,
        YearDeltaTableEval { bounds: public.bounds, lookup_elements: year_delta_elements },
        year_delta_claimed_sum,
    );
    (
        age_component,
        cal_component,
        valid_day_component,
        day_delta_component,
        month_delta_component,
        year_delta_component,
    )
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
        let mut cols = Vec::with_capacity(9);
        push_repeated_column(&mut cols, witness.dob.day, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.month, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, witness.dob.year, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, max_days_at(witness.dob.month, witness.dob.year), AGE_LOG_SIZE);

        let day_borrow = u32::from(witness.cutoff.day < witness.dob.day);
        let day_delta = witness.cutoff.day + 32 * day_borrow - witness.dob.day;

        let month_borrow = u32::from(witness.cutoff.month < witness.dob.month + day_borrow);
        let month_delta = witness.cutoff.month + 16 * month_borrow - witness.dob.month - day_borrow;

        let year_delta = witness.cutoff.year as i32 - witness.dob.year as i32 - month_borrow as i32;

        push_repeated_column(&mut cols, day_delta, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, month_delta, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, year_delta as u32, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, day_borrow, AGE_LOG_SIZE);
        push_repeated_column(&mut cols, month_borrow, AGE_LOG_SIZE);

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

        let day_borrow_val = u32::from(witness.cutoff.day < witness.dob.day);
        let day_delta_val = witness.cutoff.day + 32 * day_borrow_val - witness.dob.day;
        let month_borrow_val =
            u32::from(witness.cutoff.month < witness.dob.month + day_borrow_val);
        let month_delta_val =
            witness.cutoff.month + 16 * month_borrow_val - witness.dob.month - day_borrow_val;
        let year_delta_val = (witness.cutoff.year as i32
            - witness.dob.year as i32
            - month_borrow_val as i32) as u32;

        let cal_trace = generate_max_days_per_month(bounds);
        let valid_day_trace = valid_date_ranges();
        let day_delta_table = generate_day_delta_table();
        let month_delta_table = generate_month_delta_table();
        let year_delta_table = generate_year_delta_table(&bounds);

        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_day_trace[0].domain.log_size();
        let year_delta_log_sz = year_delta_log_size(&bounds);

        // Calendar multiplicity
        let cal_total = 1 << cal_log_size;
        let mut cal_mult_data = vec![M31::zero(); cal_total];
        cal_mult_data[table_index as usize] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let cal_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(cal_log_size).circle_domain(),
            BaseColumn::from_iter(cal_mult_data.into_iter()),
        )];

        // Valid-day multiplicity
        let valid_day_total = 1 << valid_day_log_size;
        let mut valid_day_mult_data = vec![M31::zero(); valid_day_total];
        valid_day_mult_data[valid_day_row] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let valid_day_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(valid_day_log_size).circle_domain(),
            BaseColumn::from_iter(valid_day_mult_data.into_iter()),
        )];

        // Day delta multiplicity
        let mut day_delta_mult_data = vec![M31::zero(); 1 << DAY_DELTA_LOG_SIZE];
        day_delta_mult_data[day_delta_val as usize] = M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let day_delta_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(DAY_DELTA_LOG_SIZE).circle_domain(),
            BaseColumn::from_iter(day_delta_mult_data.into_iter()),
        )];

        // Month delta multiplicity
        let mut month_delta_mult_data = vec![M31::zero(); 1 << MONTH_DELTA_LOG_SIZE];
        month_delta_mult_data[month_delta_val as usize] =
            M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let month_delta_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(MONTH_DELTA_LOG_SIZE).circle_domain(),
            BaseColumn::from_iter(month_delta_mult_data.into_iter()),
        )];

        // Year delta multiplicity
        let mut year_delta_mult_data = vec![M31::zero(); 1 << year_delta_log_sz];
        year_delta_mult_data[year_delta_val as usize] =
            M31::from_u32_unchecked(1 << AGE_LOG_SIZE);
        let year_delta_mult_trace: Trace = vec![CircleEvaluation::new(
            CanonicCoset::new(year_delta_log_sz).circle_domain(),
            BaseColumn::from_iter(year_delta_mult_data.into_iter()),
        )];

        let witness_trace = self.trace(&witness);

        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(
                cal_log_size
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

        // Tree 0: preprocessed — calendar (2), valid-day (2), day_delta (1), month_delta (1), year_delta (1)
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(cal_trace.clone());
        tb.extend_evals(valid_day_trace.clone());
        tb.extend_evals(day_delta_table.clone());
        tb.extend_evals(month_delta_table.clone());
        tb.extend_evals(year_delta_table.clone());
        tb.commit(channel);

        public.mix_into(channel);

        // Tree 1: 9 witness + 5 multiplicity columns
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(witness_trace.clone());
        tb.extend_evals(cal_mult_trace.clone());
        tb.extend_evals(valid_day_mult_trace.clone());
        tb.extend_evals(day_delta_mult_trace.clone());
        tb.extend_evals(month_delta_mult_trace.clone());
        tb.extend_evals(year_delta_mult_trace.clone());
        tb.commit(channel);

        let calendar_elements = CalendarElements::draw(channel);
        let valid_day_elements = ValidDayElements::draw(channel);
        let day_delta_elements = DayDeltaElements::draw(channel);
        let month_delta_elements = MonthDeltaElements::draw(channel);
        let year_delta_elements = YearDeltaElements::draw(channel);

        // Age component: 5 logup fractions (calendar, valid-day, day_delta, month_delta, year_delta)
        let mut logup_gen = LogupTraceGenerator::new(AGE_LOG_SIZE);

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

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                day_delta_elements
                    .combine(&[PackedM31::broadcast(M31::from_u32_unchecked(day_delta_val))]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                month_delta_elements
                    .combine(&[PackedM31::broadcast(M31::from_u32_unchecked(month_delta_val))]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..(1 << (AGE_LOG_SIZE - LOG_N_LANES)) {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                year_delta_elements
                    .combine(&[PackedM31::broadcast(M31::from_u32_unchecked(year_delta_val))]),
            );
        }
        col_gen.finalize_col();
        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

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

        // Day delta table interaction
        let mut logup_gen = LogupTraceGenerator::new(DAY_DELTA_LOG_SIZE);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (DAY_DELTA_LOG_SIZE - LOG_N_LANES)) {
            let value: PackedM31 = day_delta_table[0].values.data[vec_row];
            let mult: PackedM31 = day_delta_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                day_delta_elements.combine(&[value]),
            );
        }
        col_gen.finalize_col();
        let (day_delta_interaction, day_delta_claimed_sum) = logup_gen.finalize_last();

        // Month delta table interaction
        let mut logup_gen = LogupTraceGenerator::new(MONTH_DELTA_LOG_SIZE);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (MONTH_DELTA_LOG_SIZE - LOG_N_LANES)) {
            let value: PackedM31 = month_delta_table[0].values.data[vec_row];
            let mult: PackedM31 = month_delta_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                month_delta_elements.combine(&[value]),
            );
        }
        col_gen.finalize_col();
        let (month_delta_interaction, month_delta_claimed_sum) = logup_gen.finalize_last();

        // Year delta table interaction
        let mut logup_gen = LogupTraceGenerator::new(year_delta_log_sz);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (year_delta_log_sz - LOG_N_LANES)) {
            let value: PackedM31 = year_delta_table[0].values.data[vec_row];
            let mult: PackedM31 = year_delta_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                year_delta_elements.combine(&[value]),
            );
        }
        col_gen.finalize_col();
        let (year_delta_interaction, year_delta_claimed_sum) = logup_gen.finalize_last();

        channel.mix_felts(&[
            age_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
            day_delta_claimed_sum,
            month_delta_claimed_sum,
            year_delta_claimed_sum,
        ]);

        // Tree 2: age (5 logup cols = 20 M31) + cal (4) + valid_day (4) + day_delta (4) + month_delta (4) + year_delta (4)
        let mut tb = commitment_scheme.tree_builder();
        tb.extend_evals(age_interaction);
        tb.extend_evals(cal_interaction);
        tb.extend_evals(valid_day_interaction);
        tb.extend_evals(day_delta_interaction);
        tb.extend_evals(month_delta_interaction);
        tb.extend_evals(year_delta_interaction);
        tb.commit(channel);

        let mut allocator = make_allocator(&bounds);
        let (
            age_component,
            cal_component,
            valid_day_component,
            day_delta_component,
            month_delta_component,
            year_delta_component,
        ) = make_components(
            &mut allocator,
            public,
            calendar_elements,
            valid_day_elements,
            day_delta_elements,
            month_delta_elements,
            year_delta_elements,
            age_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
            day_delta_claimed_sum,
            month_delta_claimed_sum,
            year_delta_claimed_sum,
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
            age_claimed_sum,
            calendar_table_claimed_sum: cal_claimed_sum,
            valid_day_table_claimed_sum: valid_day_claimed_sum,
            day_delta_claimed_sum,
            month_delta_claimed_sum,
            year_delta_claimed_sum,
            stark_proof,
        })
    }

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error> {
        self.validate(&proof.public)?;

        let bounds = proof.public.bounds;
        let cal_log_size = calendar_log_size(&bounds);
        let valid_day_log_size = valid_date_ranges()[0].domain.log_size();
        let year_delta_log_sz = year_delta_log_size(&bounds);

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
                DAY_DELTA_LOG_SIZE,
                MONTH_DELTA_LOG_SIZE,
                year_delta_log_sz,
            ],
            channel,
        );

        proof.public.mix_into(channel);

        // Tree 1: 9 witness + 5 multiplicity columns
        let main_sizes: Vec<u32> = std::iter::repeat(AGE_LOG_SIZE)
            .take(9)
            .chain([
                cal_log_size,
                valid_day_log_size,
                DAY_DELTA_LOG_SIZE,
                MONTH_DELTA_LOG_SIZE,
                year_delta_log_sz,
            ])
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[1], &main_sizes, channel);

        let calendar_elements = CalendarElements::draw(channel);
        let valid_day_elements = ValidDayElements::draw(channel);
        let day_delta_elements = DayDeltaElements::draw(channel);
        let month_delta_elements = MonthDeltaElements::draw(channel);
        let year_delta_elements = YearDeltaElements::draw(channel);

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
        let tree2_sizes: Vec<u32> = std::iter::repeat(AGE_LOG_SIZE)
            .take(20)
            .chain(std::iter::repeat(cal_log_size).take(4))
            .chain(std::iter::repeat(valid_day_log_size).take(4))
            .chain(std::iter::repeat(DAY_DELTA_LOG_SIZE).take(4))
            .chain(std::iter::repeat(MONTH_DELTA_LOG_SIZE).take(4))
            .chain(std::iter::repeat(year_delta_log_sz).take(4))
            .collect();
        commitment_scheme.commit(proof.stark_proof.commitments[2], &tree2_sizes, channel);

        let mut allocator = make_allocator(&bounds);
        let (
            age_component,
            cal_component,
            valid_day_component,
            day_delta_component,
            month_delta_component,
            year_delta_component,
        ) = make_components(
            &mut allocator,
            &proof.public,
            calendar_elements,
            valid_day_elements,
            day_delta_elements,
            month_delta_elements,
            year_delta_elements,
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
