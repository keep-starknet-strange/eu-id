use crate::age::calendar::{max_days_at, valid_day_row_index};
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::types::Trace;
use crate::utils::push_repeated_column;
use crate::Witness;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

const LOG_SIZE: u32 = 5;

pub struct WitnessData {
    pub witness_trace: Trace,
    pub cal_mult_trace: Trace,
    pub valid_day_mult_trace: Trace,
    pub day_delta_mult_trace: Trace,
    pub month_delta_mult_trace: Trace,
    pub year_delta_mult_trace: Trace,
    // Lookup argument values reused when building the interaction traces.
    pub table_index: u32,
    pub dob_max_days: u32,
    pub dob_day: u32,
    pub day_delta_val: u32,
    pub month_delta_val: u32,
    pub year_delta_val: u32,
}

impl WitnessData {
    pub fn new(witness: &Witness, preprocessed: &Preprocessed) -> Self {
        let dob_max_days = max_days_at(witness.dob.month, witness.dob.year);
        let table_index = (witness.dob.year - witness.public.bounds.min_supported_year) * 12
            + witness.dob.month
            - 1;
        let valid_day_row = valid_day_row_index(dob_max_days, witness.dob.day);

        let day_borrow = u32::from(witness.cutoff.day < witness.dob.day);
        let day_delta_val = witness.cutoff.day + 32 * day_borrow - witness.dob.day;
        let month_borrow = u32::from(witness.cutoff.month < witness.dob.month + day_borrow);
        let month_delta_val =
            witness.cutoff.month + 16 * month_borrow - witness.dob.month - day_borrow;
        let year_delta_val =
            (witness.cutoff.year as i32 - witness.dob.year as i32 - month_borrow as i32) as u32;

        let cal_log_size = preprocessed.cal_trace[0].domain.log_size();
        let valid_day_log_size = preprocessed.valid_day_trace[0].domain.log_size();

        let mut cal_mult_data = vec![M31::zero(); 1 << cal_log_size];
        cal_mult_data[table_index as usize] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let cal_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(cal_log_size).circle_domain(),
            BaseColumn::from_iter(cal_mult_data),
        )];

        let mut valid_day_mult_data = vec![M31::zero(); 1 << valid_day_log_size];
        valid_day_mult_data[valid_day_row] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let valid_day_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(valid_day_log_size).circle_domain(),
            BaseColumn::from_iter(valid_day_mult_data),
        )];

        let repeated = |val: u32| vec![M31::from_u32_unchecked(val); 1 << LOG_SIZE];
        let day_delta_mult_trace = vec![Preprocessed::day_range()
            .claim()
            .gen_multiplicity_col(&[repeated(day_delta_val)])];
        let month_delta_mult_trace = vec![Preprocessed::month_range()
            .claim()
            .gen_multiplicity_col(&[repeated(month_delta_val)])];
        let year_delta_mult_trace = vec![Preprocessed::year_range(&witness.public.bounds)
            .claim()
            .gen_multiplicity_col(&[repeated(year_delta_val)])];

        Self {
            witness_trace: gen_trace(witness),
            cal_mult_trace,
            valid_day_mult_trace,
            day_delta_mult_trace,
            month_delta_mult_trace,
            year_delta_mult_trace,
            table_index,
            dob_max_days,
            dob_day: witness.dob.day,
            day_delta_val,
            month_delta_val,
            year_delta_val,
        }
    }

    pub fn log_size() -> u32 {
        LOG_SIZE
    }

    pub fn extend_evals(
        &self,
        witness_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
        witness_tree_builder.extend_evals(self.witness_trace.clone());
        witness_tree_builder.extend_evals(self.cal_mult_trace.clone());
        witness_tree_builder.extend_evals(self.valid_day_mult_trace.clone());
        witness_tree_builder.extend_evals(self.day_delta_mult_trace.clone());
        witness_tree_builder.extend_evals(self.month_delta_mult_trace.clone());
        witness_tree_builder.extend_evals(self.year_delta_mult_trace.clone());
    }
}

fn gen_trace(witness: &Witness) -> Trace {
    let mut cols = Vec::with_capacity(9);
    push_repeated_column(&mut cols, witness.dob.day, LOG_SIZE);
    push_repeated_column(&mut cols, witness.dob.month, LOG_SIZE);
    push_repeated_column(&mut cols, witness.dob.year, LOG_SIZE);
    push_repeated_column(
        &mut cols,
        max_days_at(witness.dob.month, witness.dob.year),
        LOG_SIZE,
    );

    let day_borrow = u32::from(witness.cutoff.day < witness.dob.day);
    let day_delta = witness.cutoff.day + 32 * day_borrow - witness.dob.day;

    let month_borrow = u32::from(witness.cutoff.month < witness.dob.month + day_borrow);
    let month_delta = witness.cutoff.month + 16 * month_borrow - witness.dob.month - day_borrow;

    let year_delta = witness.cutoff.year as i32 - witness.dob.year as i32 - month_borrow as i32;

    push_repeated_column(&mut cols, day_delta, LOG_SIZE);
    push_repeated_column(&mut cols, month_delta, LOG_SIZE);
    push_repeated_column(&mut cols, year_delta as u32, LOG_SIZE);
    push_repeated_column(&mut cols, day_borrow, LOG_SIZE);
    push_repeated_column(&mut cols, month_borrow, LOG_SIZE);

    cols
}
