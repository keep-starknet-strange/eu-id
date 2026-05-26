use crate::age::calendar::{max_days_at, valid_day_row_index};
use crate::age::strategy::bit_decomposition::preprocessed::Preprocessed;
use crate::types::Trace;
use crate::utils::{push_repeated_bits, push_repeated_column};
use crate::{AgeBounds, Witness};
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

pub(crate) const MONTH_OFFSET_BITS: usize = 4;
pub(crate) const DAY_OFFSET_BITS: usize = 5;
pub(crate) const DATE_VALUE_COLUMNS: usize = 4;
const LOG_SIZE: u32 = LOG_N_LANES;

pub struct WitnessData {
    pub witness_trace: Trace,
    pub cal_mult_trace: Trace,
    pub valid_day_mult_trace: Trace,
    pub table_index: u32,
    pub dob_max_days: u32,
    pub dob_day: u32,
}

impl WitnessData {
    pub fn new(witness: &Witness, preprocessed: &Preprocessed) -> Self {
        let dob_max_days = max_days_at(witness.dob.month, witness.dob.year);
        let table_index = (witness.dob.year - witness.public.bounds.min_supported_year) * 12
            + witness.dob.month
            - 1;
        let valid_day_row = valid_day_row_index(dob_max_days, witness.dob.day);

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

        WitnessData {
            witness_trace: gen_trace(witness),
            cal_mult_trace,
            valid_day_mult_trace,
            table_index,
            dob_max_days,
            dob_day: witness.dob.day,
        }
    }

    pub fn extend_evals(
        &self,
        witness_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
        witness_tree_builder.extend_evals(self.witness_trace.clone());
        witness_tree_builder.extend_evals(self.cal_mult_trace.clone());
        witness_tree_builder.extend_evals(self.valid_day_mult_trace.clone());
    }

    pub fn log_size() -> u32 {
        LOG_SIZE
    }

    pub fn trace_columns(bounds: &AgeBounds) -> usize {
        DATE_VALUE_COLUMNS + 1 // +1 for max_days witness column
            + bounds.year_offset_bits()
            + bounds.year_offset_bits()
            + MONTH_OFFSET_BITS
            + MONTH_OFFSET_BITS
            + DAY_OFFSET_BITS
            + bounds.age_slack_bits()
    }
}
fn gen_trace(witness: &Witness) -> Trace {
    let bounds = witness.public.bounds;
    let log_size = LOG_SIZE;
    let mut columns = Vec::with_capacity(WitnessData::trace_columns(&bounds));

    push_repeated_column(&mut columns, witness.dob.year, log_size);
    push_repeated_column(&mut columns, witness.dob.month, log_size);
    push_repeated_column(&mut columns, witness.dob.day, log_size);
    push_repeated_column(&mut columns, witness.age_slack, log_size);
    push_repeated_column(
        &mut columns,
        max_days_at(witness.dob.month, witness.dob.year),
        log_size,
    );

    let year_offset = witness.dob.year.wrapping_sub(bounds.min_supported_year);
    push_repeated_bits(
        &mut columns,
        year_offset,
        log_size,
        bounds.year_offset_bits(),
    );
    push_repeated_bits(
        &mut columns,
        bounds.year_span().wrapping_sub(year_offset),
        log_size,
        bounds.year_offset_bits(),
    );
    push_repeated_bits(
        &mut columns,
        witness.dob.month.wrapping_sub(1),
        log_size,
        MONTH_OFFSET_BITS,
    );
    push_repeated_bits(
        &mut columns,
        12u32.wrapping_sub(witness.dob.month),
        log_size,
        MONTH_OFFSET_BITS,
    );
    push_repeated_bits(
        &mut columns,
        witness.dob.day.wrapping_sub(1),
        log_size,
        DAY_OFFSET_BITS,
    );
    push_repeated_bits(
        &mut columns,
        witness.age_slack,
        log_size,
        bounds.age_slack_bits(),
    );

    debug_assert_eq!(columns.len(), WitnessData::trace_columns(&bounds));
    columns
}
