use crate::age::calendar::{CalendarElements, ValidDayElements};
use crate::age::strategy::bit_decomposition::preprocessed::Preprocessed;
use crate::age::strategy::bit_decomposition::witness::WitnessData;
use crate::types::Trace;
use num_traits::One;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

pub struct InteractionTraces {
    pub age_interaction: Trace,
    pub cal_interaction: Trace,
    pub valid_day_interaction: Trace,
    pub age_claimed_sum: QM31,
    pub cal_claimed_sum: QM31,
    pub valid_day_claimed_sum: QM31,
}

impl InteractionTraces {

    pub fn new(
        witness_data: &WitnessData,
        preprocessed: &Preprocessed,
        calendar_elements: &CalendarElements,
        valid_day_elements: &ValidDayElements,
    ) -> Self {
        let cal_log_size = preprocessed.cal_trace[0].domain.log_size();
        let valid_day_log_size = preprocessed.valid_day_trace[0].domain.log_size();

        // Age component: 2 logup fractions (calendar, valid-day).
        // LOG_SIZE == LOG_N_LANES, so there is exactly 1 packed row.
        let mut logup_gen = LogupTraceGenerator::new(WitnessData::log_size());

        let mut col_gen = logup_gen.new_col();
        col_gen.write_frac(
            0,
            PackedQM31::one(),
            calendar_elements.combine(&[
                PackedM31::broadcast(M31::from_u32_unchecked(witness_data.table_index)),
                PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_max_days)),
            ]),
        );
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        col_gen.write_frac(
            0,
            PackedQM31::one(),
            valid_day_elements.combine(&[
                PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_max_days)),
                PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_day)),
            ]),
        );
        col_gen.finalize_col();

        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

        // Calendar table
        let cal_packed_rows = 1 << (cal_log_size - LOG_N_LANES);
        let mut logup_gen = LogupTraceGenerator::new(cal_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..cal_packed_rows {
            let max_days_val: PackedM31 = preprocessed.cal_trace[0].values.data[vec_row];
            let index_val: PackedM31 = preprocessed.cal_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.cal_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                calendar_elements.combine(&[index_val, max_days_val]),
            );
        }
        col_gen.finalize_col();
        let (cal_interaction, cal_claimed_sum) = logup_gen.finalize_last();

        // Valid-day table
        let valid_day_packed_rows = 1 << (valid_day_log_size - LOG_N_LANES);
        let mut logup_gen = LogupTraceGenerator::new(valid_day_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..valid_day_packed_rows {
            let max_days_val: PackedM31 = preprocessed.valid_day_trace[0].values.data[vec_row];
            let day_val: PackedM31 = preprocessed.valid_day_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.valid_day_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                valid_day_elements.combine(&[max_days_val, day_val]),
            );
        }
        col_gen.finalize_col();
        let (valid_day_interaction, valid_day_claimed_sum) = logup_gen.finalize_last();

        Self {
            age_interaction,
            cal_interaction,
            valid_day_interaction,
            age_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.age_claimed_sum,
            self.cal_claimed_sum,
            self.valid_day_claimed_sum,
        ]);
    }

    pub fn extend_evals(
        &self,
        interaction_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>
    ) {
        interaction_tree_builder.extend_evals(self.age_interaction.clone());
        interaction_tree_builder.extend_evals(self.cal_interaction.clone());
        interaction_tree_builder.extend_evals(self.valid_day_interaction.clone());
    }
}