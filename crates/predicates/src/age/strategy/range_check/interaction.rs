use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::age::strategy::range_check::witness::WitnessData;
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
    pub day_delta_interaction: Trace,
    pub month_delta_interaction: Trace,
    pub year_delta_interaction: Trace,
    pub age_claimed_sum: QM31,
    pub cal_claimed_sum: QM31,
    pub valid_day_claimed_sum: QM31,
    pub day_delta_claimed_sum: QM31,
    pub month_delta_claimed_sum: QM31,
    pub year_delta_claimed_sum: QM31,
}

impl InteractionTraces {
    pub fn new(
        witness_data: &WitnessData,
        preprocessed: &Preprocessed,
        lookup_elements: &LookupElements,
    ) -> Self {
        let cal_log_size = preprocessed.cal_trace[0].domain.log_size();
        let valid_day_log_size = preprocessed.valid_day_trace[0].domain.log_size();
        let year_delta_log_sz = preprocessed.year_delta_table[0].domain.log_size();
        let n_packed = 1 << (WitnessData::log_size() - LOG_N_LANES);

        // Age component: 5 logup fractions (calendar, valid-day, day_delta, month_delta, year_delta)
        let mut logup_gen = LogupTraceGenerator::new(WitnessData::log_size());

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..n_packed {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                lookup_elements.calendar.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.table_index)),
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_max_days)),
                ]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..n_packed {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                lookup_elements.valid_day.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_max_days)),
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_day)),
                ]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..n_packed {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                lookup_elements.day_delta.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.day_delta_val),
                )]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..n_packed {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                lookup_elements.month_delta.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.month_delta_val),
                )]),
            );
        }
        col_gen.finalize_col();

        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..n_packed {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                lookup_elements.year_delta.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.year_delta_val),
                )]),
            );
        }
        col_gen.finalize_col();

        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

        // Calendar table
        let mut logup_gen = LogupTraceGenerator::new(cal_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (cal_log_size - LOG_N_LANES)) {
            let max_days_val: PackedM31 = preprocessed.cal_trace[0].values.data[vec_row];
            let index_val: PackedM31 = preprocessed.cal_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.cal_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                lookup_elements.calendar.combine(&[index_val, max_days_val]),
            );
        }
        col_gen.finalize_col();
        let (cal_interaction, cal_claimed_sum) = logup_gen.finalize_last();

        // Valid-day table
        let mut logup_gen = LogupTraceGenerator::new(valid_day_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (valid_day_log_size - LOG_N_LANES)) {
            let max_days_val: PackedM31 = preprocessed.valid_day_trace[0].values.data[vec_row];
            let day_val: PackedM31 = preprocessed.valid_day_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.valid_day_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                lookup_elements.valid_day.combine(&[max_days_val, day_val]),
            );
        }
        col_gen.finalize_col();
        let (valid_day_interaction, valid_day_claimed_sum) = logup_gen.finalize_last();

        // Day delta table
        let day_delta_log_size = Preprocessed::day_range().log_size();
        let mut logup_gen = LogupTraceGenerator::new(day_delta_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (day_delta_log_size - LOG_N_LANES)) {
            let value: PackedM31 = preprocessed.day_delta_table[0].values.data[vec_row];
            let mult: PackedM31 = witness_data.day_delta_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                lookup_elements.day_delta.combine(&[value]),
            );
        }
        col_gen.finalize_col();
        let (day_delta_interaction, day_delta_claimed_sum) = logup_gen.finalize_last();

        // Month delta table
        let month_delta_log_size = Preprocessed::month_range().log_size();
        let mut logup_gen = LogupTraceGenerator::new(month_delta_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (month_delta_log_size - LOG_N_LANES)) {
            let value: PackedM31 = preprocessed.month_delta_table[0].values.data[vec_row];
            let mult: PackedM31 = witness_data.month_delta_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                lookup_elements.month_delta.combine(&[value]),
            );
        }
        col_gen.finalize_col();
        let (month_delta_interaction, month_delta_claimed_sum) = logup_gen.finalize_last();

        // Year delta table
        let mut logup_gen = LogupTraceGenerator::new(year_delta_log_sz);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (year_delta_log_sz - LOG_N_LANES)) {
            let value: PackedM31 = preprocessed.year_delta_table[0].values.data[vec_row];
            let mult: PackedM31 = witness_data.year_delta_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult),
                lookup_elements.year_delta.combine(&[value]),
            );
        }
        col_gen.finalize_col();
        let (year_delta_interaction, year_delta_claimed_sum) = logup_gen.finalize_last();

        Self {
            age_interaction,
            cal_interaction,
            valid_day_interaction,
            day_delta_interaction,
            month_delta_interaction,
            year_delta_interaction,
            age_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
            day_delta_claimed_sum,
            month_delta_claimed_sum,
            year_delta_claimed_sum,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.age_claimed_sum,
            self.cal_claimed_sum,
            self.valid_day_claimed_sum,
            self.day_delta_claimed_sum,
            self.month_delta_claimed_sum,
            self.year_delta_claimed_sum,
        ]);
    }

    pub fn extend_evals(
        &self,
        interaction_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
        interaction_tree_builder.extend_evals(self.age_interaction.clone());
        interaction_tree_builder.extend_evals(self.cal_interaction.clone());
        interaction_tree_builder.extend_evals(self.valid_day_interaction.clone());
        interaction_tree_builder.extend_evals(self.day_delta_interaction.clone());
        interaction_tree_builder.extend_evals(self.month_delta_interaction.clone());
        interaction_tree_builder.extend_evals(self.year_delta_interaction.clone());
    }
}
