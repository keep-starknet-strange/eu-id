use crate::nat::preprocessed::Preprocessed;
use crate::nat::table::NatTableElements;
use crate::nat::witness::WitnessData;
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

pub(super) struct InteractionTraces {
    pub nat_interaction: Trace,
    pub table_interaction: Trace,
    pub nat_claimed_sum: QM31,
    pub table_claimed_sum: QM31,
}

impl InteractionTraces {
    pub fn new(
        witness_data: &WitnessData,
        preprocessed: &Preprocessed,
        lookup_elements: &NatTableElements,
    ) -> Self {
        let acceptable_nat_log_size = preprocessed.acceptable[0].domain.log_size();
        let n_packed = 1 << (WitnessData::log_size() - LOG_N_LANES);

        let mut logup_gen = LogupTraceGenerator::new(WitnessData::log_size());
        let mut col_gen = logup_gen.new_col();
        for packed_row in 0..n_packed {
            col_gen.write_frac(
                packed_row,
                PackedQM31::one(),
                lookup_elements.combine(&[PackedM31::broadcast(M31::from_u32_unchecked(
                    witness_data.nationality,
                ))]),
            );
        }
        col_gen.finalize_col();
        let (nat_interaction, nat_claimed_sum) = logup_gen.finalize_last();

        let mut logup_gen = LogupTraceGenerator::new(acceptable_nat_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (acceptable_nat_log_size - LOG_N_LANES)) {
            let nat_val: PackedM31 = preprocessed.acceptable[0].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.table_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                lookup_elements.combine(&[nat_val]),
            );
        }
        col_gen.finalize_col();
        let (table_interaction, table_claimed_sum) = logup_gen.finalize_last();

        Self {
            nat_interaction,
            table_interaction,
            nat_claimed_sum,
            table_claimed_sum,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.nat_claimed_sum, self.table_claimed_sum]);
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.nat_interaction.clone());
        tb.extend_evals(self.table_interaction.clone());
    }
}
