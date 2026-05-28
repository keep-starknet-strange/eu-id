use crate::nat::types::{PublicInput, Witness};
use crate::types::Trace;
use crate::utils::push_repeated_column;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

pub(super) struct WitnessData {
    pub witness_trace: Trace,
    pub table_mult_trace: Trace,
    pub nationality: u32,
    #[allow(dead_code)]
    pub nat_index: usize,
}

impl WitnessData {
    pub fn new(witness: &Witness, public: &PublicInput) -> Self {
        let acceptable_nats_log_size = public.log_size();

        let mut witness_trace = Vec::new();
        push_repeated_column(&mut witness_trace, witness.nationality, LOG_N_LANES);

        let mut mult_data = vec![M31::zero(); 1 << acceptable_nats_log_size];
        mult_data[witness.nat_index] = M31::from_u32_unchecked(1 << LOG_N_LANES);
        let table_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(acceptable_nats_log_size).circle_domain(),
            BaseColumn::from_iter(mult_data),
        )];

        Self {
            witness_trace,
            table_mult_trace,
            nationality: witness.nationality,
            nat_index: witness.nat_index,
        }
    }

    pub fn log_size() -> u32 {
        LOG_N_LANES
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.witness_trace.clone());
        tb.extend_evals(self.table_mult_trace.clone());
    }
}
