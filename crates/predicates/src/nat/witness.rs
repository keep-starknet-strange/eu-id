use crate::nat::table::table_log_size;
use crate::nat::types::{PublicInput, Witness};
use crate::types::Trace;
use crate::utils::push_repeated_column;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

/// Number of rows in the main component. Must be >= LOG_N_LANES (4).
const LOG_SIZE: u32 = 4;

pub(super) struct WitnessData {
    pub witness_trace: Trace,
    pub table_mult_trace: Trace,
    pub nationality: u32,
    #[allow(dead_code)]
    pub nat_index: usize,
}

impl WitnessData {
    pub fn new(witness: &Witness, public: &PublicInput) -> Self {
        let log_size = table_log_size(&public.acceptable);

        let mut mult_data = vec![M31::zero(); 1 << log_size];
        mult_data[witness.nat_index] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let table_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(log_size).circle_domain(),
            BaseColumn::from_iter(mult_data),
        )];

        Self {
            witness_trace: gen_trace(witness.nationality),
            table_mult_trace,
            nationality: witness.nationality,
            nat_index: witness.nat_index,
        }
    }

    pub fn log_size() -> u32 {
        LOG_SIZE
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.witness_trace.clone());
        tb.extend_evals(self.table_mult_trace.clone());
    }
}

fn gen_trace(nationality: u32) -> Trace {
    let mut cols = Vec::new();
    push_repeated_column(&mut cols, nationality, LOG_SIZE);
    cols
}
