use crate::age::calendar::{generate_max_days_per_month, valid_date_ranges};
use crate::types::Trace;
use crate::AgeBounds;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;

pub struct Preprocessed {
    pub cal_trace: Trace,
    pub valid_day_trace: Trace,
}

impl Preprocessed {
    pub fn new(bounds: &AgeBounds) -> Self {
        Self {
            cal_trace: generate_max_days_per_month(bounds),
            valid_day_trace: valid_date_ranges(),
        }
    }

    pub fn extend_evals(
        &self,
        preprocessed_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>
    ) {
        preprocessed_tree_builder.extend_evals(self.cal_trace.clone());
        preprocessed_tree_builder.extend_evals(self.valid_day_trace.clone());
    }
}