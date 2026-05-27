use crate::nat::table::generate_acceptable_table;
use crate::nat::types::PublicInput;
use crate::types::Trace;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;

pub(super) struct Preprocessed {
    pub nat_table: Trace,
}

impl Preprocessed {
    pub fn new(public: &PublicInput) -> Self {
        Self {
            nat_table: generate_acceptable_table(&public.acceptable),
        }
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.nat_table.clone());
    }
}
