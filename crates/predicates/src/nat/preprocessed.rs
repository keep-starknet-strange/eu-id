use crate::nat::table::{
    acceptable_dummy_column, acceptable_value_column, signed_valid_dummy_column,
    signed_valid_value_column,
};
use crate::nat::types::PublicInput;
use crate::nat::witness::WitnessData;
use crate::types::{Column, Trace};
use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

fn nat_prefix_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("nat/private-prefix/{name}"),
    }
}

pub fn row_index_col_id() -> PreProcessedColumnId {
    nat_prefix_col_id("row_index")
}

pub fn allowed_col_id() -> PreProcessedColumnId {
    nat_prefix_col_id("allowed")
}

pub fn first_col_id() -> PreProcessedColumnId {
    nat_prefix_col_id("first")
}

/// Public row metadata for a private, committed active prefix.
fn prefix_columns() -> [Column; 3] {
    let log_size = WitnessData::log_size();
    let rows = 1usize << log_size;
    let domain = CanonicCoset::new(log_size).circle_domain();

    let row_index = (0..rows)
        .map(|row| M31::from_u32_unchecked(row as u32))
        .collect::<Vec<_>>();
    let mut allowed = vec![M31::zero(); rows];
    allowed[..crate::nat::types::MAX_PRESENTED_NATIONALITIES].fill(M31::one());
    let mut first = vec![M31::zero(); rows];
    first[0] = M31::one();

    [allowed, row_index, first].map(|values| Column::new(domain, BaseColumn::from_iter(values)))
}

pub struct Preprocessed {
    pub prefix: Trace,
    /// Class-D blinded accepted-set table: `[value_column, is_dummy_column]`.
    pub acceptable: Trace,
    /// Fixed signed-code domain: assigned ISO alpha-2 plus `QU` and `QS`.
    pub signed_valid: Trace,
}

impl Preprocessed {
    pub fn new(public: &PublicInput) -> Self {
        Self {
            prefix: prefix_columns().into(),
            acceptable: vec![
                acceptable_value_column(public),
                acceptable_dummy_column(public),
            ],
            signed_valid: vec![
                signed_valid_value_column(public),
                signed_valid_dummy_column(public),
            ],
        }
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.prefix.clone());
        tb.extend_evals(self.acceptable.clone());
        tb.extend_evals(self.signed_valid.clone());
    }
}
