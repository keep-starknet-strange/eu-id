use crate::nat::table::{acceptable_dummy_column, acceptable_value_column};
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

fn nat_prefix_col_id(count: usize, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("nat/prefix/{count}/{name}"),
    }
}

pub fn active_col_id(count: usize) -> PreProcessedColumnId {
    nat_prefix_col_id(count, "active")
}

pub fn row_index_col_id(count: usize) -> PreProcessedColumnId {
    nat_prefix_col_id(count, "row_index")
}

pub fn first_col_id(count: usize) -> PreProcessedColumnId {
    nat_prefix_col_id(count, "first")
}

pub fn last_col_id(count: usize) -> PreProcessedColumnId {
    nat_prefix_col_id(count, "last")
}

/// Active-prefix metadata for the complete signed nationality array.
fn prefix_columns(count: usize) -> [Column; 4] {
    let log_size = WitnessData::log_size();
    let rows = 1usize << log_size;
    assert!((1..=rows / 2).contains(&count));
    let domain = CanonicCoset::new(log_size).circle_domain();

    let mut active = vec![M31::zero(); rows];
    for value in active.iter_mut().take(count) {
        *value = M31::one();
    }
    let row_index = (0..rows)
        .map(|row| M31::from_u32_unchecked(row as u32))
        .collect::<Vec<_>>();
    let mut first = vec![M31::zero(); rows];
    first[0] = M31::one();
    let mut last = vec![M31::zero(); rows];
    last[count - 1] = M31::one();

    [active, row_index, first, last]
        .map(|values| Column::new(domain, BaseColumn::from_iter(values)))
}

pub struct Preprocessed {
    pub active: Trace,
    /// Class-D blinded accepted-set table: `[value_column, is_dummy_column]`.
    pub acceptable: Trace,
}

impl Preprocessed {
    pub fn new(public: &PublicInput, nationality_count: usize) -> Self {
        Self {
            active: prefix_columns(nationality_count).into(),
            acceptable: vec![
                acceptable_value_column(public),
                acceptable_dummy_column(public),
            ],
        }
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.active.clone());
        tb.extend_evals(self.acceptable.clone());
    }
}
