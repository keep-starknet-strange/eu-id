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

/// Preprocessed id of the nationality component's `active` single-row selector:
/// `1` on the single active row, `0` on the Class-C blind rows.
pub fn active_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "nat/active".to_string(),
    }
}

/// The `active` selector column for the nationality component: `1` on row 0,
/// `0` elsewhere, over the component's `LOG_SIZE` domain.
pub fn active_column() -> Column {
    let log_size = WitnessData::log_size();
    let mut data = vec![M31::zero(); 1 << log_size];
    data[0] = M31::one();
    Column::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(data),
    )
}

pub struct Preprocessed {
    pub active: Trace,
    /// Class-D blinded accepted-set table: `[value_column, is_dummy_column]`.
    pub acceptable: Trace,
}

impl Preprocessed {
    pub fn new(public: &PublicInput) -> Self {
        Self {
            active: vec![active_column()],
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
