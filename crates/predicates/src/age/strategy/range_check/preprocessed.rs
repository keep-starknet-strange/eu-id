use crate::age::calendar::{generate_max_days_per_month, valid_date_ranges};
use crate::age::strategy::range_check::witness::WitnessData;
use crate::range_check::RangeCheck;
use crate::types::{Column, Trace};
use crate::{range_check, AgeBounds};
use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

/// Day Range Delta
/// Constraint: range = cutoff - day + 32 * day_borrow
/// Worst case:
///     Cutoff: 1, day: 31 => 1 - 31 + C * day_borrow = -30 + C * day_borrow => C >= 31
///     Field Size => 32 (power of 2)
pub fn day_delta_range_check() -> RangeCheck {
    RangeCheck(31)
}

/// The three delta tables are Class-D multiplicity-blinded (Q-015 §4b): their
/// providers use [`range_check::BlindComponent`].
pub type DayDeltaTableComponent = range_check::BlindComponent;

/// Month Range Delta
/// Constraint: range = cutoff - month - day_borrow + 16 * month_borrow
/// Worst case:
///     Cutoff: 1, month: 12, day_borrow: 1 => 1 - 12 - day_borrow + C * month_borrow =
///                                           -11 - 1 + C * month_borrow =
///                                           -12 + C * month_borrow =>
///                                            C >= 13
///     Field Size => 16 (power of 2)
pub fn month_delta_range_check() -> RangeCheck {
    RangeCheck(15)
}

pub type MonthDeltaTableComponent = range_check::BlindComponent;

////////// Year Range ∈ [0, max_supported_age_years + 1]

pub fn year_delta_range_check(bounds: &AgeBounds) -> RangeCheck {
    RangeCheck(bounds.max_supported_age_years + 1)
}

pub type YearDeltaTableComponent = range_check::BlindComponent;

/// Preprocessed id of the age component's `active` single-row selector: `1` on
/// the single active row, `0` on the Class-C blind rows.
pub fn active_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "age/range_check/active".to_string(),
    }
}

/// The `active` selector column for the age component: `1` on row 0, `0`
/// elsewhere, over the age component's `LOG_SIZE` domain.
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
    pub active_trace: Trace,
    pub cal_trace: Trace,
    pub valid_day_trace: Trace,
    /// Class-D blinded delta tables: each is `[value_column, is_dummy_column]`.
    pub day_delta_table: Trace,
    pub month_delta_table: Trace,
    pub year_delta_table: Trace,
}

impl Preprocessed {
    pub fn new(bounds: &AgeBounds) -> Preprocessed {
        Preprocessed {
            active_trace: vec![active_column()],
            cal_trace: generate_max_days_per_month(bounds),
            valid_day_trace: valid_date_ranges(),
            day_delta_table: vec![
                Self::day_range().blind_preprocessed_column(),
                Self::day_range().blind_dummy_column(),
            ],
            month_delta_table: vec![
                Self::month_range().blind_preprocessed_column(),
                Self::month_range().blind_dummy_column(),
            ],
            year_delta_table: vec![
                Self::year_range(bounds).blind_preprocessed_column(),
                Self::year_range(bounds).blind_dummy_column(),
            ],
        }
    }

    pub fn extend_evals(
        &self,
        preprocessed_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
        preprocessed_tree_builder.extend_evals(self.active_trace.clone());
        preprocessed_tree_builder.extend_evals(self.cal_trace.clone());
        preprocessed_tree_builder.extend_evals(self.valid_day_trace.clone());
        preprocessed_tree_builder.extend_evals(self.day_delta_table.clone());
        preprocessed_tree_builder.extend_evals(self.month_delta_table.clone());
        preprocessed_tree_builder.extend_evals(self.year_delta_table.clone());
    }

    pub fn day_range() -> RangeCheck {
        day_delta_range_check()
    }

    pub fn month_range() -> RangeCheck {
        month_delta_range_check()
    }

    pub fn year_range(bounds: &AgeBounds) -> RangeCheck {
        year_delta_range_check(bounds)
    }
}
