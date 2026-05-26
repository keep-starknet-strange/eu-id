use crate::age::calendar::{generate_max_days_per_month, valid_date_ranges};
use crate::range_check::RangeCheck;
use crate::types::Trace;
use crate::{range_check, AgeBounds};
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;

//// Day Range Delta
//// Constraint: range = cutoff - day + 32 * day_borrow
//// Worst case:
////     Cutoff: 1, day: 31 => 1 - 31 + C * day_borrow = -30 + C * day_borrow => C >= 31
////     Field Size => 32 (power of 2)
pub fn day_delta_range_check() -> RangeCheck {
    RangeCheck(31)
}

pub type DayDeltaTableComponent = range_check::Component;

//// Month Range Delta
//// Constraint: range = cutoff - month - day_borrow + 16 * month_borrow
//// Worst case:
////     Cutoff: 1, month: 12, day_borrow: 1 => 1 - 12 - day_borrow + C * month_borrow =
////                                           -11 - 1 + C * month_borrow =
////                                           -12 + C * month_borrow =>
////                                            C >= 13
////     Field Size => 16 (power of 2)
pub fn month_delta_range_check() -> RangeCheck {
    RangeCheck(13)
}

pub type MonthDeltaTableComponent = range_check::Component;

////////// Year Range ∈ [0, max_supported_age_years + 1]

pub fn year_delta_range_check(bounds: &AgeBounds) -> RangeCheck {
    RangeCheck(bounds.max_supported_age_years + 1)
}

pub type YearDeltaTableComponent = range_check::Component;

pub struct Preprocessed {
    pub cal_trace: Trace,
    pub valid_day_trace: Trace,
    pub day_delta_table: Trace,
    pub month_delta_table: Trace,
    pub year_delta_table: Trace,
}

impl Preprocessed {
    pub fn new(bounds: &AgeBounds) -> Preprocessed {
        Preprocessed {
            cal_trace: generate_max_days_per_month(bounds),
            valid_day_trace: valid_date_ranges(),
            day_delta_table: vec![Self::day_range().preprocessed_column()],
            month_delta_table: vec![Self::month_range().preprocessed_column()],
            year_delta_table: vec![Self::year_range(bounds).preprocessed_column()],
        }
    }

    pub fn extend_evals(
        &self,
        preprocessed_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
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
