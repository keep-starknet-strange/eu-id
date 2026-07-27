use crate::types::Trace;
use crate::utils::bits_needed;
use crate::AgeBounds;
use air_core::claim_mask::{add_claim_mask_fraction, CLAIM_MASK_MIN_LOG_SIZE};
use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

fn month_index(month: u32, year: u32, min_year: u32) -> usize {
    ((year - min_year) * 12 + month - 1) as usize
}

pub(crate) const VALID_DAY_REAL_ROWS: usize = 28 + 29 + 30 + 31;
const VALID_DAY_LOG_SIZE: u32 = CLAIM_MASK_MIN_LOG_SIZE;
const VALID_DAY_DUMMY_MAX_DAYS_BASE: u32 = 1 << 20;

pub(crate) fn max_days_at(month: u32, year: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400)) {
                29
            } else {
                28
            }
        }
        _ => panic!("invalid month"),
    }
}

pub fn calendar_log_size(bounds: &AgeBounds) -> u32 {
    bits_needed((bounds.max_supported_age_years + 1) * 12) as u32
}

pub(crate) fn valid_day_row_index(max_days: u32, day: u32) -> usize {
    let start: u32 = match max_days {
        28 => 0,
        29 => 28,
        30 => 57,
        31 => 87,
        _ => panic!("invalid max_days: {max_days}"),
    };
    (start + day - 1) as usize
}

pub fn generate_max_days_per_month(age_bounds: &AgeBounds) -> Trace {
    let log_size = calendar_log_size(age_bounds);

    let domain = CanonicCoset::new(log_size).circle_domain();
    let total_size = 1 << log_size;
    assert!(
        month_index(
            12,
            age_bounds.max_supported_year,
            age_bounds.min_supported_year
        ) < total_size
    );

    let mut max_days_col = BaseColumn::zeros(total_size);
    let mut index_col = BaseColumn::zeros(total_size);
    for year in age_bounds.min_supported_year..=age_bounds.max_supported_year {
        for month in 1..=12 {
            let index = month_index(month, year, age_bounds.min_supported_year);
            max_days_col.set(index, M31::from_u32_unchecked(max_days_at(month, year)));
            index_col.set(index, M31::from_u32_unchecked(index as u32));
        }
    }

    vec![
        CircleEvaluation::new(domain, max_days_col),
        CircleEvaluation::new(domain, index_col),
    ]
}

pub fn valid_date_ranges() -> Trace {
    let max_days_values: [u32; 4] = [28, 29, 30, 31];
    let total_size = 1 << VALID_DAY_LOG_SIZE;

    let domain = CanonicCoset::new(VALID_DAY_LOG_SIZE).circle_domain();
    let mut max_days_col = BaseColumn::zeros(total_size);
    let mut day_col = BaseColumn::zeros(total_size);
    let mut is_dummy_col = BaseColumn::zeros(total_size);

    let mut index = 0;
    for &max_day in &max_days_values {
        for day in 1..=max_day {
            max_days_col.set(index, M31::from_u32_unchecked(max_day));
            day_col.set(index, M31::from_u32_unchecked(day));
            index += 1;
        }
    }
    debug_assert_eq!(index, VALID_DAY_REAL_ROWS);
    for dummy_index in index..total_size {
        max_days_col.set(
            dummy_index,
            M31::from_u32_unchecked(VALID_DAY_DUMMY_MAX_DAYS_BASE + (dummy_index - index) as u32),
        );
        is_dummy_col.set(dummy_index, M31::one());
    }

    vec![
        CircleEvaluation::new(domain, max_days_col),
        CircleEvaluation::new(domain, day_col),
        CircleEvaluation::new(domain, is_dummy_col),
    ]
}

relation!(CalendarElements, 2);
relation!(ValidDayElements, 2);

pub fn calendar_max_days_col_id(bounds: &AgeBounds) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "age/calendar/max_days/{}/{}/{}",
            bounds.min_supported_year, bounds.max_supported_year, bounds.max_supported_age_years
        ),
    }
}

pub fn calendar_index_col_id(bounds: &AgeBounds) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "age/calendar/index/{}/{}/{}",
            bounds.min_supported_year, bounds.max_supported_year, bounds.max_supported_age_years
        ),
    }
}

pub fn valid_day_max_days_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "age/valid_day/max_days".to_string(),
    }
}

pub fn valid_day_day_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "age/valid_day/day".to_string(),
    }
}

pub fn valid_day_dummy_col_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "age/valid_day/is_dummy/log9".to_string(),
    }
}

#[derive(Clone)]
pub struct CalendarTableEval {
    pub bounds: AgeBounds,
    pub lookup_elements: CalendarElements,
    pub claim_mask_beta: Option<QM31>,
}

pub type CalendarTableComponent = FrameworkComponent<CalendarTableEval>;

impl FrameworkEval for CalendarTableEval {
    fn log_size(&self) -> u32 {
        calendar_log_size(&self.bounds)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let max_days = eval.get_preprocessed_column(calendar_max_days_col_id(&self.bounds));
        let table_index = eval.get_preprocessed_column(calendar_index_col_id(&self.bounds));
        let mult = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(mult),
            &[table_index, max_days],
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup();
        eval
    }
}

#[derive(Clone)]
pub struct ValidDayTableEval {
    pub lookup_elements: ValidDayElements,
    pub claim_mask_beta: Option<QM31>,
}

pub type ValidDayTableComponent = FrameworkComponent<ValidDayTableEval>;

impl FrameworkEval for ValidDayTableEval {
    fn log_size(&self) -> u32 {
        valid_date_ranges()[0].domain.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let max_days = eval.get_preprocessed_column(valid_day_max_days_col_id());
        let day = eval.get_preprocessed_column(valid_day_day_col_id());
        let is_dummy = eval.get_preprocessed_column(valid_day_dummy_col_id());
        let mult = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from((one - is_dummy) * mult),
            &[max_days, day],
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup();
        eval
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bounds(min_year: u32, max_year: u32) -> AgeBounds {
        AgeBounds {
            min_supported_year: min_year,
            max_supported_year: max_year,
            max_supported_age_years: max_year - min_year,
        }
    }

    fn read_days(trace: &Trace, month: u32, year: u32, min_year: u32) -> u32 {
        let idx = month_index(month, year, min_year);
        trace[0].values.at(idx).0
    }

    #[test]
    fn log_size_is_ceil_log2_of_year_span_times_12() {
        let b = bounds(1900, 2024);
        let trace = generate_max_days_per_month(&b);
        let rows = (2024 - 1900 + 1) * 12; // 125 years * 12 = 1500
        let expected_log = (rows as f64).log2().ceil() as u32; // 11
        assert_eq!(trace[0].domain.log_size(), expected_log);
    }

    #[test]
    fn january_march_december_have_31_days() {
        let b = bounds(2000, 2024);
        let trace = generate_max_days_per_month(&b);
        for month in [1u32, 3, 5, 7, 8, 10, 12] {
            assert_eq!(read_days(&trace, month, 2020, 2000), 31, "month {month}");
        }
    }

    #[test]
    fn april_june_september_november_have_30_days() {
        let b = bounds(2000, 2024);
        let trace = generate_max_days_per_month(&b);
        for month in [4u32, 6, 9, 11] {
            assert_eq!(read_days(&trace, month, 2020, 2000), 30, "month {month}");
        }
    }

    #[test]
    fn february_in_leap_year_has_29_days() {
        let b = bounds(1996, 2024);
        let trace = generate_max_days_per_month(&b);
        // divisible by 4, not 100
        assert_eq!(read_days(&trace, 2, 2024, 1996), 29);
        // divisible by 400
        assert_eq!(read_days(&trace, 2, 2000, 1996), 29);
    }

    #[test]
    fn february_in_non_leap_year_has_28_days() {
        let b = bounds(1897, 2024);
        let trace = generate_max_days_per_month(&b);
        // divisible by 100 but not 400
        assert_eq!(read_days(&trace, 2, 1900, 1897), 28);
        // plain non-leap
        assert_eq!(read_days(&trace, 2, 1897, 1897), 28);
        assert_eq!(read_days(&trace, 2, 2023, 1897), 28);
    }

    #[test]
    fn valid_date_ranges_log_size_is_9() {
        let trace = valid_date_ranges();
        assert_eq!(trace[0].domain.log_size(), CLAIM_MASK_MIN_LOG_SIZE);
        assert_eq!(trace[1].domain.log_size(), CLAIM_MASK_MIN_LOG_SIZE);
        assert_eq!(trace[2].domain.log_size(), CLAIM_MASK_MIN_LOG_SIZE);
    }

    #[test]
    fn valid_date_ranges_has_value_pair_and_dummy_selector() {
        let trace = valid_date_ranges();
        assert_eq!(trace.len(), 3);
    }

    #[test]
    fn valid_date_ranges_rows_are_correct() {
        let trace = valid_date_ranges();
        let mut index = 0;
        for max_day in [28u32, 29, 30, 31] {
            for day in 1..=max_day {
                assert_eq!(
                    trace[0].values.at(index).0,
                    max_day,
                    "max_days col at index {index}"
                );
                assert_eq!(trace[1].values.at(index).0, day, "day col at index {index}");
                index += 1;
            }
        }
        assert_eq!(index, 118);
    }

    #[test]
    fn valid_date_ranges_dummy_rows_are_unreachable_and_selected() {
        let trace = valid_date_ranges();
        for index in VALID_DAY_REAL_ROWS..1 << VALID_DAY_LOG_SIZE {
            assert!(
                trace[0].values.at(index).0 >= VALID_DAY_DUMMY_MAX_DAYS_BASE,
                "dummy max_days at {index}"
            );
            assert_eq!(trace[1].values.at(index).0, 0, "day padding at {index}");
            assert_eq!(trace[2].values.at(index).0, 1, "dummy selector at {index}");
        }
    }

    #[test]
    fn generate_max_days_has_two_columns() {
        let trace = generate_max_days_per_month(&bounds(2000, 2024));
        assert_eq!(trace.len(), 2);
    }

    #[test]
    fn calendar_index_col_stores_row_indices() {
        let b = bounds(2000, 2024);
        let trace = generate_max_days_per_month(&b);
        for year in 2000..=2024 {
            for month in 1..=12u32 {
                let idx = month_index(month, year, 2000);
                assert_eq!(
                    trace[1].values.at(idx).0,
                    idx as u32,
                    "index col at ({year}, {month})"
                );
            }
        }
    }

    #[test]
    fn valid_day_row_index_boundaries() {
        assert_eq!(valid_day_row_index(28, 1), 0);
        assert_eq!(valid_day_row_index(28, 28), 27);
        assert_eq!(valid_day_row_index(29, 1), 28);
        assert_eq!(valid_day_row_index(29, 29), 56);
        assert_eq!(valid_day_row_index(30, 1), 57);
        assert_eq!(valid_day_row_index(30, 30), 86);
        assert_eq!(valid_day_row_index(31, 1), 87);
        assert_eq!(valid_day_row_index(31, 31), 117);
    }

    #[test]
    fn single_year_span_has_correct_entries() {
        let b = bounds(2024, 2024);
        let trace = generate_max_days_per_month(&b);
        // 2024 is a leap year
        assert_eq!(read_days(&trace, 2, 2024, 2024), 29);
        assert_eq!(read_days(&trace, 1, 2024, 2024), 31);
        assert_eq!(read_days(&trace, 4, 2024, 2024), 30);
    }
}
