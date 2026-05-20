use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::Column;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::circle::CircleEvaluation;
use crate::age::types::Trace;
use crate::AgeBounds;
use crate::utils::bits_needed;

fn month_index(month: u32, year: u32, min_year: u32) -> usize {
    ((year - min_year) * 12 + month - 1) as usize
}

fn month_days(month: u32, year: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) {
                29
            } else {
                28
            }
        } ,
        _ => panic!("invalid month"),
    }
}

pub(crate) fn calendar_log_size(bounds: &AgeBounds) -> u32 {
    bits_needed((bounds.max_supported_age_years + 1) * 12) as u32
}

pub(crate) fn generate_max_days_per_month(age_bounds: AgeBounds) -> Trace {
    let log_size = calendar_log_size(&age_bounds);

    let domain = CanonicCoset::new(log_size).circle_domain();
    let total_size = 1 << log_size;
    assert!(month_index(12, age_bounds.max_supported_year, age_bounds.min_supported_year) < total_size);

    let mut col = BaseColumn::zeros(total_size);
    for year in age_bounds.min_supported_year..=age_bounds.max_supported_year {
        for month in 1..=12 {
            let index = month_index(month, year, age_bounds.min_supported_year);
            col.set(index, M31::from_u32_unchecked(month_days(month, year)));
        }
    }

    vec![CircleEvaluation::new(domain, col)]
}

pub(crate) fn valid_date_ranges() -> Trace {
    let max_days_values: [u32; 4] = [28, 29, 30, 31];
    let total_rows: u32 = max_days_values.iter().sum();
    let log_size = bits_needed(total_rows) as u32;
    let total_size = 1 << log_size;

    let domain = CanonicCoset::new(log_size).circle_domain();
    let mut max_days_col = BaseColumn::zeros(total_size);
    let mut day_col = BaseColumn::zeros(total_size);

    let mut index = 0;
    for &max_day in &max_days_values {
        for day in 1..=max_day {
            max_days_col.set(index, M31::from_u32_unchecked(max_day));
            day_col.set(index, M31::from_u32_unchecked(day));
            index += 1;
        }
    }

    vec![
        CircleEvaluation::new(domain, max_days_col),
        CircleEvaluation::new(domain, day_col),
    ]
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
        let trace = generate_max_days_per_month(b);
        let rows = (2024 - 1900 + 1) * 12; // 125 years * 12 = 1500
        let expected_log = (rows as f64).log2().ceil() as u32; // 11
        assert_eq!(trace[0].domain.log_size(), expected_log);
    }

    #[test]
    fn january_march_december_have_31_days() {
        let b = bounds(2000, 2024);
        let trace = generate_max_days_per_month(b);
        for month in [1u32, 3, 5, 7, 8, 10, 12] {
            assert_eq!(read_days(&trace, month, 2020, 2000), 31, "month {month}");
        }
    }

    #[test]
    fn april_june_september_november_have_30_days() {
        let b = bounds(2000, 2024);
        let trace = generate_max_days_per_month(b);
        for month in [4u32, 6, 9, 11] {
            assert_eq!(read_days(&trace, month, 2020, 2000), 30, "month {month}");
        }
    }

    #[test]
    fn february_in_leap_year_has_29_days() {
        let b = bounds(1996, 2024);
        let trace = generate_max_days_per_month(b);
        // divisible by 4, not 100
        assert_eq!(read_days(&trace, 2, 2024, 1996), 29);
        // divisible by 400
        assert_eq!(read_days(&trace, 2, 2000, 1996), 29);
    }

    #[test]
    fn february_in_non_leap_year_has_28_days() {
        let b = bounds(1897, 2024);
        let trace = generate_max_days_per_month(b);
        // divisible by 100 but not 400
        assert_eq!(read_days(&trace, 2, 1900, 1897), 28);
        // plain non-leap
        assert_eq!(read_days(&trace, 2, 1897, 1897), 28);
        assert_eq!(read_days(&trace, 2, 2023, 1897), 28);
    }

    #[test]
    fn valid_date_ranges_log_size_is_7() {
        let trace = valid_date_ranges();
        assert_eq!(trace[0].domain.log_size(), 7);
        assert_eq!(trace[1].domain.log_size(), 7);
    }

    #[test]
    fn valid_date_ranges_has_two_columns() {
        let trace = valid_date_ranges();
        assert_eq!(trace.len(), 2);
    }

    #[test]
    fn valid_date_ranges_rows_are_correct() {
        let trace = valid_date_ranges();
        let mut index = 0;
        for max_day in [28u32, 29, 30, 31] {
            for day in 1..=max_day {
                assert_eq!(trace[0].values.at(index).0, max_day, "max_days col at index {index}");
                assert_eq!(trace[1].values.at(index).0, day, "day col at index {index}");
                index += 1;
            }
        }
        assert_eq!(index, 118);
    }

    #[test]
    fn valid_date_ranges_padding_rows_are_zero() {
        let trace = valid_date_ranges();
        for index in 118..128 {
            assert_eq!(trace[0].values.at(index).0, 0, "max_days padding at {index}");
            assert_eq!(trace[1].values.at(index).0, 0, "day padding at {index}");
        }
    }

    #[test]
    fn single_year_span_has_correct_entries() {
        let b = bounds(2024, 2024);
        let trace = generate_max_days_per_month(b);
        // 2024 is a leap year
        assert_eq!(read_days(&trace, 2, 2024, 2024), 29);
        assert_eq!(read_days(&trace, 1, 2024, 2024), 31);
        assert_eq!(read_days(&trace, 4, 2024, 2024), 30);
    }
}