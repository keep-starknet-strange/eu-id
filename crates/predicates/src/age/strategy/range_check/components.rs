use crate::age::calendar::{
    calendar_index_col_id, calendar_max_days_col_id, valid_day_day_col_id,
    valid_day_max_days_col_id, CalendarElements, CalendarTableComponent, CalendarTableEval,
    ValidDayElements, ValidDayTableComponent, ValidDayTableEval,
};
use crate::age::strategy::range_check::eval::{AgeRangeCheckComponent, AgeRangeCheckEval};
use crate::age::strategy::range_check::preprocessed::{
    DayDeltaTableComponent, MonthDeltaTableComponent, Preprocessed, YearDeltaTableComponent,
};
use crate::range_check::RangeCheckLookupElements;
use crate::{AgeBounds, PublicInput};
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::TraceLocationAllocator;
fn make_allocator(bounds: &AgeBounds) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[
        calendar_max_days_col_id(bounds),
        calendar_index_col_id(bounds),
        valid_day_max_days_col_id(),
        valid_day_day_col_id(),
        Preprocessed::day_range().id(),
        Preprocessed::month_range().id(),
        Preprocessed::year_range(bounds).id(),
    ])
}

#[allow(clippy::too_many_arguments)]
pub fn components(
    public: &PublicInput,
    calendar_elements: CalendarElements,
    valid_day_elements: ValidDayElements,
    day_delta_elements: RangeCheckLookupElements,
    month_delta_elements: RangeCheckLookupElements,
    year_delta_elements: RangeCheckLookupElements,
    age_claimed_sum: QM31,
    cal_claimed_sum: QM31,
    valid_day_claimed_sum: QM31,
    day_delta_claimed_sum: QM31,
    month_delta_claimed_sum: QM31,
    year_delta_claimed_sum: QM31,
) -> (
    AgeRangeCheckComponent,
    CalendarTableComponent,
    ValidDayTableComponent,
    DayDeltaTableComponent,
    MonthDeltaTableComponent,
    YearDeltaTableComponent,
) {
    let mut allocator = make_allocator(&public.bounds);
    let age_component = AgeRangeCheckComponent::new(
        &mut allocator,
        AgeRangeCheckEval {
            public: *public,
            calendar_elements: calendar_elements.clone(),
            valid_day_elements: valid_day_elements.clone(),
            day_delta_elements: day_delta_elements.clone(),
            month_delta_elements: month_delta_elements.clone(),
            year_delta_elements: year_delta_elements.clone(),
        },
        age_claimed_sum,
    );
    let cal_component = CalendarTableComponent::new(
        &mut allocator,
        CalendarTableEval {
            bounds: public.bounds,
            lookup_elements: calendar_elements,
        },
        cal_claimed_sum,
    );
    let valid_day_component = ValidDayTableComponent::new(
        &mut allocator,
        ValidDayTableEval {
            lookup_elements: valid_day_elements,
        },
        valid_day_claimed_sum,
    );
    let day_delta_component = DayDeltaTableComponent::new(
        &mut allocator,
        Preprocessed::day_range().eval(day_delta_elements),
        day_delta_claimed_sum,
    );
    let month_delta_component = MonthDeltaTableComponent::new(
        &mut allocator,
        Preprocessed::month_range().eval(month_delta_elements),
        month_delta_claimed_sum,
    );
    let year_delta_component = YearDeltaTableComponent::new(
        &mut allocator,
        Preprocessed::year_range(&public.bounds).eval(year_delta_elements),
        year_delta_claimed_sum,
    );
    (
        age_component,
        cal_component,
        valid_day_component,
        day_delta_component,
        month_delta_component,
        year_delta_component,
    )
}
