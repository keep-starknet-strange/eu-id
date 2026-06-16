use crate::age::calendar::{
    calendar_index_col_id, calendar_max_days_col_id, valid_day_day_col_id,
    valid_day_max_days_col_id, CalendarTableComponent, CalendarTableEval, ValidDayTableComponent,
    ValidDayTableEval,
};
use crate::age::strategy::bit_decomposition::eval::{
    AgeBitDecompositionComponent, BitDecompositionEval,
};
use crate::age::strategy::bit_decomposition::lookup_elements::LookupElements;
use crate::{AgeBounds, PublicInput};
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::TraceLocationAllocator;

fn make_allocator(bounds: &AgeBounds) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[
        calendar_max_days_col_id(bounds),
        calendar_index_col_id(bounds),
        valid_day_max_days_col_id(),
        valid_day_day_col_id(),
    ])
}

pub fn components(
    public: &PublicInput,
    lookup_elements: LookupElements,
    age_claimed_sum: QM31,
    cal_claimed_sum: QM31,
    valid_day_claimed_sum: QM31,
) -> (
    AgeBitDecompositionComponent,
    CalendarTableComponent,
    ValidDayTableComponent,
) {
    let mut allocator = make_allocator(&public.bounds);
    let age_component = AgeBitDecompositionComponent::new(
        &mut allocator,
        BitDecompositionEval {
            public: *public,
            lookup_elements: lookup_elements.clone(),
        },
        age_claimed_sum,
    );
    let cal_component = CalendarTableComponent::new(
        &mut allocator,
        CalendarTableEval {
            bounds: public.bounds,
            lookup_elements: lookup_elements.calendar,
        },
        cal_claimed_sum,
    );
    let valid_day_component = ValidDayTableComponent::new(
        &mut allocator,
        ValidDayTableEval {
            lookup_elements: lookup_elements.valid_day,
        },
        valid_day_claimed_sum,
    );
    (age_component, cal_component, valid_day_component)
}
