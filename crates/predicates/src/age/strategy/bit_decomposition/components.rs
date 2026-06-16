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
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

/// Preprocessed column ids this strategy contributes, in commit order. The
/// orchestrator concatenates these to seed the shared allocator.
pub fn preprocessed_column_ids(bounds: &AgeBounds) -> Vec<PreProcessedColumnId> {
    vec![
        calendar_max_days_col_id(bounds),
        calendar_index_col_id(bounds),
        valid_day_max_days_col_id(),
        valid_day_day_col_id(),
    ]
}

pub fn components(
    allocator: &mut TraceLocationAllocator,
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
    let age_component = AgeBitDecompositionComponent::new(
        allocator,
        BitDecompositionEval {
            public: *public,
            lookup_elements: lookup_elements.clone(),
        },
        age_claimed_sum,
    );
    let cal_component = CalendarTableComponent::new(
        allocator,
        CalendarTableEval {
            bounds: public.bounds,
            lookup_elements: lookup_elements.calendar,
        },
        cal_claimed_sum,
    );
    let valid_day_component = ValidDayTableComponent::new(
        allocator,
        ValidDayTableEval {
            lookup_elements: lookup_elements.valid_day,
        },
        valid_day_claimed_sum,
    );
    (age_component, cal_component, valid_day_component)
}
