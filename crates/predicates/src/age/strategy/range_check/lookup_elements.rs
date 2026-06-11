use stwo::core::channel::Channel;
use crate::age::calendar::{CalendarElements, ValidDayElements};
use crate::range_check::RangeCheckLookupElements;

#[derive(Clone)]
pub struct LookupElements {
    pub calendar: CalendarElements,
    pub valid_day: ValidDayElements,
    pub day_delta: RangeCheckLookupElements,
    pub month_delta: RangeCheckLookupElements,
    pub year_delta: RangeCheckLookupElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            calendar: CalendarElements::draw(channel),
            valid_day: ValidDayElements::draw(channel),
            day_delta: RangeCheckLookupElements::draw(channel),
            month_delta: RangeCheckLookupElements::draw(channel),
            year_delta: RangeCheckLookupElements::draw(channel),
        }
    }
}