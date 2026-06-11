use stwo::core::channel::Channel;
use crate::age::calendar::{CalendarElements, ValidDayElements};

#[derive(Clone)]
pub struct LookupElements {
    pub calendar: CalendarElements,
    pub valid_day: ValidDayElements,
}

impl LookupElements {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            calendar: CalendarElements::draw(channel),
            valid_day: ValidDayElements::draw(channel),
        }
    }
}