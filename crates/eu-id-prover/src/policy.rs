use serde::{Deserialize, Serialize};

/// A UTC calendar date.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Date {
    pub year: u32,
    pub month: u32,
    pub day: u32,
}
