use serde::{Deserialize, Serialize};

/// A UTC calendar date.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Date {
    pub year: u32,
    pub month: u32,
    pub day: u32,
}

/// Convert an ISO 3166-1 alpha-2 code to the numeric value used by the
/// nationality predicate and the private item-normalization circuit.
pub fn iso_alpha2_to_numeric(alpha2: &str) -> Option<u32> {
    celes::Country::from_alpha2(alpha2)
        .ok()
        .and_then(|country| u32::try_from(country.value).ok())
}

#[cfg(test)]
mod tests {
    use super::iso_alpha2_to_numeric;

    #[test]
    fn alpha2_maps_to_iso_numeric_and_rejects_unknown_codes() {
        assert_eq!(iso_alpha2_to_numeric("DE"), Some(276));
        assert_eq!(iso_alpha2_to_numeric("FR"), Some(250));
        assert_eq!(iso_alpha2_to_numeric("XK"), Some(383));
        assert_eq!(iso_alpha2_to_numeric("ZZ"), None);
        assert_eq!(iso_alpha2_to_numeric(""), None);
    }
}
