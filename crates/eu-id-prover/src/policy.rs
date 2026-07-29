use predicates::{Date, NatPublicInput, PublicInput as AgePublicInput};
use serde::{Deserialize, Serialize};

/// The public relying-party policy bound by the proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    pub current_date: Date,
    pub min_age_years: u32,
    pub accepted_nationalities: Vec<u32>,
}

impl Policy {
    pub fn age_public_input(&self) -> AgePublicInput {
        AgePublicInput::new(self.current_date, self.min_age_years)
    }

    pub fn nat_public_input(&self) -> NatPublicInput {
        NatPublicInput::new(self.accepted_nationalities.clone())
    }

    pub fn age_cutoff(&self) -> Date {
        self.age_public_input().cutoff_date()
    }
}

/// Convert an ISO 3166-1 alpha-2 code to the numeric value used by the
/// nationality predicate and the private item-normalization circuit.
pub fn iso_alpha2_to_numeric(alpha2: &str) -> Option<u32> {
    celes::Country::from_alpha2(alpha2)
        .ok()
        .and_then(|country| u32::try_from(country.value).ok())
}
