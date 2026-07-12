use predicates::{Date, NatPublicInput, PublicInput as AgePublicInput};
use serde::{Deserialize, Serialize};

/// The public relying-party policy bound by the proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    pub current_date: Date,
    pub min_age_years: u32,
    pub accepted_nationalities: Vec<u32>,
    pub accepted_nationalities_alpha2: Vec<[u8; 2]>,
}

impl Policy {
    pub fn age_public_input(&self) -> AgePublicInput {
        AgePublicInput::new(self.current_date, self.min_age_years)
    }

    pub fn nat_public_input(&self) -> NatPublicInput {
        NatPublicInput::new(self.accepted_nationalities.clone())
    }

    pub fn nat_alpha2_public_input(&self) -> NatPublicInput {
        NatPublicInput::new_alpha2(
            self.accepted_nationalities_alpha2
                .iter()
                .map(|code| u32::from(u16::from_be_bytes(*code)))
                .collect(),
        )
    }

    pub fn age_cutoff(&self) -> Date {
        self.age_public_input().cutoff_date()
    }
}
