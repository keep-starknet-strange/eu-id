use crate::harness::NatBenchCase;
use predicates::{NatPrivateInput, NatPublicInput};

/// ISO 3166-1 numeric codes for the 26 Schengen Area member states.
const SCHENGEN: &[u32] = &[
    40,  // Austria
    56,  // Belgium
    203, // Czechia
    208, // Denmark
    233, // Estonia
    246, // Finland
    250, // France
    276, // Germany
    300, // Greece
    348, // Hungary
    352, // Iceland
    380, // Italy
    428, // Latvia
    438, // Liechtenstein
    440, // Lithuania
    442, // Luxembourg
    470, // Malta
    528, // Netherlands
    578, // Norway
    616, // Poland
    620, // Portugal
    703, // Slovakia
    705, // Slovenia
    724, // Spain
    752, // Sweden
    756, // Switzerland
];

pub fn greek_in_schengen_case() -> NatBenchCase {
    NatBenchCase {
        name: "nat/greek_in_schengen",
        public: NatPublicInput::new(SCHENGEN.to_vec()),
        private: NatPrivateInput {
            nationalities: vec![300], // Greece
        },
    }
}
