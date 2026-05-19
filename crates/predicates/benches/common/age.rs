use crate::harness::BenchCase;
use predicates::{AgePredicate, Date, DateOfBirth, Setup};
use stwo::core::pcs::PcsConfig;

pub struct AgeBitDecomposition {
    predicate: AgePredicate,
    setup: Setup,
    dob: DateOfBirth,
}

impl AgeBitDecomposition {
    pub fn new() -> Self {
        Self {
            predicate: AgePredicate::new(PcsConfig::default()),
            setup: Setup::new(Date { year: 2026, month: 5, day: 19 }, 18),
            dob: DateOfBirth(Date { year: 2000, month: 1, day: 1 }),
        }
    }
}

impl BenchCase for AgeBitDecomposition {
    type P = AgePredicate;

    fn name(&self) -> &'static str {
        "age/bit_decomposition"
    }

    fn predicate(&self) -> &AgePredicate {
        &self.predicate
    }

    fn public_input(&self) -> &Setup {
        &self.setup
    }

    fn private_input(&self) -> &DateOfBirth {
        &self.dob
    }
}
