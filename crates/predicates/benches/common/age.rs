use crate::harness::BenchCase;
use predicates::{AgeBitDecomposition, AgeRangeCheck, Date, DateOfBirth, Setup};
use stwo::core::pcs::PcsConfig;

pub struct AgeBitsCase {
    predicate: AgeBitDecomposition,
    setup: Setup,
    dob: DateOfBirth,
}

impl AgeBitsCase {
    pub fn new() -> Self {
        Self {
            predicate: AgeBitDecomposition::new(PcsConfig::default()),
            setup: Setup::new(Date { year: 2026, month: 5, day: 19 }, 18),
            dob: DateOfBirth(Date { year: 2000, month: 1, day: 1 }),
        }
    }
}

impl BenchCase for AgeBitsCase {
    type P = AgeBitDecomposition;

    fn name(&self) -> &'static str {
        "age/bit_decomposition"
    }

    fn predicate(&self) -> &AgeBitDecomposition {
        &self.predicate
    }

    fn public_input(&self) -> &Setup {
        &self.setup
    }

    fn private_input(&self) -> &DateOfBirth {
        &self.dob
    }
}

pub struct AgeRangeCase {
    predicate: AgeRangeCheck,
    setup: Setup,
    dob: DateOfBirth,
}

impl AgeRangeCase {
    pub fn new() -> Self {
        Self {
            predicate: AgeRangeCheck::new(PcsConfig::default()),
            setup: Setup::new(Date { year: 2026, month: 5, day: 19 }, 18),
            dob: DateOfBirth(Date { year: 2000, month: 1, day: 1 }),
        }
    }
}

impl BenchCase for AgeRangeCase {
    type P = AgeRangeCheck;

    fn name(&self) -> &'static str {
        "age/range_check"
    }

    fn predicate(&self) -> &AgeRangeCheck {
        &self.predicate
    }

    fn public_input(&self) -> &Setup {
        &self.setup
    }

    fn private_input(&self) -> &DateOfBirth {
        &self.dob
    }
}
