use crate::harness::BenchCase;
use predicates::{AgeCheckStrategy, Date, DateOfBirth, PublicInput};

fn default_case(name: &'static str, strategy: AgeCheckStrategy) -> BenchCase {
    BenchCase {
        name,
        strategy,
        public: PublicInput::new(Date { year: 2026, month: 5, day: 19 }, 18),
        dob: DateOfBirth(Date { year: 2000, month: 1, day: 1 }),
    }
}

pub fn bit_decomposition_case() -> BenchCase {
    default_case("age/bit_decomposition", AgeCheckStrategy::BitDecomposition)
}

pub fn range_check_case() -> BenchCase {
    default_case("age/range_check", AgeCheckStrategy::RangeCheck)
}
