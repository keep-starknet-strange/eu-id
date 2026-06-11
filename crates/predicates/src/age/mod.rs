// Calendar tables/components are shared proving utilities used by both strategies.
pub mod calendar;
pub(crate) mod predicate;
pub mod strategy;
pub mod types;

use strategy::{AgeCheckStrategy, AgeProof};
use types::{DateOfBirth, Error, PublicInput};

pub fn prove(
    public: &PublicInput,
    private: &DateOfBirth,
    selected: AgeCheckStrategy,
) -> Result<AgeProof, Error> {
    use self::strategy::bit_decomposition::AgeBitDecomposition;
    use self::strategy::range_check::AgeRangeCheck;
    use stwo::core::pcs::PcsConfig;

    match selected {
        AgeCheckStrategy::BitDecomposition => AgeBitDecomposition::new(PcsConfig::default())
            .prove(public, private)
            .map(AgeProof::BitDecomposition),
        AgeCheckStrategy::RangeCheck => AgeRangeCheck::new(PcsConfig::default())
            .prove(public, private)
            .map(AgeProof::RangeCheck),
    }
}

pub fn verify(proof: &AgeProof) -> Result<(), Error> {
    use self::strategy::bit_decomposition::AgeBitDecomposition;
    use self::strategy::range_check::AgeRangeCheck;
    use stwo::core::pcs::PcsConfig;

    match proof {
        AgeProof::BitDecomposition(p) => AgeBitDecomposition::new(PcsConfig::default()).verify(p),
        AgeProof::RangeCheck(p) => AgeRangeCheck::new(PcsConfig::default()).verify(p),
    }
}
