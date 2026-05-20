pub(crate) mod age;
pub(crate) mod predicate;
pub(crate) mod utils;

pub use predicate::{Predicate, StarkPredicate};
pub use age::predicate::AgePredicate;
pub use age::types::{AgeBounds, AgeInputError, AgeBitDecompositionProof, AgeRangeCheckProof, Witness, Date, DateOfBirth, Error, PublicInput};
pub use age::strategy::bit_decomposition::AgeBitDecomposition;
pub use age::strategy::range_check::AgeRangeCheck;