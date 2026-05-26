pub mod age;
pub(crate) mod predicate;
mod range_check;
mod types;
pub(crate) mod utils;

pub use age::strategy::{AgeCheckStrategy, AgeProof};
pub use age::types::{
    AgeBitDecompositionProof, AgeBounds, AgeInputError, AgeRangeCheckProof, Date, DateOfBirth,
    Error, PublicInput, Witness,
};
pub use predicate::{Predicate, StandalonePredicate};
