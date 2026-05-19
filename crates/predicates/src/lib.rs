pub(crate) mod age;
pub(crate) mod predicate;
pub(crate) mod utils;

pub use predicate::{Predicate, StarkPredicate};
pub use age::predicate::AgePredicate;
pub use age::types::{AgeBounds, AgeInputError, AgeProof, AgeWitness, Date, DateOfBirth, Error, Setup};