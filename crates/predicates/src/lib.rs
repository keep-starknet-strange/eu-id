pub mod age;
// Generic range-check gadget shared by the proving process (embedded in each
// strategy's `LookupElements`).
pub mod range_check;
// Column/Trace aliases surface in public interaction-trace fields.
pub mod nat;
pub(crate) mod predicate;
pub mod types;
pub(crate) mod utils;

// Common, strategy-agnostic surface. Strategy-specific building blocks (which
// reuse the same type names across strategies) are reached by their full path,
// e.g. `age::strategy::range_check::lookup_elements::LookupElements`.
pub use age::strategy::{AgeCheckStrategy, AgeProof};
pub use age::types::{
    AgeBitDecompositionProof, AgeBounds, AgeInputError, AgeRangeCheckProof, Date, DateOfBirth,
    Error, PublicInput, Witness,
};
pub use nat::types::{
    Error as NatError, InputError as NatInputError, PrivateInput as NatPrivateInput,
    Proof as NatProof, PublicInput as NatPublicInput,
};
pub use predicate::{Predicate, StandalonePredicate};
