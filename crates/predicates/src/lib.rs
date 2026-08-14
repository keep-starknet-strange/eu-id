pub mod age;
// Generic range-check gadget shared by the proving process (embedded in each
// strategy's `LookupElements`).
pub mod range_check;
// Column/Trace aliases surface in public interaction-trace fields.
pub mod nat;
pub(crate) mod predicate;
pub mod types;
pub(crate) mod utils;

pub use age::strategy::range_check::AgeRangeCheck;
pub use age::types::{
    AgeBounds, AgeInputError, AgeRangeCheckProof, Date, DateOfBirth, Error, PublicInput, Witness,
};
pub use nat::nationalities::{
    assigned_iso_alpha2_codes, is_assigned_iso_alpha2, is_valid_signed_alpha2, pack_alpha2,
};
pub use nat::types::{
    Error as NatError, InputError as NatInputError, PrivateInput as NatPrivateInput,
    Proof as NatProof, PublicInput as NatPublicInput,
};
pub use predicate::{PredicateProver, PredicateVerifier};
