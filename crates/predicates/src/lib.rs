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
// Each strategy is its own predicate; callers pick one and call it directly.
pub use age::strategy::range_check::AgeRangeCheck;
pub use age::types::{
    AgeBounds, AgeInputError, AgeRangeCheckProof, Date, DateOfBirth, Error, PublicInput, Witness,
};
pub use nat::types::{
    Error as NatError, InputError as NatInputError, PrivateInput as NatPrivateInput,
    Proof as NatProof, PublicInput as NatPublicInput,
};
pub use predicate::{PredicateProver, PredicateVerifier};

use strum::IntoEnumIterator;

#[doc(hidden)]
pub const STD_FEATURE_ENABLED: bool = cfg!(feature = "std");

/// Every assigned ISO-3166-1 numeric code the nationality predicate accepts, in
/// ascending order — the same domain [`nat::NationalityPredicate`] validates an
/// acceptable set against.
///
/// This is the "universal accepted set": passing it to [`NatPublicInput::new`]
/// yields a membership table every assigned nationality is trivially in, so it
/// neutralizes the nationality predicate (any held code passes) without
/// depending on the private held value — which is what makes it reconstructible
/// by a verifier that never learns the nationality.
pub fn all_nationality_codes() -> Vec<u32> {
    nat::nationalities::Nationality::iter()
        .map(|n| n as u32)
        .collect()
}
