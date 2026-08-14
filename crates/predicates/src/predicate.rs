use air_core::{Air, AirProver};
use stwo::core::fields::qm31::QM31;

/// Proving side of a predicate.
///
/// Given the public and private inputs, it validates the public statement and
/// hands back a prover module (which implements [`AirProver`]). A prover-only
/// binary depends on this half alone.
pub trait PredicateProver {
    type PublicInput;
    type PrivateInput;
    type Error;
    type Prover: AirProver;

    fn prover(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Prover, Self::Error>;
}

/// Verifying side of a predicate.
///
/// Validates public input and claimed LogUp sums.
///
/// Returns a verifier module that implements [`Air`].
/// A verifier-only binary depends only on this interface.
pub trait PredicateVerifier {
    type PublicInput;
    type Error;
    type Verifier: Air;

    fn verifier(
        &self,
        public: &Self::PublicInput,
        claimed_sums: &[QM31],
    ) -> Result<Self::Verifier, Self::Error>;
}
