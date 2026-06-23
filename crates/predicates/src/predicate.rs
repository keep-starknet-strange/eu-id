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
/// Given the public input and the claimed LogUp sums carried by a proof, it
/// validates the public statement and hands back a verifier module (which
/// implements [`Air`]). A verifier-only binary depends on this half alone.
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
