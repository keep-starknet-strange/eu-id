use stwo::core::fields::m31::M31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;

pub trait Predicate {
    type PublicInput;
    type PrivateInput;
    type Witness;
    type Error;

    fn validate(&self, public: &Self::PublicInput) -> Result<(), Self::Error>;

    fn witness(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Witness, Self::Error>;
}

pub trait StarkPredicate: Predicate {
    type Proof;
    
    fn trace(&self, witness: &Self::Witness) -> Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>;

    fn prove(
        &self,
        public: &Self::PublicInput,
        private: &Self::PrivateInput,
    ) -> Result<Self::Proof, Self::Error>;

    fn verify(&self, proof: &Self::Proof) -> Result<(), Self::Error>;
}
