use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::qm31::QM31;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::ProvingError;

/// Public statement for a nationality proof.
///
/// The prover proves knowledge of a private nationality that is a member of
/// `acceptable`. The list is normalised (sorted, deduped) by [`PublicInput::new`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicInput {
    pub acceptable: Vec<u32>,
}

impl PublicInput {
    pub fn new(mut acceptable: Vec<u32>) -> Self {
        acceptable.sort_unstable();
        acceptable.dedup();
        Self { acceptable }
    }

    pub(crate) fn mix_into(&self, channel: &mut impl Channel) {
        for &code in &self.acceptable {
            channel.mix_u64(code as u64);
        }
    }
}

/// Private nationality set supplied only to the prover.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateInput {
    pub nationalities: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
    pub public: PublicInput,
    /// The single nationality code selected by the prover.
    pub nationality: u32,
    /// Row index of `nationality` in the sorted `acceptable` table.
    pub nat_index: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Proof {
    pub public: PublicInput,
    pub nat_claimed_sum: QM31,
    pub table_claimed_sum: QM31,
    pub stark_proof: StarkProof<Blake2sMerkleHasher>,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Input(#[from] InputError),
    #[error(transparent)]
    Proving(#[from] ProvingError),
    #[error(transparent)]
    Verification(#[from] VerificationError),
}

#[derive(Debug, thiserror::Error)]
pub enum InputError {
    #[error("acceptable set must contain at least 2 nationalities")]
    AcceptableSetTooSmall,
    #[error("invalid ISO 3166-1 nationality code: {0}")]
    InvalidNationalityCode(u32),
    #[error("no matching nationality found in acceptable set")]
    NoMatch,
    #[error("proof is invalid: claimed logup sums do not cancel")]
    InvalidProof,
}
