use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::qm31::QM31;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::ProvingError;

/// The fixed log-9 nationality trace reserves at least 256 rows for
/// polynomial masking, leaving at most 256 active signed array entries.
pub const MAX_PRESENTED_NATIONALITIES: usize = 256;

/// Code space for the accepted nationality table: ISO 3166-1 numeric codes (the
/// POC path, mapped host-side) or the 2-byte ASCII alpha-2 codes stored as
/// `256*b0 + b1` (the mdoc path, bound directly to the exposed window).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PublicInputKind {
    IsoNumeric,
    Alpha2,
}

/// Public statement for a nationality proof.
///
/// The prover proves knowledge of a private nationality that is a member of
/// `acceptable`. The list is normalised (sorted, deduped) by [`PublicInput::new`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicInput {
    pub kind: PublicInputKind,
    pub acceptable: Vec<u32>,
}

impl PublicInput {
    pub fn new(mut acceptable: Vec<u32>) -> Self {
        acceptable.sort_unstable();
        acceptable.dedup();
        Self {
            kind: PublicInputKind::IsoNumeric,
            acceptable,
        }
    }

    /// Accepted set over 2-byte ASCII alpha-2 codes, each encoded as
    /// `256*b0 + b1` (`u16::from_be_bytes`).
    pub fn new_alpha2(mut acceptable: Vec<u32>) -> Self {
        acceptable.sort_unstable();
        acceptable.dedup();
        Self {
            kind: PublicInputKind::Alpha2,
            acceptable,
        }
    }

    pub fn log_size(&self) -> u32 {
        let padded = (self.acceptable.len() as u32).next_power_of_two();
        padded.ilog2().max(LOG_N_LANES)
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(match self.kind {
            PublicInputKind::IsoNumeric => 0,
            PublicInputKind::Alpha2 => 1,
        });
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
    /// Every signed nationality, in credential array order.
    pub nationalities: Vec<u32>,
    /// Per-entry membership bits. Honest generation marks every accepted
    /// entry; the AIR proves that at least one marked entry is accepted.
    pub accepted: Vec<bool>,
    /// Row in the sorted accepted table for every marked entry.
    pub accepted_rows: Vec<Option<usize>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Proof {
    pub public: PublicInput,
    pub nationality_count: u16,
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
    #[error("acceptable set must contain at least 1 nationality")]
    AcceptableSetTooSmall,
    #[error("invalid ISO 3166-1 nationality code: {0}")]
    InvalidNationalityCode(u32),
    #[error("no matching nationality found in acceptable set")]
    NoMatch,
    #[error("nationality array length {count} exceeds the supported maximum {max}")]
    TooManyNationalities { count: usize, max: usize },
    #[error("proof is invalid: claimed logup sums do not cancel")]
    InvalidProof,
}
