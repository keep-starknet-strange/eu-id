use std::collections::VecDeque;
use std::fmt;
use std::fs::File;
use std::io::{self, Read};
use std::sync::{Arc, OnceLock};

use num_traits::{One, Zero};
use stwo::core::air::Component;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{M31, P};
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs::blake2_hash::Blake2sHasher;
use stwo::core::Fraction;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::{EvalAtRow, TraceLocationAllocator};

use crate::{Air, AirProver, Ch, Mc, TreeLayout};

/// A 256-row mask already supplies the TS13 profile's full masking floor while
/// allowing its fixed log-8 merged-SHA component to join the same zero-sum
/// ring as the semantic parsers.
pub const CLAIM_MASK_MIN_LOG_SIZE: u32 = 8;
pub const CLAIM_MASK_TRACE_COLUMNS: usize = 4;

const CLAIM_MASK_PROTOCOL_VERSION: u64 = 1;
const CLAIM_MASK_MIN_COMPONENTS: usize = 2;
const CLAIM_MASK_RANDOM_WORDS: usize = 8;
const CLAIM_MASK_SEED_BYTES: usize = 32;
const M31_RANDOM_MASK: u32 = 0x7fff_ffff;
const CLAIM_MASK_CHALLENGE_DOMAIN: [u32; 8] = [
    u32::from_le_bytes(*b"eu-i"),
    u32::from_le_bytes(*b"d/cl"),
    u32::from_le_bytes(*b"aim-"),
    u32::from_le_bytes(*b"mask"),
    u32::from_le_bytes(*b"/cha"),
    u32::from_le_bytes(*b"llen"),
    u32::from_le_bytes(*b"ge/v"),
    u32::from_le_bytes(*b"1\0\0\0"),
];
const CLAIM_MASK_PRG_DOMAIN: &[u8] = b"eu-id/claim-mask/prg/v1";

pub type ClaimMaskColumn = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

#[derive(Debug)]
pub enum ClaimMaskError {
    TooFewComponents {
        count: usize,
    },
    LogSizeTooSmall {
        index: usize,
        log_size: u32,
        minimum: u32,
    },
    LogSizeTooLarge {
        index: usize,
        log_size: u32,
    },
    Entropy(io::Error),
    LogSizeOutOfOrder {
        index: usize,
        expected: u32,
        actual: u32,
    },
    Exhausted {
        requested_log_size: u32,
    },
    NotExhausted {
        remaining: usize,
    },
    ChallengeNotDrawn,
    ChallengeAlreadySet,
    ZeroChallenge,
}

impl fmt::Display for ClaimMaskError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooFewComponents { count } => {
                write!(
                    formatter,
                    "claim-mask ring needs at least 2 components, got {count}"
                )
            }
            Self::LogSizeTooSmall {
                index,
                log_size,
                minimum,
            } => write!(
                formatter,
                "claim-mask component {index} has log size {log_size}, below minimum {minimum}"
            ),
            Self::LogSizeTooLarge { index, log_size } => write!(
                formatter,
                "claim-mask component {index} log size {log_size} does not fit this platform"
            ),
            Self::Entropy(error) => write!(formatter, "claim-mask entropy unavailable: {error}"),
            Self::LogSizeOutOfOrder {
                index,
                expected,
                actual,
            } => write!(
                formatter,
                "claim-mask component {index} expected log size {expected}, got {actual}"
            ),
            Self::Exhausted { requested_log_size } => write!(
                formatter,
                "claim-mask ring exhausted before log size {requested_log_size}"
            ),
            Self::NotExhausted { remaining } => {
                write!(
                    formatter,
                    "{remaining} claim-mask trace(s) were not consumed"
                )
            }
            Self::ChallengeNotDrawn => write!(formatter, "claim-mask challenge was not drawn"),
            Self::ChallengeAlreadySet => {
                write!(formatter, "claim-mask challenge was already initialized")
            }
            Self::ZeroChallenge => write!(formatter, "claim-mask challenge must be nonzero"),
        }
    }
}

impl std::error::Error for ClaimMaskError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Entropy(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for ClaimMaskError {
    fn from(error: io::Error) -> Self {
        Self::Entropy(error)
    }
}

fn validate_ordered_log_sizes(ordered_log_sizes: &[u32]) -> Result<(), ClaimMaskError> {
    if ordered_log_sizes.len() < CLAIM_MASK_MIN_COMPONENTS {
        return Err(ClaimMaskError::TooFewComponents {
            count: ordered_log_sizes.len(),
        });
    }
    for (index, &log_size) in ordered_log_sizes.iter().enumerate() {
        if log_size < CLAIM_MASK_MIN_LOG_SIZE {
            return Err(ClaimMaskError::LogSizeTooSmall {
                index,
                log_size,
                minimum: CLAIM_MASK_MIN_LOG_SIZE,
            });
        }
        if 1usize.checked_shl(log_size).is_none() {
            return Err(ClaimMaskError::LogSizeTooLarge { index, log_size });
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Default)]
pub struct SharedClaimMaskChallenge(Arc<OnceLock<QM31>>);

impl SharedClaimMaskChallenge {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self) -> Option<QM31> {
        self.0.get().copied()
    }

    pub fn require(&self) -> Result<QM31, ClaimMaskError> {
        self.get().ok_or(ClaimMaskError::ChallengeNotDrawn)
    }

    fn set(&self, beta: QM31) -> Result<(), ClaimMaskError> {
        if beta.is_zero() {
            return Err(ClaimMaskError::ZeroChallenge);
        }
        self.0
            .set(beta)
            .map_err(|_| ClaimMaskError::ChallengeAlreadySet)
    }
}

#[derive(Clone, Debug)]
pub struct ClaimMaskChallengeModule {
    shared: SharedClaimMaskChallenge,
    ordered_log_sizes: Vec<u32>,
}

impl ClaimMaskChallengeModule {
    pub fn new(
        shared: SharedClaimMaskChallenge,
        ordered_log_sizes: impl Into<Vec<u32>>,
    ) -> Result<Self, ClaimMaskError> {
        let ordered_log_sizes = ordered_log_sizes.into();
        validate_ordered_log_sizes(&ordered_log_sizes)?;
        Ok(Self {
            shared,
            ordered_log_sizes,
        })
    }
}

fn draw_nonzero_challenge(channel: &mut impl Channel) -> QM31 {
    loop {
        let beta = channel.draw_secure_felt();
        if !beta.is_zero() {
            return beta;
        }
    }
}

impl Air for ClaimMaskChallengeModule {
    fn mix_public(&self, channel: &mut Ch) {
        channel.mix_u32s(&CLAIM_MASK_CHALLENGE_DOMAIN);
        channel.mix_u64(CLAIM_MASK_PROTOCOL_VERSION);
        channel.mix_u64(self.ordered_log_sizes.len() as u64);
        for &log_size in &self.ordered_log_sizes {
            channel.mix_u64(u64::from(log_size));
        }
    }

    fn draw_relations(&mut self, channel: &mut Ch) {
        self.shared
            .set(draw_nonzero_challenge(channel))
            .expect("claim-mask challenge anchor may be drawn only once");
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }
}

impl AirProver for ClaimMaskChallengeModule {
    fn max_log_size(&self) -> u32 {
        0
    }

    fn write_preprocessed(&mut self, _tree: &mut TreeBuilder<SimdBackend, Mc>) {}

    fn write_trace(&mut self, _tree: &mut TreeBuilder<SimdBackend, Mc>) {}

    fn write_interaction(&mut self, _tree: &mut TreeBuilder<SimdBackend, Mc>) {}

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

#[derive(Clone, Debug)]
pub struct ClaimMaskTrace {
    columns: [ClaimMaskColumn; CLAIM_MASK_TRACE_COLUMNS],
    target_sum: QM31,
}

impl ClaimMaskTrace {
    pub fn log_size(&self) -> u32 {
        self.columns[0].domain.log_size()
    }

    pub fn columns(&self) -> &[ClaimMaskColumn; CLAIM_MASK_TRACE_COLUMNS] {
        &self.columns
    }

    pub fn target_sum(&self) -> QM31 {
        self.target_sum
    }

    pub fn packed_rows(&self) -> usize {
        self.columns[0].values.data.len()
    }

    pub fn packed_at(&self, vec_row: usize) -> PackedQM31 {
        PackedQM31::from_packed_m31s(std::array::from_fn(|coordinate| {
            self.columns[coordinate].values.data[vec_row]
        }))
    }

    pub fn packed_fraction_at(&self, vec_row: usize, beta: QM31) -> (PackedQM31, PackedQM31) {
        packed_claim_mask_fraction(self.packed_at(vec_row), beta)
    }

    fn generate(
        log_size: u32,
        target_sum: QM31,
        randomness: &mut ClaimMaskPrg,
    ) -> Result<Self, ClaimMaskError> {
        let row_count = 1usize
            .checked_shl(log_size)
            .ok_or(ClaimMaskError::LogSizeTooLarge { index: 0, log_size })?;
        let mut coordinate_values: [Vec<M31>; CLAIM_MASK_TRACE_COLUMNS] =
            std::array::from_fn(|_| Vec::with_capacity(row_count));
        let mut sum = QM31::zero();
        for _ in 1..row_count {
            let value = randomness.qm31();
            for (coordinate, limb) in value.to_m31_array().into_iter().enumerate() {
                coordinate_values[coordinate].push(limb);
            }
            sum += value;
        }
        for (coordinate, limb) in (target_sum - sum).to_m31_array().into_iter().enumerate() {
            coordinate_values[coordinate].push(limb);
        }
        let domain = CanonicCoset::new(log_size).circle_domain();
        let columns = coordinate_values
            .map(|values| CircleEvaluation::new(domain, BaseColumn::from_iter(values)));
        Ok(Self {
            columns,
            target_sum,
        })
    }
}

#[derive(Debug)]
pub struct ClaimMaskRing {
    traces: VecDeque<ClaimMaskTrace>,
    consumed: usize,
}

impl ClaimMaskRing {
    pub fn new(ordered_log_sizes: &[u32]) -> Result<Self, ClaimMaskError> {
        validate_ordered_log_sizes(ordered_log_sizes)?;
        let mut randomness = ClaimMaskPrg::from_os()?;
        let edges: Vec<QM31> = (0..ordered_log_sizes.len())
            .map(|_| randomness.qm31())
            .collect();
        let targets = (0..edges.len())
            .map(|index| edges[index] - edges[(index + edges.len() - 1) % edges.len()]);
        let traces = ordered_log_sizes
            .iter()
            .copied()
            .zip(targets)
            .map(|(log_size, target)| ClaimMaskTrace::generate(log_size, target, &mut randomness))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            traces: traces.into(),
            consumed: 0,
        })
    }

    pub fn take(&mut self, log_size: u32) -> Result<ClaimMaskTrace, ClaimMaskError> {
        let trace = self.traces.front().ok_or(ClaimMaskError::Exhausted {
            requested_log_size: log_size,
        })?;
        let expected = trace.log_size();
        if expected != log_size {
            return Err(ClaimMaskError::LogSizeOutOfOrder {
                index: self.consumed,
                expected,
                actual: log_size,
            });
        }
        self.consumed += 1;
        Ok(self
            .traces
            .pop_front()
            .expect("claim-mask trace existed before pop"))
    }

    pub fn finish(&self) -> Result<(), ClaimMaskError> {
        if self.traces.is_empty() {
            Ok(())
        } else {
            Err(ClaimMaskError::NotExhausted {
                remaining: self.traces.len(),
            })
        }
    }
}

pub fn add_claim_mask_fraction<E: EvalAtRow>(eval: &mut E, beta: QM31) {
    assert!(!beta.is_zero(), "claim-mask challenge must be nonzero");
    let mask = E::combine_ef(std::array::from_fn(|_| eval.next_trace_mask()));
    eval.write_logup_frac(Fraction::new(mask * beta, E::EF::one()));
}

pub fn packed_claim_mask_fraction(mask: PackedQM31, beta: QM31) -> (PackedQM31, PackedQM31) {
    assert!(!beta.is_zero(), "claim-mask challenge must be nonzero");
    (mask * beta, PackedQM31::one())
}

struct ClaimMaskPrg {
    key: [u8; CLAIM_MASK_SEED_BYTES],
    counter: u64,
    words: [u32; CLAIM_MASK_RANDOM_WORDS],
    next_word: usize,
}

impl ClaimMaskPrg {
    fn from_os() -> Result<Self, ClaimMaskError> {
        let mut seed = [0u8; CLAIM_MASK_SEED_BYTES];
        File::open("/dev/urandom")?.read_exact(&mut seed)?;
        let mut hasher = Blake2sHasher::new();
        hasher.update(CLAIM_MASK_PRG_DOMAIN);
        hasher.update(&seed);
        Ok(Self {
            key: hasher.finalize().0,
            counter: 0,
            words: [0; CLAIM_MASK_RANDOM_WORDS],
            next_word: CLAIM_MASK_RANDOM_WORDS,
        })
    }

    fn m31(&mut self) -> M31 {
        loop {
            if self.next_word == CLAIM_MASK_RANDOM_WORDS {
                let mut hasher = Blake2sHasher::new();
                hasher.update(&self.key);
                hasher.update(&self.counter.to_le_bytes());
                hasher.update(&[0]);
                let block = hasher.finalize().0;
                self.counter = self
                    .counter
                    .checked_add(1)
                    .expect("claim-mask PRG counter exhausted");
                self.words = std::array::from_fn(|index| {
                    u32::from_le_bytes(
                        block[index * 4..index * 4 + 4]
                            .try_into()
                            .expect("four-byte PRG word"),
                    )
                });
                self.next_word = 0;
            }
            let candidate = self.words[self.next_word] & M31_RANDOM_MASK;
            self.next_word += 1;
            if candidate != P {
                return M31::from_u32_unchecked(candidate);
            }
        }
    }

    fn qm31(&mut self) -> QM31 {
        QM31::from_m31_array(std::array::from_fn(|_| self.m31()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mixed_log8_and_log9_ring_is_ordered_exhaustive_and_zero_sum() {
        let log_sizes = [8, 9, 9, 9];
        let mut ring = ClaimMaskRing::new(&log_sizes).expect("mixed-size ring");
        let mut target_sum = QM31::zero();
        for log_size in log_sizes {
            let trace = ring.take(log_size).expect("ordered mask trace");
            assert_eq!(trace.log_size(), log_size);
            target_sum += trace.target_sum();
        }
        assert_eq!(target_sum, QM31::zero());
        ring.finish().expect("all mask traces consumed");
        assert!(matches!(
            ring.take(9),
            Err(ClaimMaskError::Exhausted {
                requested_log_size: 9
            })
        ));

        let mut wrong_order = ClaimMaskRing::new(&[8, 9]).expect("second ring");
        assert!(matches!(
            wrong_order.take(9),
            Err(ClaimMaskError::LogSizeOutOfOrder {
                expected: 8,
                actual: 9,
                ..
            })
        ));
    }
}
