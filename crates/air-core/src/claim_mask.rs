//! Zero-sum masks for private per-component LogUp claimed sums.
//!
//! A proof publishes every component's LogUp claimed sum even though only their
//! global sum is semantically relevant. For private components, publishing the
//! unmasked values can disclose witness information. This module supplies a
//! shared post-tree-1 challenge `beta` and one committed mask trace per private
//! component. Component `i` adds
//!
//! ```text
//! beta * mask_i(row) / 1
//! ```
//!
//! to its LogUp argument. The trace is sampled with
//! `sum_rows(mask_i) = edge_i - edge_(i-1)`, cyclically, so all mask targets
//! cancel exactly while every proper split is freshly hidden.
//!
//! The [`ClaimMaskChallengeModule`] must be the last module in the combined AIR
//! list. [`air_core::prove`](crate::prove) and
//! [`air_core::verify`](crate::verify) commit tree 1 before drawing relations in
//! module order, making `beta` unpredictable when the mask columns are
//! committed.

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

/// Minimum mask domain: at least 512 rows leave ample unopened randomness after
/// the protocol's query openings.
pub const CLAIM_MASK_MIN_LOG_SIZE: u32 = 9;

/// Four committed base-field columns encode one `QM31` mask per row.
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

/// One committed M31 coordinate column of a claim-mask trace.
pub type ClaimMaskColumn = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

/// Structural or entropy failure while constructing or consuming claim masks.
#[derive(Debug)]
pub enum ClaimMaskError {
    /// A zero-sum ring needs at least two independently masked components.
    TooFewComponents { count: usize },
    /// Small domains expose too much of the conditionally random trace.
    LogSizeTooSmall {
        index: usize,
        log_size: u32,
        minimum: u32,
    },
    /// The requested domain does not fit this platform's address space.
    LogSizeTooLarge { index: usize, log_size: u32 },
    /// The operating system could not provide a fresh seed.
    Entropy(io::Error),
    /// A component attempted to take a mask out of declared module order.
    LogSizeOutOfOrder {
        index: usize,
        expected: u32,
        actual: u32,
    },
    /// Every declared component mask was already consumed.
    Exhausted { requested_log_size: u32 },
    /// Some declared component masks were never consumed.
    NotExhausted { remaining: usize },
    /// A downstream module read `beta` before the anchor drew it.
    ChallengeNotDrawn,
    /// More than one challenge anchor attempted to initialize the shared slot.
    ChallengeAlreadySet,
    /// Only nonzero challenges may enter the shared slot.
    ZeroChallenge,
}

impl fmt::Display for ClaimMaskError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooFewComponents { count } => write!(
                formatter,
                "claim-mask ring needs at least {CLAIM_MASK_MIN_COMPONENTS} components, got {count}"
            ),
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

/// Cloneable, write-once access to the shared post-tree-1 mask challenge.
#[derive(Clone, Debug, Default)]
pub struct SharedClaimMaskChallenge(Arc<OnceLock<QM31>>);

impl SharedClaimMaskChallenge {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the challenge after the anchor has drawn it.
    pub fn get(&self) -> Option<QM31> {
        self.0.get().copied()
    }

    /// Returns the challenge or a precise ordering error.
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

/// Transcript anchor that draws `beta` after tree 1 and after all earlier
/// modules' ordinary relation challenges.
///
/// This module contributes no columns, claimed sums, or AIR components. Append
/// it last to both the prover and verifier module lists.
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

    pub fn ordered_log_sizes(&self) -> &[u32] {
        &self.ordered_log_sizes
    }

    pub fn shared(&self) -> SharedClaimMaskChallenge {
        self.shared.clone()
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

/// Four full-domain mask columns whose coordinate sums equal one private ring
/// target.
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

    pub fn into_columns(self) -> Vec<ClaimMaskColumn> {
        Vec::from(self.columns)
    }

    /// The private cyclic target used to generate this trace.
    pub fn target_sum(&self) -> QM31 {
        self.target_sum
    }

    /// Recompute the exact extension-field sum of all mask rows.
    pub fn trace_sum(&self) -> QM31 {
        QM31::from_m31_array(std::array::from_fn(|coordinate| {
            self.columns[coordinate]
                .values
                .as_slice()
                .iter()
                .copied()
                .fold(M31::zero(), |sum, value| sum + value)
        }))
    }

    pub fn packed_rows(&self) -> usize {
        self.columns[0].values.data.len()
    }

    /// Recombine the four committed coordinate columns at one SIMD row.
    pub fn packed_at(&self, vec_row: usize) -> PackedQM31 {
        PackedQM31::from_packed_m31s(std::array::from_fn(|coordinate| {
            self.columns[coordinate].values.data[vec_row]
        }))
    }

    /// Prover-side `(numerator, denominator)` for this mask at one SIMD row.
    pub fn packed_fraction_at(&self, vec_row: usize, beta: QM31) -> (PackedQM31, PackedQM31) {
        packed_claim_mask_fraction(self.packed_at(vec_row), beta)
    }
}

/// Ordered, one-use mask traces with cyclic zero-sum targets.
#[derive(Debug)]
pub struct ClaimMaskRing {
    traces: VecDeque<ClaimMaskTrace>,
    consumed: usize,
}

impl ClaimMaskRing {
    /// Generate a fresh per-proof ring from operating-system entropy.
    pub fn new(ordered_log_sizes: &[u32]) -> Result<Self, ClaimMaskError> {
        validate_ordered_log_sizes(ordered_log_sizes)?;
        Self::generate(ordered_log_sizes, ClaimMaskPrg::from_os()?)
    }

    fn generate(
        ordered_log_sizes: &[u32],
        mut randomness: ClaimMaskPrg,
    ) -> Result<Self, ClaimMaskError> {
        let edges: Vec<QM31> = (0..ordered_log_sizes.len())
            .map(|_| randomness.qm31())
            .collect();
        let targets: Vec<QM31> = (0..edges.len())
            .map(|index| edges[index] - edges[(index + edges.len() - 1) % edges.len()])
            .collect();

        debug_assert_eq!(
            targets
                .iter()
                .copied()
                .fold(QM31::zero(), |sum, value| sum + value),
            QM31::zero()
        );

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

    pub fn len(&self) -> usize {
        self.traces.len()
    }

    pub fn is_empty(&self) -> bool {
        self.traces.is_empty()
    }

    pub fn remaining(&self) -> usize {
        self.traces.len()
    }

    pub fn target_sums(&self) -> impl ExactSizeIterator<Item = QM31> + '_ {
        self.traces.iter().map(ClaimMaskTrace::target_sum)
    }

    /// Take the next trace, rejecting any component-order mismatch without
    /// consuming the expected entry.
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
            .expect("claim-mask trace existed immediately before pop"))
    }

    /// Assert that every declared private component consumed exactly one mask.
    pub fn finish(&self) -> Result<(), ClaimMaskError> {
        let remaining = self.remaining();
        if remaining == 0 {
            Ok(())
        } else {
            Err(ClaimMaskError::NotExhausted { remaining })
        }
    }
}

impl ClaimMaskTrace {
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

/// AIR-side helper. Call after consuming the component's existing trace masks
/// and before its existing `finalize_logup*` call.
pub fn add_claim_mask_fraction<E: EvalAtRow>(eval: &mut E, beta: QM31) {
    assert!(!beta.is_zero(), "claim-mask challenge must be nonzero");
    let mask = E::combine_ef(std::array::from_fn(|_| eval.next_trace_mask()));
    eval.write_logup_frac(Fraction::new(mask * beta, E::EF::one()));
}

/// Packed prover-side counterpart to [`add_claim_mask_fraction`].
pub fn packed_claim_mask_fraction(mask: PackedQM31, beta: QM31) -> (PackedQM31, PackedQM31) {
    assert!(!beta.is_zero(), "claim-mask challenge must be nonzero");
    (mask * beta, PackedQM31::one())
}

/// Blake2s-based local CSPRNG, independently seeded for every mask ring.
///
/// The seed never enters the Fiat-Shamir transcript. Blake2s expansion avoids
/// issuing one kernel entropy read per trace cell while retaining fresh
/// per-proof masks.
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
        Ok(Self::from_seed(seed))
    }

    fn from_seed(seed: [u8; CLAIM_MASK_SEED_BYTES]) -> Self {
        let mut hasher = Blake2sHasher::new();
        hasher.update(CLAIM_MASK_PRG_DOMAIN);
        hasher.update(&seed);
        Self {
            key: hasher.finalize().0,
            counter: 0,
            words: [0; CLAIM_MASK_RANDOM_WORDS],
            next_word: CLAIM_MASK_RANDOM_WORDS,
        }
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

    const TEST_LOG_SIZES: [u32; 3] = [9, 10, 9];

    fn deterministic_ring(seed_byte: u8) -> ClaimMaskRing {
        ClaimMaskRing::generate(
            &TEST_LOG_SIZES,
            ClaimMaskPrg::from_seed([seed_byte; CLAIM_MASK_SEED_BYTES]),
        )
        .unwrap()
    }

    #[test]
    fn cyclic_targets_sum_to_zero() {
        let ring = deterministic_ring(1);
        assert_eq!(
            ring.target_sums()
                .fold(QM31::zero(), |sum, target| sum + target),
            QM31::zero()
        );
    }

    #[test]
    fn every_trace_has_its_exact_target_sum() {
        let mut ring = deterministic_ring(2);
        for log_size in TEST_LOG_SIZES {
            let trace = ring.take(log_size).unwrap();
            assert_eq!(trace.trace_sum(), trace.target_sum());
        }
        ring.finish().unwrap();
    }

    #[test]
    fn fresh_ring_generation_produces_fresh_traces() {
        let mut first = ClaimMaskRing::new(&[9, 9]).unwrap();
        let mut second = ClaimMaskRing::new(&[9, 9]).unwrap();
        let first = first.take(TEST_LOG_SIZES[0]).unwrap();
        let second = second.take(TEST_LOG_SIZES[0]).unwrap();
        assert_ne!(
            first.columns()[0].values.as_slice(),
            second.columns()[0].values.as_slice()
        );
    }

    #[test]
    fn challenge_anchor_draws_nonzero_beta() {
        let shared = SharedClaimMaskChallenge::new();
        let mut module =
            ClaimMaskChallengeModule::new(shared.clone(), TEST_LOG_SIZES.to_vec()).unwrap();
        let mut channel = Ch::default();
        module.mix_public(&mut channel);
        module.draw_relations(&mut channel);
        assert!(!shared.require().unwrap().is_zero());
    }

    #[test]
    fn transcript_binds_ordered_log_sizes() {
        let shared = SharedClaimMaskChallenge::new();
        let first = ClaimMaskChallengeModule::new(shared.clone(), vec![9, 10, 9]).unwrap();
        let second = ClaimMaskChallengeModule::new(shared, vec![10, 9, 9]).unwrap();
        let mut first_channel = Ch::default();
        let mut second_channel = Ch::default();
        first.mix_public(&mut first_channel);
        second.mix_public(&mut second_channel);
        assert_ne!(first_channel.digest(), second_channel.digest());
    }

    #[test]
    fn ring_rejects_order_mismatch_and_exhaustion() {
        let mut ring = deterministic_ring(5);
        assert!(matches!(
            ring.take(TEST_LOG_SIZES[1]),
            Err(ClaimMaskError::LogSizeOutOfOrder {
                index: 0,
                expected: 9,
                actual: 10
            })
        ));
        assert_eq!(ring.remaining(), TEST_LOG_SIZES.len());
        assert!(matches!(
            ring.finish(),
            Err(ClaimMaskError::NotExhausted { remaining: 3 })
        ));

        for log_size in TEST_LOG_SIZES {
            ring.take(log_size).unwrap();
        }
        ring.finish().unwrap();
        assert!(matches!(
            ring.take(9),
            Err(ClaimMaskError::Exhausted {
                requested_log_size: 9
            })
        ));
    }

    #[test]
    fn invalid_ring_shapes_fail_closed() {
        assert!(matches!(
            ClaimMaskRing::new(&[9]),
            Err(ClaimMaskError::TooFewComponents { count: 1 })
        ));
        assert!(matches!(
            ClaimMaskRing::new(&[9, 8]),
            Err(ClaimMaskError::LogSizeTooSmall {
                index: 1,
                log_size: 8,
                minimum: CLAIM_MASK_MIN_LOG_SIZE
            })
        ));
    }
}
