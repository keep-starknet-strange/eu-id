//! Shared SHA table-provider module.
//!
//! This module moves the message-agnostic split-pack/range table providers out
//! of the packed SHA component. The SHA consumer still owns its main trace,
//! digest relation, full-stream provider, and consumer-side lookups. This module owns
//! only the fixed table preprocessed columns plus the packed-message union
//! multiplicities that satisfy those lookups.

use air_core::claim_mask::{ClaimMaskTrace, SharedClaimMaskChallenge};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::verifier::VerificationError;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::TraceLocationAllocator;

use crate::claim_mask::{validate_claim_masks, ShaClaimMaskConfigError};
use crate::components::{
    shared_table_preprocessed_column_ids, RangeKind, SharedProducer, SharedProducerPairEval,
    RANGE_TABLES,
};
use crate::interaction::{
    build_interaction_columns, claim_mask_fraction_column, producer_blind_frac_column,
    ComponentClaim, Frac,
};
use crate::multiplicities::range_k_multiplicities;
use crate::preprocessed::{
    generate_shared_table_preprocessed_trace, shared_table_preprocessed_log_sizes,
};
use crate::relations::{Sha256Relations, SharedShaTableRelations};
use crate::types::PackedSha256Witness;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShaTablesInteractionClaim {
    /// One claim per producer *pair* (chunk of `PRODUCER_PAIRS`). A chunk of
    /// two producers carries the summed fraction of both in one interaction
    /// column. A chunk of one carries that single producer's fraction. Order
    /// matches `PRODUCER_PAIRS` (== component registration == interaction
    /// column order), so `claimed_sums()` lines up with the committed columns.
    pub pairs: Vec<ComponentClaim>,
}

impl ShaTablesInteractionClaim {
    pub fn claimed_sums(&self) -> Vec<QM31> {
        self.pairs.iter().map(|c| c.claimed_sum).collect()
    }
}

/// The shared-table producer groups.
///
/// Each inner slice contains one or two producers with the same `log_size`.
/// A two-producer group puts both fractions in one `SecureField` interaction
/// column. This list controls the interaction columns, multiplicity columns,
/// log-size layout, and component registration.
///
/// The four range tables form three groups: range₈, range₂ with range₄, and
/// range₅. Each producer emits one Class-D fraction. Thus, the unmasked layout
/// has one interaction column for each group. Claim masking adds one fraction
/// to each group.
const PRODUCER_PAIRS: &[&[SharedProducer]] = &[
    &[SharedProducer::Range(RangeKind::Range8)],
    &[
        SharedProducer::Range(RangeKind::Range2),
        SharedProducer::Range(RangeKind::Range4),
    ],
    &[SharedProducer::Range(RangeKind::Range5)],
];
pub const SHA_TABLE_INTERACTION_CLAIM_COUNT: usize = PRODUCER_PAIRS.len();

fn range_index(kind: RangeKind) -> usize {
    RANGE_TABLES
        .iter()
        .position(|&k| k == kind)
        .expect("range table is enumerated in RANGE_TABLES")
}

#[derive(Clone, Debug)]
pub(crate) struct ShaTableMultiplicities {
    pub range: Vec<Vec<u32>>,
}

impl ShaTableMultiplicities {
    pub(crate) fn from_packed(packed: &PackedSha256Witness) -> Self {
        assert!(
            !packed.messages.is_empty(),
            "shared SHA table provider needs at least one consumer",
        );

        let mut range = Vec::with_capacity(RANGE_TABLES.len());
        for &kind in RANGE_TABLES {
            let producer = SharedProducer::Range(kind);
            range.push(blind_extend(
                range_k_multiplicities(packed, kind),
                1usize << (producer.blind_log_size() - 1),
            ));
        }

        Self { range }
    }
}

/// Add Class-D masks to one multiplicity vector.
///
/// First, fill the real lower half with the honest multiplicities. Next, add a
/// dummy-key upper half of the same size. Fill this upper half with fresh M31
/// cells from the host cryptographic random number generator. The commitment
/// contains this complete vector, and the interaction fraction reads the same
/// cells.
///
/// The mask must stay secret from the verifier. Thus, do not derive it from the
/// transcript. On dummy rows, `emit_blind` multiplies the numerator by
/// `(1 - is_dummy)`. The result is zero, and the random multiplicity does not
/// affect the LogUp balance.
fn blind_extend(mut real: Vec<u32>, real_len: usize) -> Vec<u32> {
    use rand::RngCore;
    debug_assert!(
        real_len.is_power_of_two(),
        "real table size is a power of two"
    );
    assert!(
        real.len() <= real_len,
        "honest multiplicity table exceeds shared producer real region"
    );
    real.resize(real_len, 0);
    let mut out = real;
    out.reserve(real_len);
    // `thread_rng` uses ChaCha12 with an `OsRng` seed. It does not make one
    // system call for each cell in this large loop.
    let mut rng = rand::thread_rng();
    for _ in 0..real_len {
        // Full-field-width random mask cell (M31 reduces mod 2^31 − 1).
        out.push(rng.next_u32() % ((1u32 << 31) - 1));
    }
    out
}

pub struct ShaTablesProver {
    multiplicities: ShaTableMultiplicities,
    shared: SharedShaTableRelations,
    relations: Option<Sha256Relations>,
    interaction_claim: Option<ShaTablesInteractionClaim>,
    components: Option<ShaTablesComponents>,
    claim_masks: Option<Vec<ClaimMaskTrace>>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
}

impl ShaTablesProver {
    pub fn new(packed: &PackedSha256Witness, shared: SharedShaTableRelations) -> Self {
        Self {
            multiplicities: ShaTableMultiplicities::from_packed(packed),
            shared,
            relations: None,
            interaction_claim: None,
            components: None,
            claim_masks: None,
            claim_mask_challenge: None,
        }
    }

    pub fn interaction_claim(&self) -> &ShaTablesInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("shared SHA table interaction claim is set during proving")
    }

    /// Claim-bearing component log sizes in exact component/serialization
    /// order. The caller uses this to take the corresponding slice from one
    /// global zero-sum mask ring.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        PRODUCER_PAIRS
            .iter()
            .map(|chunk| chunk[0].blind_log_size())
            .collect()
    }

    /// Enable private claimed sums for all shared-table components.
    pub fn with_claim_masks(
        mut self,
        traces: Vec<ClaimMaskTrace>,
        challenge: SharedClaimMaskChallenge,
    ) -> Result<Self, ShaClaimMaskConfigError> {
        validate_claim_masks(&self.ordered_claim_mask_log_sizes(), &traces)?;
        self.claim_masks = Some(traces);
        self.claim_mask_challenge = Some(challenge);
        Ok(self)
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked SHA modules")
        })
    }

    fn relations(&self) -> &Sha256Relations {
        self.relations
            .as_ref()
            .expect("shared SHA table relations are drawn before use")
    }

    fn built_components(&self) -> &ShaTablesComponents {
        self.components
            .as_ref()
            .expect("shared SHA table components are built before use")
    }
}

pub struct ShaTablesVerifier {
    interaction_claim: ShaTablesInteractionClaim,
    shared: SharedShaTableRelations,
    relations: Option<Sha256Relations>,
    components: Option<ShaTablesComponents>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
}

impl ShaTablesVerifier {
    pub fn new(
        interaction_claim: ShaTablesInteractionClaim,
        shared: SharedShaTableRelations,
    ) -> Self {
        Self {
            interaction_claim,
            shared,
            relations: None,
            components: None,
            claim_mask_challenge: None,
        }
    }

    /// Claim-bearing component log sizes in exact component/serialization
    /// order.
    pub fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        PRODUCER_PAIRS
            .iter()
            .map(|chunk| chunk[0].blind_log_size())
            .collect()
    }

    /// Configure the verifier for a prover that masks all shared-table claims.
    pub fn with_claim_masks(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge.as_ref().map(|shared| {
            shared
                .require()
                .expect("claim-mask challenge anchor must follow all masked SHA modules")
        })
    }

    fn relations(&self) -> &Sha256Relations {
        self.relations
            .as_ref()
            .expect("shared SHA table relations are drawn before use")
    }

    fn built_components(&self) -> &ShaTablesComponents {
        self.components
            .as_ref()
            .expect("shared SHA table components are built before use")
    }
}

impl Air for ShaTablesProver {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5348_4154_4142_4c45);
        if self.claim_masks.is_some() {
            channel.mix_u64(1);
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw_sha_tables_provider(channel);
        self.shared.set(&relations.range);
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: shared_table_preprocessed_log_sizes(),
            trace: shared_table_trace_log_sizes(self.claim_masks.is_some()),
            interaction: shared_table_interaction_log_sizes(self.claim_masks.is_some()),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.interaction_claim().claimed_sums()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        shared_table_preprocessed_column_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(generate_shared_table_preprocessed_trace().0)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(ShaTablesComponents::new(
            allocator,
            self.interaction_claim(),
            self.relations(),
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for ShaTablesProver {
    fn max_log_size(&self) -> u32 {
        RANGE_TABLES
            .iter()
            .map(|&kind| SharedProducer::Range(kind).blind_log_size())
            .max()
            .expect("shared SHA provider has range tables")
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (evals, _ids, _log_sizes) = generate_shared_table_preprocessed_trace();
        tb.extend_evals(evals);
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let (evals, ids, _log_sizes) = generate_shared_table_preprocessed_trace();
        fingerprint_preprocessed_columns("stwo_sha256::ShaTablesProver", &ids, &evals)
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(shared_table_trace(
            &self.multiplicities,
            self.claim_masks.as_deref(),
        ));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (evals, claim) = shared_table_interaction_trace(
            self.relations(),
            &self.multiplicities,
            self.claim_masks.as_deref(),
            self.claim_mask_beta(),
        );
        tb.extend_evals(evals);
        self.interaction_claim = Some(claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

impl Air for ShaTablesVerifier {
    fn validate_structure(&self) -> Result<(), VerificationError> {
        if self.interaction_claim.pairs.len() != SHA_TABLE_INTERACTION_CLAIM_COUNT {
            return Err(VerificationError::InvalidStructure(format!(
                "shared SHA table claim count is {}, expected {}",
                self.interaction_claim.pairs.len(),
                SHA_TABLE_INTERACTION_CLAIM_COUNT,
            )));
        }
        Ok(())
    }

    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5348_4154_4142_4c45);
        if self.claim_mask_challenge.is_some() {
            channel.mix_u64(1);
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw_sha_tables_provider(channel);
        self.shared.set(&relations.range);
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: shared_table_preprocessed_log_sizes(),
            trace: shared_table_trace_log_sizes(self.claim_mask_challenge.is_some()),
            interaction: shared_table_interaction_log_sizes(self.claim_mask_challenge.is_some()),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        self.interaction_claim.claimed_sums()
    }

    fn preprocessed_column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        shared_table_preprocessed_column_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(generate_shared_table_preprocessed_trace().0)
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(ShaTablesComponents::new(
            allocator,
            &self.interaction_claim,
            self.relations(),
            self.claim_mask_beta(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

/// One multiplicity trace column per producer, in flattened `PRODUCER_PAIRS`
/// order (== the order the paired components read them via `next_trace_mask`).
fn shared_table_trace_log_sizes(masked: bool) -> Vec<u32> {
    let mut out = Vec::new();
    for chunk in PRODUCER_PAIRS {
        out.extend(chunk.iter().map(|producer| producer.blind_log_size()));
        if masked {
            out.extend(std::iter::repeat_n(
                chunk[0].blind_log_size(),
                air_core::claim_mask::CLAIM_MASK_TRACE_COLUMNS,
            ));
        }
    }
    out
}

/// Return the interaction log sizes in `PRODUCER_PAIRS` order.
///
/// Each group has one `SecureField` interaction column. A `SecureField` column
/// contains `SECURE_EXTENSION_DEGREE` base columns. Each Class-D producer emits
/// the fraction `-(1 - is_dummy) * mult`. `finalize_logup_in_pairs` puts two
/// producer fractions in one column. A one-producer group also gets one column.
/// If claim masking is active, add its fraction before the same pairing step.
fn shared_table_interaction_log_sizes(masked: bool) -> Vec<u32> {
    let mut out = Vec::new();
    for chunk in PRODUCER_PAIRS {
        out.extend(std::iter::repeat_n(
            chunk[0].blind_log_size(),
            (chunk.len() + usize::from(masked)).div_ceil(2) * SECURE_EXTENSION_DEGREE,
        ));
    }
    out
}

fn mult_col_to_eval(
    mults: &[u32],
    log_size: u32,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    debug_assert_eq!(mults.len(), 1usize << log_size);
    let domain = CanonicCoset::new(log_size).circle_domain();
    let col: BaseColumn = mults.iter().map(|&m| BaseField::from(m)).collect();
    CircleEvaluation::new(domain, col)
}

/// Multiplicity columns in flattened `PRODUCER_PAIRS` order, so each paired
/// component's `next_trace_mask` calls land on its own producers' columns.
fn shared_table_trace(
    multiplicities: &ShaTableMultiplicities,
    claim_masks: Option<&[ClaimMaskTrace]>,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut out = Vec::new();
    for (index, chunk) in PRODUCER_PAIRS.iter().enumerate() {
        out.extend(chunk.iter().map(|&producer| {
            // Blinded multiplicity vector (real lower half + random dummy upper
            // half), committed at the doubled `blind_log_size`.
            let mults = producer_multiplicities(multiplicities, producer);
            mult_col_to_eval(mults, producer.blind_log_size())
        }));
        if let Some(masks) = claim_masks {
            out.extend(masks[index].columns().iter().cloned());
        }
    }
    out
}

/// Borrow the stored multiplicity vector for one producer.
fn producer_multiplicities(
    multiplicities: &ShaTableMultiplicities,
    producer: SharedProducer,
) -> &[u32] {
    match producer {
        SharedProducer::Range(kind) => &multiplicities.range[range_index(kind)],
    }
}

fn shared_table_interaction_trace(
    relations: &Sha256Relations,
    multiplicities: &ShaTableMultiplicities,
    claim_masks: Option<&[ClaimMaskTrace]>,
    claim_mask_beta: Option<QM31>,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    ShaTablesInteractionClaim,
) {
    let mut combined = Vec::new();
    let mut pair_claims = Vec::with_capacity(PRODUCER_PAIRS.len());

    // One chunk (1 or 2 producers) → one interaction column carrying the
    // chunk's paired fraction, and one `ComponentClaim` per chunk. The chunk
    // order and the within-chunk producer order MUST match `ShaTablesComponents`
    // (registration order) and `shared_table_trace` (multiplicity write order).
    for (index, chunk) in PRODUCER_PAIRS.iter().enumerate() {
        let log_size = chunk[0].blind_log_size();
        // Class D (single gated fraction): each producer contributes ONE
        // fraction `-(1 − is_dummy)·mult`, matching the single `add_to_relation`
        // call `emit_blind` fires in `SharedProducer::emit_entry`.
        // `build_interaction_columns` pairs consecutive fractions, so a
        // A two-producer group `[p0, p1]` uses one column. A one-producer
        // group gets its own column. Append the optional mask last.
        let mut fracs: Vec<Vec<Frac>> = Vec::with_capacity(chunk.len());
        for &producer in chunk.iter() {
            fracs.push(producer_frac(relations, multiplicities, producer));
        }
        if let (Some(masks), Some(beta)) = (claim_masks, claim_mask_beta) {
            fracs.push(claim_mask_fraction_column(&masks[index], beta));
        }
        let (trace, sum) = build_interaction_columns(log_size, fracs, 2);
        combined.extend(trace);
        pair_claims.push(ComponentClaim { claimed_sum: sum });
    }

    (combined, ShaTablesInteractionClaim { pairs: pair_claims })
}

/// Return the Class-D LogUp fraction for one shared-table producer.
///
/// The lower half of the domain contains real rows. The upper half contains
/// dummy rows with keys at or above `2^16`. The numerator is
/// `-(1 - is_dummy) * mult / combine(row)`. It equals `-mult` on real rows and
/// zero on dummy rows. Thus, the random dummy multiplicities do not enter the
/// LogUp sum. See [`producer_blind_frac_column`] and `emit_blind`.
fn producer_frac(
    relations: &Sha256Relations,
    multiplicities: &ShaTableMultiplicities,
    producer: SharedProducer,
) -> Vec<Frac> {
    let real_len = 1usize << (producer.blind_log_size() - 1);
    match producer {
        SharedProducer::Range(kind) => {
            let i = range_index(kind);
            let mults = &multiplicities.range[i];
            let k = kind.bound() as usize;
            let row_iter = range_blind_rows(k, real_len);
            match kind {
                RangeKind::Range2 => {
                    producer_blind_frac_column(&relations.range.range_2, mults, real_len, row_iter)
                }
                RangeKind::Range4 => {
                    producer_blind_frac_column(&relations.range.range_4, mults, real_len, row_iter)
                }
                RangeKind::Range5 => {
                    producer_blind_frac_column(&relations.range.range_5, mults, real_len, row_iter)
                }
                RangeKind::Range8 => {
                    producer_blind_frac_column(&relations.range.range_8, mults, real_len, row_iter)
                }
            }
        }
    }
}

/// The dummy-key base for the masked upper half.
///
/// Honest range consumers emit only 16-bit values below `2^16`. Thus, they
/// cannot use a dummy key at or above `2^16`. The second `emit_blind` term makes
/// each dummy row net zero. A malicious prover cannot use a dummy row as a real
/// row.
const DUMMY_KEY_BASE: u32 = 1 << 16;

/// Blinded 1-cell range rows: `[0, k)` real values then zero padding up to
/// `real_len`, then dummy rows with unreachable value `2^16 + j`.
fn range_blind_rows(k: usize, real_len: usize) -> impl Iterator<Item = [BaseField; 1]> {
    (0..real_len)
        .map(move |j| {
            let value = if j < k { j as u32 } else { 0u32 };
            [BaseField::from(value)]
        })
        .chain((0..real_len).map(|j| [BaseField::from(DUMMY_KEY_BASE + j as u32)]))
}

struct ShaTablesComponents {
    /// One paired-producer component per chunk of [`PRODUCER_PAIRS`], in that
    /// order — same order as the claim's `pairs` and the interaction columns.
    pairs: Vec<stwo_constraint_framework::FrameworkComponent<SharedProducerPairEval>>,
}

impl ShaTablesComponents {
    fn new(
        allocator: &mut TraceLocationAllocator,
        claim: &ShaTablesInteractionClaim,
        relations: &Sha256Relations,
        claim_mask_beta: Option<QM31>,
    ) -> Self {
        let mut pairs = Vec::with_capacity(PRODUCER_PAIRS.len());
        for (chunk, chunk_claim) in PRODUCER_PAIRS.iter().zip(&claim.pairs) {
            pairs.push(stwo_constraint_framework::FrameworkComponent::new(
                allocator,
                SharedProducerPairEval {
                    log_size: chunk[0].blind_log_size(),
                    producers: chunk.to_vec(),
                    relations: relations.clone(),
                    claim_mask_beta,
                },
                chunk_claim.claimed_sum,
            ));
        }
        Self { pairs }
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.pairs.iter().map(|c| c as &dyn Component).collect()
    }

    fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.pairs
            .iter()
            .map(|c| c as &dyn ComponentProver<SimdBackend>)
            .collect()
    }
}
