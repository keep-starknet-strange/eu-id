//! Shared SHA table-provider module.
//!
//! This module moves the message-agnostic range table providers out
//! of repeated SHA instances. Each SHA consumer still owns its main trace,
//! digest relation, field exposure, and consumer-side lookups; this module owns
//! only the fixed table preprocessed columns plus the union multiplicities that
//! satisfy those lookups.

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
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::TraceLocationAllocator;

use crate::components::{
    shared_table_preprocessed_column_ids, RangeKind, SharedProducer, SharedProducerPairEval,
    RANGE_TABLES,
};
use crate::field_exposure::FieldExposure;
use crate::interaction::{
    build_interaction_columns, producer_blind_frac_column, ComponentClaim, Frac,
};
use crate::multiplicities::{range_k_multiplicities, sum_multiplicity_vectors};
use crate::preprocessed::{
    generate_shared_table_preprocessed_trace, shared_table_preprocessed_log_sizes, LOG_SIZE_16,
};
use crate::relations::{Sha256Relations, SharedShaTableRelations};
use crate::types::Sha256Witness;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShaTablesInteractionClaim {
    /// One claim per producer *pair* (chunk of [`PRODUCER_PAIRS`]). A chunk of
    /// two producers carries the summed fraction of both in one interaction
    /// column; a chunk of one carries that single producer's fraction. Order
    /// matches `PRODUCER_PAIRS` (== component registration == interaction
    /// column order), so `claimed_sums()` lines up with the committed columns.
    pub pairs: Vec<ComponentClaim>,
}

impl ShaTablesInteractionClaim {
    pub fn claimed_sums(&self) -> Vec<QM31> {
        self.pairs.iter().map(|c| c.claimed_sum).collect()
    }
}

/// The pairing of shared-table producers into co-located components. Each inner
/// slice is one component owning one or two producers of the *same* `log_size`;
/// a two-producer chunk pairs its fractions into a single `SecureField`
/// interaction column (R2 fraction batching). This one list drives four sites
/// that must stay in lockstep: interaction-column generation
/// (`shared_table_interaction_trace`), multiplicity-column order
/// (`shared_table_trace`), interaction/trace log-size layout, and component
/// registration (`ShaTablesComponents`). Range₁₆ is the lone log₂16 producer;
/// the three small range tables form one pair + one single = 3 chunks. Under
/// Class-D single-gated blinding each producer emits
/// ONE fraction, so each chunk yields exactly one paired interaction column:
/// 4 producers → 3 interaction columns.
const PRODUCER_PAIRS: &[&[SharedProducer]] = &[
    &[SharedProducer::Range(RangeKind::Range16)],
    &[
        SharedProducer::Range(RangeKind::Range2),
        SharedProducer::Range(RangeKind::Range4),
    ],
    &[SharedProducer::Range(RangeKind::Range5)],
];

fn range_index(kind: RangeKind) -> usize {
    RANGE_TABLES
        .iter()
        .position(|&k| k == kind)
        .expect("range table is enumerated in RANGE_TABLES")
}

#[derive(Clone, Debug)]
pub struct ShaTableMultiplicities {
    pub range: Vec<Vec<u32>>,
}

impl ShaTableMultiplicities {
    pub fn from_consumers(consumers: &[(&Sha256Witness, FieldExposure)]) -> Self {
        assert!(
            !consumers.is_empty(),
            "shared SHA table provider needs at least one consumer",
        );

        let mut range = Vec::with_capacity(RANGE_TABLES.len());
        for &kind in RANGE_TABLES {
            range.push(blind_extend(sum_multiplicity_vectors(
                consumers
                    .iter()
                    .map(|(witness, exposure)| range_k_multiplicities(witness, kind, exposure)),
            )));
        }

        Self { range }
    }
}

/// Class-D multiplicity blinding (Q-015 §4b / p4c Class D): double the committed
/// domain by appending `real.len()` fresh random M31 cells over the reserved
/// dummy-key upper half. The stored (blinded) vector is committed as the
/// multiplicity column; the interaction fraction reads the SAME committed cells.
/// Randomness is host CSPRNG, never transcript-derived: the mask must be secret
/// from the verifier. The dummy cells never touch the LogUp balance because
/// `emit_blind` gates the numerator by `(1 − is_dummy)`, forcing it to `0` on
/// every dummy row regardless of the random multiplicity committed there.
fn blind_extend(real: Vec<u32>) -> Vec<u32> {
    use rand::{rngs::OsRng, RngCore};
    let real_len = real.len();
    debug_assert!(
        real_len.is_power_of_two(),
        "real table size is a power of two"
    );
    let mut out = real;
    out.reserve(real_len);
    let mut rng = OsRng;
    for _ in 0..real_len {
        // Full-field-width random mask cell (M31 reduces mod 2^31 − 1).
        out.push(rng.next_u32() % ((1u32 << 31) - 1));
    }
    out
}

/// Per-tree committed-column counts of one shared-SHA producer *component*.
/// After R2 fraction batching a component may own two co-located producers
/// sharing one interaction column; the name
/// joins the producer tags so the probe emits TRUE per-component rows instead
/// of aggregating every producer under one `(tree, log_size)` bucket.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShaTableComponentShape {
    pub name: String,
    pub log_size: u32,
    pub preprocessed_columns: usize,
    pub trace_columns: usize,
    pub interaction_columns: usize,
}

/// Number of preprocessed columns each producer table reads: the row-content
/// value columns plus the Class-D `is_dummy` selector (excludes the
/// multiplicity trace column).
fn producer_preprocessed_cols(producer: SharedProducer) -> usize {
    let value_cols = match producer {
        SharedProducer::Range(..) => 1,
    };
    value_cols + 1 // + Class-D is_dummy selector
}

/// Stable per-producer tag, matching its preprocessed-column family.
fn producer_name(producer: SharedProducer) -> &'static str {
    match producer {
        SharedProducer::Range(kind) => kind.tag(),
    }
}

pub struct ShaTablesProver {
    multiplicities: ShaTableMultiplicities,
    shared: SharedShaTableRelations,
    relations: Option<Sha256Relations>,
    interaction_claim: Option<ShaTablesInteractionClaim>,
    components: Option<ShaTablesComponents>,
}

impl ShaTablesProver {
    pub fn new(multiplicities: ShaTableMultiplicities, shared: SharedShaTableRelations) -> Self {
        Self {
            multiplicities,
            shared,
            relations: None,
            interaction_claim: None,
            components: None,
        }
    }

    pub fn interaction_claim(&self) -> &ShaTablesInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("shared SHA table interaction claim is set during proving")
    }

    /// TRUE per-component committed shape, one row per component (chunk of
    /// [`PRODUCER_PAIRS`]), in registration/commit order. Reconciles exactly to
    /// `layout()` (Σ preprocessed / trace / interaction columns per tree). A
    /// two-producer component pairs its fractions into ONE `SecureField`
    /// interaction column (`SECURE_EXTENSION_DEGREE` base columns); its
    /// preprocessed count is the sum of both producers' tables and its trace
    /// count is 2 (one multiplicity column each).
    pub fn component_shapes(&self) -> Vec<ShaTableComponentShape> {
        PRODUCER_PAIRS
            .iter()
            .map(|chunk| {
                let name = chunk
                    .iter()
                    .map(|&p| producer_name(p))
                    .collect::<Vec<_>>()
                    .join("+");
                let preprocessed_columns =
                    chunk.iter().map(|&p| producer_preprocessed_cols(p)).sum();
                ShaTableComponentShape {
                    name,
                    log_size: chunk[0].blind_log_size(),
                    preprocessed_columns,
                    trace_columns: chunk.len(),
                    // Class D (single gated fraction): each producer emits ONE
                    // gated fraction `-(1 − is_dummy)·mult`, so a 2-producer
                    // chunk's two fractions pair into ONE interaction column and
                    // a 1-producer chunk gets one column too — one paired column
                    // per chunk regardless of producer count.
                    interaction_columns: SECURE_EXTENSION_DEGREE,
                }
            })
            .collect()
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
        }
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
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw_sha_tables_provider(channel);
        self.shared.set(&relations.range);
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: shared_table_preprocessed_log_sizes(),
            trace: shared_table_trace_log_sizes(),
            interaction: shared_table_interaction_log_sizes(),
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

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(ShaTablesComponents::new(
            allocator,
            self.interaction_claim(),
            self.relations(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

impl AirProver for ShaTablesProver {
    fn max_log_size(&self) -> u32 {
        LOG_SIZE_16
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
        tb.extend_evals(shared_table_trace(&self.multiplicities));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        let (evals, claim) = shared_table_interaction_trace(self.relations(), &self.multiplicities);
        tb.extend_evals(evals);
        self.interaction_claim = Some(claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.built_components().component_provers()
    }
}

impl Air for ShaTablesVerifier {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5348_4154_4142_4c45);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let relations = Sha256Relations::draw_sha_tables_provider(channel);
        self.shared.set(&relations.range);
        self.relations = Some(relations);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: shared_table_preprocessed_log_sizes(),
            trace: shared_table_trace_log_sizes(),
            interaction: shared_table_interaction_log_sizes(),
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

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.components = Some(ShaTablesComponents::new(
            allocator,
            &self.interaction_claim,
            self.relations(),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        self.built_components().components()
    }
}

/// One multiplicity trace column per producer, in flattened `PRODUCER_PAIRS`
/// order (== the order the paired components read them via `next_trace_mask`).
fn shared_table_trace_log_sizes() -> Vec<u32> {
    PRODUCER_PAIRS
        .iter()
        .flat_map(|chunk| chunk.iter())
        .map(|p| p.blind_log_size())
        .collect()
}

/// One `SecureField` (= `SECURE_EXTENSION_DEGREE` base columns) interaction
/// column per CHUNK, in `PRODUCER_PAIRS` order. Under Class-D single-gated
/// blinding each producer emits ONE fraction `-(1 − is_dummy)·mult`, so a
/// 2-producer chunk's two fractions pair into one column
/// (`finalize_logup_in_pairs`) and a 1-producer chunk gets one column — one
/// paired interaction column per chunk at the chunk's blinded log size.
fn shared_table_interaction_log_sizes() -> Vec<u32> {
    let mut out = Vec::new();
    for chunk in PRODUCER_PAIRS {
        out.extend(std::iter::repeat_n(
            chunk[0].blind_log_size(),
            SECURE_EXTENSION_DEGREE,
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
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    PRODUCER_PAIRS
        .iter()
        .flat_map(|chunk| chunk.iter())
        .map(|&producer| {
            // Blinded multiplicity vector (real lower half + random dummy upper
            // half), committed at the doubled `blind_log_size`.
            let mults = producer_multiplicities(multiplicities, producer);
            mult_col_to_eval(mults, producer.blind_log_size())
        })
        .collect()
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
    for chunk in PRODUCER_PAIRS {
        let log_size = chunk[0].blind_log_size();
        // Class D (single gated fraction): each producer contributes ONE
        // fraction `-(1 − is_dummy)·mult`, matching the single `add_to_relation`
        // call `emit_blind` fires in `SharedProducer::emit_entry`.
        // `build_interaction_columns` pairs consecutive fractions, so a
        // 2-producer chunk `[p0, p1]` pairs into one column and a 1-producer
        // chunk gets its own column.
        let mut fracs: Vec<Vec<Frac>> = Vec::with_capacity(chunk.len());
        for &producer in chunk.iter() {
            fracs.push(producer_frac(relations, multiplicities, producer));
        }
        // Batch 2: the paired shared-producer components finalize in pairs.
        let (trace, sum) = build_interaction_columns(log_size, 2, fracs);
        combined.extend(trace);
        pair_claims.push(ComponentClaim { claimed_sum: sum });
    }

    (combined, ShaTablesInteractionClaim { pairs: pair_claims })
}

/// The Class-D single gated LogUp fraction of one shared-table producer over
/// the doubled domain: real rows from the table, then reserved dummy rows with
/// unreachable keys `≥ 2^16`. The numerator is `-(1 − is_dummy)·mult/combine(row)`
/// — `-mult` on real rows, `0` on the dummy upper half — so the fresh random
/// blind multiplicity there never enters the LogUp sum (see
/// [`producer_blind_frac_column`] and `emit_blind`).
fn producer_frac(
    relations: &Sha256Relations,
    multiplicities: &ShaTableMultiplicities,
    producer: SharedProducer,
) -> Vec<Frac> {
    let real_len = 1usize << producer.log_size();
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
                RangeKind::Range16 => {
                    producer_blind_frac_column(&relations.range.range_16, mults, real_len, row_iter)
                }
            }
        }
    }
}

/// Reserved dummy-key base for the blinded upper half. Every honest range
/// consumer emits 16-bit values `< 2^16`, so a key `≥ 2^16` is unreachable
/// and no honest use can ever land on a dummy row. `emit_blind`'s cancelling
/// twin additionally makes every dummy row net-zero regardless of its content,
/// so a malicious prover cannot repurpose a dummy row to provide a real key.
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
    ) -> Self {
        let mut pairs = Vec::with_capacity(PRODUCER_PAIRS.len());
        for (chunk, chunk_claim) in PRODUCER_PAIRS.iter().zip(&claim.pairs) {
            pairs.push(stwo_constraint_framework::FrameworkComponent::new(
                allocator,
                SharedProducerPairEval {
                    log_size: chunk[0].blind_log_size(),
                    producers: chunk.to_vec(),
                    relations: relations.clone(),
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
