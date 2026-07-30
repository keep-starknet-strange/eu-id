//! Spike-only relation plumbing for the unlinkability cost probes.
//!
//! This module deliberately reuses the hosted-message provider and public
//! HashIo-closer patterns already exercised by `stwo-mldsa`/`stwo-keccak`.
//! Production mdoc entrypoints never construct it.

use air_core::{Air, AirProver, PreprocessedColumnFingerprint, TreeLayout};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};
use stwo_mldsa::air_util::{col_eval, m31, ColEval};
use stwo_mldsa::reference::sponge::shake128;
use stwo_mldsa::stwo_keccak::relations::{HashIoRelation, SharedKeccakRelations};
use stwo_mldsa::stwo_keccak::sponge::Shape;

const DUMMY_STREAM_BASE: u32 = 0x400;
const DUMMY_MESSAGE_LEN: usize = 34;
const DUMMY_SQUEEZE_BLOCKS: usize = 5;
const SHAKE128_RATE: usize = 168;

#[derive(Clone, Copy)]
struct DummyIoEntry {
    stream: u32,
    position: u32,
    byte: u8,
    positive: bool,
}

#[derive(Clone)]
struct DummyIoEval {
    entries: Vec<DummyIoEntry>,
    hash_io: HashIoRelation,
}

impl FrameworkEval for DummyIoEval {
    fn log_size(&self) -> u32 {
        LOG_N_LANES
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_N_LANES + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = eval.next_trace_mask();
        let one = E::F::from(m31(1));
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let enabler = E::EF::from(enabler);
        for entry in &self.entries {
            let numerator = if entry.positive {
                enabler.clone()
            } else {
                -enabler.clone()
            };
            eval.add_to_relation(RelationEntry::new(
                &self.hash_io,
                numerator,
                &[
                    E::F::from(m31(entry.stream)),
                    E::F::from(m31(entry.position)),
                    E::F::from(m31(u32::from(entry.byte))),
                ],
            ));
        }
        // All tuples are verifier-recomputed constants, so one batched
        // accumulator preserves degree <= 2 while isolating service cost.
        eval.finalize_logup_batched(self.entries.len());
        eval
    }
}

fn lane_zero_enabler_trace() -> Vec<ColEval> {
    let mut enabler = vec![m31(0); 1usize << LOG_N_LANES];
    enabler[0] = m31(1);
    vec![col_eval(LOG_N_LANES, enabler)]
}

fn dummy_interaction(
    entries: &[DummyIoEntry],
    hash_io: &HashIoRelation,
) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::from(M31::from_u32_unchecked(0));
    let one = SecureField::from(M31::from_u32_unchecked(1));
    let fractions: Vec<_> = entries
        .iter()
        .map(|entry| {
            let denominator = hash_io.combine(&[
                m31(entry.stream),
                m31(entry.position),
                m31(u32::from(entry.byte)),
            ]);
            (if entry.positive { one } else { -one }, denominator)
        })
        .collect();
    let (mut numerator, mut denominator) = fractions[0];
    for &(next_num, next_den) in &fractions[1..] {
        numerator = next_den * numerator + next_num * denominator;
        denominator *= next_den;
    }

    let mut numerator_lanes = [zero; N_LANES];
    let mut denominator_lanes = [one; N_LANES];
    numerator_lanes[0] = numerator;
    denominator_lanes[0] = denominator;
    let mut generator = LogupTraceGenerator::new(LOG_N_LANES);
    let mut column = generator.new_col();
    column.write_frac(
        0,
        PackedQM31::from_array(numerator_lanes),
        PackedQM31::from_array(denominator_lanes),
    );
    column.finalize_col();
    generator.finalize_last()
}

fn dummy_message(index: usize) -> Vec<u8> {
    let mut message = vec![0u8; DUMMY_MESSAGE_LEN];
    message[32] = (index / 6) as u8;
    message[33] = (index % 6) as u8;
    message
}

fn dummy_streams(index: usize) -> (u32, u32) {
    let absorb = DUMMY_STREAM_BASE + 2 * index as u32;
    (absorb, absorb + 1)
}

fn dummy_entries(dummy_jobs: usize) -> Vec<DummyIoEntry> {
    let mut entries =
        Vec::with_capacity(dummy_jobs * (DUMMY_MESSAGE_LEN + DUMMY_SQUEEZE_BLOCKS * SHAKE128_RATE));
    for index in 0..dummy_jobs {
        let message = dummy_message(index);
        let (absorb_stream, squeeze_stream) = dummy_streams(index);
        entries.extend(
            message
                .iter()
                .enumerate()
                .map(|(position, &byte)| DummyIoEntry {
                    stream: absorb_stream,
                    position: position as u32,
                    byte,
                    positive: true,
                }),
        );
        let (output, _) = shake128(&[message.as_slice()], DUMMY_SQUEEZE_BLOCKS * SHAKE128_RATE);
        entries.extend(
            output
                .into_iter()
                .enumerate()
                .map(|(position, byte)| DummyIoEntry {
                    stream: squeeze_stream,
                    position: position as u32,
                    byte,
                    positive: false,
                }),
        );
    }
    entries
}

pub(crate) fn append_dummy_jobs(
    shapes: &mut Vec<Shape>,
    messages: &mut Vec<Vec<u8>>,
    dummy_jobs: usize,
) {
    for index in 0..dummy_jobs {
        let (absorb_stream, squeeze_stream) = dummy_streams(index);
        shapes.push(Shape::shake128(
            DUMMY_MESSAGE_LEN,
            DUMMY_SQUEEZE_BLOCKS,
            absorb_stream,
            squeeze_stream,
        ));
        messages.push(dummy_message(index));
    }
}

pub(crate) fn append_dummy_shapes(shapes: &mut Vec<Shape>, dummy_jobs: usize) {
    for index in 0..dummy_jobs {
        let (absorb_stream, squeeze_stream) = dummy_streams(index);
        shapes.push(Shape::shake128(
            DUMMY_MESSAGE_LEN,
            DUMMY_SQUEEZE_BLOCKS,
            absorb_stream,
            squeeze_stream,
        ));
    }
}

pub(crate) struct MdocUnlinkSpikeIo {
    dummy_entries: Vec<DummyIoEntry>,
    keccak_handle: SharedKeccakRelations,
    hash_io: Option<HashIoRelation>,
    claims: Vec<SecureField>,
    dummy_component: Option<FrameworkComponent<DummyIoEval>>,
}

impl MdocUnlinkSpikeIo {
    pub(crate) fn new(dummy_jobs: usize, keccak_handle: SharedKeccakRelations) -> Self {
        assert!(dummy_jobs > 0, "empty unlinkability spike I/O module");
        Self {
            dummy_entries: dummy_entries(dummy_jobs),
            keccak_handle,
            hash_io: None,
            claims: Vec::new(),
            dummy_component: None,
        }
    }

    fn hash_io(&self) -> HashIoRelation {
        self.hash_io
            .clone()
            .expect("spike HashIo relation available")
    }
}

impl Air for MdocUnlinkSpikeIo {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x554e_4c49_4e4b);
        channel.mix_u64(self.dummy_entries.len() as u64);
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {
        self.claims.clear();
        let hash_io = self.keccak_handle.get().hash_io;
        let (_, claimed_sum) = dummy_interaction(&self.dummy_entries, &hash_io);
        self.claims.push(claimed_sum);
        self.hash_io = Some(hash_io);
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: vec![LOG_N_LANES],
            interaction: vec![LOG_N_LANES; SECURE_EXTENSION_DEGREE],
        }
    }

    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.clone()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.dummy_component = Some(FrameworkComponent::new(
            allocator,
            DummyIoEval {
                entries: self.dummy_entries.clone(),
                hash_io: self.hash_io(),
            },
            *self.claims.first().expect("dummy I/O claimed sum"),
        ));
        assert_eq!(self.claims.len(), 1, "spike claimed-sum shape");
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .dummy_component
            .as_ref()
            .expect("dummy I/O component is built")]
    }
}

impl AirProver for MdocUnlinkSpikeIo {
    fn max_log_size(&self) -> u32 {
        LOG_N_LANES
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        Vec::new()
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(lane_zero_enabler_trace());
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, claimed_sum) = dummy_interaction(&self.dummy_entries, &self.hash_io());
        debug_assert_eq!(Some(&claimed_sum), self.claims.first());
        tb.extend_evals(trace);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .dummy_component
            .as_ref()
            .expect("dummy I/O component is built")]
    }
}
