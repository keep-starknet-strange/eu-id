//! Measured Q-010 spike for the mdoc P4b Longfellow GF(2^128) MAC binding.
//!
//! This is intentionally standalone: it proves the full per-proof M31-side MAC
//! load (six 128-bit halves) before the product mdoc circuit is rewired.

use std::time::Instant;

use air_core::{fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint};
use eu_id_prover::mdoc::mdoc_production_pcs_config;
use serde::Serialize;
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
    TraceLocationAllocator,
};

const MACS_PER_PROOF: usize = 6;
const HALF_BYTES: usize = 16;
const GF_BITS: usize = 128;
const RAW_PRODUCT_BITS: usize = 255;
const TERM_COLS: usize = GF_BITS * GF_BITS;
const RAW_XOR_COLS: usize = TERM_COLS - RAW_PRODUCT_BITS;
const REDUCTION_XOR_COLS: usize = (RAW_PRODUCT_BITS - GF_BITS) * 4;
const TRACE_COLS: usize =
    HALF_BYTES + GF_BITS + GF_BITS + TERM_COLS + RAW_XOR_COLS + REDUCTION_XOR_COLS;
const PREPROCESSED_COLS: usize = 1 + GF_BITS;
const INTERACTION_COLS: usize = 4;
const LOG_SIZE: u32 = 4;

type MacColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MacSpikeComponent = FrameworkComponent<MacSpikeEval>;

#[derive(Clone)]
struct MacHalfWitness {
    ap: [u8; HALF_BYTES],
    x: [u8; HALF_BYTES],
}

struct MacSpike {
    av: [u8; HALF_BYTES],
    rows: [MacHalfWitness; MACS_PER_PROOF],
    tags: [[u8; HALF_BYTES]; MACS_PER_PROOF],
    relation: Option<MacDummyRelation>,
    component: Option<MacSpikeComponent>,
}

impl Clone for MacSpike {
    fn clone(&self) -> Self {
        Self {
            av: self.av,
            rows: self.rows.clone(),
            tags: self.tags,
            relation: None,
            component: None,
        }
    }
}

#[derive(Clone)]
struct MacSpikeEval {
    av_bits: [bool; GF_BITS],
    relation: MacDummyRelation,
}

relation!(MacDummyRelation, 1);

#[derive(Serialize)]
struct Report {
    rayon_num_threads: Option<String>,
    mac_halves: usize,
    trace_columns: usize,
    preprocessed_columns: usize,
    trace_and_interaction_cells: u64,
    preprocessed_cells: u64,
    prove_ms: u128,
    verify_ms: u128,
    proof_bytes: usize,
    byte_breakdown: StarkBreakdown,
    pcs_config: PcsConfig,
}

#[derive(Serialize)]
struct StarkBreakdown {
    config: usize,
    commitments: usize,
    sampled_values: usize,
    decommitments: usize,
    queried_values: usize,
    proof_of_work: usize,
    fri_proof: usize,
}

fn main() {
    let spike = MacSpike::fixture();
    let mut prover = spike.clone();
    let trace_and_interaction_cells = prover.layout().trace.iter().map(|&l| 1u64 << l).sum();
    let preprocessed_cells = prover
        .layout()
        .preprocessed
        .iter()
        .map(|&l| 1u64 << l)
        .sum();

    let start = Instant::now();
    let mut prover_modules: [&mut dyn AirProver; 1] = [&mut prover];
    let proof = air_core::prove(&mut prover_modules, mdoc_production_pcs_config())
        .expect("MAC spike proves");
    let prove_ms = start.elapsed().as_millis();
    let proof_bytes = bincode::serialize(&proof)
        .expect("MAC spike proof serializes")
        .len();
    let stark = &proof.0;
    let byte_breakdown = StarkBreakdown {
        config: bincode_len(&stark.config),
        commitments: bincode_len(&stark.commitments),
        sampled_values: bincode_len(&stark.sampled_values),
        decommitments: bincode_len(&stark.decommitments),
        queried_values: bincode_len(&stark.queried_values),
        proof_of_work: bincode_len(&stark.proof_of_work),
        fri_proof: bincode_len(&stark.fri_proof),
    };

    let mut verifier = spike;
    let start = Instant::now();
    let mut verifier_modules: [&mut dyn Air; 1] = [&mut verifier];
    air_core::verify(&mut verifier_modules, &proof).expect("MAC spike verifies");
    let verify_ms = start.elapsed().as_millis();

    let report = Report {
        rayon_num_threads: std::env::var("RAYON_NUM_THREADS").ok(),
        mac_halves: MACS_PER_PROOF,
        trace_columns: TRACE_COLS,
        preprocessed_columns: PREPROCESSED_COLS,
        trace_and_interaction_cells,
        preprocessed_cells,
        prove_ms,
        verify_ms,
        proof_bytes,
        byte_breakdown,
        pcs_config: proof.config,
    };
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}

impl MacSpike {
    fn fixture() -> Self {
        let av = pseudo_bytes(0xA5);
        let rows = std::array::from_fn(|i| MacHalfWitness {
            ap: pseudo_bytes(0x31u8.wrapping_add(i as u8 * 17)),
            x: pseudo_bytes(0xC7u8.wrapping_add(i as u8 * 29)),
        });
        let tags = std::array::from_fn(|i| {
            let key = xor_128(&rows[i].ap, &av);
            gf128_mul(&key, &rows[i].x)
        });
        Self {
            av,
            rows,
            tags,
            relation: None,
            component: None,
        }
    }

    fn av_bits(&self) -> [bool; GF_BITS] {
        bytes_to_bits(&self.av)
    }
}

impl Air for MacSpike {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(MACS_PER_PROOF as u64);
        for byte in self.av {
            channel.mix_u64(u64::from(byte));
        }
        for tag in self.tags {
            for byte in tag {
                channel.mix_u64(u64::from(byte));
            }
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.relation = Some(MacDummyRelation::draw(channel));
    }

    fn layout(&self) -> air_core::TreeLayout {
        air_core::TreeLayout {
            preprocessed: vec![LOG_SIZE; PREPROCESSED_COLS],
            trace: vec![LOG_SIZE; TRACE_COLS],
            interaction: vec![LOG_SIZE; INTERACTION_COLS],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![QM31::from_u32_unchecked(0, 0, 0, 0)]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut ids = Vec::with_capacity(PREPROCESSED_COLS);
        ids.push(mac_col_id("active"));
        ids.extend((0..GF_BITS).map(|i| mac_col_id(&format!("tag_bit_{i}"))));
        ids
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(MacSpikeComponent::new(
            allocator,
            MacSpikeEval {
                av_bits: self.av_bits(),
                relation: self.relation.clone().expect("MAC dummy relation drawn"),
            },
            QM31::from_u32_unchecked(0, 0, 0, 0),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self.component.as_ref().expect("MAC spike component built")]
    }
}

impl AirProver for MacSpike {
    fn max_log_size(&self) -> u32 {
        LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(preprocessed_trace(&self.tags));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_mac_spike",
            &self.preprocessed_column_ids(),
            &preprocessed_trace(&self.tags),
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(base_trace(&self.rows, &self.av));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let mut logup = LogupTraceGenerator::new(LOG_SIZE);
        logup.col_from_fn(|_| {
            (
                stwo::prover::backend::simd::qm31::PackedQM31::broadcast(QM31::from_u32_unchecked(
                    0, 0, 0, 0,
                )),
                stwo::prover::backend::simd::qm31::PackedQM31::broadcast(QM31::from_u32_unchecked(
                    1, 0, 0, 0,
                )),
            )
        });
        let (trace, claimed_sum) = logup.finalize_last();
        assert_eq!(claimed_sum, QM31::from_u32_unchecked(0, 0, 0, 0));
        tb.extend_evals(trace);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self.component.as_ref().expect("MAC spike component built")]
    }
}

impl FrameworkEval for MacSpikeEval {
    fn log_size(&self) -> u32 {
        LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mac_col_id("active"));
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));

        let mut expected = Vec::with_capacity(GF_BITS);
        for i in 0..GF_BITS {
            expected.push(eval.get_preprocessed_column(mac_col_id(&format!("tag_bit_{i}"))));
        }

        let bytes = (0..HALF_BYTES)
            .map(|_| eval.next_trace_mask())
            .collect::<Vec<_>>();
        let msg_bits = (0..GF_BITS)
            .map(|_| eval.next_trace_mask())
            .collect::<Vec<_>>();
        let ap_bits = (0..GF_BITS)
            .map(|_| eval.next_trace_mask())
            .collect::<Vec<_>>();

        for bit in msg_bits.iter().chain(&ap_bits) {
            eval.add_constraint(active.clone() * bit.clone() * (bit.clone() - one.clone()));
        }
        for byte_index in 0..HALF_BYTES {
            let mut recomposed = m31_const::<E>(0);
            for bit_index in 0..8 {
                recomposed = recomposed
                    + msg_bits[byte_index * 8 + bit_index].clone()
                        * m31_const::<E>(1u32 << bit_index);
            }
            eval.add_constraint(active.clone() * (bytes[byte_index].clone() - recomposed));
            eval.add_constraint((one.clone() - active.clone()) * bytes[byte_index].clone());
        }

        let mut terms = Vec::with_capacity(TERM_COLS);
        for key_index in 0..GF_BITS {
            let key_bit = if self.av_bits[key_index] {
                one.clone() - ap_bits[key_index].clone()
            } else {
                ap_bits[key_index].clone()
            };
            for msg_index in 0..GF_BITS {
                let term = eval.next_trace_mask();
                eval.add_constraint(
                    active.clone() * (term.clone() - key_bit.clone() * msg_bits[msg_index].clone()),
                );
                eval.add_constraint((one.clone() - active.clone()) * term.clone());
                terms.push(term);
            }
        }

        let mut coeffs = Vec::with_capacity(RAW_PRODUCT_BITS);
        for product_bit in 0..RAW_PRODUCT_BITS {
            let mut acc = None;
            for key_index in 0..GF_BITS {
                if product_bit < key_index {
                    continue;
                }
                let msg_index = product_bit - key_index;
                if msg_index >= GF_BITS {
                    continue;
                }
                let term = terms[key_index * GF_BITS + msg_index].clone();
                acc = Some(match acc {
                    None => term,
                    Some(prev) => {
                        let next = eval.next_trace_mask();
                        constrain_xor(&mut eval, &active, &prev, &term, &next);
                        next
                    }
                });
            }
            coeffs.push(acc.expect("each raw product coefficient has a term"));
        }

        for high in (GF_BITS..RAW_PRODUCT_BITS).rev() {
            let high_bit = coeffs[high].clone();
            for offset in [0usize, 1, 2, 7] {
                let target = high - GF_BITS + offset;
                let next = eval.next_trace_mask();
                constrain_xor(&mut eval, &active, &coeffs[target], &high_bit, &next);
                coeffs[target] = next;
            }
        }

        for bit in 0..GF_BITS {
            eval.add_constraint(active.clone() * (coeffs[bit].clone() - expected[bit].clone()));
        }
        let zero = m31_const::<E>(0);
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(zero.clone()),
            &[zero],
        ));
        eval.finalize_logup();
        eval
    }
}

fn constrain_xor<E: EvalAtRow>(eval: &mut E, active: &E::F, a: &E::F, b: &E::F, out: &E::F) {
    let two = m31_const::<E>(2);
    let one = m31_const::<E>(1);
    eval.add_constraint(
        active.clone() * (out.clone() - (a.clone() + b.clone() - two * a.clone() * b.clone())),
    );
    eval.add_constraint(active.clone() * out.clone() * (out.clone() - one.clone()));
    eval.add_constraint((one - active.clone()) * out.clone());
}

fn preprocessed_trace(tags: &[[u8; HALF_BYTES]; MACS_PER_PROOF]) -> Vec<MacColumnEval> {
    let mut columns = vec![vec![M31::from_u32_unchecked(0); 1 << LOG_SIZE]; PREPROCESSED_COLS];
    for row in 0..MACS_PER_PROOF {
        columns[0][row] = M31::from_u32_unchecked(1);
        let bits = bytes_to_bits(&tags[row]);
        for bit in 0..GF_BITS {
            columns[1 + bit][row] = M31::from_u32_unchecked(u32::from(bits[bit]));
        }
    }
    columns.into_iter().map(column_eval).collect()
}

fn base_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    av: &[u8; HALF_BYTES],
) -> Vec<MacColumnEval> {
    let mut columns = vec![vec![M31::from_u32_unchecked(0); 1 << LOG_SIZE]; TRACE_COLS];
    for (row_index, row) in rows.iter().enumerate() {
        let mut cursor = 0;
        for byte in row.x {
            columns[cursor][row_index] = M31::from_u32_unchecked(u32::from(byte));
            cursor += 1;
        }
        let msg_bits = bytes_to_bits(&row.x);
        let ap_bits = bytes_to_bits(&row.ap);
        for bit in msg_bits {
            columns[cursor][row_index] = M31::from_u32_unchecked(u32::from(bit));
            cursor += 1;
        }
        for bit in ap_bits {
            columns[cursor][row_index] = M31::from_u32_unchecked(u32::from(bit));
            cursor += 1;
        }

        let av_bits = bytes_to_bits(av);
        let key_bits = xor_bits(&bytes_to_bits(&row.ap), &av_bits);
        let mut terms = vec![false; TERM_COLS];
        for key_index in 0..GF_BITS {
            for msg_index in 0..GF_BITS {
                let term = key_bits[key_index] & msg_bits[msg_index];
                terms[key_index * GF_BITS + msg_index] = term;
                columns[cursor][row_index] = M31::from_u32_unchecked(u32::from(term));
                cursor += 1;
            }
        }

        let mut coeffs = vec![false; RAW_PRODUCT_BITS];
        for product_bit in 0..RAW_PRODUCT_BITS {
            let mut acc = false;
            let mut first = true;
            for key_index in 0..GF_BITS {
                if product_bit < key_index {
                    continue;
                }
                let msg_index = product_bit - key_index;
                if msg_index >= GF_BITS {
                    continue;
                }
                let term = terms[key_index * GF_BITS + msg_index];
                if first {
                    acc = term;
                    first = false;
                } else {
                    acc ^= term;
                    columns[cursor][row_index] = M31::from_u32_unchecked(u32::from(acc));
                    cursor += 1;
                }
            }
            coeffs[product_bit] = acc;
        }

        for high in (GF_BITS..RAW_PRODUCT_BITS).rev() {
            let high_bit = coeffs[high];
            for offset in [0usize, 1, 2, 7] {
                let target = high - GF_BITS + offset;
                coeffs[target] ^= high_bit;
                columns[cursor][row_index] = M31::from_u32_unchecked(u32::from(coeffs[target]));
                cursor += 1;
            }
        }
        assert_eq!(cursor, TRACE_COLS);
    }
    columns.into_iter().map(column_eval).collect()
}

fn column_eval(values: Vec<M31>) -> MacColumnEval {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << LOG_SIZE];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, LOG_SIZE),
            LOG_SIZE,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(LOG_SIZE).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

fn mac_col_id(id: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/mac_spike/{id}"),
    }
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn pseudo_bytes(seed: u8) -> [u8; HALF_BYTES] {
    let mut out = [0u8; HALF_BYTES];
    let mut state = seed;
    for byte in &mut out {
        state = state.wrapping_mul(73).wrapping_add(41);
        *byte = state;
    }
    out
}

fn bytes_to_bits(bytes: &[u8; HALF_BYTES]) -> [bool; GF_BITS] {
    let mut bits = [false; GF_BITS];
    for (byte_index, byte) in bytes.iter().enumerate() {
        for bit_index in 0..8 {
            bits[byte_index * 8 + bit_index] = ((byte >> bit_index) & 1) == 1;
        }
    }
    bits
}

fn bits_to_bytes(bits: &[bool; GF_BITS]) -> [u8; HALF_BYTES] {
    let mut bytes = [0u8; HALF_BYTES];
    for (bit_index, bit) in bits.iter().enumerate() {
        if *bit {
            bytes[bit_index / 8] |= 1 << (bit_index % 8);
        }
    }
    bytes
}

fn xor_128(left: &[u8; HALF_BYTES], right: &[u8; HALF_BYTES]) -> [u8; HALF_BYTES] {
    std::array::from_fn(|i| left[i] ^ right[i])
}

fn xor_bits(left: &[bool; GF_BITS], right: &[bool; GF_BITS]) -> [bool; GF_BITS] {
    std::array::from_fn(|i| left[i] ^ right[i])
}

fn gf128_mul(left: &[u8; HALF_BYTES], right: &[u8; HALF_BYTES]) -> [u8; HALF_BYTES] {
    let left = bytes_to_bits(left);
    let right = bytes_to_bits(right);
    let mut coeffs = [false; RAW_PRODUCT_BITS];
    for i in 0..GF_BITS {
        for j in 0..GF_BITS {
            coeffs[i + j] ^= left[i] & right[j];
        }
    }
    for high in (GF_BITS..RAW_PRODUCT_BITS).rev() {
        if coeffs[high] {
            for offset in [0usize, 1, 2, 7] {
                coeffs[high - GF_BITS + offset] ^= true;
            }
        }
    }
    let mut out = [false; GF_BITS];
    out.copy_from_slice(&coeffs[..GF_BITS]);
    bits_to_bytes(&out)
}

fn bincode_len<T: Serialize>(value: &T) -> usize {
    bincode::serialize(value)
        .expect("MAC spike proof byte breakdown serializes")
        .len()
}
