//! Measured Q-011 re-spike for the mdoc P4b Longfellow GF(2^128) MAC binding.
//!
//! This stays standalone: it prices the M31-side six-half MAC load before the
//! product mdoc circuit is rewired.

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
use stwo::core::Fraction;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};

const MACS_PER_PROOF: usize = 6;
const HALF_BYTES: usize = 16;
const GF_BITS: usize = 128;
const NIBBLES_PER_HALF: usize = 32;
const PRODUCTS_PER_MAC: usize = NIBBLES_PER_HALF * NIBBLES_PER_HALF;
const ACTIVE_ROWS: usize = MACS_PER_PROOF * PRODUCTS_PER_MAC;
const CONSUMER_LOG_SIZE: u32 = 13;
const TABLE_LOG_SIZE: u32 = 8;
const REDUCE_TABLE_LOG_SIZE: u32 = 13;
const PRODUCT_POSITIONS: usize = 63;
const REDUCE_TABLE_ROWS: usize = PRODUCT_POSITIONS * 128;
const CONSUMER_PREPROCESSED_COLS: usize = 3 + GF_BITS;
const TABLE_PREPROCESSED_COLS: usize = 3;
const REDUCE_TABLE_PREPROCESSED_COLS: usize = 2 + GF_BITS;
const CONSUMER_TRACE_COLS: usize = 4 + GF_BITS + GF_BITS + GF_BITS;
const TABLE_TRACE_COLS: usize = 1;
const REDUCE_TABLE_TRACE_COLS: usize = 1;
const INTERACTION_COLS_PER_FRACTION: usize = 4;

type MacColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type ConsumerComponent = FrameworkComponent<MacConsumerEval>;
type TableComponent = FrameworkComponent<Clmul4TableEval>;
type ReduceTableComponent = FrameworkComponent<ReduceTableEval>;

relation!(Clmul4Relation, 3);
relation!(ReduceRelation, 130);

#[derive(Clone)]
struct MacHalfWitness {
    ap: [u8; HALF_BYTES],
    x: [u8; HALF_BYTES],
}

struct MacSpike {
    av: [u8; HALF_BYTES],
    rows: [MacHalfWitness; MACS_PER_PROOF],
    tags: [[u8; HALF_BYTES]; MACS_PER_PROOF],
    clmul_relation: Option<Clmul4Relation>,
    reduce_relation: Option<ReduceRelation>,
    consumer_claim: Option<QM31>,
    clmul_table_claim: Option<QM31>,
    reduce_table_claim: Option<QM31>,
    consumer_component: Option<ConsumerComponent>,
    clmul_table_component: Option<TableComponent>,
    reduce_table_component: Option<ReduceTableComponent>,
}

impl Clone for MacSpike {
    fn clone(&self) -> Self {
        Self {
            av: self.av,
            rows: self.rows.clone(),
            tags: self.tags,
            clmul_relation: None,
            reduce_relation: None,
            consumer_claim: self.consumer_claim,
            clmul_table_claim: self.clmul_table_claim,
            reduce_table_claim: self.reduce_table_claim,
            consumer_component: None,
            clmul_table_component: None,
            reduce_table_component: None,
        }
    }
}

#[derive(Clone)]
struct MacConsumerEval {
    clmul_relation: Clmul4Relation,
    reduce_relation: ReduceRelation,
}

#[derive(Clone)]
struct Clmul4TableEval {
    relation: Clmul4Relation,
}

#[derive(Clone)]
struct ReduceTableEval {
    relation: ReduceRelation,
}

#[derive(Serialize)]
struct Report {
    rayon_num_threads: Option<String>,
    mac_halves: usize,
    active_rows: usize,
    consumer_trace_columns: usize,
    consumer_preprocessed_columns: usize,
    clmul_table_trace_columns: usize,
    clmul_table_preprocessed_columns: usize,
    reduce_table_trace_columns: usize,
    reduce_table_preprocessed_columns: usize,
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
    assert_component_shape(&spike);
    let mut prover = spike.clone();
    let preprocessed_cells = cells(&prover.layout().preprocessed);
    let trace_and_interaction_cells =
        cells(&prover.layout().trace) + cells(&prover.layout().interaction);

    let start = Instant::now();
    let mut prover_modules: [&mut dyn AirProver; 1] = [&mut prover];
    let proof = air_core::prove(&mut prover_modules, mdoc_production_pcs_config())
        .expect("MAC spike proves");
    let prove_ms = start.elapsed().as_millis();
    let proof_bytes = bincode_len(&proof);
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

    let mut verifier = spike.with_claims(
        prover.consumer_claim.expect("consumer claim set"),
        prover.clmul_table_claim.expect("clmul table claim set"),
        prover.reduce_table_claim.expect("reduce table claim set"),
    );
    let start = Instant::now();
    let mut verifier_modules: [&mut dyn Air; 1] = [&mut verifier];
    air_core::verify(&mut verifier_modules, &proof).expect("MAC spike verifies");
    let verify_ms = start.elapsed().as_millis();

    let report = Report {
        rayon_num_threads: std::env::var("RAYON_NUM_THREADS").ok(),
        mac_halves: MACS_PER_PROOF,
        active_rows: ACTIVE_ROWS,
        consumer_trace_columns: CONSUMER_TRACE_COLS,
        consumer_preprocessed_columns: CONSUMER_PREPROCESSED_COLS,
        clmul_table_trace_columns: TABLE_TRACE_COLS,
        clmul_table_preprocessed_columns: TABLE_PREPROCESSED_COLS,
        reduce_table_trace_columns: REDUCE_TABLE_TRACE_COLS,
        reduce_table_preprocessed_columns: REDUCE_TABLE_PREPROCESSED_COLS,
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

fn assert_component_shape(spike: &MacSpike) {
    let zero = QM31::from_u32_unchecked(0, 0, 0, 0);
    let mut module = spike.clone().with_claims(zero, zero, zero);
    let mut channel = Blake2sChannel::default();
    module.draw_relations(&mut channel);
    let mut allocator =
        TraceLocationAllocator::new_with_preprocessed_columns(&module.preprocessed_column_ids());
    module.build_components(&mut allocator);
    let consumer_logs = module
        .consumer_component
        .as_ref()
        .expect("consumer component built")
        .trace_log_degree_bounds();
    assert_eq!(
        consumer_logs[stwo_constraint_framework::ORIGINAL_TRACE_IDX].len(),
        CONSUMER_TRACE_COLS,
        "consumer component trace column count"
    );
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
            clmul_relation: None,
            reduce_relation: None,
            consumer_claim: None,
            clmul_table_claim: None,
            reduce_table_claim: None,
            consumer_component: None,
            clmul_table_component: None,
            reduce_table_component: None,
        }
    }

    fn with_claims(
        mut self,
        consumer_claim: QM31,
        clmul_table_claim: QM31,
        reduce_table_claim: QM31,
    ) -> Self {
        self.consumer_claim = Some(consumer_claim);
        self.clmul_table_claim = Some(clmul_table_claim);
        self.reduce_table_claim = Some(reduce_table_claim);
        self
    }

    fn clmul_relation(&self) -> &Clmul4Relation {
        self.clmul_relation
            .as_ref()
            .expect("clmul_4 relation drawn before use")
    }

    fn reduce_relation(&self) -> &ReduceRelation {
        self.reduce_relation
            .as_ref()
            .expect("reduce relation drawn before use")
    }
}

impl Air for MacSpike {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x4d44_4f43_4d41_4302);
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
        self.clmul_relation = Some(Clmul4Relation::draw(channel));
        self.reduce_relation = Some(ReduceRelation::draw(channel));
    }

    fn layout(&self) -> air_core::TreeLayout {
        air_core::TreeLayout {
            preprocessed: std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_PREPROCESSED_COLS)
                .chain(std::iter::repeat_n(TABLE_LOG_SIZE, TABLE_PREPROCESSED_COLS))
                .chain(std::iter::repeat_n(
                    REDUCE_TABLE_LOG_SIZE,
                    REDUCE_TABLE_PREPROCESSED_COLS,
                ))
                .collect(),
            trace: std::iter::repeat_n(CONSUMER_LOG_SIZE, CONSUMER_TRACE_COLS)
                .chain([TABLE_LOG_SIZE])
                .chain([REDUCE_TABLE_LOG_SIZE])
                .collect(),
            interaction: std::iter::repeat_n(CONSUMER_LOG_SIZE, INTERACTION_COLS_PER_FRACTION)
                .chain(std::iter::repeat_n(
                    TABLE_LOG_SIZE,
                    INTERACTION_COLS_PER_FRACTION,
                ))
                .chain(std::iter::repeat_n(
                    REDUCE_TABLE_LOG_SIZE,
                    INTERACTION_COLS_PER_FRACTION,
                ))
                .collect(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![
            self.consumer_claim.expect("consumer claim set"),
            self.clmul_table_claim.expect("clmul table claim set"),
            self.reduce_table_claim.expect("reduce table claim set"),
        ]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut ids = Vec::with_capacity(CONSUMER_PREPROCESSED_COLS + TABLE_PREPROCESSED_COLS);
        ids.push(mac_col_id("consumer/active"));
        ids.push(mac_col_id("consumer/first"));
        ids.push(mac_col_id("consumer/last"));
        ids.extend((0..GF_BITS).map(|i| mac_col_id(&format!("consumer/tag_bit_{i}"))));
        ids.push(mac_col_id("clmul_4/a"));
        ids.push(mac_col_id("clmul_4/b"));
        ids.push(mac_col_id("clmul_4/product"));
        ids.push(mac_col_id("reduce/position"));
        ids.push(mac_col_id("reduce/product"));
        ids.extend((0..GF_BITS).map(|i| mac_col_id(&format!("reduce/contribution_bit_{i}"))));
        ids
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.consumer_component = Some(ConsumerComponent::new(
            allocator,
            MacConsumerEval {
                clmul_relation: self.clmul_relation().clone(),
                reduce_relation: self.reduce_relation().clone(),
            },
            self.consumer_claim.expect("consumer claim set"),
        ));
        self.clmul_table_component = Some(TableComponent::new(
            allocator,
            Clmul4TableEval {
                relation: self.clmul_relation().clone(),
            },
            self.clmul_table_claim.expect("clmul table claim set"),
        ));
        self.reduce_table_component = Some(ReduceTableComponent::new(
            allocator,
            ReduceTableEval {
                relation: self.reduce_relation().clone(),
            },
            self.reduce_table_claim.expect("reduce table claim set"),
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.consumer_component
                .as_ref()
                .expect("consumer component built"),
            self.clmul_table_component
                .as_ref()
                .expect("clmul table component built"),
            self.reduce_table_component
                .as_ref()
                .expect("reduce table component built"),
        ]
    }
}

impl AirProver for MacSpike {
    fn max_log_size(&self) -> u32 {
        CONSUMER_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        CONSUMER_LOG_SIZE + 1
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
        let (consumer, clmul_multiplicities, reduce_multiplicities) =
            consumer_trace(&self.rows, &self.av);
        tb.extend_evals(consumer);
        tb.extend_evals(clmul_table_trace(&clmul_multiplicities));
        tb.extend_evals(reduce_table_trace(&reduce_multiplicities));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (_consumer, clmul_multiplicities, reduce_multiplicities) =
            consumer_trace(&self.rows, &self.av);
        let (consumer_trace, consumer_claim) = consumer_interaction_trace(
            &self.rows,
            &self.av,
            self.clmul_relation(),
            self.reduce_relation(),
        );
        let (clmul_table_trace, clmul_table_claim) =
            clmul_table_interaction_trace(&clmul_multiplicities, self.clmul_relation());
        let (reduce_table_trace, reduce_table_claim) =
            reduce_table_interaction_trace(&reduce_multiplicities, self.reduce_relation());
        tb.extend_evals(consumer_trace);
        tb.extend_evals(clmul_table_trace);
        tb.extend_evals(reduce_table_trace);
        self.consumer_claim = Some(consumer_claim);
        self.clmul_table_claim = Some(clmul_table_claim);
        self.reduce_table_claim = Some(reduce_table_claim);
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.consumer_component
                .as_ref()
                .expect("consumer component built"),
            self.clmul_table_component
                .as_ref()
                .expect("clmul table component built"),
            self.reduce_table_component
                .as_ref()
                .expect("reduce table component built"),
        ]
    }
}

impl FrameworkEval for MacConsumerEval {
    fn log_size(&self) -> u32 {
        CONSUMER_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        CONSUMER_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mac_col_id("consumer/active"));
        let first = eval.get_preprocessed_column(mac_col_id("consumer/first"));
        let last = eval.get_preprocessed_column(mac_col_id("consumer/last"));
        let one = m31_const::<E>(1);

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(first.clone() * (first.clone() - one.clone()));
        eval.add_constraint(last.clone() * (last.clone() - one.clone()));
        eval.add_constraint(first.clone() * (one.clone() - active.clone()));
        eval.add_constraint(last.clone() * (one.clone() - active.clone()));

        let tag_bits = (0..GF_BITS)
            .map(|i| eval.get_preprocessed_column(mac_col_id(&format!("consumer/tag_bit_{i}"))))
            .collect::<Vec<_>>();

        let a = eval.next_trace_mask();
        let b = eval.next_trace_mask();
        let product = eval.next_trace_mask();
        let position = eval.next_trace_mask();
        let contribution_bits = (0..GF_BITS)
            .map(|_| eval.next_trace_mask())
            .collect::<Vec<_>>();
        let carry_bits = (0..GF_BITS)
            .map(|_| eval.next_trace_mask())
            .collect::<Vec<_>>();

        eval.add_constraint((one.clone() - active.clone()) * a.clone());
        eval.add_constraint((one.clone() - active.clone()) * b.clone());
        eval.add_constraint((one.clone() - active.clone()) * product.clone());
        eval.add_constraint((one.clone() - active.clone()) * position.clone());
        for bit in &contribution_bits {
            eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * bit.clone());
        }
        for bit in &carry_bits {
            eval.add_constraint(bit.clone() * (bit.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * bit.clone());
        }

        let clmul_denominator: E::EF = self.clmul_relation.combine(&[a, b, product.clone()]);

        let mut reduce_values = Vec::with_capacity(2 + GF_BITS);
        reduce_values.push(position);
        reduce_values.push(product);
        reduce_values.extend(contribution_bits.iter().cloned());
        let reduce_denominator: E::EF = self.reduce_relation.combine(&reduce_values);
        let active_ef = E::EF::from(active.clone());
        eval.write_logup_frac(Fraction::new(
            active_ef.clone() * reduce_denominator.clone() + active_ef * clmul_denominator.clone(),
            clmul_denominator * reduce_denominator,
        ));

        for bit_index in 0..GF_BITS {
            let [acc, prev_acc] =
                eval.next_interaction_mask(stwo_constraint_framework::ORIGINAL_TRACE_IDX, [0, -1]);
            eval.add_constraint(acc.clone() * (acc.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * acc.clone());

            let carry = carry_bits[bit_index].clone();
            eval.add_constraint(first.clone() * carry.clone());
            eval.add_constraint((active.clone() - first.clone()) * (carry.clone() - prev_acc));
            let expected = xor_expr::<E>(carry, contribution_bits[bit_index].clone());
            eval.add_constraint(acc.clone() - expected);
            eval.add_constraint(last.clone() * (acc - tag_bits[bit_index].clone()));
        }

        eval.finalize_logup();
        eval
    }
}

impl FrameworkEval for Clmul4TableEval {
    fn log_size(&self) -> u32 {
        TABLE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        TABLE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let a = eval.get_preprocessed_column(mac_col_id("clmul_4/a"));
        let b = eval.get_preprocessed_column(mac_col_id("clmul_4/b"));
        let product = eval.get_preprocessed_column(mac_col_id("clmul_4/product"));
        let mult = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(mult),
            &[a, b, product],
        ));
        eval.finalize_logup();
        eval
    }
}

impl FrameworkEval for ReduceTableEval {
    fn log_size(&self) -> u32 {
        REDUCE_TABLE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        REDUCE_TABLE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let mut values = Vec::with_capacity(2 + GF_BITS);
        values.push(eval.get_preprocessed_column(mac_col_id("reduce/position")));
        values.push(eval.get_preprocessed_column(mac_col_id("reduce/product")));
        values.extend((0..GF_BITS).map(|i| {
            eval.get_preprocessed_column(mac_col_id(&format!("reduce/contribution_bit_{i}")))
        }));
        let mult = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(mult),
            &values,
        ));
        eval.finalize_logup();
        eval
    }
}

fn preprocessed_trace(tags: &[[u8; HALF_BYTES]; MACS_PER_PROOF]) -> Vec<MacColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; CONSUMER_PREPROCESSED_COLS];
    for mac_index in 0..MACS_PER_PROOF {
        let tag_bits = bytes_to_bits(&tags[mac_index]);
        for product_index in 0..PRODUCTS_PER_MAC {
            let row = mac_index * PRODUCTS_PER_MAC + product_index;
            columns[0][row] = M31::from_u32_unchecked(1);
            columns[1][row] = M31::from_u32_unchecked(u32::from(product_index == 0));
            columns[2][row] =
                M31::from_u32_unchecked(u32::from(product_index == PRODUCTS_PER_MAC - 1));
            for bit in 0..GF_BITS {
                columns[3 + bit][row] = M31::from_u32_unchecked(u32::from(
                    product_index == PRODUCTS_PER_MAC - 1 && tag_bits[bit],
                ));
            }
        }
    }
    let mut out = columns
        .into_iter()
        .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
        .collect::<Vec<_>>();

    let mut table_cols = vec![vec![M31::from_u32_unchecked(0); 1 << TABLE_LOG_SIZE]; 3];
    for a in 0..16 {
        for b in 0..16 {
            let row = a * 16 + b;
            table_cols[0][row] = M31::from_u32_unchecked(a as u32);
            table_cols[1][row] = M31::from_u32_unchecked(b as u32);
            table_cols[2][row] = M31::from_u32_unchecked(clmul4(a as u8, b as u8) as u32);
        }
    }
    out.extend(
        table_cols
            .into_iter()
            .map(|values| column_eval(TABLE_LOG_SIZE, values)),
    );

    let mut reduce_cols =
        vec![vec![M31::from_u32_unchecked(0); 1 << REDUCE_TABLE_LOG_SIZE]; 2 + GF_BITS];
    for position in 0..PRODUCT_POSITIONS {
        for product in 0..128 {
            let row = position * 128 + product;
            let contribution = reduced_product_contribution(position, product as u8);
            reduce_cols[0][row] = M31::from_u32_unchecked(position as u32);
            reduce_cols[1][row] = M31::from_u32_unchecked(product as u32);
            for bit in 0..GF_BITS {
                reduce_cols[2 + bit][row] = M31::from_u32_unchecked(u32::from(contribution[bit]));
            }
        }
    }
    out.extend(
        reduce_cols
            .into_iter()
            .map(|values| column_eval(REDUCE_TABLE_LOG_SIZE, values)),
    );
    out
}

fn consumer_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    av: &[u8; HALF_BYTES],
) -> (Vec<MacColumnEval>, [u32; 256], [u32; REDUCE_TABLE_ROWS]) {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; CONSUMER_TRACE_COLS];
    let mut clmul_multiplicities = [0u32; 256];
    let mut reduce_multiplicities = [0u32; REDUCE_TABLE_ROWS];
    for (mac_index, row) in rows.iter().enumerate() {
        let key = xor_128(&row.ap, av);
        let key_nibbles = bytes_to_nibbles(&key);
        let msg_nibbles = bytes_to_nibbles(&row.x);
        let mut acc = [false; GF_BITS];
        for i in 0..NIBBLES_PER_HALF {
            for j in 0..NIBBLES_PER_HALF {
                let product_index = i * NIBBLES_PER_HALF + j;
                let out_row = mac_index * PRODUCTS_PER_MAC + product_index;
                let a = key_nibbles[i];
                let b = msg_nibbles[j];
                let product = clmul4(a, b);
                let position = i + j;
                let contribution = reduced_product_contribution(position, product);
                clmul_multiplicities[usize::from(a) * 16 + usize::from(b)] += 1;
                reduce_multiplicities[position * 128 + usize::from(product)] += 1;
                columns[0][out_row] = M31::from_u32_unchecked(u32::from(a));
                columns[1][out_row] = M31::from_u32_unchecked(u32::from(b));
                columns[2][out_row] = M31::from_u32_unchecked(u32::from(product));
                columns[3][out_row] = M31::from_u32_unchecked(position as u32);
                for bit_index in 0..GF_BITS {
                    columns[4 + bit_index][out_row] =
                        M31::from_u32_unchecked(u32::from(contribution[bit_index]));
                    columns[4 + GF_BITS + bit_index][out_row] =
                        M31::from_u32_unchecked(u32::from(acc[bit_index]));
                    acc[bit_index] ^= contribution[bit_index];
                }
                for bit_index in 0..GF_BITS {
                    columns[4 + GF_BITS + GF_BITS + bit_index][out_row] =
                        M31::from_u32_unchecked(u32::from(acc[bit_index]));
                }
            }
        }
        debug_assert_eq!(
            bits_to_bytes(&acc),
            gf128_mul(&xor_128(&row.ap, av), &row.x)
        );
    }
    (
        columns
            .into_iter()
            .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
            .collect(),
        clmul_multiplicities,
        reduce_multiplicities,
    )
}

fn clmul_table_trace(multiplicities: &[u32; 256]) -> Vec<MacColumnEval> {
    vec![column_eval(
        TABLE_LOG_SIZE,
        multiplicities
            .iter()
            .map(|&m| M31::from_u32_unchecked(m))
            .collect(),
    )]
}

fn reduce_table_trace(multiplicities: &[u32; REDUCE_TABLE_ROWS]) -> Vec<MacColumnEval> {
    vec![column_eval(
        REDUCE_TABLE_LOG_SIZE,
        multiplicities
            .iter()
            .map(|&m| M31::from_u32_unchecked(m))
            .chain(std::iter::repeat_n(
                M31::from_u32_unchecked(0),
                (1 << REDUCE_TABLE_LOG_SIZE) - REDUCE_TABLE_ROWS,
            ))
            .collect(),
    )]
}

fn consumer_interaction_trace(
    rows: &[MacHalfWitness; MACS_PER_PROOF],
    av: &[u8; HALF_BYTES],
    clmul_relation: &Clmul4Relation,
    reduce_relation: &ReduceRelation,
) -> (Vec<MacColumnEval>, QM31) {
    let mut columns = vec![vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE]; 4 + GF_BITS];
    let mut active = vec![M31::from_u32_unchecked(0); 1 << CONSUMER_LOG_SIZE];
    for row in 0..ACTIVE_ROWS {
        let mac = row / PRODUCTS_PER_MAC;
        let product_index = row % PRODUCTS_PER_MAC;
        let i = product_index / NIBBLES_PER_HALF;
        let j = product_index % NIBBLES_PER_HALF;
        let key = xor_128(&rows[mac].ap, av);
        let a = bytes_to_nibbles(&key)[i];
        let b = bytes_to_nibbles(&rows[mac].x)[j];
        let product = clmul4(a, b);
        let position = i + j;
        let contribution = reduced_product_contribution(position, product);
        active[row] = M31::from_u32_unchecked(1);
        columns[0][row] = M31::from_u32_unchecked(u32::from(a));
        columns[1][row] = M31::from_u32_unchecked(u32::from(b));
        columns[2][row] = M31::from_u32_unchecked(u32::from(product));
        columns[3][row] = M31::from_u32_unchecked(position as u32);
        for bit in 0..GF_BITS {
            columns[4 + bit][row] = M31::from_u32_unchecked(u32::from(contribution[bit]));
        }
    }
    let active = column_eval(CONSUMER_LOG_SIZE, active);
    let columns = columns
        .into_iter()
        .map(|values| column_eval(CONSUMER_LOG_SIZE, values))
        .collect::<Vec<_>>();
    let mut logup = LogupTraceGenerator::new(CONSUMER_LOG_SIZE);
    logup.col_from_fn(|vec_row| {
        let values = [
            columns[0].data[vec_row],
            columns[1].data[vec_row],
            columns[2].data[vec_row],
        ];
        let clmul_denominator: PackedQM31 = clmul_relation.combine(&values);
        let mut reduce_values = Vec::with_capacity(2 + GF_BITS);
        reduce_values.push(columns[3].data[vec_row]);
        reduce_values.push(columns[2].data[vec_row]);
        reduce_values.extend((0..GF_BITS).map(|bit| columns[4 + bit].data[vec_row]));
        let reduce_denominator: PackedQM31 = reduce_relation.combine(&reduce_values);
        let numerator = PackedQM31::from(active.data[vec_row]);
        (
            numerator * reduce_denominator + numerator * clmul_denominator,
            clmul_denominator * reduce_denominator,
        )
    });
    logup.finalize_last()
}

fn clmul_table_interaction_trace(
    multiplicities: &[u32; 256],
    relation: &Clmul4Relation,
) -> (Vec<MacColumnEval>, QM31) {
    let preprocessed =
        preprocessed_trace(&[[[0u8; HALF_BYTES]; MACS_PER_PROOF][0]; MACS_PER_PROOF]);
    let table_start = CONSUMER_PREPROCESSED_COLS;
    let mult = clmul_table_trace(multiplicities);
    let mut logup = LogupTraceGenerator::new(TABLE_LOG_SIZE);
    logup.col_from_fn(|vec_row| {
        let values = [
            preprocessed[table_start].data[vec_row],
            preprocessed[table_start + 1].data[vec_row],
            preprocessed[table_start + 2].data[vec_row],
        ];
        let numerator = -PackedQM31::from(mult[0].data[vec_row]);
        let denominator = relation.combine(&values);
        (numerator, denominator)
    });
    logup.finalize_last()
}

fn reduce_table_interaction_trace(
    multiplicities: &[u32; REDUCE_TABLE_ROWS],
    relation: &ReduceRelation,
) -> (Vec<MacColumnEval>, QM31) {
    let preprocessed =
        preprocessed_trace(&[[[0u8; HALF_BYTES]; MACS_PER_PROOF][0]; MACS_PER_PROOF]);
    let table_start = CONSUMER_PREPROCESSED_COLS + TABLE_PREPROCESSED_COLS;
    let mult = reduce_table_trace(multiplicities);
    let mut logup = LogupTraceGenerator::new(REDUCE_TABLE_LOG_SIZE);
    logup.col_from_fn(|vec_row| {
        let mut values = Vec::with_capacity(2 + GF_BITS);
        values.push(preprocessed[table_start].data[vec_row]);
        values.push(preprocessed[table_start + 1].data[vec_row]);
        values.extend((0..GF_BITS).map(|bit| preprocessed[table_start + 2 + bit].data[vec_row]));
        let numerator = -PackedQM31::from(mult[0].data[vec_row]);
        let denominator = relation.combine(&values);
        (numerator, denominator)
    });
    logup.finalize_last()
}

fn column_eval(log_size: u32, values: Vec<M31>) -> MacColumnEval {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(ordered),
    )
}

fn reduced_monomial_mask(degree: usize) -> [bool; GF_BITS] {
    let mut coeffs = vec![false; 255];
    coeffs[degree] = true;
    for high in (GF_BITS..=degree).rev() {
        if coeffs[high] {
            coeffs[high] = false;
            for offset in [0usize, 1, 2, 7] {
                coeffs[high - GF_BITS + offset] ^= true;
            }
        }
    }
    let mut out = [false; GF_BITS];
    out.copy_from_slice(&coeffs[..GF_BITS]);
    out
}

fn reduced_product_contribution(position: usize, product: u8) -> [bool; GF_BITS] {
    let mut out = [false; GF_BITS];
    for product_bit in 0..7 {
        if ((product >> product_bit) & 1) == 1 {
            let mask = reduced_monomial_mask(4 * position + product_bit);
            for bit in 0..GF_BITS {
                out[bit] ^= mask[bit];
            }
        }
    }
    out
}

fn clmul4(a: u8, b: u8) -> u8 {
    let mut out = 0u8;
    for i in 0..4 {
        for j in 0..4 {
            let bit = ((a >> i) & 1) & ((b >> j) & 1);
            out ^= bit << (i + j);
        }
    }
    out
}

fn xor_expr<E: EvalAtRow>(a: E::F, b: E::F) -> E::F {
    a.clone() + b.clone() - m31_const::<E>(2) * a * b
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

fn bytes_to_nibbles(bytes: &[u8; HALF_BYTES]) -> [u8; NIBBLES_PER_HALF] {
    std::array::from_fn(|i| {
        let byte = bytes[i / 2];
        if i % 2 == 0 {
            byte & 0x0f
        } else {
            byte >> 4
        }
    })
}

fn xor_128(left: &[u8; HALF_BYTES], right: &[u8; HALF_BYTES]) -> [u8; HALF_BYTES] {
    std::array::from_fn(|i| left[i] ^ right[i])
}

fn gf128_mul(left: &[u8; HALF_BYTES], right: &[u8; HALF_BYTES]) -> [u8; HALF_BYTES] {
    let left = bytes_to_bits(left);
    let right = bytes_to_bits(right);
    let mut coeffs = [false; 255];
    for i in 0..GF_BITS {
        for j in 0..GF_BITS {
            coeffs[i + j] ^= left[i] & right[j];
        }
    }
    for high in (GF_BITS..255).rev() {
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

fn cells(logs: &[u32]) -> u64 {
    logs.iter().map(|&log| 1u64 << log).sum()
}

fn bincode_len<T: Serialize>(value: &T) -> usize {
    bincode::serialize(value)
        .expect("MAC spike proof byte breakdown serializes")
        .len()
}
