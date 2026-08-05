//! Tests for a hosted `stwo-mldsa` statement and a test host module.
//! The host yields the ML-DSA message bytes under a shared
//! `air_core::relations::FieldBytesRelation` (the mdoc issuer-SHA swap point).
//!
//! A two-module proof `[field_producer, hosted_mldsa]` proves and verifies
//! without a standalone `msglink` component. Changing one message byte
//! on the producer side (so the yielded bytes differ from what the µ-absorb
//! bridge requires) makes the global LogUp unbalanced → verify rejects. This
//! proves that the MsgLink-to-FieldBytes connection binds the message.
//!
//! Run single-threaded (proofs must not run concurrently):
//! `RUST_MIN_STACK=536870912 cargo test -p stwo-mldsa --release --test hosted \
//!   -- --test-threads=1`.

mod common;

use common::{composed_pcs_config as pcs_config, oracle_input};

use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::SecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use num_traits::{One, Zero};

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};

use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;

use stwo_keccak::relations::SharedKeccakRelations;
use stwo_keccak::service::{service_claimed_sums_len, KeccakServiceProver, KeccakServiceVerifier};
use stwo_keccak::sponge::{Shape, XofMode};
use stwo_keccak::sponge_v::{generate_jobs, JobList};
use stwo_mldsa::air_util::{col_eval, m31, ColEval};
use stwo_mldsa::binding::{
    RhoCellRelation, SharedRhoCellRelation, SharedT1CellRelation, T1CellRelation,
    STREAM_ID_SIB_SQUEEZE,
};
use stwo_mldsa::coeffs::relations::SharedRangeRelation;
use stwo_mldsa::coeffs::tables::SharedRangeTable;
use stwo_mldsa::constants::N;
use stwo_mldsa::expand_a::{
    derive_expand_a_witness, shake128_job_shapes, ExpandABindings, ExpandAClaim, ExpandAProver,
    ExpandAVerifier,
};
use stwo_mldsa::private_key_eval::PrivateKeyEvalBindings;
use stwo_mldsa::profile::ML_DSA_65;
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::statement::{
    hosted_claimed_sums_len, hosted_private_key_claimed_sums_len,
    hosted_private_key_keccak_job_shapes, hosted_private_key_layout,
    hosted_public_claimed_sums_len, keccak_job_shapes, n_private_key_group_evals,
    try_hosted_private_key_keccak_job_shapes, try_hosted_private_key_layout, MlDsaProver,
    MlDsaVerifier, CT_ABSORB, CT_SQUEEZE, DEVICE_SIG_STRUCTURE_CAPACITY, HOSTED_DEVICE_PK_FIELD_ID,
    HOSTED_MSG_FIELD_ID, MU_ABSORB, MU_SQUEEZE, SIB_ABSORB, STREAM_BASE_STRIDE, TR_ABSORB,
    TR_SQUEEZE,
};
use stwo_mldsa::witness::generate_witness;
use stwo_mldsa::{MlDsaPrivateKeyPublicInput, MlDsaVerifyInput};

// =====================================================================
// Test host module. It yields the complete message on the shared
// FieldBytesRelation at HOSTED_MSG_FIELD_ID.
// =====================================================================

/// One packed row with lane 0 active and one relation entry per message byte.
/// This uses the same tuple order as `stwo_mldsa::msglink::MsgLinkEval`.
#[derive(Clone)]
struct FieldProducerEval {
    bytes: Vec<u8>,
    field_id: u32,
    field: FieldBytesRelation,
}

impl FrameworkEval for FieldProducerEval {
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
        // (−enabler): match the stwo-sha256 field-provider sign convention
        // (provider −, consuming bridge +).
        let en = -E::EF::from(enabler);
        for (i, &b) in self.bytes.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.field,
                en.clone(),
                &[
                    E::F::from(m31(self.field_id)),
                    E::F::from(m31(i as u32)),
                    E::F::from(m31(b as u32)),
                ],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// The host module: draws the shared field relation, sets the handle, and yields
/// the message bytes. Composed FIRST so its `draw_relations` populates the handle
/// before the hosted mldsa module reads it.
struct FieldProducer {
    bytes: Vec<u8>,
    field_id: u32,
    handle: SharedFieldRelation,
    field: Option<FieldBytesRelation>,
    claimed_sum: SecureField,
    component: Option<FrameworkComponent<FieldProducerEval>>,
}

impl FieldProducer {
    fn new(bytes: Vec<u8>, handle: SharedFieldRelation) -> Self {
        Self::for_field(HOSTED_MSG_FIELD_ID, bytes, handle)
    }

    fn for_field(field_id: u32, bytes: Vec<u8>, handle: SharedFieldRelation) -> Self {
        Self {
            bytes,
            field_id,
            handle,
            field: None,
            claimed_sum: SecureField::zero(),
            component: None,
        }
    }
    fn field(&self) -> FieldBytesRelation {
        self.field.clone().expect("relation drawn")
    }
}

fn producer_base_trace() -> Vec<ColEval> {
    let rows = 1usize << LOG_N_LANES;
    let mut enabler = vec![m31(0); rows];
    enabler[0] = m31(1);
    vec![col_eval(LOG_N_LANES, enabler)]
}

/// One `−enabler / combine(tuple)` fraction per byte, paired two-per-column
/// (msglink pattern, sign flipped to the stwo-sha256 provider convention).
fn producer_interaction(
    field_id: u32,
    bytes: &[u8],
    field: &FieldBytesRelation,
) -> (Vec<ColEval>, SecureField) {
    use stwo::prover::backend::simd::m31::PackedM31;
    let mut gen = LogupTraceGenerator::new(LOG_N_LANES);
    let mut en_lanes = [m31(0); N_LANES];
    en_lanes[0] = m31(1);
    let en = -PackedQM31::from(PackedM31::from_array(en_lanes));
    let fracs: Vec<(PackedQM31, PackedQM31)> = bytes
        .iter()
        .enumerate()
        .map(|(i, &b)| {
            let tuple = [
                PackedM31::from(m31(field_id)),
                PackedM31::from(m31(i as u32)),
                PackedM31::from(m31(b as u32)),
            ];
            (en, field.combine(&tuple))
        })
        .collect();
    let mut i = 0;
    while i + 2 <= fracs.len() {
        let mut col = gen.new_col();
        let (n0, d0) = fracs[i];
        let (n1, d1) = fracs[i + 1];
        col.write_frac(0, n0 * d1 + n1 * d0, d0 * d1);
        col.finalize_col();
        i += 2;
    }
    if i < fracs.len() {
        let mut col = gen.new_col();
        let (n, d) = fracs[i];
        col.write_frac(0, n, d);
        col.finalize_col();
    }
    gen.finalize_last()
}

fn producer_interaction_cols(msg_len: usize) -> usize {
    use stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
    msg_len.div_ceil(2) * SECURE_EXTENSION_DEGREE
}

impl Air for FieldProducer {
    fn mix_public(&self, _channel: &mut Blake2sChannel) {}
    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let field = FieldBytesRelation::draw(channel);
        self.handle.set(field.clone());
        // Compute the claimed sum now (both prove and verify run draw_relations
        // identically), so the verifier reconstructs the same value with no
        // witness beyond the public producer bytes.
        let (_, sum) = producer_interaction(self.field_id, &self.bytes, &field);
        self.claimed_sum = sum;
        self.field = Some(field);
    }
    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: vec![LOG_N_LANES],
            interaction: vec![LOG_N_LANES; producer_interaction_cols(self.bytes.len())],
        }
    }
    fn claimed_sums(&self) -> Vec<SecureField> {
        vec![self.claimed_sum]
    }
    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }
    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(FrameworkComponent::new(
            allocator,
            FieldProducerEval {
                bytes: self.bytes.clone(),
                field_id: self.field_id,
                field: self.field(),
            },
            self.claimed_sum,
        ));
    }
    fn components(&self) -> Vec<&dyn Component> {
        vec![self.component.as_ref().expect("built")]
    }
}

impl AirProver for FieldProducer {
    fn max_log_size(&self) -> u32 {
        LOG_N_LANES
    }
    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}
    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        Vec::new()
    }
    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(producer_base_trace());
    }
    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (trace, sum) = producer_interaction(self.field_id, &self.bytes, &self.field());
        debug_assert_eq!(
            sum, self.claimed_sum,
            "producer sum drifted from draw_relations"
        );
        tb.extend_evals(trace);
    }
    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self.component.as_ref().expect("built")]
    }
}

// =====================================================================
// This focused source supplies the private key for hosted verification.
//
// Its private bit trace proves the FIPS-204 5-byte -> 4x10-bit t1 packing,
// publishes the exact normalized
// pkEncode bytes, and binds the same rho bytes to real ExpandA. The verifier
// receives only its two LogUp claims.
// =====================================================================

const PRIVATE_KEY_BINDER_TAG: u64 = 0x504b_4249_4e44_0001;
const EXPAND_A_NAMESPACE: &str = "hosted-private-key-expand-a";
const EXPAND_A_STREAM_BASE: u32 = 256;
const RHO_BIND_LOG_SIZE: u32 = 5;
const T1_BIND_LOG_SIZE: u32 = 9;
const T1_GROUP_BYTES: usize = 5;
const T1_GROUP_COEFFS: usize = 4;
const T1_GROUPS_PER_POLY: usize = N / T1_GROUP_COEFFS;
const DEVICE_K: usize = ML_DSA_65.k();
const DEVICE_PK_BYTES: usize = ML_DSA_65.pk_bytes();
const T1_ACTIVE_ROWS: usize = DEVICE_K * T1_GROUPS_PER_POLY;
const RHO_TRACE_COLS: usize = 8;
const T1_TRACE_COLS: usize = T1_GROUP_BYTES * 8;
const RHO_LOGUP_ENTRIES: usize = 2;
const T1_LOGUP_ENTRIES: usize = T1_GROUP_BYTES + T1_GROUP_COEFFS;
const RHO_INTERACTION_COLS: usize = stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
const T1_INTERACTION_COLS: usize =
    stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE * T1_LOGUP_ENTRIES.div_ceil(4);

fn rho_index_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "hosted_private_key_rho_index".to_string(),
    }
}

fn t1_active_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "hosted_private_key_t1_active".to_string(),
    }
}

fn t1_poly_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "hosted_private_key_t1_poly".to_string(),
    }
}

fn t1_group_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "hosted_private_key_t1_group".to_string(),
    }
}

fn private_key_source_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    vec![rho_index_id(), t1_active_id(), t1_poly_id(), t1_group_id()]
}

fn private_key_source_preprocessed() -> Vec<ColEval> {
    let rho_index = (0..(1usize << RHO_BIND_LOG_SIZE))
        .map(|index| m31(index as u32))
        .collect();
    let mut active = vec![m31(0); 1usize << T1_BIND_LOG_SIZE];
    let mut poly = vec![m31(0); 1usize << T1_BIND_LOG_SIZE];
    let mut group = vec![m31(0); 1usize << T1_BIND_LOG_SIZE];
    for row in 0..T1_ACTIVE_ROWS {
        active[row] = m31(1);
        poly[row] = m31((row / T1_GROUPS_PER_POLY) as u32);
        group[row] = m31((row % T1_GROUPS_PER_POLY) as u32);
    }
    vec![
        col_eval(RHO_BIND_LOG_SIZE, rho_index),
        col_eval(T1_BIND_LOG_SIZE, active),
        col_eval(T1_BIND_LOG_SIZE, poly),
        col_eval(T1_BIND_LOG_SIZE, group),
    ]
}

#[derive(Clone)]
struct PrivateKeySourceRelations {
    field: FieldBytesRelation,
    rho: RhoCellRelation,
    t1: T1CellRelation,
}

#[derive(Clone)]
struct PrivateRhoEval {
    relations: PrivateKeySourceRelations,
}

impl FrameworkEval for PrivateRhoEval {
    fn log_size(&self) -> u32 {
        RHO_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    #[allow(clippy::assign_op_pattern)]
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let index = eval.get_preprocessed_column(rho_index_id());
        let bits: Vec<_> = (0..8).map(|_| eval.next_trace_mask()).collect();
        let one = E::F::from(m31(1));
        let mut byte = E::F::zero();
        for (bit_index, bit) in bits.into_iter().enumerate() {
            eval.add_constraint(bit.clone() * (one.clone() - bit.clone()));
            byte = byte + E::F::from(m31(1 << bit_index)) * bit;
        }
        eval.add_to_relation(RelationEntry::base(
            &self.relations.field,
            -one.clone(),
            &[
                E::F::from(m31(HOSTED_DEVICE_PK_FIELD_ID)),
                index.clone(),
                byte.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.rho,
            -one,
            &[index, byte],
        ));
        eval.finalize_logup_batched(4);
        eval
    }
}

#[derive(Clone)]
struct PrivateT1Eval {
    relations: PrivateKeySourceRelations,
}

impl FrameworkEval for PrivateT1Eval {
    fn log_size(&self) -> u32 {
        T1_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    #[allow(clippy::assign_op_pattern)]
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(t1_active_id());
        let poly = eval.get_preprocessed_column(t1_poly_id());
        let group = eval.get_preprocessed_column(t1_group_id());
        let bits: Vec<_> = (0..T1_TRACE_COLS).map(|_| eval.next_trace_mask()).collect();
        let one = E::F::from(m31(1));
        for bit in &bits {
            eval.add_constraint(bit.clone() * (one.clone() - bit.clone()));
            eval.add_constraint((one.clone() - active.clone()) * bit.clone());
        }
        for byte_index in 0..T1_GROUP_BYTES {
            let mut byte = E::F::zero();
            for bit_index in 0..8 {
                byte = byte
                    + E::F::from(m31(1 << bit_index)) * bits[byte_index * 8 + bit_index].clone();
            }
            let position = E::F::from(m31((32 + byte_index) as u32))
                + E::F::from(m31(320)) * poly.clone()
                + E::F::from(m31(T1_GROUP_BYTES as u32)) * group.clone();
            eval.add_to_relation(RelationEntry::base(
                &self.relations.field,
                -active.clone(),
                &[E::F::from(m31(HOSTED_DEVICE_PK_FIELD_ID)), position, byte],
            ));
        }
        for coefficient in 0..T1_GROUP_COEFFS {
            let bit_base = coefficient * 10;
            let mut lo9 = E::F::zero();
            for bit_index in 0..9 {
                lo9 = lo9 + E::F::from(m31(1 << bit_index)) * bits[bit_base + bit_index].clone();
            }
            let coefficient_index = E::F::from(m31(T1_GROUP_COEFFS as u32)) * group.clone()
                + E::F::from(m31(coefficient as u32));
            eval.add_to_relation(RelationEntry::base(
                &self.relations.t1,
                -active.clone(),
                &[
                    poly.clone(),
                    coefficient_index,
                    lo9,
                    bits[bit_base + 9].clone(),
                ],
            ));
        }
        eval.finalize_logup_batched(4);
        eval
    }
}

fn private_key_source_trace(pk_encode: &[u8]) -> Vec<ColEval> {
    assert_eq!(pk_encode.len(), DEVICE_PK_BYTES);
    let mut rho_columns = vec![vec![m31(0); 1usize << RHO_BIND_LOG_SIZE]; RHO_TRACE_COLS];
    for (row, &byte) in pk_encode[..32].iter().enumerate() {
        for (bit, column) in rho_columns.iter_mut().enumerate() {
            column[row] = m31(((byte >> bit) & 1) as u32);
        }
    }
    let mut t1_columns = vec![vec![m31(0); 1usize << T1_BIND_LOG_SIZE]; T1_TRACE_COLS];
    for row in 0..T1_ACTIVE_ROWS {
        let bytes = &pk_encode[32 + row * T1_GROUP_BYTES..32 + (row + 1) * T1_GROUP_BYTES];
        for (byte_index, &byte) in bytes.iter().enumerate() {
            for bit in 0..8 {
                t1_columns[byte_index * 8 + bit][row] = m31(((byte >> bit) & 1) as u32);
            }
        }
    }
    rho_columns
        .into_iter()
        .map(|column| col_eval(RHO_BIND_LOG_SIZE, column))
        .chain(
            t1_columns
                .into_iter()
                .map(|column| col_eval(T1_BIND_LOG_SIZE, column)),
        )
        .collect()
}

fn combine_logup_batch(entries: &[(SecureField, SecureField)]) -> (SecureField, SecureField) {
    let denominator = entries
        .iter()
        .fold(SecureField::one(), |acc, (_, denominator)| {
            acc * *denominator
        });
    let numerator =
        entries
            .iter()
            .enumerate()
            .fold(SecureField::zero(), |acc, (index, (numerator, _))| {
                let other_denominators = entries
                    .iter()
                    .enumerate()
                    .filter(|(other, _)| *other != index)
                    .fold(SecureField::one(), |product, (_, (_, denominator))| {
                        product * *denominator
                    });
                acc + *numerator * other_denominators
            });
    (numerator, denominator)
}

fn private_key_source_logup(
    log_size: u32,
    rows: &[Vec<(SecureField, SecureField)>],
    entries_per_row: usize,
) -> (Vec<ColEval>, SecureField) {
    let circle_to_coset = stwo_mldsa::air_util::circle_row_to_coset(log_size);
    let mut logup = LogupTraceGenerator::new(log_size);
    for start in (0..entries_per_row).step_by(4) {
        let end = (start + 4).min(entries_per_row);
        logup.col_from_fn(|vec_row| {
            let mut numerators = [SecureField::zero(); N_LANES];
            let mut denominators = [SecureField::zero(); N_LANES];
            for lane in 0..N_LANES {
                let circle_row = vec_row * N_LANES + lane;
                let coset_row = circle_to_coset[circle_row];
                let (numerator, denominator) = combine_logup_batch(&rows[coset_row][start..end]);
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            (
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            )
        });
    }
    logup.finalize_last()
}

fn private_key_source_interaction(
    pk_encode: &[u8],
    relations: &PrivateKeySourceRelations,
) -> ([Vec<ColEval>; 2], [SecureField; 2]) {
    assert_eq!(pk_encode.len(), DEVICE_PK_BYTES);
    let minus_one = -SecureField::one();
    let one = SecureField::one();
    let rho_rows: Vec<_> = pk_encode[..32]
        .iter()
        .enumerate()
        .map(|(index, &byte)| {
            vec![
                (
                    minus_one,
                    relations.field.combine(&[
                        m31(HOSTED_DEVICE_PK_FIELD_ID),
                        m31(index as u32),
                        m31(byte as u32),
                    ]),
                ),
                (
                    minus_one,
                    relations
                        .rho
                        .combine(&[m31(index as u32), m31(byte as u32)]),
                ),
            ]
        })
        .collect();
    let (rho_trace, rho_claim) =
        private_key_source_logup(RHO_BIND_LOG_SIZE, &rho_rows, RHO_LOGUP_ENTRIES);

    let mut t1_rows =
        vec![vec![(SecureField::zero(), one); T1_LOGUP_ENTRIES]; 1usize << T1_BIND_LOG_SIZE];
    for (row, entries) in t1_rows.iter_mut().enumerate().take(T1_ACTIVE_ROWS) {
        let poly = row / T1_GROUPS_PER_POLY;
        let group = row % T1_GROUPS_PER_POLY;
        let byte_start = 32 + row * T1_GROUP_BYTES;
        let bytes = &pk_encode[byte_start..byte_start + T1_GROUP_BYTES];
        let packed = bytes
            .iter()
            .enumerate()
            .fold(0u64, |value, (index, &byte)| {
                value | ((byte as u64) << (8 * index))
            });
        let mut row_entries = Vec::with_capacity(T1_LOGUP_ENTRIES);
        for (byte_index, &byte) in bytes.iter().enumerate() {
            row_entries.push((
                minus_one,
                relations.field.combine(&[
                    m31(HOSTED_DEVICE_PK_FIELD_ID),
                    m31((byte_start + byte_index) as u32),
                    m31(byte as u32),
                ]),
            ));
        }
        for coefficient in 0..T1_GROUP_COEFFS {
            let value = ((packed >> (10 * coefficient)) & 0x3ff) as u32;
            row_entries.push((
                minus_one,
                relations.t1.combine(&[
                    m31(poly as u32),
                    m31((group * T1_GROUP_COEFFS + coefficient) as u32),
                    m31(value & 0x1ff),
                    m31(value >> 9),
                ]),
            ));
        }
        *entries = row_entries;
    }
    let (t1_trace, t1_claim) =
        private_key_source_logup(T1_BIND_LOG_SIZE, &t1_rows, T1_LOGUP_ENTRIES);
    ([rho_trace, t1_trace], [rho_claim, t1_claim])
}

struct PrivateKeySource {
    pk_encode: Option<Vec<u8>>,
    field_handle: SharedFieldRelation,
    rho_handle: SharedRhoCellRelation,
    t1_handle: SharedT1CellRelation,
    relations: Option<PrivateKeySourceRelations>,
    claims: [SecureField; 2],
    rho_component: Option<FrameworkComponent<PrivateRhoEval>>,
    t1_component: Option<FrameworkComponent<PrivateT1Eval>>,
}

impl PrivateKeySource {
    fn prover(
        pk_encode: Vec<u8>,
        field_handle: SharedFieldRelation,
        rho_handle: SharedRhoCellRelation,
        t1_handle: SharedT1CellRelation,
    ) -> Self {
        assert_eq!(pk_encode.len(), DEVICE_PK_BYTES);
        Self {
            pk_encode: Some(pk_encode),
            field_handle,
            rho_handle,
            t1_handle,
            relations: None,
            claims: [SecureField::zero(); 2],
            rho_component: None,
            t1_component: None,
        }
    }

    fn verifier(
        claims: [SecureField; 2],
        field_handle: SharedFieldRelation,
        rho_handle: SharedRhoCellRelation,
        t1_handle: SharedT1CellRelation,
    ) -> Self {
        Self {
            pk_encode: None,
            field_handle,
            rho_handle,
            t1_handle,
            relations: None,
            claims,
            rho_component: None,
            t1_component: None,
        }
    }

    fn relations(&self) -> &PrivateKeySourceRelations {
        self.relations
            .as_ref()
            .expect("private-key source relations")
    }
}

impl Air for PrivateKeySource {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(PRIVATE_KEY_BINDER_TAG);
        channel.mix_u64(ML_DSA_65.transcript_tag());
        channel.mix_u64(DEVICE_PK_BYTES as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        let field = FieldBytesRelation::draw(channel);
        self.field_handle.set(field.clone());
        let t1 = T1CellRelation::draw(channel);
        self.t1_handle.set(t1.clone());
        self.relations = Some(PrivateKeySourceRelations {
            field,
            rho: self.rho_handle.get(),
            t1,
        });
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![
                RHO_BIND_LOG_SIZE,
                T1_BIND_LOG_SIZE,
                T1_BIND_LOG_SIZE,
                T1_BIND_LOG_SIZE,
            ],
            trace: [vec![RHO_BIND_LOG_SIZE; RHO_TRACE_COLS], {
                vec![T1_BIND_LOG_SIZE; T1_TRACE_COLS]
            }]
            .concat(),
            interaction: [
                vec![RHO_BIND_LOG_SIZE; RHO_INTERACTION_COLS],
                vec![T1_BIND_LOG_SIZE; T1_INTERACTION_COLS],
            ]
            .concat(),
        }
    }

    fn claimed_sums(&self) -> Vec<SecureField> {
        self.claims.to_vec()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        private_key_source_preprocessed_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(private_key_source_preprocessed())
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let relations = self.relations().clone();
        self.rho_component = Some(FrameworkComponent::new(
            allocator,
            PrivateRhoEval {
                relations: relations.clone(),
            },
            self.claims[0],
        ));
        self.t1_component = Some(FrameworkComponent::new(
            allocator,
            PrivateT1Eval { relations },
            self.claims[1],
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.rho_component.as_ref().expect("rho component"),
            self.t1_component.as_ref().expect("t1 component"),
        ]
    }
}

impl AirProver for PrivateKeySource {
    fn max_log_size(&self) -> u32 {
        T1_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        T1_BIND_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(private_key_source_preprocessed());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        let ids = private_key_source_preprocessed_ids();
        let columns = private_key_source_preprocessed();
        fingerprint_preprocessed_columns("hosted_private_key_source", &ids, &columns)
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(private_key_source_trace(
            self.pk_encode.as_ref().expect("prover pkEncode"),
        ));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let (traces, claims) = private_key_source_interaction(
            self.pk_encode.as_ref().expect("prover pkEncode"),
            self.relations(),
        );
        self.claims = claims;
        tb.extend_evals(traces.into_iter().flatten().collect());
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.rho_component.as_ref().expect("rho component"),
            self.t1_component.as_ref().expect("t1 component"),
        ]
    }
}

// =====================================================================
// Fixture (model: composed.rs).
// =====================================================================

#[derive(Clone)]
struct HostedProof {
    input: MlDsaVerifyInput,
    group_evals: Vec<SecureField>,
    claimed_sums: Vec<SecureField>,
    range_table_claimed_sum: SecureField,
    service_claimed_sums: Vec<SecureField>,
    post_interaction_payloads: Vec<Vec<u8>>,
    stark_proof: stwo::core::proof::StarkProof<air_core::Hasher>,
}

/// Prove the hosted statement: `[range_table, keccak_service,
/// field_producer(producer_bytes), hosted_mldsa]`. `producer_bytes` is what the
/// HOST yields (honest = the message; tamper it to simulate a mismatched issuer
/// preimage).
fn prove_hosted(seed: u64, msg: &[u8], producer_bytes: Vec<u8>) -> HostedProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(ML_DSA_65, &input).expect("witness");

    let handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut mldsa = MlDsaProver::hosted(
        witness,
        input.clone(),
        handle,
        range_handle.clone(),
        keccak_handle.clone(),
    );
    let mut range_table = SharedRangeTable::prover(&[mldsa.range_uses().clone()], range_handle);
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, keccak_handle);

    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [&mut range_table, &mut service, &mut producer, &mut mldsa],
        pcs_config(),
    )
    .expect("prove");

    let claimed_sums = mldsa.claimed_sums();
    assert_eq!(claimed_sums.len(), hosted_claimed_sums_len());
    HostedProof {
        input,
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums,
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    }
}

/// Verify a hosted proof by reconstructing `[range_table, keccak_service,
/// field_producer, hosted_mldsa]`.
fn verify_hosted(
    proof: &HostedProof,
    producer_bytes: Vec<u8>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    // The producer recomputes its claimed sum in draw_relations from the public
    // bytes, so the same FieldProducer serves verification with no witness.
    let mut producer = FieldProducer::new(producer_bytes, handle.clone());
    let mut service = KeccakServiceVerifier::new(
        keccak_job_shapes(proof.input.message.len(), 0, false),
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut mldsa = MlDsaVerifier::hosted(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        handle,
        range_handle,
        keccak_handle,
    );
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut range_table, &mut service, &mut producer, &mut mldsa],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|e| match e {
        air_core::VerifyError::Stark(e) => e,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
}

fn prove_hosted_public(seed: u64, msg: &[u8]) -> HostedProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(ML_DSA_65, &input).expect("witness");
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut mldsa =
        MlDsaProver::hosted_public(witness, input, range_handle.clone(), keccak_handle.clone());
    let mut range_table = SharedRangeTable::prover(&[mldsa.range_uses().clone()], range_handle);
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    assert_eq!(job_shapes.len(), 2, "native-µ mode keeps only c̃ and SIB");
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, keccak_handle);
    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [&mut range_table, &mut service, &mut mldsa],
        pcs_config(),
    )
    .expect("hosted-public prove");
    let claimed_sums = mldsa.claimed_sums();
    assert_eq!(claimed_sums.len(), hosted_public_claimed_sums_len());
    HostedProof {
        input: mldsa.input().clone(),
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums,
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    }
}

fn verify_hosted_public(
    proof: &HostedProof,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut service = KeccakServiceVerifier::new(
        keccak_job_shapes(proof.input.message.len(), 0, true),
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut mldsa = MlDsaVerifier::hosted_public(
        proof.input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        range_handle,
        keccak_handle,
    );
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [&mut range_table, &mut service, &mut mldsa],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
}

#[derive(Clone)]
struct HostedPrivateKeyProof {
    public_input: MlDsaPrivateKeyPublicInput,
    group_evals: Vec<SecureField>,
    claimed_sums: Vec<SecureField>,
    expand_a_claim: ExpandAClaim,
    private_key_source_claims: [SecureField; 2],
    range_table_claimed_sum: SecureField,
    service_claimed_sums: Vec<SecureField>,
    post_interaction_payloads: Vec<Vec<u8>>,
    stark_proof: stwo::core::proof::StarkProof<air_core::Hasher>,
}

/// Compose the exact private-key seams:
/// `[range, keccak, ExpandA(rho -> NttCell), packed-key source
/// (pkEncode -> FieldBytes + rho + T1Cell), hosted private-key ML-DSA]`.
fn prove_hosted_private_key(seed: u64, msg: &[u8]) -> HostedPrivateKeyProof {
    let input = oracle_input(seed, msg);
    let witness = generate_witness(ML_DSA_65, &input).expect("ML-DSA-65 witness");
    let pk_bytes = input.encode_pk(ML_DSA_65);

    let field_handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let expand_bindings = ExpandABindings::new();
    let t1_handle = SharedT1CellRelation::new();
    let private_key_bindings =
        PrivateKeyEvalBindings::new(expand_bindings.ntt.clone(), t1_handle.clone());
    let mut expand_a = ExpandAProver::new(
        ML_DSA_65,
        derive_expand_a_witness(ML_DSA_65, input.rho).expect("ExpandA witness"),
        EXPAND_A_NAMESPACE,
        EXPAND_A_STREAM_BASE,
        range_handle.clone(),
        keccak_handle.clone(),
        expand_bindings.clone(),
    )
    .expect("ExpandA prover");
    let mut private_key_source = PrivateKeySource::prover(
        pk_bytes,
        field_handle.clone(),
        expand_bindings.rho.clone(),
        t1_handle,
    );
    let mut mldsa = MlDsaProver::hosted_private_key(
        witness,
        input,
        field_handle,
        range_handle.clone(),
        keccak_handle.clone(),
        private_key_bindings,
    )
    .expect("private-key ML-DSA prover");
    let mut range_table = SharedRangeTable::prover(
        &[expand_a.range_uses().clone(), mldsa.range_uses().clone()],
        range_handle,
    );
    let (mut job_shapes, mut job_streams) = expand_a.keccak_jobs().expect("ExpandA Keccak jobs");
    let (mldsa_shapes, mldsa_streams) = mldsa.keccak_jobs();
    assert_eq!(
        mldsa_shapes,
        hosted_private_key_keccak_job_shapes(mldsa.input().message.len(), 0)
    );
    job_shapes.extend(mldsa_shapes);
    job_streams.extend(mldsa_streams);
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, keccak_handle);
    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [
            &mut range_table,
            &mut service,
            &mut expand_a,
            &mut private_key_source,
            &mut mldsa,
        ],
        pcs_config(),
    )
    .expect("hosted-private-key prove");
    let claimed_sums = mldsa.claimed_sums();
    assert_eq!(claimed_sums.len(), hosted_private_key_claimed_sums_len());
    HostedPrivateKeyProof {
        public_input: mldsa.private_key_public_input(),
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums,
        expand_a_claim: expand_a.claim(),
        private_key_source_claims: private_key_source.claims,
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    }
}

fn verify_hosted_private_key_with_shapes(
    proof: &HostedPrivateKeyProof,
    mldsa_job_shapes: Vec<stwo_keccak::sponge::Shape>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let field_handle = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let expand_bindings = ExpandABindings::new();
    let t1_handle = SharedT1CellRelation::new();
    let private_key_bindings =
        PrivateKeyEvalBindings::new(expand_bindings.ntt.clone(), t1_handle.clone());
    let mut job_shapes =
        shake128_job_shapes(ML_DSA_65, EXPAND_A_STREAM_BASE).expect("valid ExpandA service shapes");
    job_shapes.extend(mldsa_job_shapes);
    let mut service = KeccakServiceVerifier::new(
        job_shapes,
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut expand_a = ExpandAVerifier::new(
        ML_DSA_65,
        proof.expand_a_claim.clone(),
        EXPAND_A_NAMESPACE,
        EXPAND_A_STREAM_BASE,
        range_handle.clone(),
        keccak_handle.clone(),
        expand_bindings.clone(),
    )
    .expect("ExpandA verifier");
    let mut private_key_source = PrivateKeySource::verifier(
        proof.private_key_source_claims,
        field_handle.clone(),
        expand_bindings.rho,
        t1_handle,
    );
    let mut mldsa = MlDsaVerifier::hosted_private_key(
        proof.public_input.clone(),
        proof.group_evals.clone(),
        proof.claimed_sums.clone(),
        field_handle,
        range_handle,
        keccak_handle,
        private_key_bindings,
    )?;
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [
            &mut range_table,
            &mut service,
            &mut expand_a,
            &mut private_key_source,
            &mut mldsa,
        ],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|error| match error {
        air_core::VerifyError::Stark(error) => error,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
}

fn verify_hosted_private_key(
    proof: &HostedPrivateKeyProof,
) -> Result<(), stwo::core::verifier::VerificationError> {
    verify_hosted_private_key_with_shapes(
        proof,
        hosted_private_key_keccak_job_shapes(proof.public_input.message.len(), 0),
    )
}

// =====================================================================
// Tests.
// =====================================================================

#[test]
fn hosted_proves_and_verifies() {
    let msg = b"the hosted message bytes come from the host".to_vec();
    let proof = prove_hosted(4242, &msg, msg.clone());
    verify_hosted(&proof, msg.clone()).expect("hosted verify");
}

#[test]
fn hosted_public_native_mu_proves_and_verifies() {
    let msg = b"issuer/device public message uses verifier-native mu".to_vec();
    let proof = prove_hosted_public(4244, &msg);
    verify_hosted_public(&proof).expect("hosted-public verify");
}

#[test]
fn hosted_private_key_shapes_kat_and_layout_are_exact() {
    const EXPECTED_PREPROCESSED_COLUMNS: usize = 76;
    const EXPECTED_TRACE_COLUMNS: usize = 160;
    const EXPECTED_INTERACTION_COLUMNS: usize = 288;
    const EXPECTED_PREPROCESSED_CELLS: usize = 441_360;
    const EXPECTED_TRACE_CELLS: usize = 1_332_304;
    const EXPECTED_INTERACTION_M31_CELLS: usize = 1_419_392;

    let msg = b"private device key tr reference vector".to_vec();
    let input = oracle_input(4_260, &msg);
    let witness = generate_witness(ML_DSA_65, &input).expect("ML-DSA-65 witness");
    let pk_bytes = input.encode_pk(ML_DSA_65);
    let expected_mu_absorbed = witness.sponge.mu_absorbed.clone();
    assert_eq!(pk_bytes.len(), DEVICE_PK_BYTES);

    let expand_bindings = ExpandABindings::new();
    let mut private = MlDsaProver::hosted_private_key(
        witness,
        input,
        SharedFieldRelation::new(),
        SharedRangeRelation::new(),
        SharedKeccakRelations::new(),
        PrivateKeyEvalBindings::new(expand_bindings.ntt, SharedT1CellRelation::new()),
    )
    .expect("private-key prover");
    let (job_shapes, job_streams) = private.keccak_jobs();
    assert_eq!(job_shapes.len(), 4);
    assert_eq!(job_streams.len(), 4);
    assert_eq!(job_streams[0], pk_bytes);
    assert_eq!(job_streams[1], expected_mu_absorbed);
    assert_eq!(
        private.input().tr,
        [0; 64],
        "hosted-private-key mode must not retain native tr"
    );

    let tr = job_shapes[0];
    assert_eq!(tr.message_len, DEVICE_PK_BYTES);
    assert_eq!(tr.n_absorb, 15);
    assert_eq!(tr.n_squeeze, 1);
    assert_eq!(tr.absorb_stream_id, TR_ABSORB);
    assert_eq!(tr.squeeze_stream_id, TR_SQUEEZE);

    let mu = job_shapes[1];
    assert_eq!(mu.message_len, 66 + msg.len());
    assert_eq!(
        mu.message_capacity,
        Some(66 + DEVICE_SIG_STRUCTURE_CAPACITY)
    );
    assert_eq!(
        mu.n_absorb,
        (67 + DEVICE_SIG_STRUCTURE_CAPACITY).div_ceil(136)
    );
    assert_eq!(mu.n_squeeze, 1);
    assert_eq!(mu.absorb_stream_id, MU_ABSORB);
    assert_eq!(mu.squeeze_stream_id, MU_SQUEEZE);

    let ct = job_shapes[2];
    assert_eq!(ct.message_len, 64 + 768);
    assert_eq!(ct.absorb_stream_id, CT_ABSORB);
    assert_eq!(ct.squeeze_stream_id, CT_SQUEEZE);

    let sib = job_shapes[3];
    assert_eq!(sib.message_len, ML_DSA_65.c_tilde_bytes());
    assert_eq!(sib.n_squeeze, 2);
    assert_eq!(sib.absorb_stream_id, SIB_ABSORB);
    assert_eq!(sib.squeeze_stream_id, STREAM_ID_SIB_SQUEEZE);

    let (reference_tr, _) = shake256(&[&job_streams[0]], 136);
    assert_eq!(
        reference_tr[..64],
        job_streams[1][..64],
        "the in-service tr KAT must feed the µ preimage exactly"
    );

    let private_layout = hosted_private_key_layout(private.input().message.len());
    let direct_layout = private.layout();
    assert_eq!(private_layout.preprocessed, direct_layout.preprocessed);
    assert_eq!(private_layout.trace, direct_layout.trace);
    assert_eq!(private_layout.interaction, direct_layout.interaction);
    assert_eq!(private.max_log_size(), 15);
    assert_eq!(private.max_constraint_log_degree_bound(), 17);
    assert!(private_layout
        .preprocessed
        .iter()
        .chain(&private_layout.trace)
        .chain(&private_layout.interaction)
        .all(|&log_size| log_size <= private.max_log_size()));
    let cells = |log_sizes: &[u32]| {
        log_sizes
            .iter()
            .map(|&log_size| 1usize << log_size)
            .sum::<usize>()
    };
    assert_eq!(
        private_layout.preprocessed.len(),
        EXPECTED_PREPROCESSED_COLUMNS
    );
    assert_eq!(private_layout.trace.len(), EXPECTED_TRACE_COLUMNS);
    assert_eq!(
        private_layout.interaction.len(),
        EXPECTED_INTERACTION_COLUMNS
    );
    assert_eq!(
        cells(&private_layout.preprocessed),
        EXPECTED_PREPROCESSED_CELLS
    );
    assert_eq!(cells(&private_layout.trace), EXPECTED_TRACE_CELLS);
    assert_eq!(
        cells(&private_layout.interaction),
        EXPECTED_INTERACTION_M31_CELLS
    );
    assert_eq!(hosted_private_key_claimed_sums_len(), 16);

    // Exercise canonical tree-0 generation too: ids and columns must agree
    // before relations are drawn.
    assert_eq!(
        private.preprocessed_column_ids().len(),
        private
            .canonical_preprocessed_columns()
            .expect("private-key preprocessed columns")
            .len()
    );
}

#[test]
fn hosted_private_key_capacity_fixes_composed_layout_and_tree_zero() {
    const LENGTHS: [usize; 4] = [130, 303, 456, DEVICE_SIG_STRUCTURE_CAPACITY];

    let public_shape = |message_len: usize| {
        let message = (0..message_len)
            .map(|i| (i as u8).wrapping_mul(31).wrapping_add(5))
            .collect::<Vec<_>>();
        let keccak_handle = SharedKeccakRelations::new();
        let range_handle = SharedRangeRelation::new();
        let field_handle = SharedFieldRelation::new();
        let expand_bindings = ExpandABindings::new();
        let mut service_shapes =
            shake128_job_shapes(ML_DSA_65, EXPAND_A_STREAM_BASE).expect("ExpandA service shapes");
        service_shapes.extend(hosted_private_key_keccak_job_shapes(message_len, 0));
        let mut service = KeccakServiceVerifier::new(
            service_shapes,
            vec![SecureField::zero(); service_claimed_sums_len()],
            keccak_handle.clone(),
        );
        let mut mldsa = MlDsaVerifier::hosted_private_key(
            MlDsaPrivateKeyPublicInput { message },
            vec![SecureField::zero(); n_private_key_group_evals()],
            vec![SecureField::zero(); hosted_private_key_claimed_sums_len()],
            field_handle,
            range_handle,
            keccak_handle,
            PrivateKeyEvalBindings::new(expand_bindings.ntt, SharedT1CellRelation::new()),
        )
        .expect("capacity-valid verifier");

        let service_layout = service.layout();
        let mldsa_layout = mldsa.layout();
        let public_shape = (
            service_layout.preprocessed,
            service_layout.trace,
            service_layout.interaction,
            service.preprocessed_column_ids(),
            mldsa_layout.preprocessed,
            mldsa_layout.trace,
            mldsa_layout.interaction,
            mldsa.preprocessed_column_ids(),
        );
        let root = air_core::compute_canonical_preprocessed_root(
            &mut [&mut service, &mut mldsa],
            pcs_config(),
        )
        .expect("canonical service + ML-DSA root");
        (public_shape, root)
    };

    let baseline = public_shape(LENGTHS[0]);
    for len in LENGTHS {
        let current = public_shape(len);
        assert_eq!(
            current.0, baseline.0,
            "device message length {len} changed the composed public shape"
        );
        assert_eq!(
            current.1, baseline.1,
            "device message length {len} changed the composed tree-zero root"
        );

        let shape = hosted_private_key_keccak_job_shapes(len, 0)[1];
        let preimage = (0..shape.message_len)
            .map(|i| (i as u8).wrapping_mul(13).wrapping_add(11))
            .collect::<Vec<_>>();
        let run = generate_jobs(&JobList::new([shape]), std::slice::from_ref(&preimage));
        assert_eq!(
            run.outputs[0],
            shake256(&[&preimage], 136).0,
            "capacity µ output must hash only the actual prefix at length {len}"
        );
    }
}

#[test]
fn hosted_private_key_over_capacity_is_a_checked_error() {
    let over = DEVICE_SIG_STRUCTURE_CAPACITY + 1;
    assert!(try_hosted_private_key_keccak_job_shapes(over, 0).is_err());
    assert!(try_hosted_private_key_layout(over).is_err());

    let result = MlDsaVerifier::hosted_private_key(
        MlDsaPrivateKeyPublicInput {
            message: vec![0; over],
        },
        vec![SecureField::zero(); n_private_key_group_evals()],
        vec![SecureField::zero(); hosted_private_key_claimed_sums_len()],
        SharedFieldRelation::new(),
        SharedRangeRelation::new(),
        SharedKeccakRelations::new(),
        PrivateKeyEvalBindings::new(ExpandABindings::new().ntt, SharedT1CellRelation::new()),
    );
    assert!(matches!(
        result,
        Err(stwo::core::verifier::VerificationError::InvalidStructure(_))
    ));
}

#[test]
fn fixed_shape_wire_is_exact_and_capacity_shape_is_not_serialized() {
    #[derive(serde::Serialize)]
    struct FixedShapeWire {
        xof_mode: XofMode,
        message_len: usize,
        n_absorb: usize,
        n_squeeze: usize,
        absorb_stream_id: u32,
        squeeze_stream_id: u32,
        perm_id_base: usize,
    }

    let fixed = Shape::with_perm_id_base(303, 2, 11, 12, 73);
    let expected_wire = FixedShapeWire {
        xof_mode: fixed.xof_mode,
        message_len: fixed.message_len,
        n_absorb: fixed.n_absorb,
        n_squeeze: fixed.n_squeeze,
        absorb_stream_id: fixed.absorb_stream_id,
        squeeze_stream_id: fixed.squeeze_stream_id,
        perm_id_base: fixed.perm_id_base,
    };
    let encoded = bincode::serialize(&fixed).expect("fixed shape remains serializable");
    assert_eq!(
        encoded,
        bincode::serialize(&expected_wire).expect("expected fixed wire")
    );
    assert_eq!(
        bincode::deserialize::<Shape>(&encoded).expect("fixed shape round trip"),
        fixed
    );

    let capacity = Shape::with_message_capacity(303, DEVICE_SIG_STRUCTURE_CAPACITY + 66, 1, 11, 12)
        .expect("capacity shape");
    let error = bincode::serialize(&capacity).expect_err("capacity must not silently downgrade");
    assert!(error
        .to_string()
        .contains("must be reconstructed from the verifier profile"));
}

#[test]
fn hosted_private_key_public_mix_is_key_independent() {
    let msg = b"the public transcript exposes no stable device key".to_vec();
    let input_a = oracle_input(4_261, &msg);
    let input_b = oracle_input(4_262, &msg);
    assert_ne!(input_a.rho, input_b.rho);
    let witness_a = generate_witness(ML_DSA_65, &input_a).expect("witness a");
    let witness_b = generate_witness(ML_DSA_65, &input_b).expect("witness b");
    let bindings_a = ExpandABindings::new();
    let bindings_b = ExpandABindings::new();
    let first = MlDsaProver::hosted_private_key(
        witness_a,
        input_a,
        SharedFieldRelation::new(),
        SharedRangeRelation::new(),
        SharedKeccakRelations::new(),
        PrivateKeyEvalBindings::new(bindings_a.ntt, SharedT1CellRelation::new()),
    )
    .expect("first private-key prover");
    let second = MlDsaProver::hosted_private_key(
        witness_b,
        input_b,
        SharedFieldRelation::new(),
        SharedRangeRelation::new(),
        SharedKeccakRelations::new(),
        PrivateKeyEvalBindings::new(bindings_b.ntt, SharedT1CellRelation::new()),
    )
    .expect("second private-key prover");

    let mut first_channel = Blake2sChannel::default();
    let mut second_channel = Blake2sChannel::default();
    first.mix_public(&mut first_channel);
    second.mix_public(&mut second_channel);
    assert_eq!(
        FieldBytesRelation::draw(&mut first_channel),
        FieldBytesRelation::draw(&mut second_channel),
        "rho, t1, and derived tr must not enter the private-key public mix"
    );
}

#[test]
fn hosted_private_key_proves_and_adversarial_bindings_reject() {
    let msg = b"device authentication with a private ML-DSA public key".to_vec();
    let proof = prove_hosted_private_key(4_263, &msg);
    assert_eq!(proof.public_input.message, msg);
    assert_eq!(proof.group_evals.len(), 66);
    assert_eq!(proof.claimed_sums.len(), 16);
    verify_hosted_private_key(&proof).expect("hosted-private-key verify");

    let mut message_tamper = proof.clone();
    message_tamper.public_input.message[0] ^= 1;
    assert!(
        verify_hosted_private_key(&message_tamper).is_err(),
        "the public 00||00||M prefix must bind the µ job"
    );

    for group_eval_index in 0..proof.group_evals.len() {
        let mut eval_tamper = proof.clone();
        eval_tamper.group_evals[group_eval_index] += SecureField::from(m31(1));
        assert!(
            verify_hosted_private_key(&eval_tamper).is_err(),
            "a change to private group evaluation {group_eval_index} must be rejected"
        );
    }

    let mut source_tamper = proof.clone();
    source_tamper.private_key_source_claims[1] += SecureField::from(m31(1));
    assert!(
        verify_hosted_private_key(&source_tamper).is_err(),
        "a change to the packed-t1 source claim must be rejected"
    );

    for claimed_sum_index in 0..hosted_private_key_claimed_sums_len() {
        let mut claimed_sum_tamper = proof.clone();
        claimed_sum_tamper.claimed_sums[claimed_sum_index] += SecureField::from(m31(1));
        assert!(
            verify_hosted_private_key(&claimed_sum_tamper).is_err(),
            "a change to private-device claimed sum {claimed_sum_index} must be rejected"
        );
    }

    let mut reordered_evals = proof.clone();
    assert_ne!(
        reordered_evals.group_evals[30],
        reordered_evals.group_evals[31]
    );
    reordered_evals.group_evals.swap(30, 31);
    assert!(
        verify_hosted_private_key(&reordered_evals).is_err(),
        "reordering two fixed-position private evaluations must be rejected"
    );

    let public_key_shapes = keccak_job_shapes(msg.len(), 0, true);
    let public_key_shape_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_hosted_private_key_with_shapes(&proof, public_key_shapes)
    }));
    assert!(
        matches!(public_key_shape_result, Ok(Err(_))),
        "omitting the tr and µ service jobs must return an error, not panic"
    );
}

#[test]
fn hosted_private_key_capacity_crosses_mu_rate_boundary() {
    let msg = (0..130u32)
        .map(|i| i.wrapping_mul(23).wrapping_add(17) as u8)
        .collect::<Vec<_>>();
    let proof = prove_hosted_private_key(4_264, &msg);
    verify_hosted_private_key(&proof)
        .expect("130-byte device message must cancel every composed HashIo claim");
}

#[test]
fn hosted_private_key_malformed_claim_shapes_return_error_not_panic() {
    let public_input = MlDsaPrivateKeyPublicInput {
        message: b"malformed hosted private-key claim vectors".to_vec(),
    };
    let assert_rejected = |label: &str, group_evals: Vec<_>, claimed_sums: Vec<_>| {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let expand_bindings = ExpandABindings::new();
            MlDsaVerifier::hosted_private_key(
                public_input.clone(),
                group_evals,
                claimed_sums,
                SharedFieldRelation::new(),
                SharedRangeRelation::new(),
                SharedKeccakRelations::new(),
                PrivateKeyEvalBindings::new(expand_bindings.ntt, SharedT1CellRelation::new()),
            )
        }));
        assert!(
            matches!(
                result,
                Ok(Err(
                    stwo::core::verifier::VerificationError::InvalidStructure(_)
                ))
            ),
            "{label} must return InvalidStructure without panicking"
        );
    };

    assert_rejected(
        "short group vector",
        vec![SecureField::zero(); 65],
        vec![SecureField::zero(); 22],
    );
    assert_rejected(
        "long group vector",
        vec![SecureField::zero(); 67],
        vec![SecureField::zero(); 22],
    );
    assert_rejected(
        "short claimed-sum vector",
        vec![SecureField::zero(); 66],
        vec![SecureField::zero(); 21],
    );
    assert_rejected(
        "long claimed-sum vector",
        vec![SecureField::zero(); 66],
        vec![SecureField::zero(); 23],
    );
}

#[test]
fn hosted_tampered_shared_range_claim_rejects() {
    let msg = b"proof-wide range claim is transcript-bound".to_vec();
    let mut proof = prove_hosted_public(4252, &msg);
    proof.range_table_claimed_sum += SecureField::from(m31(1));
    assert!(verify_hosted_public(&proof).is_err());
}

#[test]
fn hosted_public_message_tamper_rejects_native_mu_prefix() {
    let msg = b"issuer/device public message native mu tamper".to_vec();
    let mut proof = prove_hosted_public(4245, &msg);
    proof.input.message[0] ^= 1;
    assert!(
        verify_hosted_public(&proof).is_err(),
        "tampered public message must change verifier-native µ and reject"
    );
}

#[test]
fn hosted_public_native_mu_mismatch_returns_error_not_panic() {
    let msg = b"native mu mismatch is an AIR rejection".to_vec();
    let mut input = oracle_input(4247, &msg);
    let witness = generate_witness(ML_DSA_65, &input).expect("honest witness");
    input.message[0] ^= 1;

    let handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut mldsa =
        MlDsaProver::hosted_public(witness, input, range_handle.clone(), handle.clone());
    let mut range_table = SharedRangeTable::prover(&[mldsa.range_uses().clone()], range_handle);
    let (job_shapes, job_streams) = mldsa.keccak_jobs();
    let mut service = KeccakServiceProver::new(job_shapes, job_streams, handle);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        air_core::prove_with_post_interaction(
            &mut [&mut range_table, &mut service, &mut mldsa],
            pcs_config(),
        )
    }));
    let (stark_proof, post_interaction_payloads) = result
        .expect("native µ mismatch must not panic")
        .expect("prover may commit the inconsistent trace; verifier rejects it");
    let proof = HostedProof {
        input: mldsa.input().clone(),
        group_evals: mldsa.group_evals().to_vec(),
        claimed_sums: mldsa.claimed_sums(),
        range_table_claimed_sum: range_table.claimed_sum(),
        service_claimed_sums: service.claimed_sums(),
        post_interaction_payloads,
        stark_proof,
    };
    assert!(verify_hosted_public(&proof).is_err());
}

#[test]
fn hosted_missing_round_gkr_payload_rejects() {
    let msg = b"hosted proof must carry the round GKR payload".to_vec();
    let mut proof = prove_hosted(4242, &msg, msg.clone());
    proof.post_interaction_payloads.clear();
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_hosted(&proof, msg)));
    assert!(
        matches!(result, Ok(Err(_))),
        "missing hosted round-GKR payload must return an error, not panic"
    );
}

#[test]
fn hosted_tampered_message_byte_rejects() {
    let msg = b"the hosted message bytes come from the host".to_vec();
    let proof = prove_hosted(4242, &msg, msg.clone());
    // The prover committed the honest proof. Verify against a producer that
    // yields a different first byte. This makes the global LogUp unbalanced.
    let mut tampered = msg.clone();
    tampered[0] ^= 0x01;
    assert!(
        verify_hosted(&proof, tampered).is_err(),
        "tampered producer bytes must break the swap balance"
    );
}

#[test]
fn hosted_verifier_derives_tr_from_the_public_key() {
    let msg = b"hosted tr is derived from the public key".to_vec();
    let mut proof = prove_hosted(4243, &msg, msg.clone());
    proof.input.tr[0] ^= 1;
    verify_hosted(&proof, msg).expect("the supplied tr value must not influence verification");
}

#[test]
fn hosted_public_key_tamper_recomputes_tr_and_rejects() {
    let msg = b"hosted native tr remains bound to the public key".to_vec();
    let mut proof = prove_hosted(4246, &msg, msg.clone());
    proof.input.rho[0] ^= 1;
    assert!(verify_hosted(&proof, msg).is_err());
}

// =====================================================================
// Multi-instance hosting: one proof contains device and revocation modules
// with different namespaces. One module uses a private message.
// =====================================================================

/// The claims one hosted instance contributes to the host's proof struct.
struct InstanceClaims {
    input: MlDsaVerifyInput,
    group_evals: Vec<SecureField>,
    claimed_sums: Vec<SecureField>,
}

struct TwoHostedProof {
    a: InstanceClaims,
    b: InstanceClaims,
    service_claimed_sums: Vec<SecureField>,
    range_table_claimed_sum: SecureField,
    post_interaction_payloads: Vec<Vec<u8>>,
    stark_proof: stwo::core::proof::StarkProof<air_core::Hasher>,
}

/// Prove `[range_table(uses a+b), keccak_service(jobs a+b), producer_a,
/// mldsa_a(ns_a, base 0), producer_b, mldsa_b(ns_b, base 16, private-msg)]`.
/// The ONE service and ONE range table host both instances; the stream bases
/// keep their HashIo ids disjoint under the single shared relation set.
fn prove_two_hosted(
    seed_a: u64,
    msg_a: &[u8],
    ns_a: &str,
    seed_b: u64,
    msg_b: &[u8],
    ns_b: &str,
) -> TwoHostedProof {
    let input_a = oracle_input(seed_a, msg_a);
    let input_b = oracle_input(seed_b, msg_b);
    let witness_a = generate_witness(ML_DSA_65, &input_a).expect("witness a");
    let witness_b = generate_witness(ML_DSA_65, &input_b).expect("witness b");

    let handle_a = SharedFieldRelation::new();
    let handle_b = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut producer_a = FieldProducer::new(msg_a.to_vec(), handle_a.clone());
    let mut producer_b = FieldProducer::new(msg_b.to_vec(), handle_b.clone());
    let mut mldsa_a = MlDsaProver::hosted(
        witness_a,
        input_a.clone(),
        handle_a,
        range_handle.clone(),
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_a);
    let mut mldsa_b = MlDsaProver::hosted(
        witness_b,
        input_b.clone(),
        handle_b,
        range_handle.clone(),
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_b)
    .with_stream_base(STREAM_BASE_STRIDE)
    .with_private_message();
    let mut range_table = SharedRangeTable::prover(
        &[mldsa_a.range_uses().clone(), mldsa_b.range_uses().clone()],
        range_handle,
    );

    let (shapes_a, streams_a) = mldsa_a.keccak_jobs();
    let (shapes_b, streams_b) = mldsa_b.keccak_jobs();
    let mut service = KeccakServiceProver::new(
        [shapes_a, shapes_b].concat(),
        [streams_a, streams_b].concat(),
        keccak_handle,
    );

    let (stark_proof, post_interaction_payloads) = air_core::prove_with_post_interaction(
        &mut [
            &mut range_table,
            &mut service,
            &mut producer_a,
            &mut mldsa_a,
            &mut producer_b,
            &mut mldsa_b,
        ],
        pcs_config(),
    )
    .expect("two-instance prove");

    let claims = |m: &MlDsaProver, input: &MlDsaVerifyInput| InstanceClaims {
        input: input.clone(),
        group_evals: m.group_evals().to_vec(),
        claimed_sums: m.claimed_sums(),
    };
    TwoHostedProof {
        a: claims(&mldsa_a, &input_a),
        b: claims(&mldsa_b, &input_b),
        service_claimed_sums: service.claimed_sums(),
        range_table_claimed_sum: range_table.claimed_sum(),
        post_interaction_payloads,
        stark_proof,
    }
}

/// Verify the two-instance composition. Instance B runs in private-message
/// mode: its verifier-side input carries ZEROED message bytes (only the length
/// is real) — the bytes reach the µ absorption exclusively through producer_b.
fn verify_two_hosted(
    a: &InstanceClaims,
    ns_a: &str,
    b: &InstanceClaims,
    ns_b: &str,
    proof: &TwoHostedProof,
    producer_a_bytes: Vec<u8>,
    producer_b_bytes: Vec<u8>,
) -> Result<(), stwo::core::verifier::VerificationError> {
    let handle_a = SharedFieldRelation::new();
    let handle_b = SharedFieldRelation::new();
    let keccak_handle = SharedKeccakRelations::new();
    let range_handle = SharedRangeRelation::new();
    let mut producer_a = FieldProducer::new(producer_a_bytes, handle_a.clone());
    let mut producer_b = FieldProducer::new(producer_b_bytes, handle_b.clone());
    let job_shapes = [
        keccak_job_shapes(a.input.message.len(), 0, false),
        keccak_job_shapes(b.input.message.len(), STREAM_BASE_STRIDE, false),
    ]
    .concat();
    let mut service = KeccakServiceVerifier::new(
        job_shapes,
        proof.service_claimed_sums.clone(),
        keccak_handle.clone(),
    );
    let mut range_table =
        SharedRangeTable::verifier(proof.range_table_claimed_sum, range_handle.clone());
    let mut mldsa_a = MlDsaVerifier::hosted(
        a.input.clone(),
        a.group_evals.clone(),
        a.claimed_sums.clone(),
        handle_a,
        range_handle.clone(),
        keccak_handle.clone(),
    )
    .with_instance_namespace(ns_a);
    let mut zeroed_b = b.input.clone();
    zeroed_b.message = vec![0u8; b.input.message.len()];
    let mut mldsa_b = MlDsaVerifier::hosted(
        zeroed_b,
        b.group_evals.clone(),
        b.claimed_sums.clone(),
        handle_b,
        range_handle,
        keccak_handle,
    )
    .with_instance_namespace(ns_b)
    .with_stream_base(STREAM_BASE_STRIDE)
    .with_private_message();
    air_core::verify_with_expected_preprocessed_root_and_payloads(
        &mut [
            &mut range_table,
            &mut service,
            &mut producer_a,
            &mut mldsa_a,
            &mut producer_b,
            &mut mldsa_b,
        ],
        &proof.stark_proof,
        None,
        &proof.post_interaction_payloads,
    )
    .map_err(|e| match e {
        air_core::VerifyError::Stark(e) => e,
        air_core::VerifyError::PreprocessedRootMismatch { .. } => unreachable!("no root pinned"),
    })
}

#[test]
fn two_namespaced_hosted_instances_prove_and_verify() {
    // Different message LENGTHS on purpose: the bridge/sink preprocessed
    // columns are shape-dependent, so this exercises disjoint ids end to end.
    let msg_a = b"instance-a: the issuer-style public message".to_vec();
    let msg_b = b"instance-b-private".to_vec();
    let proof = prove_two_hosted(111, &msg_a, "test/a", 222, &msg_b, "test/b");
    verify_two_hosted(&proof.a, "test/a", &proof.b, "test/b", &proof, msg_a, msg_b)
        .expect("two-instance verify");
}

#[test]
fn two_hosted_instances_swapped_claims_reject() {
    // Same message LENGTH so the swap is not rejected trivially on shape: the
    // role separation must come from the namespaced transcript + inputs.
    let msg_a = b"same-length-message-aaaaaaaa".to_vec();
    let msg_b = b"same-length-message-bbbbbbbb".to_vec();
    let proof = prove_two_hosted(111, &msg_a, "test/a", 222, &msg_b, "test/b");
    // Present A's claim tree in B's slot and vice versa (inputs stay put).
    let swapped_a = InstanceClaims {
        input: proof.a.input.clone(),
        group_evals: proof.b.group_evals.clone(),
        claimed_sums: proof.b.claimed_sums.clone(),
    };
    let swapped_b = InstanceClaims {
        input: proof.b.input.clone(),
        group_evals: proof.a.group_evals.clone(),
        claimed_sums: proof.a.claimed_sums.clone(),
    };
    assert!(
        verify_two_hosted(&swapped_a, "test/a", &swapped_b, "test/b", &proof, msg_a, msg_b)
            .is_err(),
        "cross-instance claim replay must be rejected"
    );
}

/// Static SIB schedules with identical content can use the same namespace.
/// Their preprocessed identifiers deduplicate safely, so the pair proves and verifies.
/// The generic differing-content panic remains covered directly by
/// `air_core::tests::preprocessed_invariant_rejects_duplicate_id_with_different_content`.
#[test]
fn two_instances_same_namespace_share_static_preprocessed() {
    let msg_a = b"same-length-message-aaaaaaaa".to_vec();
    let msg_b = b"same-length-message-bbbbbbbb".to_vec();
    let proof = prove_two_hosted(111, &msg_a, "test/dup", 222, &msg_b, "test/dup");
    verify_two_hosted(
        &proof.a, "test/dup", &proof.b, "test/dup", &proof, msg_a, msg_b,
    )
    .expect("same-namespace static preprocessing deduplicates");
}
