//! Bind and normalize the private ML-DSA device public key in the MSO.
//!
//! The private MSO binder emits the first FIPS 204 `pkEncode` position.
//! This component consumes the 1,312 ML-DSA-44 `pkEncode` bytes.
//! It emits the same bytes for the private-key evaluator.
//! It consumes the `rho` cells from `ExpandA`.
//! It also consumes the evaluator's split `t1` cells.

use std::fmt;

use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, QM31, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator, ORIGINAL_TRACE_IDX,
};
use stwo_mldsa::air_util::{col_eval, m31, ColEval};
use stwo_mldsa::binding::{
    RhoCellRelation, SharedRhoCellRelation, SharedT1CellRelation, T1CellRelation,
};
use stwo_mldsa::coeffs::relations::{RangeRelation, SharedRangeRelation};
use stwo_mldsa::coeffs::tables::RcKind;
use stwo_mldsa::coeffs::RcUses;
use stwo_mldsa::constants::N;
use stwo_mldsa::profile::ML_DSA_44;
use stwo_mldsa::statement::{HOSTED_DEVICE_PK_FIELD_ID, HOSTED_MSG_FIELD_ID};

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};
use crate::mdoc_private_mso_bind::{MdocDevicePkStartRelation, SharedMdocDevicePkStartRelation};

pub(crate) const MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_PRIVATE_DEVICE_KEY_ROWS: usize = 1usize << MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE;
const DEVICE_K: usize = 4;
const DEVICE_PK_BYTES: usize = 1_312;
pub(crate) const MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS: usize = 32 + DEVICE_K * 64;
pub(crate) const MDOC_PRIVATE_DEVICE_KEY_BLIND_ROWS: usize =
    MDOC_PRIVATE_DEVICE_KEY_ROWS - MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS;

const DEVICE_KEY_BIND_DOMAIN: u64 = 0x4d44_4f43_504b_5539;
const DEVICE_KEY_BIND_VERSION: u64 = 1;
const T1_GROUP_BYTES: usize = 5;
const T1_COEFFICIENTS_PER_GROUP: usize = 4;
const T1_BYTES_PER_POLYNOMIAL: u32 = 64 * T1_GROUP_BYTES as u32;
/// `4 / 5` in M31. This converts a five-byte group offset to its first
/// coefficient index.
const COEFFICIENT_BASE_SCALE: u32 = 1_288_490_189;
const PREPROCESSED_COLS: usize = 5;
const TRACE_COLS: usize = 34;
const MAIN_LOGUP_SITES: usize = 23;
const MAIN_INTERACTION_COLS: usize = MAIN_LOGUP_SITES.div_ceil(2) * SECURE_EXTENSION_DEGREE;
const BLINDER_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

const PP_ACTIVE: usize = 0;
const PP_T1_ROW: usize = 1;
const PP_FIRST: usize = 2;
const PP_BYTE_BASE: usize = 3;
const PP_POLY: usize = 4;

const COL_DEVICE_PK_START: usize = 0;
const COL_BYTE_START: usize = 1;
const COL_B1_BITS: usize = COL_BYTE_START + T1_GROUP_BYTES;
const COL_B2_BITS: usize = COL_B1_BITS + 8;
const COL_B3_BITS: usize = COL_B2_BITS + 8;
const COL_T1_HI_START: usize = COL_B3_BITS + 8;

const _: () = assert!(MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS == 288);
const _: () = assert!(MDOC_PRIVATE_DEVICE_KEY_BLIND_ROWS == 224);
const _: () = assert!(DEVICE_PK_BYTES == ML_DSA_44.pk_bytes());
const _: () = assert!(DEVICE_K == ML_DSA_44.k());
const _: () = assert!(N == 256);
const _: () = assert!(COL_T1_HI_START + T1_COEFFICIENTS_PER_GROUP == TRACE_COLS);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateDeviceKeyBindError {
    IssuerMessageLengthOutOfRange {
        length: usize,
        max: usize,
    },
    PublicKeyLength {
        length: usize,
        expected: usize,
    },
    DeviceKeyWindowOutOfBounds {
        start: usize,
        length: usize,
        issuer_message_len: usize,
    },
}

impl fmt::Display for MdocPrivateDeviceKeyBindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IssuerMessageLengthOutOfRange { length, max } => write!(
                f,
                "issuer message length {length} is outside 1..={max}"
            ),
            Self::PublicKeyLength { length, expected } => {
                write!(f, "device public key has {length} bytes; expected {expected}")
            }
            Self::DeviceKeyWindowOutOfBounds {
                start,
                length,
                issuer_message_len,
            } => write!(
                f,
                "device public-key window [{start}, {}) exceeds the {issuer_message_len}-byte issuer message",
                start.saturating_add(*length)
            ),
        }
    }
}

impl std::error::Error for MdocPrivateDeviceKeyBindError {}

#[derive(Clone)]
pub(crate) struct MdocPrivateDeviceKeyUseCensus {
    pub(crate) issuer_position_uses: Vec<u32>,
    pub(crate) normalized_uses: usize,
    pub(crate) rho_uses: usize,
    pub(crate) t1_uses: usize,
    pub(crate) device_pk_start_uses: usize,
    pub(crate) range_uses: RcUses,
    pub(crate) active_rows: usize,
    pub(crate) blind_rows: usize,
}

impl MdocPrivateDeviceKeyUseCensus {
    pub(crate) fn has_fixed_demo_shape(&self) -> bool {
        self.normalized_uses == DEVICE_PK_BYTES
            && self.rho_uses == 32
            && self.t1_uses == DEVICE_K * N
            && self.device_pk_start_uses == 1
            && self.active_rows == MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS
            && self.blind_rows == MDOC_PRIVATE_DEVICE_KEY_BLIND_ROWS
            && self.range_uses.rc8.iter().sum::<u32>()
                == (MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS + DEVICE_K * 64) as u32
            && self.range_uses.rc9.iter().sum::<u32>() == (DEVICE_K * N) as u32
            && self.range_uses.rc7.iter().all(|&count| count == 0)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocPrivateDeviceKeyInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

#[derive(Clone, Copy)]
struct Row {
    byte_base: usize,
    poly: usize,
}

impl Row {
    fn is_rho(self) -> bool {
        self.byte_base < 32
    }

    fn is_t1(self) -> bool {
        !self.is_rho()
    }

    fn is_first(self) -> bool {
        self.byte_base == 0
    }

    fn lane_active(self, lane: usize) -> bool {
        lane == 0 || self.is_t1()
    }

    #[cfg(test)]
    fn coefficient_base(self) -> usize {
        if self.is_t1() {
            let group_byte = self.byte_base - 32 - self.poly * T1_BYTES_PER_POLYNOMIAL as usize;
            group_byte / T1_GROUP_BYTES * T1_COEFFICIENTS_PER_GROUP
        } else {
            0
        }
    }
}

fn schedule() -> Vec<Row> {
    let mut rows = Vec::with_capacity(MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS);
    for byte_index in 0..32 {
        rows.push(Row {
            byte_base: byte_index,
            poly: 0,
        });
    }
    for poly in 0..DEVICE_K {
        for group in 0..64 {
            rows.push(Row {
                byte_base: 32 + (poly * 64 + group) * T1_GROUP_BYTES,
                poly,
            });
        }
    }
    debug_assert_eq!(rows.len(), MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS);
    rows
}

fn col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/private_device_key_bind/v{DEVICE_KEY_BIND_VERSION}/{name}"),
    }
}

fn preprocessed_ids() -> Vec<PreProcessedColumnId> {
    let ids = ["active", "t1_row", "first", "byte_base", "poly"]
        .into_iter()
        .map(col_id)
        .collect::<Vec<_>>();
    debug_assert_eq!(ids.len(), PREPROCESSED_COLS);
    ids
}

fn preprocessed_columns() -> Vec<ColEval> {
    let mut columns = vec![vec![m31(0); MDOC_PRIVATE_DEVICE_KEY_ROWS]; PREPROCESSED_COLS];
    for (row_index, row) in schedule().iter().enumerate() {
        columns[PP_ACTIVE][row_index] = m31(1);
        columns[PP_T1_ROW][row_index] = m31(row.is_t1() as u32);
        columns[PP_FIRST][row_index] = m31(row.is_first() as u32);
        columns[PP_BYTE_BASE][row_index] = m31(row.byte_base as u32);
        columns[PP_POLY][row_index] = m31(row.poly as u32);
    }
    columns
        .into_iter()
        .map(|column| col_eval(MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE, column))
        .collect()
}

fn random_m31() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return m31(candidate);
        }
    }
}

fn random_bit() -> M31 {
    m31(rand::thread_rng().next_u32() & 1)
}

fn set_bits(columns: &mut [Vec<M31>], start: usize, row: usize, byte: u8) {
    for bit in 0..8 {
        columns[start + bit][row] = m31(u32::from((byte >> bit) & 1));
    }
}

fn bit_value(byte: u8, start: usize, width: usize) -> u32 {
    (u32::from(byte) >> start) & ((1u32 << width) - 1)
}

fn unpack_group(bytes: &[u8]) -> [u32; T1_COEFFICIENTS_PER_GROUP] {
    let [b0, b1, b2, b3, b4]: [u8; T1_GROUP_BYTES] =
        bytes.try_into().expect("one five-byte t1 group");
    let l2 = bit_value(b1, 0, 2);
    let h6 = bit_value(b1, 2, 6);
    let l4 = bit_value(b2, 0, 4);
    let h4 = bit_value(b2, 4, 4);
    let l6 = bit_value(b3, 0, 6);
    let h2 = bit_value(b3, 6, 2);
    [
        u32::from(b0) + (l2 << 8),
        h6 + (l4 << 6),
        h4 + (l6 << 4),
        h2 + (u32::from(b4) << 2),
    ]
}

#[derive(Clone)]
struct MdocPrivateDeviceKeyTrace {
    columns: Vec<Vec<M31>>,
}

impl MdocPrivateDeviceKeyTrace {
    fn evals(&self) -> Vec<ColEval> {
        self.columns
            .iter()
            .cloned()
            .map(|column| col_eval(MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE, column))
            .collect()
    }
}

fn validate_public_shape(issuer_message_len: usize) -> Result<(), MdocPrivateDeviceKeyBindError> {
    let max = crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES;
    if issuer_message_len == 0 || issuer_message_len > max {
        return Err(
            MdocPrivateDeviceKeyBindError::IssuerMessageLengthOutOfRange {
                length: issuer_message_len,
                max,
            },
        );
    }
    Ok(())
}

fn build_trace(
    pk_encode: &[u8],
    device_pk_start: usize,
    issuer_message_len: usize,
) -> Result<(MdocPrivateDeviceKeyTrace, MdocPrivateDeviceKeyUseCensus), MdocPrivateDeviceKeyBindError>
{
    validate_public_shape(issuer_message_len)?;
    if pk_encode.len() != DEVICE_PK_BYTES {
        return Err(MdocPrivateDeviceKeyBindError::PublicKeyLength {
            length: pk_encode.len(),
            expected: DEVICE_PK_BYTES,
        });
    }
    let end = device_pk_start.checked_add(DEVICE_PK_BYTES).ok_or(
        MdocPrivateDeviceKeyBindError::DeviceKeyWindowOutOfBounds {
            start: device_pk_start,
            length: DEVICE_PK_BYTES,
            issuer_message_len,
        },
    )?;
    if end > issuer_message_len {
        return Err(MdocPrivateDeviceKeyBindError::DeviceKeyWindowOutOfBounds {
            start: device_pk_start,
            length: DEVICE_PK_BYTES,
            issuer_message_len,
        });
    }

    let mut columns = vec![vec![m31(0); MDOC_PRIVATE_DEVICE_KEY_ROWS]; TRACE_COLS];
    for column in &mut columns {
        for cell in column {
            *cell = random_m31();
        }
    }
    for column in &mut columns[COL_B1_BITS..TRACE_COLS] {
        for cell in column {
            *cell = random_bit();
        }
    }

    let mut range_uses = RcUses::new();
    let mut issuer_position_uses = vec![0u32; issuer_message_len];
    for (row_index, row) in schedule().iter().enumerate() {
        columns[COL_DEVICE_PK_START][row_index] = m31(device_pk_start as u32);
        for lane in 0..T1_GROUP_BYTES {
            if row.lane_active(lane) {
                let relative = row.byte_base + lane;
                let byte = pk_encode[relative];
                columns[COL_BYTE_START + lane][row_index] = m31(u32::from(byte));
                issuer_position_uses[device_pk_start + relative] = 1;
            }
        }
        let b0 = pk_encode[row.byte_base];
        range_uses.record(RcKind::Rc8, u32::from(b0));
        if row.is_t1() {
            let group = &pk_encode[row.byte_base..row.byte_base + T1_GROUP_BYTES];
            set_bits(&mut columns, COL_B1_BITS, row_index, group[1]);
            set_bits(&mut columns, COL_B2_BITS, row_index, group[2]);
            set_bits(&mut columns, COL_B3_BITS, row_index, group[3]);
            let unpacked = unpack_group(group);
            for (lane, value) in unpacked.into_iter().enumerate() {
                columns[COL_T1_HI_START + lane][row_index] = m31(value >> 9);
                range_uses.record(RcKind::Rc9, value & 0x1ff);
            }
            range_uses.record(RcKind::Rc8, u32::from(group[4]));
        }
    }

    Ok((
        MdocPrivateDeviceKeyTrace { columns },
        MdocPrivateDeviceKeyUseCensus {
            issuer_position_uses,
            normalized_uses: DEVICE_PK_BYTES,
            rho_uses: 32,
            t1_uses: DEVICE_K * N,
            device_pk_start_uses: 1,
            range_uses,
            active_rows: MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS,
            blind_rows: MDOC_PRIVATE_DEVICE_KEY_BLIND_ROWS,
        },
    ))
}

fn constant<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(m31(value))
}

fn bit_sum<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(constant::<E>(0), |sum, (bit, value)| {
            sum + constant::<E>(1 << bit) * value.clone()
        })
}

fn add_boolean<E: EvalAtRow>(eval: &mut E, value: E::F, one: &E::F) {
    eval.add_constraint(value.clone() * (value - one.clone()));
}

#[derive(Clone)]
struct MdocPrivateDeviceKeyRelations {
    issuer: FieldBytesRelation,
    range: RangeRelation,
    rho: RhoCellRelation,
    t1: T1CellRelation,
    start: MdocDevicePkStartRelation,
    blinder: ClaimedSumBlinderRelation,
}

#[derive(Clone)]
struct MdocPrivateDeviceKeyEval {
    relations: MdocPrivateDeviceKeyRelations,
    blinder_v: QM31,
    blinder_m: QM31,
}

impl FrameworkEval for MdocPrivateDeviceKeyEval {
    fn log_size(&self) -> u32 {
        MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(col_id("active"));
        let t1_row = eval.get_preprocessed_column(col_id("t1_row"));
        let first = eval.get_preprocessed_column(col_id("first"));
        let byte_base = eval.get_preprocessed_column(col_id("byte_base"));
        let poly = eval.get_preprocessed_column(col_id("poly"));
        let rho_row = active.clone() - t1_row.clone();
        let coefficient_base = constant::<E>(COEFFICIENT_BASE_SCALE)
            * (byte_base.clone()
                - constant::<E>(32) * t1_row.clone()
                - constant::<E>(T1_BYTES_PER_POLYNOMIAL) * poly.clone());
        let lane_active: [E::F; T1_GROUP_BYTES] = std::array::from_fn(|lane| {
            if lane == 0 {
                active.clone()
            } else {
                t1_row.clone()
            }
        });

        let [device_pk_start, device_pk_start_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let bytes: [E::F; T1_GROUP_BYTES] = std::array::from_fn(|_| eval.next_trace_mask());
        let b1_bits: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());
        let b2_bits: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());
        let b3_bits: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());
        let hi1: [E::F; T1_COEFFICIENTS_PER_GROUP] =
            std::array::from_fn(|_| eval.next_trace_mask());

        let one = constant::<E>(1);
        for selector in [active.clone(), t1_row.clone(), first.clone()] {
            add_boolean(&mut eval, selector, &one);
        }
        eval.add_constraint(
            (active.clone() - first.clone()) * (device_pk_start.clone() - device_pk_start_prev),
        );

        for bit in b1_bits
            .iter()
            .chain(b2_bits.iter())
            .chain(b3_bits.iter())
            .chain(hi1.iter())
        {
            add_boolean(&mut eval, bit.clone(), &one);
        }
        eval.add_constraint(t1_row.clone() * (bytes[1].clone() - bit_sum::<E>(&b1_bits)));
        eval.add_constraint(t1_row.clone() * (bytes[2].clone() - bit_sum::<E>(&b2_bits)));
        eval.add_constraint(t1_row.clone() * (bytes[3].clone() - bit_sum::<E>(&b3_bits)));

        let l2 = bit_sum::<E>(&b1_bits[0..2]);
        let h6 = bit_sum::<E>(&b1_bits[2..8]);
        let l4 = bit_sum::<E>(&b2_bits[0..4]);
        let h4 = bit_sum::<E>(&b2_bits[4..8]);
        let l6 = bit_sum::<E>(&b3_bits[0..6]);
        let h2 = bit_sum::<E>(&b3_bits[6..8]);
        let values = [
            bytes[0].clone() + constant::<E>(256) * l2,
            h6 + constant::<E>(64) * l4,
            h4 + constant::<E>(16) * l6,
            h2 + constant::<E>(4) * bytes[4].clone(),
        ];
        let lo9: [E::F; T1_COEFFICIENTS_PER_GROUP] = std::array::from_fn(|lane| {
            values[lane].clone() - constant::<E>(512) * hi1[lane].clone()
        });

        // Fixed site order: source bytes, normalized bytes, Rc8, Rc9, T1,
        // rho, device-pk start, then the claimed-sum blinder.
        for lane in 0..T1_GROUP_BYTES {
            let relative_index = byte_base.clone() + constant::<E>(lane as u32);
            eval.add_to_relation(RelationEntry::new(
                &self.relations.issuer,
                E::EF::from(lane_active[lane].clone()),
                &[
                    constant::<E>(HOSTED_MSG_FIELD_ID),
                    device_pk_start.clone() + relative_index.clone(),
                    bytes[lane].clone(),
                ],
            ));
        }
        for lane in 0..T1_GROUP_BYTES {
            eval.add_to_relation(RelationEntry::new(
                &self.relations.issuer,
                -E::EF::from(lane_active[lane].clone()),
                &[
                    constant::<E>(HOSTED_DEVICE_PK_FIELD_ID),
                    byte_base.clone() + constant::<E>(lane as u32),
                    bytes[lane].clone(),
                ],
            ));
        }
        for (value, numerator) in [
            (bytes[0].clone(), active.clone()),
            (bytes[4].clone(), t1_row.clone()),
        ] {
            eval.add_to_relation(RelationEntry::new(
                &self.relations.range,
                E::EF::from(numerator),
                &[value, constant::<E>(RcKind::Rc8.bound_id())],
            ));
        }
        for value in &lo9 {
            eval.add_to_relation(RelationEntry::new(
                &self.relations.range,
                E::EF::from(t1_row.clone()),
                &[value.clone(), constant::<E>(RcKind::Rc9.bound_id())],
            ));
        }
        for lane in 0..T1_COEFFICIENTS_PER_GROUP {
            eval.add_to_relation(RelationEntry::new(
                &self.relations.t1,
                -E::EF::from(t1_row.clone()),
                &[
                    poly.clone(),
                    coefficient_base.clone() + constant::<E>(lane as u32),
                    lo9[lane].clone(),
                    hi1[lane].clone(),
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::new(
            &self.relations.rho,
            -E::EF::from(rho_row),
            &[byte_base, bytes[0].clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.relations.start,
            E::EF::from(first),
            &[device_pk_start],
        ));
        add_blinder_relation_entry(
            &mut eval,
            &self.relations.blinder,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn packed_bit_sum(trace: &[ColEval], start: usize, vec_row: usize, width: usize) -> PackedM31 {
    (0..width).fold(PackedM31::broadcast(m31(0)), |sum, bit| {
        sum + PackedM31::broadcast(m31(1 << bit)) * trace[start + bit].data[vec_row]
    })
}

fn combine_pairwise_sites(sites: &[Vec<(PackedQM31, PackedQM31)>]) -> (Vec<ColEval>, SecureField) {
    debug_assert_eq!(sites.len(), MAIN_LOGUP_SITES);
    let vec_rows = 1usize << (MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE);
    let mut site = 0;
    while site + 1 < sites.len() {
        logup.col_from_iter((0..vec_rows).map(|row| {
            let (left_num, left_den) = sites[site][row];
            let (right_num, right_den) = sites[site + 1][row];
            (
                left_num * right_den + right_num * left_den,
                left_den * right_den,
            )
        }));
        site += 2;
    }
    if site < sites.len() {
        logup.col_from_iter((0..vec_rows).map(|row| sites[site][row]));
    }
    logup.finalize_last()
}

fn interaction_trace(
    trace: &MdocPrivateDeviceKeyTrace,
    relations: &MdocPrivateDeviceKeyRelations,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<ColEval>, SecureField) {
    let preprocessed = preprocessed_columns();
    let trace = trace.evals();
    let vec_rows = 1usize << (MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(MAIN_LOGUP_SITES);

    for lane in 0..T1_GROUP_BYTES {
        sites.push(
            (0..vec_rows)
                .map(|row| {
                    let relative = preprocessed[PP_BYTE_BASE].data[row]
                        + PackedM31::broadcast(m31(lane as u32));
                    let lane_active = if lane == 0 {
                        preprocessed[PP_ACTIVE].data[row]
                    } else {
                        preprocessed[PP_T1_ROW].data[row]
                    };
                    (
                        PackedQM31::from(lane_active),
                        relations.issuer.combine(&[
                            PackedM31::broadcast(m31(HOSTED_MSG_FIELD_ID)),
                            trace[COL_DEVICE_PK_START].data[row] + relative,
                            trace[COL_BYTE_START + lane].data[row],
                        ]),
                    )
                })
                .collect(),
        );
    }
    for lane in 0..T1_GROUP_BYTES {
        sites.push(
            (0..vec_rows)
                .map(|row| {
                    let lane_active = if lane == 0 {
                        preprocessed[PP_ACTIVE].data[row]
                    } else {
                        preprocessed[PP_T1_ROW].data[row]
                    };
                    (
                        -PackedQM31::from(lane_active),
                        relations.issuer.combine(&[
                            PackedM31::broadcast(m31(HOSTED_DEVICE_PK_FIELD_ID)),
                            preprocessed[PP_BYTE_BASE].data[row]
                                + PackedM31::broadcast(m31(lane as u32)),
                            trace[COL_BYTE_START + lane].data[row],
                        ]),
                    )
                })
                .collect(),
        );
    }
    for (byte_column, selector) in [(COL_BYTE_START, PP_ACTIVE), (COL_BYTE_START + 4, PP_T1_ROW)] {
        sites.push(
            (0..vec_rows)
                .map(|row| {
                    (
                        PackedQM31::from(preprocessed[selector].data[row]),
                        relations.range.combine(&[
                            trace[byte_column].data[row],
                            PackedM31::broadcast(m31(RcKind::Rc8.bound_id())),
                        ]),
                    )
                })
                .collect(),
        );
    }

    for lane in 0..T1_COEFFICIENTS_PER_GROUP {
        sites.push(
            (0..vec_rows)
                .map(|row| {
                    let l2 = packed_bit_sum(&trace, COL_B1_BITS, row, 2);
                    let h6 = packed_bit_sum(&trace, COL_B1_BITS + 2, row, 6);
                    let l4 = packed_bit_sum(&trace, COL_B2_BITS, row, 4);
                    let h4 = packed_bit_sum(&trace, COL_B2_BITS + 4, row, 4);
                    let l6 = packed_bit_sum(&trace, COL_B3_BITS, row, 6);
                    let h2 = packed_bit_sum(&trace, COL_B3_BITS + 6, row, 2);
                    let value = match lane {
                        0 => trace[COL_BYTE_START].data[row] + PackedM31::broadcast(m31(256)) * l2,
                        1 => h6 + PackedM31::broadcast(m31(64)) * l4,
                        2 => h4 + PackedM31::broadcast(m31(16)) * l6,
                        3 => {
                            h2 + PackedM31::broadcast(m31(4)) * trace[COL_BYTE_START + 4].data[row]
                        }
                        _ => unreachable!(),
                    };
                    let lo9 = value
                        - PackedM31::broadcast(m31(512)) * trace[COL_T1_HI_START + lane].data[row];
                    (
                        PackedQM31::from(preprocessed[PP_T1_ROW].data[row]),
                        relations
                            .range
                            .combine(&[lo9, PackedM31::broadcast(m31(RcKind::Rc9.bound_id()))]),
                    )
                })
                .collect(),
        );
    }
    for lane in 0..T1_COEFFICIENTS_PER_GROUP {
        sites.push(
            (0..vec_rows)
                .map(|row| {
                    let l2 = packed_bit_sum(&trace, COL_B1_BITS, row, 2);
                    let h6 = packed_bit_sum(&trace, COL_B1_BITS + 2, row, 6);
                    let l4 = packed_bit_sum(&trace, COL_B2_BITS, row, 4);
                    let h4 = packed_bit_sum(&trace, COL_B2_BITS + 4, row, 4);
                    let l6 = packed_bit_sum(&trace, COL_B3_BITS, row, 6);
                    let h2 = packed_bit_sum(&trace, COL_B3_BITS + 6, row, 2);
                    let value = match lane {
                        0 => trace[COL_BYTE_START].data[row] + PackedM31::broadcast(m31(256)) * l2,
                        1 => h6 + PackedM31::broadcast(m31(64)) * l4,
                        2 => h4 + PackedM31::broadcast(m31(16)) * l6,
                        3 => {
                            h2 + PackedM31::broadcast(m31(4)) * trace[COL_BYTE_START + 4].data[row]
                        }
                        _ => unreachable!(),
                    };
                    let hi = trace[COL_T1_HI_START + lane].data[row];
                    let lo = value - PackedM31::broadcast(m31(512)) * hi;
                    let coefficient_base = PackedM31::broadcast(m31(COEFFICIENT_BASE_SCALE))
                        * (preprocessed[PP_BYTE_BASE].data[row]
                            - PackedM31::broadcast(m31(32)) * preprocessed[PP_T1_ROW].data[row]
                            - PackedM31::broadcast(m31(T1_BYTES_PER_POLYNOMIAL))
                                * preprocessed[PP_POLY].data[row]);
                    (
                        -PackedQM31::from(preprocessed[PP_T1_ROW].data[row]),
                        relations.t1.combine(&[
                            preprocessed[PP_POLY].data[row],
                            coefficient_base + PackedM31::broadcast(m31(lane as u32)),
                            lo,
                            hi,
                        ]),
                    )
                })
                .collect(),
        );
    }
    sites.push(
        (0..vec_rows)
            .map(|row| {
                let rho_row = preprocessed[PP_ACTIVE].data[row] - preprocessed[PP_T1_ROW].data[row];
                (
                    -PackedQM31::from(rho_row),
                    relations.rho.combine(&[
                        preprocessed[PP_BYTE_BASE].data[row],
                        trace[COL_BYTE_START].data[row],
                    ]),
                )
            })
            .collect(),
    );
    sites.push(
        (0..vec_rows)
            .map(|row| {
                (
                    PackedQM31::from(preprocessed[PP_FIRST].data[row]),
                    relations
                        .start
                        .combine(&[trace[COL_DEVICE_PK_START].data[row]]),
                )
            })
            .collect(),
    );
    sites.push(vec![
        (
            PackedQM31::broadcast(blinder_m),
            blinder_denominator(&relations.blinder, blinder_v),
        );
        vec_rows
    ]);
    combine_pairwise_sites(&sites)
}

type MdocPrivateDeviceKeyComponent = FrameworkComponent<MdocPrivateDeviceKeyEval>;

pub(crate) struct MdocPrivateDeviceKeyBind {
    issuer_message_len: usize,
    trace: Option<MdocPrivateDeviceKeyTrace>,
    range_uses: Option<RcUses>,
    issuer_handle: SharedFieldRelation,
    range_handle: SharedRangeRelation,
    rho_handle: SharedRhoCellRelation,
    t1_handle: SharedT1CellRelation,
    start_handle: SharedMdocDevicePkStartRelation,
    relations: Option<MdocPrivateDeviceKeyRelations>,
    claim: Option<MdocPrivateDeviceKeyInteractionClaim>,
    component: Option<MdocPrivateDeviceKeyComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocPrivateDeviceKeyBind {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prover(
        pk_encode: Vec<u8>,
        device_pk_start: usize,
        issuer_message_len: usize,
        issuer_handle: SharedFieldRelation,
        range_handle: SharedRangeRelation,
        rho_handle: SharedRhoCellRelation,
        t1_handle: SharedT1CellRelation,
        start_handle: SharedMdocDevicePkStartRelation,
    ) -> Result<(Self, MdocPrivateDeviceKeyUseCensus), MdocPrivateDeviceKeyBindError> {
        let (trace, census) = build_trace(&pk_encode, device_pk_start, issuer_message_len)?;
        Ok((
            Self {
                issuer_message_len,
                trace: Some(trace),
                range_uses: Some(census.range_uses.clone()),
                issuer_handle,
                range_handle,
                rho_handle,
                t1_handle,
                start_handle,
                relations: None,
                claim: None,
                component: None,
                blinder_component: None,
            },
            census,
        ))
    }

    pub(crate) fn verifier(
        issuer_message_len: usize,
        issuer_handle: SharedFieldRelation,
        range_handle: SharedRangeRelation,
        rho_handle: SharedRhoCellRelation,
        t1_handle: SharedT1CellRelation,
        start_handle: SharedMdocDevicePkStartRelation,
        claim: MdocPrivateDeviceKeyInteractionClaim,
    ) -> Result<Self, MdocPrivateDeviceKeyBindError> {
        validate_public_shape(issuer_message_len)?;
        Ok(Self {
            issuer_message_len,
            trace: None,
            range_uses: None,
            issuer_handle,
            range_handle,
            rho_handle,
            t1_handle,
            start_handle,
            relations: None,
            claim: Some(claim),
            component: None,
            blinder_component: None,
        })
    }

    pub(crate) fn range_uses(&self) -> &RcUses {
        self.range_uses
            .as_ref()
            .expect("only the device-key binder prover has range multiplicities")
    }

    pub(crate) fn interaction_claim(&self) -> &MdocPrivateDeviceKeyInteractionClaim {
        self.claim
            .as_ref()
            .expect("device-key interaction claim is available after proving")
    }

    fn relations(&self) -> &MdocPrivateDeviceKeyRelations {
        self.relations
            .as_ref()
            .expect("device-key relations have been drawn")
    }
}

impl Air for MdocPrivateDeviceKeyBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(DEVICE_KEY_BIND_DOMAIN);
        channel.mix_u64(DEVICE_KEY_BIND_VERSION);
        channel.mix_u64(ML_DSA_44.transcript_tag());
        channel.mix_u64(self.issuer_message_len as u64);
        channel.mix_u64(DEVICE_PK_BYTES as u64);
        channel.mix_u64(MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE as u64);
        channel.mix_u64(MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS as u64);
        channel.mix_u64(PREPROCESSED_COLS as u64);
        channel.mix_u64(TRACE_COLS as u64);
        channel.mix_u64((MAIN_INTERACTION_COLS + BLINDER_INTERACTION_COLS) as u64);
        channel.mix_u64(HOSTED_MSG_FIELD_ID as u64);
        channel.mix_u64(HOSTED_DEVICE_PK_FIELD_ID as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        assert!(
            !self.t1_handle.is_set(),
            "the device-key binder requires a fresh T1Cell relation handle"
        );
        let t1 = T1CellRelation::draw(channel);
        self.t1_handle.set(t1.clone());
        self.relations = Some(MdocPrivateDeviceKeyRelations {
            issuer: self.issuer_handle.get(),
            range: self.range_handle.get(),
            rho: self.rho_handle.get(),
            t1,
            start: self.start_handle.get(),
            blinder: ClaimedSumBlinderRelation::draw(channel),
        });
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE; PREPROCESSED_COLS],
            trace: vec![MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE; TRACE_COLS],
            interaction: vec![
                MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE;
                MAIN_INTERACTION_COLS + BLINDER_INTERACTION_COLS
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns())
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let relations = self.relations().clone();
        self.component = Some(FrameworkComponent::new(
            allocator,
            MdocPrivateDeviceKeyEval {
                relations: relations.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE,
                relation: relations.blinder,
                v: claim.blinder_v,
                m: claim.blinder_m,
            },
            claim.blinder_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("device-key binder component is built"),
            self.blinder_component
                .as_ref()
                .expect("device-key binder blinder component is built"),
        ]
    }
}

impl AirProver for MdocPrivateDeviceKeyBind {
    fn max_log_size(&self) -> u32 {
        MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(preprocessed_columns());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_private_device_key_bind::MdocPrivateDeviceKeyBind",
            &preprocessed_ids(),
            &preprocessed_columns(),
        )
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(
            self.trace
                .as_ref()
                .expect("device-key binder prover has a private key")
                .evals(),
        );
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let (trace, claimed_sum) = interaction_trace(
            self.trace
                .as_ref()
                .expect("device-key binder prover has a private key"),
            self.relations(),
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (counterpart, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE,
            &self.relations().blinder,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(counterpart);
        self.claim = Some(MdocPrivateDeviceKeyInteractionClaim {
            claimed_sum,
            blinder_v,
            blinder_m,
            blinder_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("device-key binder component is built"),
            self.blinder_component
                .as_ref()
                .expect("device-key binder blinder component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    fn test_pk(seed: u8) -> Vec<u8> {
        (0..DEVICE_PK_BYTES)
            .map(|index| seed.wrapping_add((index * 73) as u8))
            .collect()
    }

    fn logical_value(column: &ColEval, row: usize) -> M31 {
        use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
        use stwo::prover::backend::Column as _;

        let index = bit_reverse_index(
            coset_index_to_circle_domain_index(row, MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE),
            MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE,
        );
        column.values.at(index)
    }

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn for_row(trace: &MdocPrivateDeviceKeyTrace, row: usize) -> Self {
            let previous = if row == 0 {
                MDOC_PRIVATE_DEVICE_KEY_ROWS - 1
            } else {
                row - 1
            };
            let mut eval = Self::default();
            for column in preprocessed_columns() {
                eval.preprocessed
                    .push_back(vec![logical_value(&column, row)]);
            }
            for (column, values) in trace.columns.iter().enumerate() {
                if column == COL_DEVICE_PK_START {
                    eval.original.push_back(vec![values[row], values[previous]]);
                } else {
                    eval.original.push_back(vec![values[row]]);
                }
            }
            eval
        }

        fn has_nonzero_constraint(&self) -> bool {
            self.constraints
                .iter()
                .any(|value| *value != QM31::from(m31(0)))
        }
    }

    impl EvalAtRow for RowEval {
        type F = M31;
        type EF = QM31;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            _offsets: [isize; N],
        ) -> [Self::F; N] {
            let queue = match interaction {
                PREPROCESSED_TRACE_IDX => &mut self.preprocessed,
                ORIGINAL_TRACE_IDX => &mut self.original,
                other => panic!("unexpected interaction index {other}"),
            };
            let values = queue.pop_front().expect("test mask exists");
            assert_eq!(values.len(), N);
            std::array::from_fn(|index| values[index])
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.constraints.push(QM31::from(constraint));
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            QM31::from_m31_array(values)
        }

        fn add_to_relation<R: Relation<Self::F, Self::EF>>(
            &mut self,
            _entry: RelationEntry<'_, Self::F, Self::EF, R>,
        ) {
        }

        fn write_logup_frac_typed(
            &mut self,
            _numerator: Multiplicity<Self::F, Self::EF>,
            _denominator: Self::EF,
        ) {
        }

        fn finalize_logup_in_pairs(&mut self) {}
    }

    fn dummy_eval() -> MdocPrivateDeviceKeyEval {
        MdocPrivateDeviceKeyEval {
            relations: MdocPrivateDeviceKeyRelations {
                issuer: FieldBytesRelation::dummy(),
                range: RangeRelation::dummy(),
                rho: RhoCellRelation::dummy(),
                t1: T1CellRelation::dummy(),
                start: MdocDevicePkStartRelation::dummy(),
                blinder: ClaimedSumBlinderRelation::dummy(),
            },
            blinder_v: QM31::from(m31(17)),
            blinder_m: QM31::from(m31(19)),
        }
    }

    fn interaction_claim_for(
        trace: &MdocPrivateDeviceKeyTrace,
        relations: &MdocPrivateDeviceKeyRelations,
    ) -> SecureField {
        interaction_trace(trace, relations, QM31::from(m31(17)), QM31::from(m31(19))).1
    }

    #[test]
    fn packing_matches_fips_decoder_for_every_t1_coefficient() {
        let pk = test_pk(11);
        let decoded = stwo_mldsa::reference::encoding::pk_decode(&pk).unwrap();
        for poly in 0..DEVICE_K {
            for group in 0..64 {
                let start = 32 + (poly * 64 + group) * T1_GROUP_BYTES;
                let unpacked = unpack_group(&pk[start..start + T1_GROUP_BYTES]);
                let expected: [u32; T1_COEFFICIENTS_PER_GROUP] = decoded.t1[poly]
                    [group * T1_COEFFICIENTS_PER_GROUP..(group + 1) * T1_COEFFICIENTS_PER_GROUP]
                    .try_into()
                    .unwrap();
                assert_eq!(unpacked, expected);
            }
        }
    }

    #[test]
    fn compact_schedule_derives_row_roles_lanes_and_coefficient_keys() {
        assert_eq!(m31(COEFFICIENT_BASE_SCALE) * m31(5), m31(4));
        for row in schedule() {
            let active = m31(1);
            let t1 = m31(row.is_t1() as u32);
            assert_eq!(active - t1, m31(row.is_rho() as u32));
            assert_eq!(row.is_first(), row.byte_base == 0);
            for lane in 0..T1_GROUP_BYTES {
                assert_eq!(row.lane_active(lane), lane == 0 || row.is_t1());
            }
            let derived = m31(COEFFICIENT_BASE_SCALE)
                * (m31(row.byte_base as u32)
                    - m31(32) * t1
                    - m31(T1_BYTES_PER_POLYNOMIAL) * m31(row.poly as u32));
            if row.is_t1() {
                assert_eq!(derived, m31(row.coefficient_base() as u32));
            }
        }
    }

    #[test]
    fn fixed_geometry_and_range_census_are_exact() {
        let start = 100;
        let pk = test_pk(29);
        let (_, census) = build_trace(&pk, start, 4_096).unwrap();
        assert_eq!(PREPROCESSED_COLS, 5);
        assert_eq!(TRACE_COLS, 34);
        assert_eq!(MAIN_INTERACTION_COLS + BLINDER_INTERACTION_COLS, 52);
        assert_eq!(census.active_rows, 288);
        assert_eq!(census.blind_rows, 224);
        assert_eq!(census.normalized_uses, 1_312);
        assert_eq!(census.rho_uses, 32);
        assert_eq!(census.t1_uses, 1_024);
        assert_eq!(census.device_pk_start_uses, 1);
        assert_eq!(
            census
                .issuer_position_uses
                .iter()
                .map(|&count| count as usize)
                .sum::<usize>(),
            DEVICE_PK_BYTES
        );
        assert!(census.issuer_position_uses[..start]
            .iter()
            .all(|&count| count == 0));
        assert!(census.issuer_position_uses[start..start + DEVICE_PK_BYTES]
            .iter()
            .all(|&count| count == 1));
        assert_eq!(
            census.range_uses.rc8.iter().sum::<u32>(),
            (MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS + DEVICE_K * 64) as u32
        );
        assert_eq!(
            census.range_uses.rc9.iter().sum::<u32>(),
            (DEVICE_K * N) as u32
        );
        assert_eq!(census.range_uses.rc7.iter().sum::<u32>(), 0);
    }

    #[test]
    fn honest_rows_satisfy_local_constraints_and_fragment_mutation_rejects() {
        let (trace, _) = build_trace(&test_pk(7), 64, 4_096).unwrap();
        for row in 0..MDOC_PRIVATE_DEVICE_KEY_ROWS {
            let evaluated = dummy_eval().evaluate(RowEval::for_row(&trace, row));
            assert!(!evaluated.has_nonzero_constraint(), "honest row {row}");
        }

        let row = 32;
        let mut attacked = trace.clone();
        attacked.columns[COL_B1_BITS][row] = m31(1) - attacked.columns[COL_B1_BITS][row];
        assert!(
            dummy_eval()
                .evaluate(RowEval::for_row(&attacked, row))
                .has_nonzero_constraint(),
            "a packed-fragment bit cannot detach from its source byte"
        );
    }

    #[test]
    fn every_relation_seam_changes_the_device_key_claim() {
        let (trace, _) = build_trace(&test_pk(41), 96, 4_096).unwrap();
        let mut channel = Blake2sChannel::default();
        let relations = MdocPrivateDeviceKeyRelations {
            issuer: FieldBytesRelation::draw(&mut channel),
            range: RangeRelation::draw(&mut channel),
            rho: RhoCellRelation::draw(&mut channel),
            t1: T1CellRelation::draw(&mut channel),
            start: MdocDevicePkStartRelation::draw(&mut channel),
            blinder: ClaimedSumBlinderRelation::draw(&mut channel),
        };
        let honest = interaction_claim_for(&trace, &relations);

        let assert_changes = |name: &str, attacked: MdocPrivateDeviceKeyTrace| {
            assert_ne!(
                interaction_claim_for(&attacked, &relations),
                honest,
                "{name}"
            );
        };

        let mut rho = trace.clone();
        rho.columns[COL_BYTE_START][3] += m31(1);
        assert_changes("rho byte", rho);

        let mut start = trace.clone();
        for row in 0..MDOC_PRIVATE_DEVICE_KEY_ACTIVE_ROWS {
            start.columns[COL_DEVICE_PK_START][row] += m31(1);
        }
        assert_changes("device public-key start", start);

        let mut packed = trace.clone();
        let row = 32;
        packed.columns[COL_BYTE_START + 1][row] =
            m31(packed.columns[COL_BYTE_START + 1][row].0 ^ 1);
        packed.columns[COL_B1_BITS][row] = m31(packed.columns[COL_B1_BITS][row].0 ^ 1);
        assert_changes("self-consistent alternate packed fragment", packed);

        let mut high = trace.clone();
        high.columns[COL_T1_HI_START][row] = m31(1) - high.columns[COL_T1_HI_START][row];
        assert_changes("t1 high bit", high);

        let mut tail = trace.clone();
        tail.columns[COL_BYTE_START + 4][row] += m31(1);
        assert_changes("t1 packed tail byte", tail);
    }

    #[test]
    fn key_and_start_are_absent_from_tree_zero_and_public_mix() {
        let issuer_len = 4_096;
        let (first_trace, _) = build_trace(&test_pk(1), 10, issuer_len).unwrap();
        let (second_trace, _) = build_trace(&test_pk(2), 20, issuer_len).unwrap();
        assert_ne!(first_trace.columns, second_trace.columns);
        assert_eq!(preprocessed_ids(), preprocessed_ids());

        let handles = || {
            (
                SharedFieldRelation::new(),
                SharedRangeRelation::new(),
                SharedRhoCellRelation::new(),
                SharedT1CellRelation::new(),
                SharedMdocDevicePkStartRelation::new(),
            )
        };
        let (issuer, range, rho, t1, start) = handles();
        let (first, _) = MdocPrivateDeviceKeyBind::prover(
            test_pk(1),
            10,
            issuer_len,
            issuer,
            range,
            rho,
            t1,
            start,
        )
        .unwrap();
        let (issuer, range, rho, t1, start) = handles();
        let (second, _) = MdocPrivateDeviceKeyBind::prover(
            test_pk(2),
            20,
            issuer_len,
            issuer,
            range,
            rho,
            t1,
            start,
        )
        .unwrap();
        let mut first_channel = Blake2sChannel::default();
        let mut second_channel = Blake2sChannel::default();
        first.mix_public(&mut first_channel);
        second.mix_public(&mut second_channel);
        assert_eq!(
            FieldBytesRelation::draw(&mut first_channel),
            FieldBytesRelation::draw(&mut second_channel)
        );
    }

    #[test]
    fn device_key_binder_owns_and_publishes_the_t1_challenge_after_shared_inputs() {
        let issuer = SharedFieldRelation::new();
        let range = SharedRangeRelation::new();
        let rho = SharedRhoCellRelation::new();
        let t1 = SharedT1CellRelation::new();
        let start = SharedMdocDevicePkStartRelation::new();
        let mut channel = Blake2sChannel::default();
        issuer.set(FieldBytesRelation::draw(&mut channel));
        range.set(RangeRelation::draw(&mut channel));
        rho.set(RhoCellRelation::draw(&mut channel));
        start.set(MdocDevicePkStartRelation::draw(&mut channel));

        let (mut binder, _) = MdocPrivateDeviceKeyBind::prover(
            test_pk(9),
            64,
            4_096,
            issuer,
            range,
            rho,
            t1.clone(),
            start,
        )
        .unwrap();
        assert!(!t1.is_set());
        assert_eq!(
            binder.range_uses().rc9.iter().sum::<u32>(),
            (DEVICE_K * N) as u32
        );
        binder.draw_relations(&mut channel);
        assert!(t1.is_set());

        let issuer = SharedFieldRelation::new();
        let range = SharedRangeRelation::new();
        let rho = SharedRhoCellRelation::new();
        let t1 = SharedT1CellRelation::new();
        let start = SharedMdocDevicePkStartRelation::new();
        issuer.set(FieldBytesRelation::draw(&mut channel));
        range.set(RangeRelation::draw(&mut channel));
        rho.set(RhoCellRelation::draw(&mut channel));
        start.set(MdocDevicePkStartRelation::draw(&mut channel));
        let claim = MdocPrivateDeviceKeyInteractionClaim::default();
        let claim: MdocPrivateDeviceKeyInteractionClaim =
            bincode::deserialize(&bincode::serialize(&claim).unwrap()).unwrap();
        let mut verifier =
            MdocPrivateDeviceKeyBind::verifier(4_096, issuer, range, rho, t1.clone(), start, claim)
                .unwrap();
        assert_eq!(
            verifier.layout().interaction,
            vec![
                MDOC_PRIVATE_DEVICE_KEY_LOG_SIZE;
                MAIN_INTERACTION_COLS + BLINDER_INTERACTION_COLS
            ]
        );
        verifier.draw_relations(&mut channel);
        assert!(t1.is_set());
    }

    const TEST_COUNTER_DOMAIN: u64 = 0x5539_434f_554e_5445;
    const TEST_SOURCE: usize = 0;
    const TEST_NORMALIZED: usize = 1;
    const TEST_RANGE: usize = 2;
    const TEST_RHO: usize = 3;
    const TEST_T1: usize = 4;
    const TEST_START: usize = 5;
    const TEST_SELECTOR_COUNT: usize = 6;
    const TEST_VALUE_COUNT: usize = 4;
    const TEST_COUNTER_COLS: usize = TEST_SELECTOR_COUNT + TEST_VALUE_COUNT;

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct TestCounterRow {
        selectors: [u32; TEST_SELECTOR_COUNT],
        values: [u32; TEST_VALUE_COUNT],
    }

    impl TestCounterRow {
        fn new(selector: usize, values: [u32; TEST_VALUE_COUNT]) -> Self {
            let mut selectors = [0; TEST_SELECTOR_COUNT];
            selectors[selector] = 1;
            Self { selectors, values }
        }

        fn selected(&self, selector: usize) -> bool {
            self.selectors[selector] == 1
        }
    }

    fn test_counter_log_size(rows: usize) -> u32 {
        rows.next_power_of_two().ilog2().max(LOG_N_LANES)
    }

    fn test_counter_columns(rows: &[TestCounterRow], log_size: u32) -> Vec<Vec<M31>> {
        let mut columns = vec![vec![m31(0); 1usize << log_size]; TEST_COUNTER_COLS];
        for (row_index, row) in rows.iter().enumerate() {
            for (column, value) in row.selectors.into_iter().chain(row.values).enumerate() {
                columns[column][row_index] = m31(value);
            }
        }
        columns
    }

    fn test_counter_evals(rows: &[TestCounterRow], log_size: u32) -> Vec<ColEval> {
        test_counter_columns(rows, log_size)
            .into_iter()
            .map(|column| col_eval(log_size, column))
            .collect()
    }

    #[derive(Clone)]
    struct TestCounterEval {
        log_size: u32,
        issuer: FieldBytesRelation,
        range: RangeRelation,
        rho: RhoCellRelation,
        t1: T1CellRelation,
        start: MdocDevicePkStartRelation,
    }

    impl FrameworkEval for TestCounterEval {
        fn log_size(&self) -> u32 {
            self.log_size
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size + 2
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let selectors: [E::F; TEST_SELECTOR_COUNT] =
                std::array::from_fn(|_| eval.next_trace_mask());
            let values: [E::F; TEST_VALUE_COUNT] = std::array::from_fn(|_| eval.next_trace_mask());
            let one = constant::<E>(1);
            let active = selectors
                .iter()
                .cloned()
                .fold(constant::<E>(0), |sum, selector| sum + selector);
            for selector in &selectors {
                add_boolean(&mut eval, selector.clone(), &one);
            }
            add_boolean(&mut eval, active, &one);

            eval.add_to_relation(RelationEntry::new(
                &self.issuer,
                E::EF::from(selectors[TEST_NORMALIZED].clone() - selectors[TEST_SOURCE].clone()),
                &[values[0].clone(), values[1].clone(), values[2].clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.range,
                -E::EF::from(selectors[TEST_RANGE].clone()),
                &[values[0].clone(), values[1].clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.rho,
                E::EF::from(selectors[TEST_RHO].clone()),
                &[values[0].clone(), values[1].clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.t1,
                E::EF::from(selectors[TEST_T1].clone()),
                &values,
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.start,
                -E::EF::from(selectors[TEST_START].clone()),
                &[values[0].clone()],
            ));
            eval.finalize_logup_in_pairs();
            eval
        }
    }

    fn test_counter_interaction(
        rows: &[TestCounterRow],
        log_size: u32,
        issuer: &FieldBytesRelation,
        range: &RangeRelation,
        rho: &RhoCellRelation,
        t1: &T1CellRelation,
        start: &MdocDevicePkStartRelation,
    ) -> (Vec<ColEval>, SecureField) {
        let trace = test_counter_evals(rows, log_size);
        let vec_rows = 1usize << (log_size - LOG_N_LANES);
        let sites = [
            (0..vec_rows)
                .map(|row| {
                    (
                        PackedQM31::from(trace[TEST_NORMALIZED].data[row])
                            - PackedQM31::from(trace[TEST_SOURCE].data[row]),
                        issuer.combine(&[
                            trace[TEST_SELECTOR_COUNT].data[row],
                            trace[TEST_SELECTOR_COUNT + 1].data[row],
                            trace[TEST_SELECTOR_COUNT + 2].data[row],
                        ]),
                    )
                })
                .collect::<Vec<_>>(),
            (0..vec_rows)
                .map(|row| {
                    (
                        -PackedQM31::from(trace[TEST_RANGE].data[row]),
                        range.combine(&[
                            trace[TEST_SELECTOR_COUNT].data[row],
                            trace[TEST_SELECTOR_COUNT + 1].data[row],
                        ]),
                    )
                })
                .collect(),
            (0..vec_rows)
                .map(|row| {
                    (
                        PackedQM31::from(trace[TEST_RHO].data[row]),
                        rho.combine(&[
                            trace[TEST_SELECTOR_COUNT].data[row],
                            trace[TEST_SELECTOR_COUNT + 1].data[row],
                        ]),
                    )
                })
                .collect(),
            (0..vec_rows)
                .map(|row| {
                    (
                        PackedQM31::from(trace[TEST_T1].data[row]),
                        t1.combine(&[
                            trace[TEST_SELECTOR_COUNT].data[row],
                            trace[TEST_SELECTOR_COUNT + 1].data[row],
                            trace[TEST_SELECTOR_COUNT + 2].data[row],
                            trace[TEST_SELECTOR_COUNT + 3].data[row],
                        ]),
                    )
                })
                .collect(),
            (0..vec_rows)
                .map(|row| {
                    (
                        -PackedQM31::from(trace[TEST_START].data[row]),
                        start.combine(&[trace[TEST_SELECTOR_COUNT].data[row]]),
                    )
                })
                .collect(),
        ];

        let mut logup = LogupTraceGenerator::new(log_size);
        for pair in sites.chunks(2) {
            if let [left, right] = pair {
                logup.col_from_iter((0..vec_rows).map(|row| {
                    let (left_num, left_den) = left[row];
                    let (right_num, right_den) = right[row];
                    (
                        left_num * right_den + right_num * left_den,
                        left_den * right_den,
                    )
                }));
            } else {
                logup.col_from_iter((0..vec_rows).map(|row| pair[0][row]));
            }
        }
        logup.finalize_last()
    }

    struct TestRelationCounter {
        rows: Vec<TestCounterRow>,
        log_size: u32,
        issuer_handle: SharedFieldRelation,
        range_handle: SharedRangeRelation,
        rho_handle: SharedRhoCellRelation,
        t1_handle: SharedT1CellRelation,
        start_handle: SharedMdocDevicePkStartRelation,
        component: Option<FrameworkComponent<TestCounterEval>>,
    }

    impl TestRelationCounter {
        fn new(
            rows: Vec<TestCounterRow>,
            issuer_handle: SharedFieldRelation,
            range_handle: SharedRangeRelation,
            rho_handle: SharedRhoCellRelation,
            t1_handle: SharedT1CellRelation,
            start_handle: SharedMdocDevicePkStartRelation,
        ) -> Self {
            Self {
                log_size: test_counter_log_size(rows.len()),
                rows,
                issuer_handle,
                range_handle,
                rho_handle,
                t1_handle,
                start_handle,
                component: None,
            }
        }

        fn interaction(&self) -> (Vec<ColEval>, SecureField) {
            test_counter_interaction(
                &self.rows,
                self.log_size,
                &self.issuer_handle.get(),
                &self.range_handle.get(),
                &self.rho_handle.get(),
                &self.t1_handle.get(),
                &self.start_handle.get(),
            )
        }
    }

    impl Air for TestRelationCounter {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_u64(TEST_COUNTER_DOMAIN);
            channel.mix_u64(self.log_size as u64);
            channel.mix_u64(self.rows.len() as u64);
        }

        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            assert!(!self.issuer_handle.is_set());
            assert!(!self.range_handle.is_set());
            assert!(!self.rho_handle.is_set());
            assert!(!self.t1_handle.is_set());
            assert!(!self.start_handle.is_set());
            self.issuer_handle.set(FieldBytesRelation::draw(channel));
            self.range_handle.set(RangeRelation::draw(channel));
            self.rho_handle.set(RhoCellRelation::draw(channel));
            self.start_handle
                .set(MdocDevicePkStartRelation::draw(channel));
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: Vec::new(),
                trace: vec![self.log_size; TEST_COUNTER_COLS],
                interaction: vec![self.log_size; 3 * SECURE_EXTENSION_DEGREE],
            }
        }

        fn claimed_sums(&self) -> Vec<QM31> {
            vec![self.interaction().1]
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            Vec::new()
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                TestCounterEval {
                    log_size: self.log_size,
                    issuer: self.issuer_handle.get(),
                    range: self.range_handle.get(),
                    rho: self.rho_handle.get(),
                    t1: self.t1_handle.get(),
                    start: self.start_handle.get(),
                },
                self.interaction().1,
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self
                .component
                .as_ref()
                .expect("device-key binder test counter component is built")]
        }
    }

    impl AirProver for TestRelationCounter {
        fn max_log_size(&self) -> u32 {
            self.log_size
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size + 2
        }

        fn store_polynomial_coefficients(&self) -> bool {
            true
        }

        fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

        fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
            Vec::new()
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(test_counter_evals(&self.rows, self.log_size));
        }

        fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(self.interaction().0);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self
                .component
                .as_ref()
                .expect("device-key binder test counter component is built")]
        }
    }

    fn counterpart_rows(
        authenticated_pk: &[u8],
        normalized_pk: &[u8],
        device_pk_start: usize,
    ) -> Vec<TestCounterRow> {
        assert_eq!(authenticated_pk.len(), DEVICE_PK_BYTES);
        assert_eq!(normalized_pk.len(), DEVICE_PK_BYTES);
        let mut rows = Vec::new();
        for (index, &byte) in authenticated_pk.iter().enumerate() {
            rows.push(TestCounterRow::new(
                TEST_SOURCE,
                [
                    HOSTED_MSG_FIELD_ID,
                    (device_pk_start + index) as u32,
                    u32::from(byte),
                    0,
                ],
            ));
        }
        for (index, &byte) in normalized_pk.iter().enumerate() {
            rows.push(TestCounterRow::new(
                TEST_NORMALIZED,
                [HOSTED_DEVICE_PK_FIELD_ID, index as u32, u32::from(byte), 0],
            ));
        }
        for row in schedule() {
            rows.push(TestCounterRow::new(
                TEST_RANGE,
                [
                    u32::from(normalized_pk[row.byte_base]),
                    RcKind::Rc8.bound_id(),
                    0,
                    0,
                ],
            ));
            if row.is_rho() {
                rows.push(TestCounterRow::new(
                    TEST_RHO,
                    [
                        row.byte_base as u32,
                        u32::from(normalized_pk[row.byte_base]),
                        0,
                        0,
                    ],
                ));
            } else {
                let group = &normalized_pk[row.byte_base..row.byte_base + T1_GROUP_BYTES];
                rows.push(TestCounterRow::new(
                    TEST_RANGE,
                    [u32::from(group[4]), RcKind::Rc8.bound_id(), 0, 0],
                ));
                for (lane, coefficient) in unpack_group(group).into_iter().enumerate() {
                    let lo = coefficient & 0x1ff;
                    let hi = coefficient >> 9;
                    rows.push(TestCounterRow::new(
                        TEST_RANGE,
                        [lo, RcKind::Rc9.bound_id(), 0, 0],
                    ));
                    rows.push(TestCounterRow::new(
                        TEST_T1,
                        [
                            row.poly as u32,
                            (row.coefficient_base() + lane) as u32,
                            lo,
                            hi,
                        ],
                    ));
                }
            }
        }
        rows.push(TestCounterRow::new(
            TEST_START,
            [device_pk_start as u32, 0, 0, 0],
        ));
        rows.push(TestCounterRow::default());
        rows
    }

    struct TestComposedDeviceKeyProof {
        stark: stwo::core::proof::StarkProof<air_core::Hasher>,
        device_key_claim: MdocPrivateDeviceKeyInteractionClaim,
        rows: Vec<TestCounterRow>,
        issuer_message_len: usize,
    }

    fn prove_composed_device_key(
        authenticated_pk: &[u8],
        normalized_pk: Vec<u8>,
    ) -> TestComposedDeviceKeyProof {
        let issuer_message_len = 4_096;
        let device_pk_start = 64;
        let issuer = SharedFieldRelation::new();
        let range = SharedRangeRelation::new();
        let rho = SharedRhoCellRelation::new();
        let t1 = SharedT1CellRelation::new();
        let start = SharedMdocDevicePkStartRelation::new();
        let rows = counterpart_rows(authenticated_pk, &normalized_pk, device_pk_start);
        let mut counter = TestRelationCounter::new(
            rows.clone(),
            issuer.clone(),
            range.clone(),
            rho.clone(),
            t1.clone(),
            start.clone(),
        );
        let (mut device_key_bind, _) = MdocPrivateDeviceKeyBind::prover(
            normalized_pk,
            device_pk_start,
            issuer_message_len,
            issuer,
            range,
            rho,
            t1,
            start,
        )
        .unwrap();
        let stark = air_core::prove(
            &mut [&mut counter, &mut device_key_bind],
            crate::mdoc::mdoc_ts13_pcs_config(),
        )
        .expect("locally constrained device-key composition must produce a proof");
        TestComposedDeviceKeyProof {
            stark,
            device_key_claim: device_key_bind.interaction_claim().clone(),
            rows,
            issuer_message_len,
        }
    }

    fn verify_composed_device_key(
        fixture: &TestComposedDeviceKeyProof,
        rows: Vec<TestCounterRow>,
    ) -> Result<(), air_core::VerifyError> {
        let issuer = SharedFieldRelation::new();
        let range = SharedRangeRelation::new();
        let rho = SharedRhoCellRelation::new();
        let t1 = SharedT1CellRelation::new();
        let start = SharedMdocDevicePkStartRelation::new();
        let mut counter = TestRelationCounter::new(
            rows,
            issuer.clone(),
            range.clone(),
            rho.clone(),
            t1.clone(),
            start.clone(),
        );
        let mut device_key_bind = MdocPrivateDeviceKeyBind::verifier(
            fixture.issuer_message_len,
            issuer,
            range,
            rho,
            t1,
            start,
            fixture.device_key_claim.clone(),
        )
        .unwrap();
        let expected_root = air_core::compute_canonical_preprocessed_root(
            &mut [&mut counter, &mut device_key_bind],
            fixture.stark.config,
        )
        .expect("canonical device-key binder preprocessing");
        air_core::verify_with_expected_preprocessed_root(
            &mut [&mut counter, &mut device_key_bind],
            &fixture.stark,
            Some(expected_root),
        )
    }

    fn assert_logup_rejects(
        fixture: &TestComposedDeviceKeyProof,
        rows: Vec<TestCounterRow>,
        name: &str,
    ) {
        match verify_composed_device_key(fixture, rows)
            .expect_err("mutated device-key relation counterpart must not verify")
        {
            air_core::VerifyError::Stark(
                stwo::core::verifier::VerificationError::InvalidStructure(reason),
            ) => assert_eq!(reason, "LogUp claimed sums do not cancel", "{name}"),
            other => panic!("{name}: expected global LogUp rejection, got {other:?}"),
        }
    }

    #[test]
    fn composed_stark_rejects_every_device_key_tuple_and_multiplicity_attack() {
        let pk = test_pk(53);
        let fixture = prove_composed_device_key(&pk, pk.clone());
        verify_composed_device_key(&fixture, fixture.rows.clone())
            .expect("honest device-key relation composition must verify");
        assert!(
            fixture
                .rows
                .last()
                .is_some_and(|row| *row == TestCounterRow::default()),
            "the final fixed-shape counter row is reserved for extra-use attacks"
        );

        for (name, selector, value_index) in [
            ("authenticated field id", TEST_SOURCE, 0),
            ("authenticated absolute byte position", TEST_SOURCE, 1),
            ("normalized field id", TEST_NORMALIZED, 0),
            ("normalized relative byte position", TEST_NORMALIZED, 1),
            ("range value", TEST_RANGE, 0),
            ("range bound id", TEST_RANGE, 1),
            ("RhoCell byte index", TEST_RHO, 0),
            ("RhoCell byte", TEST_RHO, 1),
            ("T1Cell polynomial", TEST_T1, 0),
            ("T1Cell coefficient index", TEST_T1, 1),
            ("T1Cell lo9", TEST_T1, 2),
            ("T1Cell hi1", TEST_T1, 3),
            ("device-key start", TEST_START, 0),
        ] {
            let mut rows = fixture.rows.clone();
            rows.iter_mut()
                .find(|row| row.selected(selector))
                .unwrap()
                .values[value_index] ^= 1;
            assert_logup_rejects(&fixture, rows, name);
        }

        for (name, selector) in [
            ("authenticated source", TEST_SOURCE),
            ("normalized byte", TEST_NORMALIZED),
            ("range lookup", TEST_RANGE),
            ("RhoCell", TEST_RHO),
            ("T1Cell", TEST_T1),
            ("device-key start", TEST_START),
        ] {
            let source = fixture
                .rows
                .iter()
                .copied()
                .find(|row| row.selected(selector))
                .unwrap();

            let mut missing = fixture.rows.clone();
            missing
                .iter_mut()
                .find(|row| row.selected(selector))
                .unwrap()
                .selectors[selector] = 0;
            assert_logup_rejects(&fixture, missing, &format!("missing {name} counterpart"));

            let mut extra = fixture.rows.clone();
            *extra.last_mut().unwrap() = source;
            assert_logup_rejects(&fixture, extra, &format!("extra {name} counterpart"));
        }
    }

    #[test]
    fn composed_stark_rejects_self_consistent_alternate_byte_decomposition() {
        let authenticated_pk = test_pk(71);
        let mut alternate_pk = authenticated_pk.clone();
        let byte_index = 33;
        alternate_pk[byte_index] ^= 1;
        let group_start = 32;
        assert_ne!(
            unpack_group(&authenticated_pk[group_start..group_start + T1_GROUP_BYTES]),
            unpack_group(&alternate_pk[group_start..group_start + T1_GROUP_BYTES]),
            "the alternate byte must induce a different canonical t1 fragment"
        );

        let forged = prove_composed_device_key(&authenticated_pk, alternate_pk);
        assert_logup_rejects(
            &forged,
            forged.rows.clone(),
            "self-consistent alternate normalized byte/t1 decomposition",
        );
    }

    #[test]
    fn invalid_lengths_and_window_fail_before_trace_allocation() {
        assert!(matches!(
            build_trace(&test_pk(1)[..DEVICE_PK_BYTES - 1], 0, 4_096),
            Err(MdocPrivateDeviceKeyBindError::PublicKeyLength { .. })
        ));
        assert!(matches!(
            build_trace(&test_pk(1), 4_096 - DEVICE_PK_BYTES + 1, 4_096),
            Err(MdocPrivateDeviceKeyBindError::DeviceKeyWindowOutOfBounds { .. })
        ));
        assert!(matches!(
            build_trace(&test_pk(1), 0, 0),
            Err(MdocPrivateDeviceKeyBindError::IssuerMessageLengthOutOfRange { .. })
        ));
    }
}
