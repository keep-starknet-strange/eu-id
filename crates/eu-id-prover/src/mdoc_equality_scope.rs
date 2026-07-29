//! Sound semantic binding for the single-item TS13 equality profile.
//!
//! The outer parser consumes the complete SHA-padded
//! `IssuerSignedItemBytes`. This component consumes every parsed outer byte,
//! reindexes the tag-24 byte-string content into a raw inner stream, and then
//! consumes every parsed inner byte. The public schedule fixes the complete
//! profile-v2 item grammar except for the issuer's random salt bytes:
//!
//! `{"random": bstr, "digestID": uint, "elementValue": <public CBOR>,
//!   "elementIdentifier": <public text>}`.
//!
//! Consequently offsets, anchors, and host-selected byte windows are not part
//! of the verifier statement. The digest ID is intentionally public for this
//! linkable TS13 demo profile.

use std::fmt;

use air_core::claim_mask::{
    add_claim_mask_fraction, ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS,
};
use air_core::relations::{FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use crate::mdoc_cbor_stream::{
    parser_log_size, MdocCborInputMode, MdocCborStreamError, MdocCborWitness, MdocCborWitnessRow,
    ParsedCborByteRelation, SharedParsedCborByteRelation,
};

pub(crate) const MDOC_EQUALITY_OUTER_STREAM_ID: u32 = 0x4d49_0000;
pub(crate) const MDOC_EQUALITY_INNER_STREAM_ID: u32 = 0x4d49_0001;

const MIN_LOG_SIZE: u32 = 9;
const MAX_LOG_SIZE: u32 = 10;
const BLIND_ROWS: usize = 256;
const MAX_RANDOM_BYTES: usize = 128;
const MAX_PUBLIC_IDENTIFIER_BYTES: usize = 64;
const MAX_PUBLIC_VALUE_BYTES: usize = 32;
const TRACE_COLS: usize = 13;
const PREPROCESSED_COLS: usize = 8;

type Column = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type EqualityScopeComponent = FrameworkComponent<MdocEqualityScopeEval>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocEqualityScopeError {
    EmptyIdentifier,
    InvalidIdentifierUtf8,
    IdentifierTooLong(usize),
    InvalidPublicValue(MdocCborStreamError),
    PublicValueTooLong(usize),
    DigestIdOutOfRange(u32),
    InvalidPaddedLength(u16),
    WrongOuterShape,
    WrongInnerShape,
    RandomTooShort(usize),
    RandomTooLong(usize),
    TraceTooLarge(usize),
}

impl fmt::Display for MdocEqualityScopeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyIdentifier => write!(f, "TS13 elementIdentifier is empty"),
            Self::InvalidIdentifierUtf8 => write!(f, "TS13 elementIdentifier is not UTF-8"),
            Self::IdentifierTooLong(len) => {
                write!(f, "TS13 elementIdentifier is too long ({len} bytes)")
            }
            Self::InvalidPublicValue(error) => write!(f, "invalid TS13 equality value: {error}"),
            Self::PublicValueTooLong(len) => {
                write!(f, "TS13 equality value is too long ({len} bytes)")
            }
            Self::DigestIdOutOfRange(id) => {
                write!(f, "TS13 requested digest ID {id} exceeds the u16 profile")
            }
            Self::InvalidPaddedLength(len) => {
                write!(f, "invalid TS13 item SHA padded length {len}")
            }
            Self::WrongOuterShape => write!(f, "wrong TS13 IssuerSignedItemBytes wrapper"),
            Self::WrongInnerShape => write!(f, "wrong TS13 IssuerSignedItem map"),
            Self::RandomTooShort(len) => {
                write!(f, "TS13 IssuerSignedItem random is too short ({len} bytes)")
            }
            Self::RandomTooLong(len) => {
                write!(f, "TS13 IssuerSignedItem random is too long ({len} bytes)")
            }
            Self::TraceTooLarge(rows) => {
                write!(
                    f,
                    "TS13 equality semantic scope needs too many rows ({rows})"
                )
            }
        }
    }
}

impl std::error::Error for MdocEqualityScopeError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocEqualityScopeStatement {
    pub(crate) element_identifier: Vec<u8>,
    pub(crate) element_value: Vec<u8>,
    pub(crate) digest_id: u32,
    pub(crate) item_padded_len: u16,
}

impl MdocEqualityScopeStatement {
    fn validate(&self) -> Result<(), MdocEqualityScopeError> {
        if self.element_identifier.is_empty() {
            return Err(MdocEqualityScopeError::EmptyIdentifier);
        }
        if std::str::from_utf8(&self.element_identifier).is_err() {
            return Err(MdocEqualityScopeError::InvalidIdentifierUtf8);
        }
        if self.element_identifier.len() > MAX_PUBLIC_IDENTIFIER_BYTES {
            return Err(MdocEqualityScopeError::IdentifierTooLong(
                self.element_identifier.len(),
            ));
        }
        if self.element_value.len() > MAX_PUBLIC_VALUE_BYTES {
            return Err(MdocEqualityScopeError::PublicValueTooLong(
                self.element_value.len(),
            ));
        }
        MdocCborWitness::new(&self.element_value, MdocCborInputMode::Raw)
            .map_err(MdocEqualityScopeError::InvalidPublicValue)?;
        if self.digest_id > u32::from(u16::MAX) {
            return Err(MdocEqualityScopeError::DigestIdOutOfRange(self.digest_id));
        }
        if !matches!(self.item_padded_len, 64 | 128 | 192) {
            return Err(MdocEqualityScopeError::InvalidPaddedLength(
                self.item_padded_len,
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocEqualityScopeProofMetadata {
    pub(crate) random_len: u16,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocEqualityScopeInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

#[derive(Clone)]
pub(crate) struct MdocEqualityScopeHandles {
    pub(crate) outer_parsed: SharedParsedCborByteRelation,
    pub(crate) inner_parsed: SharedParsedCborByteRelation,
    pub(crate) inner_raw: SharedFieldRelation,
}

impl MdocEqualityScopeHandles {
    pub(crate) fn fresh() -> Self {
        Self {
            outer_parsed: SharedParsedCborByteRelation::new(),
            inner_parsed: SharedParsedCborByteRelation::new(),
            inner_raw: SharedFieldRelation::new(),
        }
    }
}

#[derive(Clone, Copy)]
enum Stream {
    Outer,
    Inner,
}

#[derive(Clone)]
struct ScheduledRow {
    stream: Stream,
    byte_index: u32,
    expected: Option<u8>,
    raw_index: Option<u32>,
}

#[derive(Clone)]
struct ScopeSchedule {
    rows: Vec<ScheduledRow>,
    outer_len: usize,
    inner_len: usize,
    log_size: u32,
}

fn cbor_head(major: u8, value: usize) -> Vec<u8> {
    let prefix = major << 5;
    match value {
        0..=23 => vec![prefix | value as u8],
        24..=0xff => vec![prefix | 24, value as u8],
        0x100..=0xffff => {
            let value = (value as u16).to_be_bytes();
            vec![prefix | 25, value[0], value[1]]
        }
        _ => panic!("TS13 bounded CBOR length fits u16"),
    }
}

fn cbor_text(value: &[u8]) -> Vec<u8> {
    let mut encoded = cbor_head(3, value.len());
    encoded.extend_from_slice(value);
    encoded
}

fn cbor_uint(value: u32) -> Vec<u8> {
    match value {
        0..=23 => vec![value as u8],
        24..=0xff => vec![0x18, value as u8],
        _ => {
            let bytes = (value as u16).to_be_bytes();
            vec![0x19, bytes[0], bytes[1]]
        }
    }
}

fn push_exact(target: &mut Vec<Option<u8>>, bytes: &[u8]) {
    target.extend(bytes.iter().copied().map(Some));
}

fn expected_inner(statement: &MdocEqualityScopeStatement, random_len: usize) -> Vec<Option<u8>> {
    let mut expected = Vec::new();
    expected.push(Some(0xa4));
    push_exact(&mut expected, &cbor_text(b"random"));
    push_exact(&mut expected, &cbor_head(2, random_len));
    expected.extend((0..random_len).map(|_| None));
    push_exact(&mut expected, &cbor_text(b"digestID"));
    push_exact(&mut expected, &cbor_uint(statement.digest_id));
    push_exact(&mut expected, &cbor_text(b"elementValue"));
    push_exact(&mut expected, &statement.element_value);
    push_exact(&mut expected, &cbor_text(b"elementIdentifier"));
    push_exact(&mut expected, &cbor_text(&statement.element_identifier));
    expected
}

fn sha_padded_len(message_len: usize) -> usize {
    (message_len + 9).div_ceil(64) * 64
}

fn scope_log_size(active_rows: usize) -> Result<u32, MdocEqualityScopeError> {
    let needed = active_rows
        .checked_add(BLIND_ROWS)
        .ok_or(MdocEqualityScopeError::TraceTooLarge(active_rows))?;
    let log_size = needed
        .next_power_of_two()
        .trailing_zeros()
        .max(MIN_LOG_SIZE);
    if log_size > MAX_LOG_SIZE {
        return Err(MdocEqualityScopeError::TraceTooLarge(active_rows));
    }
    Ok(log_size)
}

fn schedule(
    statement: &MdocEqualityScopeStatement,
    metadata: &MdocEqualityScopeProofMetadata,
) -> Result<ScopeSchedule, MdocEqualityScopeError> {
    statement.validate()?;
    let random_len = usize::from(metadata.random_len);
    if random_len < 16 {
        return Err(MdocEqualityScopeError::RandomTooShort(random_len));
    }
    if random_len > MAX_RANDOM_BYTES {
        return Err(MdocEqualityScopeError::RandomTooLong(random_len));
    }
    let inner = expected_inner(statement, random_len);
    let inner_len = inner.len();
    let mut outer_expected = Vec::new();
    push_exact(&mut outer_expected, &[0xd8, 0x18]);
    push_exact(&mut outer_expected, &cbor_head(2, inner_len));
    let content_start = outer_expected.len();
    outer_expected.extend((0..inner_len).map(|_| None));
    let outer_len = outer_expected.len();
    if sha_padded_len(outer_len) != usize::from(statement.item_padded_len) {
        return Err(MdocEqualityScopeError::InvalidPaddedLength(
            statement.item_padded_len,
        ));
    }

    let mut rows = Vec::with_capacity(outer_len + inner_len);
    rows.extend(
        outer_expected
            .into_iter()
            .enumerate()
            .map(|(index, expected)| ScheduledRow {
                stream: Stream::Outer,
                byte_index: index as u32,
                expected,
                raw_index: (index >= content_start).then(|| (index - content_start) as u32),
            }),
    );
    rows.extend(
        inner
            .into_iter()
            .enumerate()
            .map(|(index, expected)| ScheduledRow {
                stream: Stream::Inner,
                byte_index: index as u32,
                expected,
                raw_index: None,
            }),
    );
    let log_size = scope_log_size(rows.len())?;
    Ok(ScopeSchedule {
        rows,
        outer_len,
        inner_len,
        log_size,
    })
}

fn parse_canonical_bstr_head(
    bytes: &[u8],
    offset: usize,
) -> Result<(usize, usize), MdocEqualityScopeError> {
    let first = *bytes
        .get(offset)
        .ok_or(MdocEqualityScopeError::WrongInnerShape)?;
    if first >> 5 != 2 {
        return Err(MdocEqualityScopeError::WrongInnerShape);
    }
    match first & 0x1f {
        value @ 0..=23 => Ok((usize::from(value), 1)),
        24 => {
            let value = usize::from(
                *bytes
                    .get(offset + 1)
                    .ok_or(MdocEqualityScopeError::WrongInnerShape)?,
            );
            if value < 24 {
                return Err(MdocEqualityScopeError::WrongInnerShape);
            }
            Ok((value, 2))
        }
        25 => {
            let value = u16::from_be_bytes([
                *bytes
                    .get(offset + 1)
                    .ok_or(MdocEqualityScopeError::WrongInnerShape)?,
                *bytes
                    .get(offset + 2)
                    .ok_or(MdocEqualityScopeError::WrongInnerShape)?,
            ]);
            if value <= u16::from(u8::MAX) {
                return Err(MdocEqualityScopeError::WrongInnerShape);
            }
            Ok((usize::from(value), 3))
        }
        _ => Err(MdocEqualityScopeError::WrongInnerShape),
    }
}

fn extract_inner(outer: &[u8]) -> Result<&[u8], MdocEqualityScopeError> {
    if !outer.starts_with(&[0xd8, 0x18]) {
        return Err(MdocEqualityScopeError::WrongOuterShape);
    }
    let (len, head_len) =
        parse_canonical_bstr_head(outer, 2).map_err(|_| MdocEqualityScopeError::WrongOuterShape)?;
    let start = 2 + head_len;
    let end = start
        .checked_add(len)
        .ok_or(MdocEqualityScopeError::WrongOuterShape)?;
    if end != outer.len() {
        return Err(MdocEqualityScopeError::WrongOuterShape);
    }
    Ok(&outer[start..end])
}

fn infer_random_len(inner: &[u8]) -> Result<usize, MdocEqualityScopeError> {
    let mut prefix = vec![0xa4];
    prefix.extend_from_slice(&cbor_text(b"random"));
    if !inner.starts_with(&prefix) {
        return Err(MdocEqualityScopeError::WrongInnerShape);
    }
    parse_canonical_bstr_head(inner, prefix.len()).map(|(len, _)| len)
}

fn rows_match_expected(bytes: &[u8], expected: &[Option<u8>]) -> bool {
    bytes.len() == expected.len()
        && bytes
            .iter()
            .zip(expected)
            .all(|(actual, expected)| expected.is_none_or(|expected| *actual == expected))
}

#[derive(Clone)]
struct MdocEqualityScopeWitness {
    rows: Vec<MdocCborWitnessRow>,
}

impl MdocEqualityScopeWitness {
    fn new(
        statement: &MdocEqualityScopeStatement,
        outer: &[u8],
    ) -> Result<(Self, MdocEqualityScopeProofMetadata, ScopeSchedule), MdocEqualityScopeError> {
        statement.validate()?;
        let inner = extract_inner(outer)?;
        let random_len = infer_random_len(inner)?;
        let metadata = MdocEqualityScopeProofMetadata {
            random_len: random_len
                .try_into()
                .map_err(|_| MdocEqualityScopeError::RandomTooLong(random_len))?,
        };
        let schedule = schedule(statement, &metadata)?;
        if schedule.outer_len != outer.len()
            || schedule.inner_len != inner.len()
            || !rows_match_expected(
                inner,
                &schedule.rows[schedule.outer_len..]
                    .iter()
                    .map(|row| row.expected)
                    .collect::<Vec<_>>(),
            )
        {
            return Err(MdocEqualityScopeError::WrongInnerShape);
        }
        let outer_witness = MdocCborWitness::new(outer, MdocCborInputMode::Raw)
            .map_err(MdocEqualityScopeError::InvalidPublicValue)?;
        let inner_witness = MdocCborWitness::new(inner, MdocCborInputMode::Raw)
            .map_err(MdocEqualityScopeError::InvalidPublicValue)?;
        let rows = outer_witness
            .rows
            .into_iter()
            .chain(inner_witness.rows)
            .collect();
        Ok((Self { rows }, metadata, schedule))
    }
}

pub(crate) struct MdocEqualityScope {
    statement: MdocEqualityScopeStatement,
    metadata: MdocEqualityScopeProofMetadata,
    schedule: ScopeSchedule,
    handles: MdocEqualityScopeHandles,
    witness: Option<MdocEqualityScopeWitness>,
    claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocEqualityScopeInteractionClaim>,
    component: Option<EqualityScopeComponent>,
}

impl MdocEqualityScope {
    pub(crate) fn new(
        statement: MdocEqualityScopeStatement,
        outer: Vec<u8>,
        handles: MdocEqualityScopeHandles,
    ) -> Result<Self, MdocEqualityScopeError> {
        let (witness, metadata, schedule) = MdocEqualityScopeWitness::new(&statement, &outer)?;
        Ok(Self {
            statement,
            metadata,
            schedule,
            handles,
            witness: Some(witness),
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
        })
    }

    pub(crate) fn verifier(
        statement: MdocEqualityScopeStatement,
        metadata: MdocEqualityScopeProofMetadata,
        handles: MdocEqualityScopeHandles,
        interaction_claim: MdocEqualityScopeInteractionClaim,
    ) -> Result<Self, MdocEqualityScopeError> {
        let schedule = schedule(&statement, &metadata)?;
        Ok(Self {
            statement,
            metadata,
            schedule,
            handles,
            witness: None,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
        })
    }

    pub(crate) fn metadata(&self) -> &MdocEqualityScopeProofMetadata {
        &self.metadata
    }

    pub(crate) fn interaction_claim(&self) -> &MdocEqualityScopeInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("TS13 equality scope interaction claim is set")
    }

    pub(crate) fn outer_parser_log_size(&self) -> u32 {
        parser_log_size(usize::from(self.statement.item_padded_len))
            .expect("validated TS13 padded length has a parser domain")
    }

    pub(crate) fn inner_parser_log_size(&self) -> u32 {
        parser_log_size(self.schedule.inner_len)
            .expect("validated TS13 inner item has a parser domain")
    }

    pub(crate) fn inner_bytes(&self) -> Vec<u8> {
        self.witness
            .as_ref()
            .expect("TS13 equality scope prover has a witness")
            .rows[self.schedule.outer_len..]
            .iter()
            .map(|row| row.byte)
            .collect()
    }

    pub(crate) fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![self.schedule.log_size]
    }

    pub(crate) fn with_claim_mask(
        mut self,
        trace: ClaimMaskTrace,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        assert_eq!(trace.log_size(), self.schedule.log_size);
        self.claim_mask_trace = Some(trace);
        self.claim_mask_challenge = Some(challenge);
        self
    }

    pub(crate) fn with_claim_mask_verifier(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|challenge| challenge.require().expect("claim-mask anchor drawn first"))
    }

    fn prefix(&self) -> String {
        schedule_prefix(&self.statement, &self.metadata)
    }

    fn n_lookups(&self) -> usize {
        3 + usize::from(self.claim_mask_challenge.is_some())
    }
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
        if value != 0x7fff_ffff {
            return m31(value);
        }
    }
}

fn schedule_prefix(
    statement: &MdocEqualityScopeStatement,
    metadata: &MdocEqualityScopeProofMetadata,
) -> String {
    let mut hash = Sha256::new();
    hash.update(b"euid/mdoc/ts13-equality-scope/v1");
    hash.update(statement.digest_id.to_le_bytes());
    hash.update(statement.item_padded_len.to_le_bytes());
    hash.update(metadata.random_len.to_le_bytes());
    hash.update((statement.element_identifier.len() as u64).to_le_bytes());
    hash.update(&statement.element_identifier);
    hash.update((statement.element_value.len() as u64).to_le_bytes());
    hash.update(&statement.element_value);
    let digest = hash.finalize();
    let hex = digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    format!("mdoc/ts13_equality_scope/{hex}")
}

fn column_id(prefix: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{prefix}/{name}"),
    }
}

fn preprocessed_ids(prefix: &str) -> Vec<PreProcessedColumnId> {
    [
        "active",
        "outer",
        "inner",
        "byte_index",
        "expected_active",
        "expected",
        "raw_yield",
        "raw_index",
    ]
    .into_iter()
    .map(|name| column_id(prefix, name))
    .collect()
}

fn coset_to_circle_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![m31(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        ordered[bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        )] = value;
    }
    ordered
}

fn column(log_size: u32, values: Vec<M31>) -> Column {
    Column::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_to_circle_order(log_size, values)),
    )
}

fn preprocessed_columns(schedule: &ScopeSchedule) -> Vec<Column> {
    let n_rows = 1usize << schedule.log_size;
    let mut values = vec![vec![m31(0); n_rows]; PREPROCESSED_COLS];
    for (index, row) in schedule.rows.iter().enumerate() {
        values[0][index] = m31(1);
        match row.stream {
            Stream::Outer => values[1][index] = m31(1),
            Stream::Inner => values[2][index] = m31(1),
        }
        values[3][index] = m31(row.byte_index);
        if let Some(expected) = row.expected {
            values[4][index] = m31(1);
            values[5][index] = m31(u32::from(expected));
        }
        if let Some(raw_index) = row.raw_index {
            values[6][index] = m31(1);
            values[7][index] = m31(raw_index);
        }
    }
    values
        .into_iter()
        .map(|values| column(schedule.log_size, values))
        .collect()
}

fn witness_row_values(row: &MdocCborWitnessRow) -> [M31; TRACE_COLS] {
    let argument = row.argument_limbs();
    [
        m31(u32::from(row.byte)),
        m31(u32::from(row.header)),
        m31(u32::from(row.major)),
        m31(u32::from(argument[0])),
        m31(u32::from(argument[1])),
        m31(u32::from(argument[2])),
        m31(u32::from(argument[3])),
        m31(row.content_len),
        m31(u32::from(row.depth)),
        m31(row.parent_header_index),
        m31(row.child_ordinal),
        m31(u32::from(row.map_key)),
        m31(u32::from(row.map_value)),
    ]
}

fn base_trace(witness: &MdocEqualityScopeWitness, schedule: &ScopeSchedule) -> Vec<Column> {
    assert_eq!(witness.rows.len(), schedule.rows.len());
    let n_rows = 1usize << schedule.log_size;
    let mut values = (0..TRACE_COLS)
        .map(|_| (0..n_rows).map(|_| random_m31_cell()).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    for (row_index, row) in witness.rows.iter().enumerate() {
        for (column_index, value) in witness_row_values(row).into_iter().enumerate() {
            values[column_index][row_index] = value;
        }
    }
    values
        .into_iter()
        .map(|values| column(schedule.log_size, values))
        .collect()
}

#[derive(Clone)]
struct MdocEqualityScopeEval {
    log_size: u32,
    prefix: String,
    outer_parsed: ParsedCborByteRelation,
    inner_parsed: ParsedCborByteRelation,
    inner_raw: FieldBytesRelation,
    claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for MdocEqualityScopeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let outer = eval.get_preprocessed_column(column_id(&self.prefix, "outer"));
        let inner = eval.get_preprocessed_column(column_id(&self.prefix, "inner"));
        let byte_index = eval.get_preprocessed_column(column_id(&self.prefix, "byte_index"));
        let expected_active =
            eval.get_preprocessed_column(column_id(&self.prefix, "expected_active"));
        let expected = eval.get_preprocessed_column(column_id(&self.prefix, "expected"));
        let raw_yield = eval.get_preprocessed_column(column_id(&self.prefix, "raw_yield"));
        let raw_index = eval.get_preprocessed_column(column_id(&self.prefix, "raw_index"));

        let byte = eval.next_trace_mask();
        let header = eval.next_trace_mask();
        let major = eval.next_trace_mask();
        let argument: [E::F; 4] = std::array::from_fn(|_| eval.next_trace_mask());
        let content_len = eval.next_trace_mask();
        let depth = eval.next_trace_mask();
        let parent = eval.next_trace_mask();
        let ordinal = eval.next_trace_mask();
        let map_key = eval.next_trace_mask();
        let map_value = eval.next_trace_mask();

        eval.add_constraint(expected_active * (byte.clone() - expected));

        let tuple = [
            E::F::from(m31(MDOC_EQUALITY_OUTER_STREAM_ID)),
            byte_index.clone(),
            byte.clone(),
            header.clone(),
            major.clone(),
            argument[0].clone(),
            argument[1].clone(),
            argument[2].clone(),
            argument[3].clone(),
            content_len.clone(),
            depth.clone(),
            parent.clone(),
            ordinal.clone(),
            map_key.clone(),
            map_value.clone(),
        ];
        eval.add_to_relation(RelationEntry::new(
            &self.outer_parsed,
            E::EF::from(outer),
            &tuple,
        ));

        let inner_tuple = [
            E::F::from(m31(MDOC_EQUALITY_INNER_STREAM_ID)),
            byte_index,
            byte.clone(),
            header,
            major,
            argument[0].clone(),
            argument[1].clone(),
            argument[2].clone(),
            argument[3].clone(),
            content_len,
            depth,
            parent,
            ordinal,
            map_key,
            map_value,
        ];
        eval.add_to_relation(RelationEntry::new(
            &self.inner_parsed,
            E::EF::from(inner),
            &inner_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.inner_raw,
            -E::EF::from(raw_yield),
            &[
                E::F::from(m31(MDOC_EQUALITY_INNER_STREAM_ID)),
                raw_index,
                byte,
            ],
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn parsed_denominator(
    relation: &ParsedCborByteRelation,
    stream_id: u32,
    preprocessed: &[Column],
    base: &[Column],
    row: usize,
) -> PackedQM31 {
    relation.combine(&[
        PackedM31::broadcast(m31(stream_id)),
        preprocessed[3].data[row],
        base[0].data[row],
        base[1].data[row],
        base[2].data[row],
        base[3].data[row],
        base[4].data[row],
        base[5].data[row],
        base[6].data[row],
        base[7].data[row],
        base[8].data[row],
        base[9].data[row],
        base[10].data[row],
        base[11].data[row],
        base[12].data[row],
    ])
}

fn interaction_trace(
    witness: &MdocEqualityScopeWitness,
    schedule: &ScopeSchedule,
    outer_parsed: &ParsedCborByteRelation,
    inner_parsed: &ParsedCborByteRelation,
    inner_raw: &FieldBytesRelation,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<Column>, QM31) {
    let base = base_trace(witness, schedule);
    let preprocessed = preprocessed_columns(schedule);
    let n_vec_rows = 1usize << (schedule.log_size - LOG_N_LANES);
    let mut sites = Vec::with_capacity(4);
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                (
                    PackedQM31::from(preprocessed[1].data[row]),
                    parsed_denominator(
                        outer_parsed,
                        MDOC_EQUALITY_OUTER_STREAM_ID,
                        &preprocessed,
                        &base,
                        row,
                    ),
                )
            })
            .collect::<Vec<_>>(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                (
                    PackedQM31::from(preprocessed[2].data[row]),
                    parsed_denominator(
                        inner_parsed,
                        MDOC_EQUALITY_INNER_STREAM_ID,
                        &preprocessed,
                        &base,
                        row,
                    ),
                )
            })
            .collect::<Vec<_>>(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                (
                    -PackedQM31::from(preprocessed[6].data[row]),
                    inner_raw.combine(&[
                        PackedM31::broadcast(m31(MDOC_EQUALITY_INNER_STREAM_ID)),
                        preprocessed[7].data[row],
                        base[0].data[row],
                    ]),
                )
            })
            .collect::<Vec<_>>(),
    );
    if let Some((mask, beta)) = claim_mask {
        assert_eq!(mask.packed_rows(), n_vec_rows);
        sites.push(
            (0..n_vec_rows)
                .map(|row| mask.packed_fraction_at(row, beta))
                .collect::<Vec<_>>(),
        );
    }

    let mut logup = LogupTraceGenerator::new(schedule.log_size);
    let mut site = 0;
    while site + 1 < sites.len() {
        let left = &sites[site];
        let right = &sites[site + 1];
        logup.col_from_iter((0..n_vec_rows).map(|row| {
            let (n0, d0) = left[row];
            let (n1, d1) = right[row];
            (n0 * d1 + n1 * d0, d0 * d1)
        }));
        site += 2;
    }
    if site < sites.len() {
        logup.col_from_iter((0..n_vec_rows).map(|row| sites[site][row]));
    }
    logup.finalize_last()
}

impl Air for MdocEqualityScope {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x5453_3133_4551_0001);
        channel.mix_u64(u64::from(self.statement.digest_id));
        channel.mix_u64(u64::from(self.statement.item_padded_len));
        channel.mix_u64(u64::from(self.metadata.random_len));
        channel.mix_u64(self.statement.element_identifier.len() as u64);
        for byte in &self.statement.element_identifier {
            channel.mix_u64(u64::from(*byte));
        }
        channel.mix_u64(self.statement.element_value.len() as u64);
        for byte in &self.statement.element_value {
            channel.mix_u64(u64::from(*byte));
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        assert!(
            !self.handles.inner_raw.is_set(),
            "TS13 equality scope owns the inner raw-stream relation"
        );
        self.handles
            .inner_raw
            .set(FieldBytesRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.schedule.log_size; PREPROCESSED_COLS],
            trace: vec![
                self.schedule.log_size;
                TRACE_COLS
                    + usize::from(self.claim_mask_challenge.is_some())
                        * CLAIM_MASK_TRACE_COLUMNS
            ],
            interaction: vec![
                self.schedule.log_size;
                self.n_lookups().div_ceil(2) * SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(&self.prefix())
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns(&self.schedule))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        self.component = Some(EqualityScopeComponent::new(
            allocator,
            MdocEqualityScopeEval {
                log_size: self.schedule.log_size,
                prefix: self.prefix(),
                outer_parsed: self.handles.outer_parsed.get(),
                inner_parsed: self.handles.inner_parsed.get(),
                inner_raw: self.handles.inner_raw.get(),
                claim_mask_beta: self.claim_mask_beta(),
            },
            self.interaction_claim().claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("TS13 equality scope component is built")]
    }
}

impl AirProver for MdocEqualityScope {
    fn max_log_size(&self) -> u32 {
        self.schedule.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.schedule.log_size + 2
    }

    fn write_preprocessed(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tree, &preprocessed_ids(&self.prefix()));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_equality_scope::MdocEqualityScope",
            &preprocessed_ids(&self.prefix()),
            &preprocessed_columns(&self.schedule),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tree: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = preprocessed_ids(&self.prefix());
        let all_columns = preprocessed_columns(&self.schedule);
        tree.extend_evals(
            selected_ids
                .iter()
                .map(|id| {
                    all_ids
                        .iter()
                        .position(|candidate| candidate == id)
                        .map(|index| all_columns[index].clone())
                        .expect("unexpected TS13 equality preprocessed selection")
                })
                .collect(),
        );
    }

    fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tree.extend_evals(base_trace(
            self.witness
                .as_ref()
                .expect("TS13 equality scope prover has a witness"),
            &self.schedule,
        ));
        if let Some(mask) = &self.claim_mask_trace {
            tree.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let claim_mask = self.claim_mask_trace.as_ref().zip(self.claim_mask_beta());
        let (trace, claimed_sum) = interaction_trace(
            self.witness
                .as_ref()
                .expect("TS13 equality scope prover has a witness"),
            &self.schedule,
            &self.handles.outer_parsed.get(),
            &self.handles.inner_parsed.get(),
            &self.handles.inner_raw.get(),
            claim_mask,
        );
        tree.extend_evals(trace);
        self.interaction_claim = Some(MdocEqualityScopeInteractionClaim { claimed_sum });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("TS13 equality scope component is built")]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn statement(digest_id: u32, value: Vec<u8>, padded_len: u16) -> MdocEqualityScopeStatement {
        MdocEqualityScopeStatement {
            element_identifier: b"age_over_18".to_vec(),
            element_value: value,
            digest_id,
            item_padded_len: padded_len,
        }
    }

    fn item(digest_id: u32, identifier: &[u8], value: &[u8], random: &[u8]) -> Vec<u8> {
        let statement = MdocEqualityScopeStatement {
            element_identifier: identifier.to_vec(),
            element_value: value.to_vec(),
            digest_id,
            item_padded_len: 128,
        };
        let expected = expected_inner(&statement, random.len());
        let mut inner = expected
            .into_iter()
            .map(|byte| byte.unwrap_or(0))
            .collect::<Vec<_>>();
        let random_prefix = 1 + cbor_text(b"random").len() + cbor_head(2, random.len()).len();
        inner[random_prefix..random_prefix + random.len()].copy_from_slice(random);
        let mut outer = vec![0xd8, 0x18];
        outer.extend_from_slice(&cbor_head(2, inner.len()));
        outer.extend_from_slice(&inner);
        outer
    }

    #[test]
    fn canonical_item_builds_complete_two_parser_schedule() {
        let outer = item(7, b"age_over_18", &[0xf5], &[0x42; 16]);
        let padded_len = sha_padded_len(outer.len()) as u16;
        let scope = MdocEqualityScope::new(
            statement(7, vec![0xf5], padded_len),
            outer,
            MdocEqualityScopeHandles::fresh(),
        )
        .expect("canonical TS13 item");
        assert_eq!(scope.metadata().random_len, 16);
        assert_eq!(scope.outer_parser_log_size(), MIN_LOG_SIZE);
        assert_eq!(scope.inner_parser_log_size(), MIN_LOG_SIZE);
        assert_eq!(scope.inner_bytes().len(), scope.schedule.inner_len);
    }

    #[test]
    fn semantic_substitutions_reject() {
        let outer = item(7, b"age_over_18", &[0xf5], &[0x42; 16]);
        let padded_len = sha_padded_len(outer.len()) as u16;
        for wrong in [
            statement(8, vec![0xf5], padded_len),
            MdocEqualityScopeStatement {
                element_identifier: b"age_over_21".to_vec(),
                ..statement(7, vec![0xf5], padded_len)
            },
            statement(7, vec![0xf4], padded_len),
        ] {
            assert!(
                MdocEqualityScope::new(wrong, outer.clone(), MdocEqualityScopeHandles::fresh())
                    .is_err(),
                "digest ID, identifier, and value substitutions must reject",
            );
        }
    }

    #[test]
    fn digest_id_canonical_boundaries_are_accepted_and_profile_bound_is_enforced() {
        for (digest_id, encoding) in [
            (23, vec![0x17]),
            (24, vec![0x18, 0x18]),
            (255, vec![0x18, 0xff]),
            (256, vec![0x19, 0x01, 0x00]),
            (u32::from(u16::MAX), vec![0x19, 0xff, 0xff]),
        ] {
            assert_eq!(cbor_uint(digest_id), encoding);
            let outer = item(digest_id, b"age_over_18", &[0xf5], &[0x42; 16]);
            let padded_len = sha_padded_len(outer.len()) as u16;
            MdocEqualityScope::new(
                statement(digest_id, vec![0xf5], padded_len),
                outer,
                MdocEqualityScopeHandles::fresh(),
            )
            .expect("canonical digest-ID boundary item");
        }

        let error = match MdocEqualityScope::new(
            statement(u32::from(u16::MAX) + 1, vec![0xf5], 128),
            item(
                u32::from(u16::MAX) + 1,
                b"age_over_18",
                &[0xf5],
                &[0x42; 16],
            ),
            MdocEqualityScopeHandles::fresh(),
        ) {
            Ok(_) => panic!("digest ID above the published u16 profile must reject"),
            Err(error) => error,
        };
        assert!(matches!(
            error,
            MdocEqualityScopeError::DigestIdOutOfRange(_)
        ));
    }

    #[test]
    fn duplicate_nonminimal_trailing_and_indefinite_items_reject() {
        let honest = item(7, b"age_over_18", &[0xf5], &[0x42; 16]);
        let padded_len = sha_padded_len(honest.len()) as u16;
        let public = statement(7, vec![0xf5], padded_len);

        let inner = extract_inner(&honest).unwrap();
        let mut duplicate_inner = inner.to_vec();
        duplicate_inner[0] = 0xa5;
        duplicate_inner.extend_from_slice(&cbor_text(b"digestID"));
        duplicate_inner.push(7);
        let mut duplicate = vec![0xd8, 0x18];
        duplicate.extend_from_slice(&cbor_head(2, duplicate_inner.len()));
        duplicate.extend_from_slice(&duplicate_inner);

        let mut nonminimal_inner = inner.to_vec();
        let digest_key_end = 1
            + cbor_text(b"random").len()
            + cbor_head(2, 16).len()
            + 16
            + cbor_text(b"digestID").len();
        nonminimal_inner.splice(digest_key_end..=digest_key_end, [0x18, 0x07]);
        let mut nonminimal = vec![0xd8, 0x18];
        nonminimal.extend_from_slice(&cbor_head(2, nonminimal_inner.len()));
        nonminimal.extend_from_slice(&nonminimal_inner);

        let mut trailing_inner = inner.to_vec();
        trailing_inner.push(0);
        let mut trailing = vec![0xd8, 0x18];
        trailing.extend_from_slice(&cbor_head(2, trailing_inner.len()));
        trailing.extend_from_slice(&trailing_inner);

        let mut indefinite_inner = inner.to_vec();
        indefinite_inner[0] = 0xbf;
        indefinite_inner.push(0xff);
        let mut indefinite = vec![0xd8, 0x18];
        indefinite.extend_from_slice(&cbor_head(2, indefinite_inner.len()));
        indefinite.extend_from_slice(&indefinite_inner);

        for malformed in [duplicate, nonminimal, trailing, indefinite] {
            assert!(
                MdocEqualityScope::new(
                    public.clone(),
                    malformed,
                    MdocEqualityScopeHandles::fresh()
                )
                .is_err(),
                "malformed semantic item must reject",
            );
        }
    }
}
