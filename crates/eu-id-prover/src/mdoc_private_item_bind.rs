//! Private `IssuerSignedItemBytes` semantic binding.
//!
//! The CBOR parsers prove the complete SHA-padded outer item.
//! They also prove the tag-24 inner map.
//! This component consumes both parsed streams.
//! It checks the four `IssuerSignedItem` fields without public offsets.
//! It also checks the fields without public lengths.
//! It emits the semantic identifier and value through [`FieldBytesRelation`].
//! It emits one private canonical digest-ID tuple for the `valueDigests` scan.
//! It constrains the disclosed value to `age_over_18 = true`.

use std::fmt;

use air_core::relations::{FieldBytesRelation, SharedFieldRelation, SharedRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use serde::{Deserialize, Serialize};
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
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator, ORIGINAL_TRACE_IDX,
};

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};
use crate::mdoc_cbor_stream::{
    parser_log_size, MdocCborInputMode, MdocCborPhase, MdocCborStreamError, MdocCborWitness,
    MdocCborWitnessRow, ParsedCborByteRelation, SharedParsedCborByteRelation,
};

const MDOC_PRIVATE_ITEM_PADDED_BYTES: usize = 128;
const MDOC_PRIVATE_ITEM_TRANSCRIPT_ATTRIBUTE_INDEX: u64 = 0;
pub(crate) const MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES: usize = 128;
pub(crate) const MDOC_PRIVATE_ITEM_DIGEST_ID_MAX: u32 = u16::MAX as u32;

const MDOC_PRIVATE_ITEM_VERSION: u64 = 1;
const MDOC_PRIVATE_ITEM_DOMAIN: u64 = 0x4d44_4f43_4954_454d;
const MDOC_PRIVATE_ITEM_TRANSCRIPT_TAG: u64 = 2;
const MDOC_PRIVATE_ITEM_BLIND_ROWS: usize = 256;
const MDOC_PRIVATE_ITEM_MAX_INNER_BYTES: usize = 192;
const OUTER_PREFIX_BYTES: usize = 4;
const PREPROCESSED_COLS: usize = 5;
const PP_OUTER_PREFIX_START: usize = 1;
const KEY_COUNT: usize = 4;
const DIGEST_COPY_BYTES: usize = 5;
const RANDOM_BOUND_BITS: usize = 8;

const KEY_RANDOM: usize = 0;
const KEY_DIGEST_ID: usize = 1;
const KEY_ELEMENT_VALUE: usize = 2;
const KEY_ELEMENT_IDENTIFIER: usize = 3;
const KEY_LABELS: [&[u8]; KEY_COUNT] = [
    b"random",
    b"digestID",
    b"elementValue",
    b"elementIdentifier",
];
const KEY_ENCODED_BYTES: usize = (1 + 6) + (1 + 8) + (1 + 12) + (1 + 17);
const CANONICAL_ELEMENT_IDENTIFIER: &[u8] = b"age_over_18";
const CANONICAL_ELEMENT_VALUE: &[u8] = &[0xf5];
const CANONICAL_SEMANTIC_TUPLES: usize =
    CANONICAL_ELEMENT_IDENTIFIER.len() + CANONICAL_ELEMENT_VALUE.len();

// One private digest-ID tuple:
// (encoding_len, b0, b1, b2, b3, b4, value_lo16, value_hi16).
// The fixed profile sets b3, b4, and value_hi16 to zero.
relation!(MdocPrivateDigestIdRelation, 8);
relation!(MdocPrivateItemKeyRelation, 3);

pub(crate) type SharedMdocPrivateDigestIdRelation = SharedRelation<MdocPrivateDigestIdRelation>;

/// Prover-only item data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateItemPrivateInput {
    pub(crate) padded_item: Vec<u8>,
}

impl MdocPrivateItemPrivateInput {
    pub(crate) fn new(padded_item: Vec<u8>) -> Self {
        Self { padded_item }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateItemFieldIds {
    pub(crate) outer_stream: u32,
    pub(crate) inner_stream: u32,
    /// Field ID for the encoded element identifier.
    pub(crate) element_identifier: u32,
    /// Field ID for the encoded `age_over_18` value.
    pub(crate) element_value: u32,
}

#[derive(Clone)]
pub(crate) struct MdocPrivateItemHandles {
    /// The attribute SHA provider draws this relation.
    pub(crate) item_fields: SharedFieldRelation,
    pub(crate) outer_parsed: SharedParsedCborByteRelation,
    pub(crate) inner_parsed: SharedParsedCborByteRelation,
    /// This module draws this relation for the raw inner CBOR parser.
    pub(crate) inner_raw: SharedFieldRelation,
    /// This module draws this relation for one MSO valueDigests scan.
    pub(crate) digest_id: SharedMdocPrivateDigestIdRelation,
}

impl MdocPrivateItemHandles {
    pub(crate) fn fresh(item_fields: SharedFieldRelation) -> Self {
        Self {
            item_fields,
            outer_parsed: SharedParsedCborByteRelation::new(),
            inner_parsed: SharedParsedCborByteRelation::new(),
            inner_raw: SharedFieldRelation::new(),
            digest_id: SharedMdocPrivateDigestIdRelation::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateTag24WrapperReason {
    TruncatedToken { needed: usize },
    ExpectedTag24,
    ExpectedByteString,
    ExpectedU8ByteStringLength { additional: u8 },
    ByteStringLengthMismatch { declared: usize, actual: usize },
}

impl fmt::Display for MdocPrivateTag24WrapperReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TruncatedToken { needed } => {
                write!(f, "truncated token needs {needed} argument bytes")
            }
            Self::ExpectedTag24 => write!(f, "expected canonical tag 24"),
            Self::ExpectedByteString => write!(f, "expected tag-24 byte string"),
            Self::ExpectedU8ByteStringLength { additional } => write!(
                f,
                "expected tag-24 byte-string length in u8 form, got additional info {additional}"
            ),
            Self::ByteStringLengthMismatch { declared, actual } => write!(
                f,
                "tag-24 byte string declares {declared} bytes but contains {actual}"
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateItemError {
    PaddedLengthMismatch {
        expected: usize,
        actual: usize,
    },
    OuterParser(MdocCborStreamError),
    InnerParser(MdocCborStreamError),
    InvalidTag24Wrapper {
        offset: usize,
        reason: MdocPrivateTag24WrapperReason,
    },
    InvalidIssuerSignedItemRoot,
    MissingKey(&'static str),
    DuplicateKey(&'static str),
    InvalidRandom,
    InvalidDigestId,
    DigestIdOutOfRange {
        value: u64,
        max: u32,
    },
    InvalidElementIdentifier,
    InvalidElementValue,
    TraceTooLarge {
        rows: usize,
    },
}

impl fmt::Display for MdocPrivateItemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PaddedLengthMismatch { expected, actual } => write!(
                f,
                "private IssuerSignedItem must have {expected} padded bytes; witness has {actual}"
            ),
            Self::OuterParser(error) => {
                write!(f, "invalid private IssuerSignedItem outer CBOR: {error}")
            }
            Self::InnerParser(error) => {
                write!(f, "invalid private IssuerSignedItem inner CBOR: {error}")
            }
            Self::InvalidTag24Wrapper { offset, reason } => write!(
                f,
                "private IssuerSignedItem is not canonical tag-24 bstr at byte {offset}: {reason}"
            ),
            Self::InvalidIssuerSignedItemRoot => {
                write!(
                    f,
                    "private IssuerSignedItem inner root is not a four-entry map"
                )
            }
            Self::MissingKey(key) => write!(f, "private IssuerSignedItem misses key {key}"),
            Self::DuplicateKey(key) => {
                write!(f, "private IssuerSignedItem duplicates key {key}")
            }
            Self::InvalidRandom => {
                write!(f, "private IssuerSignedItem random field is invalid")
            }
            Self::InvalidDigestId => {
                write!(
                    f,
                    "private IssuerSignedItem digestID is not a canonical uint"
                )
            }
            Self::DigestIdOutOfRange { value, max } => write!(
                f,
                "private IssuerSignedItem digestID {value} exceeds public cap {max}"
            ),
            Self::InvalidElementIdentifier => {
                write!(f, "private IssuerSignedItem elementIdentifier is invalid")
            }
            Self::InvalidElementValue => {
                write!(f, "private IssuerSignedItem elementValue shape is invalid")
            }
            Self::TraceTooLarge { rows } => {
                write!(
                    f,
                    "private IssuerSignedItem semantic trace needs {rows} rows"
                )
            }
        }
    }
}

impl std::error::Error for MdocPrivateItemError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::OuterParser(error) | Self::InnerParser(error) => Some(error),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocPrivateItemInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

type Column = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type PrivateItemComponent = FrameworkComponent<MdocPrivateItemEval>;

mod trace_col {
    pub(super) const ACTIVE: usize = 0;
    pub(super) const OUTER: usize = 1;
    pub(super) const INNER: usize = 2;
    pub(super) const OUTER_END: usize = 3;
    pub(super) const INNER_START: usize = 4;
    pub(super) const INNER_END: usize = 5;
    pub(super) const STREAM_INDEX: usize = 6;
    pub(super) const INNER_LEN: usize = 7;
    pub(super) const RAW_YIELD: usize = 8;
    pub(super) const RAW_INDEX: usize = 9;

    pub(super) const BYTE: usize = 10;
    pub(super) const HEADER: usize = 11;
    pub(super) const MAJOR: usize = 12;
    pub(super) const ARGUMENT: usize = 13;
    pub(super) const CONTENT_LEN: usize = 17;
    pub(super) const DEPTH: usize = 18;
    pub(super) const PARENT: usize = 19;
    pub(super) const ORDINAL: usize = 20;
    pub(super) const MAP_KEY: usize = 21;
    pub(super) const MAP_VALUE: usize = 22;

    pub(super) const KEY_ACTIVE: usize = 23;
    pub(super) const KEY_START: usize = 27;
    pub(super) const KEY_END: usize = 31;
    pub(super) const KEY_SEEN: usize = 35;
    pub(super) const KEY_INDEX: usize = 39;
    pub(super) const VALUE_START: usize = 40;

    pub(super) const RANDOM_LOWER_BITS: usize = 44;
    pub(super) const RANDOM_UPPER_BITS: usize = 52;

    pub(super) const DIGEST_START_KIND: usize = 60;
    pub(super) const DIGEST_COPY: usize = 64;
    pub(super) const DIGEST_SHORT_SLACK_BITS: usize = 69;

    pub(super) const IDENTIFIER_CONTENT_ACTIVE: usize = 74;
    pub(super) const IDENTIFIER_CONTENT_END: usize = 75;
    pub(super) const IDENTIFIER_CONTENT_INDEX: usize = 76;

    pub(super) const VALUE_ACTIVE: usize = 77;
    pub(super) const VALUE_END: usize = 78;
    pub(super) const VALUE_INDEX: usize = 79;
    pub(super) const COUNT: usize = 80;
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
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

fn item_log_size() -> u32 {
    let max_outer = MDOC_PRIVATE_ITEM_PADDED_BYTES - 9;
    let max_inner = max_outer - OUTER_PREFIX_BYTES;
    let rows = max_outer
        .checked_add(max_inner)
        .and_then(|rows| rows.checked_add(MDOC_PRIVATE_ITEM_BLIND_ROWS))
        .expect("the fixed private item row count fits usize");
    rows.next_power_of_two().ilog2()
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![m31(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn column(log_size: u32, values: Vec<M31>) -> Column {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, values)),
    )
}

fn preprocessed_id(log_size: u32, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/private_item/v{MDOC_PRIVATE_ITEM_VERSION}/log{log_size}/{name}"),
    }
}

fn preprocessed_ids(log_size: u32) -> Vec<PreProcessedColumnId> {
    let mut ids = vec![preprocessed_id(log_size, "last")];
    ids.extend(
        (0..OUTER_PREFIX_BYTES)
            .map(|index| preprocessed_id(log_size, &format!("outer_prefix_{index}"))),
    );
    ids
}

fn preprocessed_columns(log_size: u32) -> Vec<Column> {
    let rows = 1usize << log_size;
    let mut values = vec![vec![m31(0); rows]; PREPROCESSED_COLS];
    values[0][rows - 1] = m31(1);
    for index in 0..OUTER_PREFIX_BYTES {
        values[PP_OUTER_PREFIX_START + index][index] = m31(1);
    }
    values
        .into_iter()
        .map(|values| column(log_size, values))
        .collect()
}

fn tuple_values(row: &MdocCborWitnessRow) -> [M31; 13] {
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

fn bit_values(value: usize, count: usize) -> impl Iterator<Item = M31> {
    (0..count).map(move |bit| m31(((value >> bit) & 1) as u32))
}

fn ts13_semantic_tuples(
    field_ids: MdocPrivateItemFieldIds,
) -> impl Iterator<Item = (u32, usize, u8)> {
    CANONICAL_ELEMENT_IDENTIFIER
        .iter()
        .copied()
        .enumerate()
        .map(move |(index, byte)| (field_ids.element_identifier, index, byte))
        .chain(
            CANONICAL_ELEMENT_VALUE
                .iter()
                .copied()
                .enumerate()
                .map(move |(index, byte)| (field_ids.element_value, index, byte)),
        )
}

#[derive(Clone, Copy)]
struct KeySpan {
    start: usize,
    end: usize,
    value_start: usize,
}

#[derive(Clone)]
struct ItemAnalysis {
    key_spans: [KeySpan; KEY_COUNT],
    random_len: usize,
    digest_encoding: Vec<u8>,
    digest_value: u64,
    identifier_content_start: usize,
    value_root: usize,
    value_end: usize,
}

fn key_kind(bytes: &[u8]) -> Option<usize> {
    KEY_LABELS.iter().position(|label| *label == bytes)
}

fn analyze_inner(
    inner: &[u8],
    rows: &[MdocCborWitnessRow],
) -> Result<ItemAnalysis, MdocPrivateItemError> {
    let root = rows
        .first()
        .ok_or(MdocPrivateItemError::InvalidIssuerSignedItemRoot)?;
    if !root.header || root.byte != 0xa4 || root.major != 5 || root.argument != 4 || root.depth != 0
    {
        return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
    }

    let mut spans: [Option<KeySpan>; KEY_COUNT] = [None; KEY_COUNT];
    for row in rows.iter().filter(|row| {
        row.header
            && row.depth == 1
            && row.parent_header_index == 0
            && row.map_key
            && row.major == 3
    }) {
        let start = row.byte_index as usize;
        let len = row.content_len as usize;
        if len >= 24 {
            return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
        }
        let content_start = start + 1;
        let end = content_start
            .checked_add(len)
            .ok_or(MdocPrivateItemError::InvalidIssuerSignedItemRoot)?;
        let label = inner
            .get(content_start..end)
            .ok_or(MdocPrivateItemError::InvalidIssuerSignedItemRoot)?;
        let kind = key_kind(label).ok_or(MdocPrivateItemError::InvalidIssuerSignedItemRoot)?;
        if spans[kind].is_some() {
            return Err(MdocPrivateItemError::DuplicateKey(
                std::str::from_utf8(KEY_LABELS[kind]).expect("ASCII key"),
            ));
        }
        let value_start = end;
        if !rows.get(value_start).is_some_and(|value| {
            value.header
                && value.depth == 1
                && value.parent_header_index == 0
                && value.map_value
                && value.child_ordinal == row.child_ordinal + 1
        }) {
            return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
        }
        spans[kind] = Some(KeySpan {
            start,
            end: end - 1,
            value_start,
        });
    }
    for (kind, span) in spans.iter().enumerate() {
        if span.is_none() {
            return Err(MdocPrivateItemError::MissingKey(
                std::str::from_utf8(KEY_LABELS[kind]).expect("ASCII key"),
            ));
        }
    }
    let key_spans = spans.map(Option::unwrap);

    let random = &rows[key_spans[KEY_RANDOM].value_start];
    let random_len = random.content_len as usize;
    if random.major != 2 || !(16..=MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES).contains(&random_len) {
        return Err(MdocPrivateItemError::InvalidRandom);
    }

    let digest = &rows[key_spans[KEY_DIGEST_ID].value_start];
    if digest.major != 0 {
        return Err(MdocPrivateItemError::InvalidDigestId);
    }
    let digest_width = match digest.byte {
        0x00..=0x17 => 1,
        0x18 => 2,
        0x19 => 3,
        // Parse this form to report the exact u16 range error below.
        0x1a => 5,
        _ => return Err(MdocPrivateItemError::InvalidDigestId),
    };
    let digest_start = digest.byte_index as usize;
    let digest_encoding = inner
        .get(digest_start..digest_start + digest_width)
        .ok_or(MdocPrivateItemError::InvalidDigestId)?
        .to_vec();
    if digest.argument > u64::from(MDOC_PRIVATE_ITEM_DIGEST_ID_MAX) {
        return Err(MdocPrivateItemError::DigestIdOutOfRange {
            value: digest.argument,
            max: MDOC_PRIVATE_ITEM_DIGEST_ID_MAX,
        });
    }

    let identifier = &rows[key_spans[KEY_ELEMENT_IDENTIFIER].value_start];
    if identifier.major != 3
        || identifier.byte != 0x60 + CANONICAL_ELEMENT_IDENTIFIER.len() as u8
        || identifier.content_len as usize != CANONICAL_ELEMENT_IDENTIFIER.len()
    {
        return Err(MdocPrivateItemError::InvalidElementIdentifier);
    }
    let identifier_content_start = identifier.byte_index as usize + 1;
    let identifier_content_end = identifier_content_start
        .checked_add(CANONICAL_ELEMENT_IDENTIFIER.len())
        .ok_or(MdocPrivateItemError::InvalidElementIdentifier)?;
    let identifier_content = inner
        .get(identifier_content_start..identifier_content_end)
        .ok_or(MdocPrivateItemError::InvalidElementIdentifier)?;
    if identifier_content != CANONICAL_ELEMENT_IDENTIFIER {
        return Err(MdocPrivateItemError::InvalidElementIdentifier);
    }

    let value_root = key_spans[KEY_ELEMENT_VALUE].value_start;
    let value_end = key_spans
        .iter()
        .map(|span| span.start)
        .filter(|start| *start > value_root)
        .min()
        .unwrap_or(inner.len())
        - 1;
    if value_end < value_root {
        return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
    }

    if inner.get(value_root..=value_end) != Some(CANONICAL_ELEMENT_VALUE) {
        return Err(MdocPrivateItemError::InvalidElementValue);
    }
    Ok(ItemAnalysis {
        key_spans,
        random_len,
        digest_encoding,
        digest_value: digest.argument,
        identifier_content_start,
        value_root,
        value_end,
    })
}

fn extract_outer_and_inner(
    padded_item: &[u8],
) -> Result<(MdocCborWitness, Vec<u8>, MdocCborWitness), MdocPrivateItemError> {
    if let Some(message_len) = sha_padded_message_len(padded_item) {
        validate_tag24_wrapper(&padded_item[..message_len])?;
    }
    let outer = MdocCborWitness::new(padded_item, MdocCborInputMode::ShaPadded)
        .map_err(MdocPrivateItemError::OuterParser)?;
    let outer_len = outer
        .rows
        .iter()
        .take_while(|row| row.phase == MdocCborPhase::Cbor)
        .count();
    let outer_bytes = &padded_item[..outer_len];
    validate_tag24_wrapper(outer_bytes)?;
    let inner = outer_bytes[OUTER_PREFIX_BYTES..].to_vec();
    let inner_witness = MdocCborWitness::new(&inner, MdocCborInputMode::Raw)
        .map_err(MdocPrivateItemError::InnerParser)?;
    Ok((outer, inner, inner_witness))
}

fn sha_padded_message_len(bytes: &[u8]) -> Option<usize> {
    const SHA_LENGTH_BYTES: usize = 8;
    let length_start = bytes.len().checked_sub(SHA_LENGTH_BYTES)?;
    let bit_len = u64::from_be_bytes(bytes.get(length_start..)?.try_into().ok()?);
    if bit_len % 8 != 0 {
        return None;
    }
    let message_len = usize::try_from(bit_len / 8).ok()?;
    (message_len < length_start && bytes.get(message_len) == Some(&0x80)).then_some(message_len)
}

fn validate_tag24_wrapper(bytes: &[u8]) -> Result<(), MdocPrivateItemError> {
    let invalid = |offset, reason| MdocPrivateItemError::InvalidTag24Wrapper { offset, reason };
    match (bytes.first(), bytes.get(1)) {
        (None, _) => {
            return Err(invalid(
                0,
                MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
            ));
        }
        (Some(0xd8), None) => {
            return Err(invalid(
                0,
                MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
            ));
        }
        (Some(0xd8), Some(0x18)) => {}
        _ => return Err(invalid(0, MdocPrivateTag24WrapperReason::ExpectedTag24)),
    }

    let Some(&byte_string_head) = bytes.get(2) else {
        return Err(invalid(
            2,
            MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
        ));
    };
    if byte_string_head >> 5 != 2 {
        return Err(invalid(
            2,
            MdocPrivateTag24WrapperReason::ExpectedByteString,
        ));
    }
    let additional = byte_string_head & 0x1f;
    if additional != 24 {
        return Err(invalid(
            2,
            MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength { additional },
        ));
    }
    let Some(&declared) = bytes.get(3) else {
        return Err(invalid(
            3,
            MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
        ));
    };
    let actual = bytes.len() - OUTER_PREFIX_BYTES;
    if usize::from(declared) != actual {
        return Err(invalid(
            3,
            MdocPrivateTag24WrapperReason::ByteStringLengthMismatch {
                declared: usize::from(declared),
                actual,
            },
        ));
    }
    Ok(())
}

#[derive(Clone)]
struct MdocPrivateItemWitness {
    columns: Vec<Vec<M31>>,
    inner_bytes: Vec<u8>,
}

impl MdocPrivateItemWitness {
    fn new(
        private_input: MdocPrivateItemPrivateInput,
        log_size: u32,
    ) -> Result<Self, MdocPrivateItemError> {
        let MdocPrivateItemPrivateInput { padded_item } = private_input;
        if padded_item.len() != MDOC_PRIVATE_ITEM_PADDED_BYTES {
            return Err(MdocPrivateItemError::PaddedLengthMismatch {
                expected: MDOC_PRIVATE_ITEM_PADDED_BYTES,
                actual: padded_item.len(),
            });
        }
        let (outer, inner_bytes, inner) = extract_outer_and_inner(&padded_item)?;
        let outer_rows: Vec<_> = outer
            .rows
            .iter()
            .take_while(|row| row.phase == MdocCborPhase::Cbor)
            .cloned()
            .collect();
        let analysis = analyze_inner(&inner_bytes, &inner.rows)?;
        let active_rows = outer_rows.len() + inner.rows.len();
        let domain_rows = 1usize << log_size;
        if active_rows + MDOC_PRIVATE_ITEM_BLIND_ROWS > domain_rows {
            return Err(MdocPrivateItemError::TraceTooLarge { rows: active_rows });
        }

        let mut columns = (0..trace_col::COUNT)
            .map(|_| (0..domain_rows).map(|_| random_m31()).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for column_index in [
            trace_col::ACTIVE,
            trace_col::OUTER,
            trace_col::INNER,
            trace_col::OUTER_END,
            trace_col::INNER_START,
            trace_col::INNER_END,
            trace_col::RAW_YIELD,
            trace_col::KEY_ACTIVE,
            trace_col::KEY_ACTIVE + 1,
            trace_col::KEY_ACTIVE + 2,
            trace_col::KEY_ACTIVE + 3,
            trace_col::KEY_START,
            trace_col::KEY_START + 1,
            trace_col::KEY_START + 2,
            trace_col::KEY_START + 3,
            trace_col::KEY_END,
            trace_col::KEY_END + 1,
            trace_col::KEY_END + 2,
            trace_col::KEY_END + 3,
            trace_col::VALUE_START,
            trace_col::VALUE_START + 1,
            trace_col::VALUE_START + 2,
            trace_col::VALUE_START + 3,
            trace_col::DIGEST_START_KIND,
            trace_col::DIGEST_START_KIND + 1,
            trace_col::DIGEST_START_KIND + 2,
            trace_col::DIGEST_START_KIND + 3,
            trace_col::IDENTIFIER_CONTENT_ACTIVE,
            trace_col::IDENTIFIER_CONTENT_END,
            trace_col::VALUE_ACTIVE,
            trace_col::VALUE_END,
        ] {
            columns[column_index].fill(m31(0));
        }
        columns[trace_col::KEY_SEEN..trace_col::KEY_SEEN + KEY_COUNT]
            .iter_mut()
            .for_each(|column| {
                column.iter_mut().for_each(|value| *value = random_bit());
            });
        for index in 0..RANDOM_BOUND_BITS {
            columns[trace_col::RANDOM_LOWER_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
            columns[trace_col::RANDOM_UPPER_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        for index in 0..5 {
            columns[trace_col::DIGEST_SHORT_SLACK_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        columns[trace_col::INNER_LEN][..active_rows].fill(m31(inner.rows.len() as u32));

        for (index, row) in outer_rows.iter().enumerate() {
            columns[trace_col::ACTIVE][index] = m31(1);
            columns[trace_col::OUTER][index] = m31(1);
            columns[trace_col::STREAM_INDEX][index] = m31(index as u32);
            columns[trace_col::OUTER_END][index] = m31(u32::from(index + 1 == outer_rows.len()));
            columns[trace_col::RAW_YIELD][index] = m31(u32::from(index >= OUTER_PREFIX_BYTES));
            if index >= OUTER_PREFIX_BYTES {
                columns[trace_col::RAW_INDEX][index] = m31((index - OUTER_PREFIX_BYTES) as u32);
            }
            for (offset, value) in tuple_values(row).into_iter().enumerate() {
                columns[trace_col::BYTE + offset][index] = value;
            }
        }

        let inner_base = outer_rows.len();
        for (inner_index, row) in inner.rows.iter().enumerate() {
            let index = inner_base + inner_index;
            columns[trace_col::ACTIVE][index] = m31(1);
            columns[trace_col::INNER][index] = m31(1);
            columns[trace_col::INNER_START][index] = m31(u32::from(inner_index == 0));
            columns[trace_col::INNER_END][index] =
                m31(u32::from(inner_index + 1 == inner.rows.len()));
            columns[trace_col::STREAM_INDEX][index] = m31(inner_index as u32);
            for (offset, value) in tuple_values(row).into_iter().enumerate() {
                columns[trace_col::BYTE + offset][index] = value;
            }
        }

        for (kind, span) in analysis.key_spans.iter().enumerate() {
            let start = inner_base + span.start;
            let end = inner_base + span.end;
            for (key_index, index) in (start..=end).enumerate() {
                columns[trace_col::KEY_ACTIVE + kind][index] = m31(1);
                columns[trace_col::KEY_INDEX][index] = m31(key_index as u32);
            }
            columns[trace_col::KEY_START + kind][start] = m31(1);
            columns[trace_col::KEY_END + kind][end] = m31(1);
            columns[trace_col::VALUE_START + kind][inner_base + span.value_start] = m31(1);
            columns[trace_col::KEY_SEEN + kind][inner_base..start].fill(m31(0));
            columns[trace_col::KEY_SEEN + kind][start..active_rows].fill(m31(1));
        }

        let random_start = inner_base + analysis.key_spans[KEY_RANDOM].value_start;
        for (offset, bit) in bit_values(analysis.random_len - 16, RANDOM_BOUND_BITS).enumerate() {
            columns[trace_col::RANDOM_LOWER_BITS + offset][random_start] = bit;
        }
        for (offset, bit) in bit_values(
            MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES - analysis.random_len,
            RANDOM_BOUND_BITS,
        )
        .enumerate()
        {
            columns[trace_col::RANDOM_UPPER_BITS + offset][random_start] = bit;
        }

        let digest_start = inner_base + analysis.key_spans[KEY_DIGEST_ID].value_start;
        let digest_kind = match analysis.digest_encoding.len() {
            1 => 0,
            2 => 1,
            3 => 2,
            5 => 3,
            _ => return Err(MdocPrivateItemError::InvalidDigestId),
        };
        columns[trace_col::DIGEST_START_KIND + digest_kind][digest_start] = m31(1);
        for index in 0..DIGEST_COPY_BYTES {
            columns[trace_col::DIGEST_COPY + index][digest_start] = m31(u32::from(
                analysis.digest_encoding.get(index).copied().unwrap_or(0),
            ));
        }
        if analysis.digest_encoding.len() == 1 {
            for (offset, bit) in bit_values(23 - analysis.digest_value as usize, 5).enumerate() {
                columns[trace_col::DIGEST_SHORT_SLACK_BITS + offset][digest_start] = bit;
            }
        }

        let identifier_content_start = inner_base + analysis.identifier_content_start;
        let identifier_content_end =
            identifier_content_start + CANONICAL_ELEMENT_IDENTIFIER.len() - 1;
        columns[trace_col::IDENTIFIER_CONTENT_END][identifier_content_end] = m31(1);
        for (content_index, index) in
            (identifier_content_start..=identifier_content_end).enumerate()
        {
            columns[trace_col::IDENTIFIER_CONTENT_ACTIVE][index] = m31(1);
            columns[trace_col::IDENTIFIER_CONTENT_INDEX][index] = m31(content_index as u32);
        }
        let value_start = inner_base + analysis.value_root;
        let value_end = inner_base + analysis.value_end;
        columns[trace_col::VALUE_END][value_end] = m31(1);
        for (value_index, index) in (value_start..=value_end).enumerate() {
            columns[trace_col::VALUE_ACTIVE][index] = m31(1);
            columns[trace_col::VALUE_INDEX][index] = m31(value_index as u32);
        }
        Ok(Self {
            columns,
            inner_bytes,
        })
    }

    fn trace(&self, log_size: u32) -> Vec<Column> {
        self.columns
            .iter()
            .cloned()
            .map(|values| column(log_size, values))
            .collect()
    }
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(m31(value))
}

fn sum_bits<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |sum, (index, bit)| {
            sum + m31_const::<E>(1u32 << index) * bit.clone()
        })
}

fn parsed_tuple<E: EvalAtRow>(
    stream_id: u32,
    fields: [E::F; 10],
    argument: &[E::F; 4],
) -> [E::F; 15] {
    let [stream_index, byte, header, major, content_len, depth, parent, ordinal, map_key, map_value] =
        fields;
    [
        m31_const::<E>(stream_id),
        stream_index,
        byte,
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
    ]
}

#[derive(Clone)]
struct MdocPrivateItemEval {
    log_size: u32,
    field_ids: MdocPrivateItemFieldIds,
    item_fields: FieldBytesRelation,
    outer_parsed: ParsedCborByteRelation,
    inner_parsed: ParsedCborByteRelation,
    inner_raw: FieldBytesRelation,
    digest_id: MdocPrivateDigestIdRelation,
    key_relation: MdocPrivateItemKeyRelation,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

impl FrameworkEval for MdocPrivateItemEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let last = eval.get_preprocessed_column(preprocessed_id(self.log_size, "last"));
        let prefix: [E::F; OUTER_PREFIX_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(preprocessed_id(
                self.log_size,
                &format!("outer_prefix_{index}"),
            ))
        });
        let first = prefix[0].clone();
        let prefix_sum = prefix
            .iter()
            .cloned()
            .fold(m31_const::<E>(0), |sum, value| sum + value);
        let one = m31_const::<E>(1);
        let zero = m31_const::<E>(0);

        let [active, _active_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [outer, outer_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [inner, inner_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let outer_end = eval.next_trace_mask();
        let [inner_start, inner_start_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let inner_end = eval.next_trace_mask();
        let [stream_index, stream_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [inner_len, inner_len_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let raw_yield = eval.next_trace_mask();
        let raw_index = eval.next_trace_mask();

        let byte_window: [E::F; DIGEST_COPY_BYTES] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1, 2, 3, 4]);
        let byte = byte_window[0].clone();
        let header = eval.next_trace_mask();
        let major = eval.next_trace_mask();
        let argument: [E::F; 4] = std::array::from_fn(|_| eval.next_trace_mask());
        let content_len = eval.next_trace_mask();
        let depth = eval.next_trace_mask();
        let parent = eval.next_trace_mask();
        let ordinal = eval.next_trace_mask();
        let map_key = eval.next_trace_mask();
        let map_value = eval.next_trace_mask();

        let key_active: [[E::F; 2]; KEY_COUNT] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let key_start: [[E::F; 2]; KEY_COUNT] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let key_end: [E::F; KEY_COUNT] = std::array::from_fn(|_| eval.next_trace_mask());
        let key_seen: [[E::F; 2]; KEY_COUNT] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let [key_index, key_index_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let value_start: [[E::F; 2]; KEY_COUNT] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));

        let random_lower_bits: [E::F; RANDOM_BOUND_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let random_upper_bits: [E::F; RANDOM_BOUND_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let digest_start_kind: [E::F; 4] = std::array::from_fn(|_| eval.next_trace_mask());
        let digest_copy: [E::F; DIGEST_COPY_BYTES] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let digest_short_slack_bits: [E::F; 5] = std::array::from_fn(|_| eval.next_trace_mask());

        let [identifier_content_active, identifier_content_active_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let identifier_content_end = eval.next_trace_mask();
        let [identifier_content_index, identifier_content_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);

        let [element_value_active, element_value_active_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let element_value_end = eval.next_trace_mask();
        let [element_value_index, element_value_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);

        for selector in [
            active.clone(),
            outer.clone(),
            inner.clone(),
            outer_end.clone(),
            inner_start.clone(),
            inner_end.clone(),
            raw_yield.clone(),
            identifier_content_active.clone(),
            identifier_content_end.clone(),
            element_value_active.clone(),
            element_value_end.clone(),
        ]
        .into_iter()
        .chain(key_active.iter().flat_map(|pair| [pair[0].clone()]))
        .chain(key_start.iter().flat_map(|pair| [pair[0].clone()]))
        .chain(key_end.iter().cloned())
        .chain(key_seen.iter().flat_map(|pair| [pair[0].clone()]))
        .chain(value_start.iter().flat_map(|pair| [pair[0].clone()]))
        .chain(digest_start_kind.iter().cloned())
        .chain(random_lower_bits.iter().cloned())
        .chain(random_upper_bits.iter().cloned())
        .chain(digest_short_slack_bits.iter().cloned())
        {
            eval.add_constraint(selector.clone() * (selector - one.clone()));
        }

        eval.add_constraint(active.clone() - outer.clone() - inner.clone());
        eval.add_constraint(first.clone() * (outer.clone() - one.clone()));
        eval.add_constraint(first.clone() * stream_index.clone());
        eval.add_constraint(last.clone() * outer.clone());
        eval.add_constraint(last.clone() * inner.clone());
        eval.add_constraint(outer_end.clone() * (one.clone() - outer.clone()));
        eval.add_constraint(inner_start.clone() * (one.clone() - inner.clone()));
        eval.add_constraint(inner_end.clone() * (one.clone() - inner.clone()));
        eval.add_constraint(outer_next - outer.clone() + outer_end.clone() - last.clone());
        eval.add_constraint(
            inner_next - inner.clone() - inner_start_next.clone() + inner_end.clone(),
        );
        eval.add_constraint(inner_start_next - outer_end.clone());
        eval.add_constraint(
            (outer.clone() - outer_end.clone())
                * (stream_index_next.clone() - stream_index.clone() - one.clone()),
        );
        eval.add_constraint(inner_start.clone() * stream_index.clone());
        eval.add_constraint(
            (inner.clone() - inner_end.clone())
                * (stream_index_next - stream_index.clone() - one.clone()),
        );
        eval.add_constraint(
            (active.clone() - inner_end.clone()) * (inner_len_next - inner_len.clone()),
        );
        eval.add_constraint(raw_yield.clone() - outer.clone() * (one.clone() - prefix_sum.clone()));
        eval.add_constraint(
            raw_yield.clone()
                * (raw_index.clone() + m31_const::<E>(OUTER_PREFIX_BYTES as u32)
                    - stream_index.clone()),
        );
        eval.add_constraint(outer_end.clone() * (raw_yield.clone() - one.clone()));
        eval.add_constraint(
            outer_end.clone() * (raw_index.clone() + one.clone() - inner_len.clone()),
        );
        eval.add_constraint(
            inner_end.clone() * (stream_index.clone() + one.clone() - inner_len.clone()),
        );

        let pin = |eval: &mut E, gate: E::F, value: E::F, expected: u32| {
            eval.add_constraint(gate * (value - m31_const::<E>(expected)));
        };
        for gate in &prefix {
            eval.add_constraint(gate.clone() * (outer.clone() - one.clone()));
        }
        pin(&mut eval, prefix[0].clone(), byte.clone(), 0xd8);
        pin(&mut eval, prefix[0].clone(), header.clone(), 1);
        pin(&mut eval, prefix[0].clone(), major.clone(), 6);
        pin(&mut eval, prefix[0].clone(), argument[0].clone(), 24);
        pin(&mut eval, prefix[0].clone(), depth.clone(), 0);
        pin(&mut eval, prefix[0].clone(), parent.clone(), 0);
        pin(&mut eval, prefix[0].clone(), ordinal.clone(), 0);
        pin(&mut eval, prefix[0].clone(), map_key.clone(), 0);
        pin(&mut eval, prefix[0].clone(), map_value.clone(), 0);
        pin(&mut eval, prefix[1].clone(), byte.clone(), 0x18);
        pin(&mut eval, prefix[1].clone(), header.clone(), 0);
        pin(&mut eval, prefix[2].clone(), byte.clone(), 0x58);
        pin(&mut eval, prefix[2].clone(), header.clone(), 1);
        pin(&mut eval, prefix[2].clone(), major.clone(), 2);
        eval.add_constraint(prefix[2].clone() * (content_len.clone() - inner_len.clone()));
        pin(&mut eval, prefix[2].clone(), depth.clone(), 1);
        pin(&mut eval, prefix[2].clone(), parent.clone(), 0);
        pin(&mut eval, prefix[2].clone(), ordinal.clone(), 0);
        eval.add_constraint(prefix[3].clone() * (byte.clone() - inner_len.clone()));
        pin(&mut eval, prefix[3].clone(), header.clone(), 0);

        pin(&mut eval, inner_start.clone(), byte.clone(), 0xa4);
        pin(&mut eval, inner_start.clone(), header.clone(), 1);
        pin(&mut eval, inner_start.clone(), major.clone(), 5);
        pin(&mut eval, inner_start.clone(), argument[0].clone(), 4);
        for limb in &argument[1..] {
            pin(&mut eval, inner_start.clone(), limb.clone(), 0);
        }
        pin(&mut eval, inner_start.clone(), depth.clone(), 0);
        pin(&mut eval, inner_start.clone(), parent.clone(), 0);
        pin(&mut eval, inner_start.clone(), ordinal.clone(), 0);
        pin(&mut eval, inner_start.clone(), map_key.clone(), 0);
        pin(&mut eval, inner_start.clone(), map_value.clone(), 0);

        let key_active_sum = key_active
            .iter()
            .fold(zero.clone(), |sum, pair| sum + pair[0].clone());
        eval.add_constraint(key_active_sum.clone() * (key_active_sum.clone() - one.clone()));
        let key_start_next_sum = key_start
            .iter()
            .fold(zero.clone(), |sum, pair| sum + pair[1].clone());
        for kind in 0..KEY_COUNT {
            let encoded_len = KEY_LABELS[kind].len() + 1;
            eval.add_constraint(
                key_start[kind][0].clone() * (one.clone() - key_active[kind][0].clone()),
            );
            eval.add_constraint(
                key_end[kind].clone() * (one.clone() - key_active[kind][0].clone()),
            );
            eval.add_constraint(
                key_active[kind][1].clone()
                    - key_active[kind][0].clone()
                    - key_start[kind][1].clone()
                    + key_end[kind].clone(),
            );
            eval.add_constraint(key_start[kind][0].clone() * key_index.clone());
            eval.add_constraint(
                (key_active[kind][0].clone() - key_end[kind].clone())
                    * (key_index_next.clone() - key_index.clone() - one.clone()),
            );
            eval.add_constraint(
                key_end[kind].clone()
                    * (key_index.clone() - m31_const::<E>((encoded_len - 1) as u32)),
            );
            eval.add_constraint(
                (inner.clone() - inner_end.clone())
                    * (key_seen[kind][1].clone()
                        - key_seen[kind][0].clone()
                        - key_start[kind][1].clone()),
            );
            eval.add_constraint(inner_start.clone() * key_seen[kind][0].clone());
            eval.add_constraint(inner_end.clone() * (key_seen[kind][0].clone() - one.clone()));
            pin(&mut eval, key_start[kind][0].clone(), header.clone(), 1);
            pin(&mut eval, key_start[kind][0].clone(), major.clone(), 3);
            pin(
                &mut eval,
                key_start[kind][0].clone(),
                content_len.clone(),
                KEY_LABELS[kind].len() as u32,
            );
            pin(&mut eval, key_start[kind][0].clone(), depth.clone(), 1);
            pin(&mut eval, key_start[kind][0].clone(), parent.clone(), 0);
            pin(&mut eval, key_start[kind][0].clone(), map_key.clone(), 1);
            pin(&mut eval, key_start[kind][0].clone(), map_value.clone(), 0);
            eval.add_constraint(
                (key_active[kind][0].clone() - key_start[kind][0].clone()) * header.clone(),
            );
            eval.add_constraint(value_start[kind][1].clone() - key_end[kind].clone());
            eval.add_constraint(value_start[kind][0].clone() * (one.clone() - inner.clone()));
            pin(&mut eval, value_start[kind][0].clone(), header.clone(), 1);
            pin(&mut eval, value_start[kind][0].clone(), depth.clone(), 1);
            pin(&mut eval, value_start[kind][0].clone(), parent.clone(), 0);
            pin(&mut eval, value_start[kind][0].clone(), map_key.clone(), 0);
            pin(
                &mut eval,
                value_start[kind][0].clone(),
                map_value.clone(),
                1,
            );
        }

        let random_start = value_start[KEY_RANDOM][0].clone();
        pin(&mut eval, random_start.clone(), major.clone(), 2);
        eval.add_constraint(
            random_start.clone()
                * (content_len.clone() - m31_const::<E>(16) - sum_bits::<E>(&random_lower_bits)),
        );
        eval.add_constraint(
            random_start
                * (content_len.clone() + sum_bits::<E>(&random_upper_bits)
                    - m31_const::<E>(MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES as u32)),
        );

        let digest_start = digest_start_kind
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, value| sum + value);
        eval.add_constraint(digest_start.clone() - value_start[KEY_DIGEST_ID][0].clone());
        pin(&mut eval, digest_start.clone(), major.clone(), 0);
        pin(&mut eval, digest_start.clone(), argument[2].clone(), 0);
        pin(&mut eval, digest_start.clone(), argument[3].clone(), 0);
        let digest_lengths = [1usize, 2, 3, 5];
        let digest_headers = [None, Some(0x18), Some(0x19), Some(0x1a)];
        for (kind, &len) in digest_lengths.iter().enumerate() {
            if let Some(expected) = digest_headers[kind] {
                pin(
                    &mut eval,
                    digest_start_kind[kind].clone(),
                    byte.clone(),
                    expected,
                );
            } else {
                eval.add_constraint(
                    digest_start_kind[kind].clone() * (byte.clone() - argument[0].clone()),
                );
                eval.add_constraint(
                    digest_start_kind[kind].clone()
                        * (argument[0].clone() + sum_bits::<E>(&digest_short_slack_bits)
                            - m31_const::<E>(23)),
                );
                pin(
                    &mut eval,
                    digest_start_kind[kind].clone(),
                    argument[1].clone(),
                    0,
                );
            }
            for copy_index in 0..DIGEST_COPY_BYTES {
                if copy_index < len {
                    eval.add_constraint(
                        digest_start_kind[kind].clone()
                            * (digest_copy[copy_index].clone() - byte_window[copy_index].clone()),
                    );
                } else {
                    eval.add_constraint(
                        digest_start_kind[kind].clone() * digest_copy[copy_index].clone(),
                    );
                }
            }
        }
        // The fixed profile accepts only one-, two-, and three-byte IDs.
        eval.add_constraint(digest_start_kind[3].clone());
        pin(&mut eval, digest_start.clone(), argument[1].clone(), 0);

        let identifier_start = value_start[KEY_ELEMENT_IDENTIFIER][0].clone();
        pin(
            &mut eval,
            identifier_start.clone(),
            byte.clone(),
            0x60 + CANONICAL_ELEMENT_IDENTIFIER.len() as u32,
        );
        pin(&mut eval, identifier_start.clone(), major.clone(), 3);
        pin(
            &mut eval,
            identifier_start.clone(),
            content_len.clone(),
            CANONICAL_ELEMENT_IDENTIFIER.len() as u32,
        );
        eval.add_constraint(
            identifier_content_active_next
                - identifier_content_active.clone()
                - identifier_start.clone()
                + identifier_content_end.clone(),
        );
        eval.add_constraint(
            identifier_content_end.clone() * (one.clone() - identifier_content_active.clone()),
        );
        eval.add_constraint(identifier_start.clone() * identifier_content_active.clone());
        eval.add_constraint(identifier_start * identifier_content_index_next.clone());
        eval.add_constraint(
            (identifier_content_active.clone() - identifier_content_end.clone())
                * (identifier_content_index_next - identifier_content_index.clone() - one.clone()),
        );
        eval.add_constraint(
            identifier_content_end.clone()
                * (identifier_content_index.clone()
                    - m31_const::<E>((CANONICAL_ELEMENT_IDENTIFIER.len() - 1) as u32)),
        );

        let element_value_start = value_start[KEY_ELEMENT_VALUE][0].clone();
        eval.add_constraint(
            element_value_active_next
                - element_value_active.clone()
                - value_start[KEY_ELEMENT_VALUE][1].clone()
                + element_value_end.clone(),
        );
        eval.add_constraint(
            element_value_start.clone() * (one.clone() - element_value_active.clone()),
        );
        eval.add_constraint(
            element_value_end.clone() * (one.clone() - element_value_active.clone()),
        );
        eval.add_constraint(
            element_value_end.clone()
                - element_value_active.clone() * (inner_end.clone() + key_start_next_sum.clone()),
        );
        eval.add_constraint(element_value_start * element_value_index.clone());
        eval.add_constraint(
            (element_value_active.clone() - element_value_end.clone())
                * (element_value_index_next - element_value_index.clone() - one.clone()),
        );

        let outer_tuple = parsed_tuple::<E>(
            self.field_ids.outer_stream,
            [
                stream_index.clone(),
                byte.clone(),
                header.clone(),
                major.clone(),
                content_len.clone(),
                depth.clone(),
                parent.clone(),
                ordinal.clone(),
                map_key.clone(),
                map_value.clone(),
            ],
            &argument,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.outer_parsed,
            E::EF::from(outer.clone()),
            &outer_tuple,
        ));
        let inner_tuple = parsed_tuple::<E>(
            self.field_ids.inner_stream,
            [
                stream_index,
                byte.clone(),
                header,
                major,
                content_len,
                depth,
                parent,
                ordinal,
                map_key,
                map_value,
            ],
            &argument,
        );
        eval.add_to_relation(RelationEntry::new(
            &self.inner_parsed,
            E::EF::from(inner),
            &inner_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.inner_raw,
            -E::EF::from(raw_yield),
            &[
                m31_const::<E>(self.field_ids.inner_stream),
                raw_index,
                byte.clone(),
            ],
        ));
        let key_kind = key_active
            .iter()
            .enumerate()
            .fold(zero, |sum, (kind, pair)| {
                sum + m31_const::<E>((kind + 1) as u32) * pair[0].clone()
            });
        eval.add_to_relation(RelationEntry::new(
            &self.key_relation,
            E::EF::from(key_active_sum),
            &[key_kind, key_index, byte.clone()],
        ));
        for (kind, label) in KEY_LABELS.iter().enumerate() {
            let encoded = std::iter::once(0x60 + label.len() as u8).chain(label.iter().copied());
            for (index, byte) in encoded.enumerate() {
                eval.add_to_relation(RelationEntry::new(
                    &self.key_relation,
                    -E::EF::from(first.clone()),
                    &[
                        m31_const::<E>((kind + 1) as u32),
                        m31_const::<E>(index as u32),
                        m31_const::<E>(u32::from(byte)),
                    ],
                ));
            }
        }
        let encoding_len = digest_start_kind
            .iter()
            .zip([1u32, 2, 3, 5])
            .fold(m31_const::<E>(0), |sum, (selector, len)| {
                sum + m31_const::<E>(len) * selector.clone()
            });
        eval.add_to_relation(RelationEntry::new(
            &self.digest_id,
            -E::EF::from(digest_start),
            &[
                encoding_len,
                digest_copy[0].clone(),
                digest_copy[1].clone(),
                digest_copy[2].clone(),
                digest_copy[3].clone(),
                digest_copy[4].clone(),
                argument[0].clone(),
                argument[1].clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.item_fields,
            -E::EF::from(identifier_content_active),
            &[
                m31_const::<E>(self.field_ids.element_identifier),
                identifier_content_index,
                byte.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.item_fields,
            -E::EF::from(element_value_active),
            &[
                m31_const::<E>(self.field_ids.element_value),
                element_value_index,
                byte,
            ],
        ));
        for (field_id, index, byte) in ts13_semantic_tuples(self.field_ids) {
            eval.add_to_relation(RelationEntry::new(
                &self.item_fields,
                E::EF::from(first.clone()),
                &[
                    m31_const::<E>(field_id),
                    m31_const::<E>(index as u32),
                    m31_const::<E>(u32::from(byte)),
                ],
            ));
        }
        // Main claimed-sum blinder is always the final interaction site.
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn packed_parsed_denominator(
    relation: &ParsedCborByteRelation,
    stream_id: u32,
    base: &[Column],
    row: usize,
) -> PackedQM31 {
    relation.combine(&[
        PackedM31::broadcast(m31(stream_id)),
        base[trace_col::STREAM_INDEX].data[row],
        base[trace_col::BYTE].data[row],
        base[trace_col::HEADER].data[row],
        base[trace_col::MAJOR].data[row],
        base[trace_col::ARGUMENT].data[row],
        base[trace_col::ARGUMENT + 1].data[row],
        base[trace_col::ARGUMENT + 2].data[row],
        base[trace_col::ARGUMENT + 3].data[row],
        base[trace_col::CONTENT_LEN].data[row],
        base[trace_col::DEPTH].data[row],
        base[trace_col::PARENT].data[row],
        base[trace_col::ORDINAL].data[row],
        base[trace_col::MAP_KEY].data[row],
        base[trace_col::MAP_VALUE].data[row],
    ])
}

#[allow(clippy::too_many_arguments)]
fn interaction_trace(
    witness: &MdocPrivateItemWitness,
    log_size: u32,
    field_ids: MdocPrivateItemFieldIds,
    item_fields: &FieldBytesRelation,
    outer_parsed: &ParsedCborByteRelation,
    inner_parsed: &ParsedCborByteRelation,
    inner_raw: &FieldBytesRelation,
    digest_id: &MdocPrivateDigestIdRelation,
    key_relation: &MdocPrivateItemKeyRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<Column>, QM31) {
    let base = witness.trace(log_size);
    let preprocessed = preprocessed_columns(log_size);
    let packed_rows = 1usize << (log_size - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(KEY_ENCODED_BYTES + 9 + CANONICAL_SEMANTIC_TUPLES);
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    PackedQM31::from(base[trace_col::OUTER].data[row]),
                    packed_parsed_denominator(outer_parsed, field_ids.outer_stream, &base, row),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    PackedQM31::from(base[trace_col::INNER].data[row]),
                    packed_parsed_denominator(inner_parsed, field_ids.inner_stream, &base, row),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    -PackedQM31::from(base[trace_col::RAW_YIELD].data[row]),
                    inner_raw.combine(&[
                        PackedM31::broadcast(m31(field_ids.inner_stream)),
                        base[trace_col::RAW_INDEX].data[row],
                        base[trace_col::BYTE].data[row],
                    ]),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                let key_active = (0..KEY_COUNT).fold(PackedM31::broadcast(m31(0)), |sum, kind| {
                    sum + base[trace_col::KEY_ACTIVE + kind].data[row]
                });
                let key_kind = (0..KEY_COUNT).fold(PackedM31::broadcast(m31(0)), |sum, kind| {
                    sum + base[trace_col::KEY_ACTIVE + kind].data[row]
                        * PackedM31::broadcast(m31((kind + 1) as u32))
                });
                (
                    PackedQM31::from(key_active),
                    key_relation.combine(&[
                        key_kind,
                        base[trace_col::KEY_INDEX].data[row],
                        base[trace_col::BYTE].data[row],
                    ]),
                )
            })
            .collect(),
    );
    for (kind, label) in KEY_LABELS.iter().enumerate() {
        let encoded = std::iter::once(0x60 + label.len() as u8).chain(label.iter().copied());
        for (index, byte) in encoded.enumerate() {
            sites.push(
                (0..packed_rows)
                    .map(|row| {
                        (
                            -PackedQM31::from(preprocessed[PP_OUTER_PREFIX_START].data[row]),
                            key_relation.combine(&[
                                PackedM31::broadcast(m31((kind + 1) as u32)),
                                PackedM31::broadcast(m31(index as u32)),
                                PackedM31::broadcast(m31(u32::from(byte))),
                            ]),
                        )
                    })
                    .collect(),
            );
        }
    }
    sites.push(
        (0..packed_rows)
            .map(|row| {
                let digest_start = (0..4).fold(PackedM31::broadcast(m31(0)), |sum, kind| {
                    sum + base[trace_col::DIGEST_START_KIND + kind].data[row]
                });
                let encoding_len = (0..4).zip([1u32, 2, 3, 5]).fold(
                    PackedM31::broadcast(m31(0)),
                    |sum, (kind, len)| {
                        sum + base[trace_col::DIGEST_START_KIND + kind].data[row]
                            * PackedM31::broadcast(m31(len))
                    },
                );
                (
                    -PackedQM31::from(digest_start),
                    digest_id.combine(&[
                        encoding_len,
                        base[trace_col::DIGEST_COPY].data[row],
                        base[trace_col::DIGEST_COPY + 1].data[row],
                        base[trace_col::DIGEST_COPY + 2].data[row],
                        base[trace_col::DIGEST_COPY + 3].data[row],
                        base[trace_col::DIGEST_COPY + 4].data[row],
                        base[trace_col::ARGUMENT].data[row],
                        base[trace_col::ARGUMENT + 1].data[row],
                    ]),
                )
            })
            .collect(),
    );
    for (selector, field_id, index_column, byte_column) in [
        (
            trace_col::IDENTIFIER_CONTENT_ACTIVE,
            field_ids.element_identifier,
            trace_col::IDENTIFIER_CONTENT_INDEX,
            trace_col::BYTE,
        ),
        (
            trace_col::VALUE_ACTIVE,
            field_ids.element_value,
            trace_col::VALUE_INDEX,
            trace_col::BYTE,
        ),
    ] {
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    (
                        -PackedQM31::from(base[selector].data[row]),
                        item_fields.combine(&[
                            PackedM31::broadcast(m31(field_id)),
                            base[index_column].data[row],
                            base[byte_column].data[row],
                        ]),
                    )
                })
                .collect(),
        );
    }
    for (field_id, index, byte) in ts13_semantic_tuples(field_ids) {
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    (
                        PackedQM31::from(preprocessed[PP_OUTER_PREFIX_START].data[row]),
                        item_fields.combine(&[
                            PackedM31::broadcast(m31(field_id)),
                            PackedM31::broadcast(m31(index as u32)),
                            PackedM31::broadcast(m31(u32::from(byte))),
                        ]),
                    )
                })
                .collect(),
        );
    }
    let blinder_numerator = PackedQM31::broadcast(blinder_m);
    let blinder_denominator = blinder_denominator(blinder_relation, blinder_v);
    sites.push(vec![(blinder_numerator, blinder_denominator); packed_rows]);

    let mut logup = LogupTraceGenerator::new(log_size);
    let mut site = 0;
    while site + 1 < sites.len() {
        let left = &sites[site];
        let right = &sites[site + 1];
        logup.col_from_iter((0..packed_rows).map(|row| {
            let (left_num, left_den) = left[row];
            let (right_num, right_den) = right[row];
            (
                left_num * right_den + right_num * left_den,
                left_den * right_den,
            )
        }));
        site += 2;
    }
    if site < sites.len() {
        logup.col_from_iter((0..packed_rows).map(|row| sites[site][row]));
    }
    logup.finalize_last()
}

/// Private semantic bridge for one `IssuerSignedItemBytes`.
///
/// Relation polarity is from this component:
///
/// - `outer_parsed` and `inner_parsed`: positive consumers of the two CBOR
///   parsers;
/// - `inner_raw`: negative provider for the raw inner parser;
/// - `digest_id`: negative provider for the MSO `valueDigests` scan;
/// - `item_fields`: negative provider of the identifier and value bytes. The
///   component also provides the fixed `age_over_18 = true` tuples.
///
/// The SHA full-padded-stream relation supplies the outer parser. The combined
/// proof binds every private SHA-padded byte. Tree zero does not contain the raw
/// item length, random length, offsets, digest ID, or contents.
pub(crate) struct MdocPrivateItemBind {
    log_size: u32,
    field_ids: MdocPrivateItemFieldIds,
    handles: MdocPrivateItemHandles,
    witness: Option<MdocPrivateItemWitness>,
    key_relation: Option<MdocPrivateItemKeyRelation>,
    inner_raw_relation: Option<FieldBytesRelation>,
    digest_id_relation: Option<MdocPrivateDigestIdRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocPrivateItemInteractionClaim>,
    component: Option<PrivateItemComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocPrivateItemBind {
    pub(crate) fn new(
        private_input: MdocPrivateItemPrivateInput,
        field_ids: MdocPrivateItemFieldIds,
        handles: MdocPrivateItemHandles,
    ) -> Result<Self, MdocPrivateItemError> {
        let log_size = item_log_size();
        let witness = MdocPrivateItemWitness::new(private_input, log_size)?;
        Ok(Self {
            log_size,
            field_ids,
            handles,
            witness: Some(witness),
            key_relation: None,
            inner_raw_relation: None,
            digest_id_relation: None,
            blinder_relation: None,
            interaction_claim: None,
            component: None,
            blinder_component: None,
        })
    }

    pub(crate) fn verifier(
        field_ids: MdocPrivateItemFieldIds,
        handles: MdocPrivateItemHandles,
        interaction_claim: MdocPrivateItemInteractionClaim,
    ) -> Self {
        Self {
            log_size: item_log_size(),
            field_ids,
            handles,
            witness: None,
            key_relation: None,
            inner_raw_relation: None,
            digest_id_relation: None,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn log_size(&self) -> u32 {
        self.log_size
    }

    pub(crate) fn outer_parser_log_size(&self) -> u32 {
        parser_log_size(MDOC_PRIVATE_ITEM_PADDED_BYTES)
            .expect("the fixed private item has a parser domain")
    }

    pub(crate) fn inner_parser_log_size(&self) -> u32 {
        // The inner item is at most 192 bytes. The parser adds 256 inactive
        // filler rows and uses a minimum log size of nine.
        parser_log_size(MDOC_PRIVATE_ITEM_MAX_INNER_BYTES)
            .expect("private item cap has a parser domain")
    }

    pub(crate) fn inner_bytes(&self) -> &[u8] {
        self.witness
            .as_ref()
            .expect("private item prover has a witness")
            .inner_bytes
            .as_slice()
    }

    pub(crate) fn claim(&self) -> &MdocPrivateItemInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("private item interaction claim is set")
    }

    fn item_fields(&self) -> FieldBytesRelation {
        self.handles.item_fields.get()
    }

    fn outer_parsed(&self) -> ParsedCborByteRelation {
        self.handles.outer_parsed.get()
    }

    fn inner_parsed(&self) -> ParsedCborByteRelation {
        self.handles.inner_parsed.get()
    }

    fn inner_raw(&self) -> FieldBytesRelation {
        self.inner_raw_relation
            .clone()
            .expect("private item inner-raw relation is drawn")
    }

    fn digest_id(&self) -> MdocPrivateDigestIdRelation {
        self.digest_id_relation
            .clone()
            .expect("private item digest-ID relation is drawn")
    }

    fn key_relation(&self) -> MdocPrivateItemKeyRelation {
        self.key_relation
            .clone()
            .expect("private item key relation is drawn")
    }

    fn main_interaction_sites(&self) -> usize {
        // Count the outer, inner, and raw-inner relations.
        // Count the key witness and 47 key constants.
        // Count the digest, identifier, and value relations.
        // Count the fixed semantics.
        // Count the final blinder.
        KEY_ENCODED_BYTES + 8 + CANONICAL_SEMANTIC_TUPLES
    }
}

impl Air for MdocPrivateItemBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(MDOC_PRIVATE_ITEM_DOMAIN);
        channel.mix_u64(MDOC_PRIVATE_ITEM_VERSION);
        channel.mix_u64(MDOC_PRIVATE_ITEM_TRANSCRIPT_TAG);
        channel.mix_u64(MDOC_PRIVATE_ITEM_TRANSCRIPT_ATTRIBUTE_INDEX);
        channel.mix_u64(MDOC_PRIVATE_ITEM_PADDED_BYTES as u64);
        channel.mix_u64(u64::from(self.log_size));
        channel.mix_u64(u64::from(self.outer_parser_log_size()));
        channel.mix_u64(u64::from(self.inner_parser_log_size()));
        channel.mix_u64(MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES as u64);
        channel.mix_u64(CANONICAL_ELEMENT_IDENTIFIER.len() as u64);
        channel.mix_u64(CANONICAL_ELEMENT_VALUE.len() as u64);
        channel.mix_u64(u64::from(MDOC_PRIVATE_ITEM_DIGEST_ID_MAX));
        channel.mix_u64(u64::from(self.field_ids.outer_stream));
        channel.mix_u64(u64::from(self.field_ids.inner_stream));
        channel.mix_u64(u64::from(self.field_ids.element_identifier));
        channel.mix_u64(u64::from(self.field_ids.element_value));
        channel.mix_u64(self.main_interaction_sites() as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        assert!(
            !self.handles.inner_raw.is_set(),
            "private item bind owns a fresh inner-raw relation"
        );
        let inner_raw = FieldBytesRelation::draw(channel);
        self.handles.inner_raw.set(inner_raw.clone());
        self.inner_raw_relation = Some(inner_raw);

        assert!(
            !self.handles.digest_id.is_set(),
            "private item bind owns a fresh digest-ID relation"
        );
        let digest_id = MdocPrivateDigestIdRelation::draw(channel);
        self.handles.digest_id.set(digest_id.clone());
        self.digest_id_relation = Some(digest_id);

        self.key_relation = Some(MdocPrivateItemKeyRelation::draw(channel));
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.log_size; PREPROCESSED_COLS],
            trace: vec![self.log_size; trace_col::COUNT],
            interaction: vec![
                self.log_size;
                self.main_interaction_sites().div_ceil(2) * SECURE_EXTENSION_DEGREE
                    + SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(self.log_size)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns(self.log_size))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private item blinder relation is drawn");
        self.component = Some(PrivateItemComponent::new(
            allocator,
            MdocPrivateItemEval {
                log_size: self.log_size,
                field_ids: self.field_ids,
                item_fields: self.item_fields(),
                outer_parsed: self.outer_parsed(),
                inner_parsed: self.inner_parsed(),
                inner_raw: self.inner_raw(),
                digest_id: self.digest_id(),
                key_relation: self.key_relation(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: self.log_size,
                relation: blinder_relation,
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
                .expect("private item component is built"),
            self.blinder_component
                .as_ref()
                .expect("private item blinder component is built"),
        ]
    }
}

impl AirProver for MdocPrivateItemBind {
    fn max_log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tree, &preprocessed_ids(self.log_size));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_private_item_bind::MdocPrivateItemBind",
            &preprocessed_ids(self.log_size),
            &preprocessed_columns(self.log_size),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tree: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = preprocessed_ids(self.log_size);
        let all_columns = preprocessed_columns(self.log_size);
        tree.extend_evals(
            selected_ids
                .iter()
                .map(|id| {
                    all_ids
                        .iter()
                        .position(|candidate| candidate == id)
                        .map(|index| all_columns[index].clone())
                        .expect("unexpected private item preprocessed selection")
                })
                .collect(),
        );
    }

    fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tree.extend_evals(
            self.witness
                .as_ref()
                .expect("private item prover has a witness")
                .trace(self.log_size),
        );
    }

    fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private item blinder relation is drawn");
        let (trace, claimed_sum) = interaction_trace(
            self.witness
                .as_ref()
                .expect("private item prover has a witness"),
            self.log_size,
            self.field_ids,
            &self.item_fields(),
            &self.outer_parsed(),
            &self.inner_parsed(),
            &self.inner_raw(),
            &self.digest_id(),
            &self.key_relation(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tree.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) =
            blinder_counter_interaction(self.log_size, &blinder_relation, blinder_v, blinder_m);
        tree.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocPrivateItemInteractionClaim {
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
                .expect("private item component is built"),
            self.blinder_component
                .as_ref()
                .expect("private item blinder component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CANONICAL_ORDER: [usize; KEY_COUNT] = [
        KEY_RANDOM,
        KEY_DIGEST_ID,
        KEY_ELEMENT_VALUE,
        KEY_ELEMENT_IDENTIFIER,
    ];

    fn qm31(value: u32) -> QM31 {
        QM31::from(m31(value))
    }

    fn test_claim() -> MdocPrivateItemInteractionClaim {
        MdocPrivateItemInteractionClaim {
            claimed_sum: qm31(1),
            blinder_v: qm31(2),
            blinder_m: qm31(3),
            blinder_claimed_sum: qm31(4),
        }
    }

    fn field_ids() -> MdocPrivateItemFieldIds {
        MdocPrivateItemFieldIds {
            outer_stream: 700,
            inner_stream: 701,
            element_identifier: 702,
            element_value: 703,
        }
    }

    fn push_head(output: &mut Vec<u8>, major: u8, value: usize) {
        match value {
            0..=23 => output.push((major << 5) | value as u8),
            24..=255 => {
                output.push((major << 5) | 24);
                output.push(value as u8);
            }
            _ => panic!("test CBOR length {value} is unsupported"),
        }
    }

    fn push_text(output: &mut Vec<u8>, value: &[u8]) {
        push_head(output, 3, value.len());
        output.extend_from_slice(value);
    }

    fn push_bytes(output: &mut Vec<u8>, value: &[u8]) {
        push_head(output, 2, value.len());
        output.extend_from_slice(value);
    }

    fn canonical_uint(value: u32) -> Vec<u8> {
        match value {
            0..=23 => vec![value as u8],
            24..=0xff => vec![0x18, value as u8],
            0x100..=0xffff => {
                let bytes = (value as u16).to_be_bytes();
                vec![0x19, bytes[0], bytes[1]]
            }
            _ => {
                let bytes = value.to_be_bytes();
                vec![0x1a, bytes[0], bytes[1], bytes[2], bytes[3]]
            }
        }
    }

    fn inner_item_with_digest_encoding(
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_encoding: &[u8],
        identifier: &[u8],
        element_value: &[u8],
    ) -> Vec<u8> {
        let mut inner = vec![0xa4];
        for kind in order {
            push_text(&mut inner, KEY_LABELS[kind]);
            match kind {
                KEY_RANDOM => {
                    let random = (0..random_len)
                        .map(|index| 0x80u8.wrapping_add(index as u8))
                        .collect::<Vec<_>>();
                    push_bytes(&mut inner, &random);
                }
                KEY_DIGEST_ID => inner.extend_from_slice(digest_encoding),
                KEY_ELEMENT_VALUE => inner.extend_from_slice(element_value),
                KEY_ELEMENT_IDENTIFIER => push_text(&mut inner, identifier),
                _ => unreachable!("all item fields are covered"),
            }
        }
        inner
    }

    fn inner_item(
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Vec<u8> {
        inner_item_with_digest_encoding(
            order,
            random_len,
            &canonical_uint(digest_id),
            identifier,
            element_value,
        )
    }

    fn wrap_and_pad(inner: &[u8]) -> Vec<u8> {
        let mut outer = vec![0xd8, 0x18];
        push_bytes(&mut outer, inner);
        stwo_sha256::native::pad_message(&outer)
    }

    fn padded_item(
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Vec<u8> {
        wrap_and_pad(&inner_item(
            order,
            random_len,
            digest_id,
            identifier,
            element_value,
        ))
    }

    fn test_bind_with_order(
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        let padded = padded_item(order, random_len, digest_id, identifier, element_value);
        MdocPrivateItemBind::new(
            MdocPrivateItemPrivateInput::new(padded),
            field_ids(),
            MdocPrivateItemHandles::fresh(SharedFieldRelation::new()),
        )
    }

    fn test_bind(digest_id: u32) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        test_bind_with_order(
            CANONICAL_ORDER,
            16,
            digest_id,
            CANONICAL_ELEMENT_IDENTIFIER,
            CANONICAL_ELEMENT_VALUE,
        )
    }

    fn all_key_orders() -> Vec<[usize; KEY_COUNT]> {
        let mut orders = Vec::with_capacity(24);
        for first in 0..KEY_COUNT {
            for second in 0..KEY_COUNT {
                for third in 0..KEY_COUNT {
                    for fourth in 0..KEY_COUNT {
                        let order = [first, second, third, fourth];
                        if (0..KEY_COUNT).all(|kind| order.contains(&kind)) {
                            orders.push(order);
                        }
                    }
                }
            }
        }
        orders
    }

    fn analyze_test_inner(
        random_len: usize,
        digest_encoding: &[u8],
        identifier: &[u8],
        value: &[u8],
    ) -> Result<ItemAnalysis, MdocPrivateItemError> {
        let inner = inner_item_with_digest_encoding(
            CANONICAL_ORDER,
            random_len,
            digest_encoding,
            identifier,
            value,
        );
        analyze_inner_bytes(&inner)
    }

    fn analyze_inner_bytes(inner: &[u8]) -> Result<ItemAnalysis, MdocPrivateItemError> {
        let witness = MdocCborWitness::new(inner, MdocCborInputMode::Raw)
            .map_err(MdocPrivateItemError::InnerParser)?;
        analyze_inner(inner, &witness.rows)
    }

    #[test]
    fn tag24_wrapper_reports_exact_rejection() {
        let cases = [
            (
                vec![0xd8, 0x17, 0x58, 0x01, 0xa0],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 0,
                    reason: MdocPrivateTag24WrapperReason::ExpectedTag24,
                },
            ),
            (
                vec![0xd8, 0x18, 0x58, 0x00, 0xa0],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 3,
                    reason: MdocPrivateTag24WrapperReason::ByteStringLengthMismatch {
                        declared: 0,
                        actual: 1,
                    },
                },
            ),
            (
                vec![0xd8, 0x18, 0x41, 0xa0],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 2,
                    reason: MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength {
                        additional: 1,
                    },
                },
            ),
            (
                vec![0xd8, 0x18, 0x58],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 3,
                    reason: MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
                },
            ),
        ];

        for (outer, expected) in cases {
            let padded = stwo_sha256::native::pad_message(&outer);
            assert_eq!(extract_outer_and_inner(&padded).unwrap_err(), expected);
        }
    }

    #[test]
    fn item_accepts_each_u16_digest_encoding() {
        for digest_id in [0, 23, 24, 255, 256, MDOC_PRIVATE_ITEM_DIGEST_ID_MAX] {
            let bind = test_bind(digest_id)
                .unwrap_or_else(|error| panic!("digest ID {digest_id} was rejected: {error}"));
            assert_eq!(
                bind.inner_bytes(),
                inner_item(
                    CANONICAL_ORDER,
                    16,
                    digest_id,
                    CANONICAL_ELEMENT_IDENTIFIER,
                    CANONICAL_ELEMENT_VALUE,
                )
            );
        }
    }

    #[test]
    fn item_accepts_all_key_orders_and_preserves_exact_bytes() {
        let orders = all_key_orders();
        assert_eq!(orders.len(), 24);
        for order in orders {
            let expected = inner_item(
                order,
                16,
                42,
                CANONICAL_ELEMENT_IDENTIFIER,
                CANONICAL_ELEMENT_VALUE,
            );
            let bind = test_bind_with_order(
                order,
                16,
                42,
                CANONICAL_ELEMENT_IDENTIFIER,
                CANONICAL_ELEMENT_VALUE,
            )
            .unwrap_or_else(|error| panic!("key order {order:?} was rejected: {error}"));
            assert_eq!(bind.inner_bytes(), expected);
        }
    }

    #[test]
    fn item_rejects_duplicate_missing_and_unknown_keys() {
        let duplicate = inner_item(
            [
                KEY_RANDOM,
                KEY_RANDOM,
                KEY_ELEMENT_VALUE,
                KEY_ELEMENT_IDENTIFIER,
            ],
            16,
            42,
            CANONICAL_ELEMENT_IDENTIFIER,
            CANONICAL_ELEMENT_VALUE,
        );
        assert_eq!(
            analyze_inner_bytes(&duplicate).err().unwrap(),
            MdocPrivateItemError::DuplicateKey("random")
        );

        let mut missing = inner_item(
            CANONICAL_ORDER,
            16,
            42,
            CANONICAL_ELEMENT_IDENTIFIER,
            CANONICAL_ELEMENT_VALUE,
        );
        let last_key_start = missing
            .windows(KEY_LABELS[KEY_ELEMENT_IDENTIFIER].len())
            .position(|window| window == KEY_LABELS[KEY_ELEMENT_IDENTIFIER])
            .expect("the final key is present")
            - 1;
        missing.truncate(last_key_start);
        missing[0] = 0xa3;
        assert_eq!(
            analyze_inner_bytes(&missing).err().unwrap(),
            MdocPrivateItemError::InvalidIssuerSignedItemRoot
        );

        let mut unknown = inner_item(
            CANONICAL_ORDER,
            16,
            42,
            CANONICAL_ELEMENT_IDENTIFIER,
            CANONICAL_ELEMENT_VALUE,
        );
        unknown[2] = b'R';
        assert_eq!(
            analyze_inner_bytes(&unknown).err().unwrap(),
            MdocPrivateItemError::InvalidIssuerSignedItemRoot
        );
    }

    #[test]
    fn item_rejects_wrong_semantics() {
        for identifier in [
            b"age_over_1".as_slice(),
            b"age_over_19".as_slice(),
            b"age_over_21".as_slice(),
        ] {
            assert_eq!(
                test_bind_with_order(CANONICAL_ORDER, 16, 0, identifier, CANONICAL_ELEMENT_VALUE,)
                    .err()
                    .unwrap(),
                MdocPrivateItemError::InvalidElementIdentifier
            );
        }

        for value in [vec![0xf4], vec![0xf6], vec![0x01], vec![0x81, 0xf5]] {
            assert_eq!(
                test_bind_with_order(CANONICAL_ORDER, 16, 0, CANONICAL_ELEMENT_IDENTIFIER, &value,)
                    .err()
                    .unwrap(),
                MdocPrivateItemError::InvalidElementValue
            );
        }
    }

    #[test]
    fn random_and_digest_bounds_are_exact() {
        assert_eq!(
            analyze_test_inner(
                15,
                &canonical_uint(0),
                CANONICAL_ELEMENT_IDENTIFIER,
                CANONICAL_ELEMENT_VALUE,
            )
            .err()
            .unwrap(),
            MdocPrivateItemError::InvalidRandom
        );
        assert_eq!(
            analyze_test_inner(
                129,
                &canonical_uint(0),
                CANONICAL_ELEMENT_IDENTIFIER,
                CANONICAL_ELEMENT_VALUE,
            )
            .err()
            .unwrap(),
            MdocPrivateItemError::InvalidRandom
        );
        assert_eq!(
            analyze_test_inner(
                128,
                &canonical_uint(MDOC_PRIVATE_ITEM_DIGEST_ID_MAX),
                CANONICAL_ELEMENT_IDENTIFIER,
                CANONICAL_ELEMENT_VALUE,
            )
            .unwrap()
            .digest_value,
            u64::from(MDOC_PRIVATE_ITEM_DIGEST_ID_MAX)
        );

        let too_large = MDOC_PRIVATE_ITEM_DIGEST_ID_MAX + 1;
        assert_eq!(
            analyze_test_inner(
                16,
                &canonical_uint(too_large),
                CANONICAL_ELEMENT_IDENTIFIER,
                CANONICAL_ELEMENT_VALUE,
            )
            .err()
            .unwrap(),
            MdocPrivateItemError::DigestIdOutOfRange {
                value: u64::from(too_large),
                max: MDOC_PRIVATE_ITEM_DIGEST_ID_MAX,
            }
        );
        assert!(analyze_test_inner(
            16,
            &[0x18, 0x17],
            CANONICAL_ELEMENT_IDENTIFIER,
            CANONICAL_ELEMENT_VALUE,
        )
        .is_err());
    }

    #[test]
    fn witness_exposes_only_fixed_semantic_bytes() {
        let bind = test_bind(42).unwrap();
        let witness = bind.witness.as_ref().unwrap();

        let identifier = (0..witness.columns[trace_col::ACTIVE].len())
            .filter(|&row| witness.columns[trace_col::IDENTIFIER_CONTENT_ACTIVE][row] == m31(1))
            .map(|row| {
                (
                    witness.columns[trace_col::IDENTIFIER_CONTENT_INDEX][row].0 as usize,
                    witness.columns[trace_col::BYTE][row].0 as u8,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            identifier,
            CANONICAL_ELEMENT_IDENTIFIER
                .iter()
                .copied()
                .enumerate()
                .collect::<Vec<_>>()
        );

        let value = (0..witness.columns[trace_col::ACTIVE].len())
            .filter(|&row| witness.columns[trace_col::VALUE_ACTIVE][row] == m31(1))
            .map(|row| {
                (
                    witness.columns[trace_col::VALUE_INDEX][row].0 as usize,
                    witness.columns[trace_col::BYTE][row].0 as u8,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(value, vec![(0, 0xf5)]);
    }

    #[test]
    fn prover_requires_the_fixed_padded_item_size() {
        let padded = padded_item(
            CANONICAL_ORDER,
            16,
            0,
            CANONICAL_ELEMENT_IDENTIFIER,
            CANONICAL_ELEMENT_VALUE,
        );
        let actual = padded.len();
        assert_eq!(actual, MDOC_PRIVATE_ITEM_PADDED_BYTES);
        let mut short = padded;
        short.pop();
        assert_eq!(
            MdocPrivateItemBind::new(
                MdocPrivateItemPrivateInput::new(short),
                field_ids(),
                MdocPrivateItemHandles::fresh(SharedFieldRelation::new()),
            )
            .err()
            .unwrap(),
            MdocPrivateItemError::PaddedLengthMismatch {
                expected: MDOC_PRIVATE_ITEM_PADDED_BYTES,
                actual: actual - 1,
            }
        );
    }

    #[test]
    fn verifier_layout_has_one_canonical_shape() {
        let bind = test_bind(7).unwrap();
        let verifier = MdocPrivateItemBind::verifier(
            field_ids(),
            MdocPrivateItemHandles::fresh(SharedFieldRelation::new()),
            test_claim(),
        );

        assert_eq!(verifier.log_size(), bind.log_size());
        assert_eq!(verifier.main_interaction_sites(), 67);
        assert_eq!(verifier.layout().preprocessed.len(), PREPROCESSED_COLS);
        assert_eq!(verifier.layout().trace.len(), trace_col::COUNT);
        assert_eq!(
            verifier.layout().interaction.len(),
            35 * SECURE_EXTENSION_DEGREE
        );
        assert_eq!(trace_col::COUNT, 80);
    }

    #[test]
    fn semantic_relation_constants_match_ts13() {
        assert_eq!(
            ts13_semantic_tuples(field_ids()).collect::<Vec<_>>(),
            CANONICAL_ELEMENT_IDENTIFIER
                .iter()
                .copied()
                .enumerate()
                .map(|(index, byte)| (field_ids().element_identifier, index, byte))
                .chain(
                    CANONICAL_ELEMENT_VALUE
                        .iter()
                        .copied()
                        .enumerate()
                        .map(|(index, byte)| (field_ids().element_value, index, byte)),
                )
                .collect::<Vec<_>>()
        );
    }
}
