//! Private `IssuerSignedItemBytes` semantic binding.
//!
//! The existing CBOR stream parsers prove the complete SHA-padded outer item
//! and its tag-24 inner map. This component consumes both parsed streams,
//! checks the four `IssuerSignedItem` fields without public offsets or lengths,
//! re-provides the semantic identifier/value windows on the existing
//! per-attribute [`FieldBytesRelation`], and yields one private canonical
//! digest-ID tuple for the MSO `valueDigests` scan. The frozen TS13 profile
//! closes its semantic field lookups in this component against the exact
//! `age_over_18 = true` request instead of adding another protocol module.

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
use crate::mdoc_country_code_table::{
    mdoc_country_code_alpha2_tuple, mdoc_country_code_numeric_dummy_tuple, MdocCountryCodeError,
    MdocCountryCodeRelation, MdocCountryCodeTuple, MdocCountryCodeUses,
    SharedMdocCountryCodeRelation,
};
use crate::mdoc_private_mso_bind::MdocPrivateMsoVersion;

pub(crate) const MDOC_PRIVATE_ITEM_PADDED_BUCKETS: [u16; 3] = [64, 128, 192];
pub(crate) const MDOC_PRIVATE_ITEM_MAX_ATTRIBUTES: usize = 4;
pub(crate) const MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES: usize = 128;
pub(crate) const MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES: usize = 64;
pub(crate) const MDOC_PRIVATE_ITEM_MAX_VALUE_BYTES: usize = 192;
pub(crate) const MDOC_PRIVATE_ITEM_MAX_NATIONALITY_MEMBERS: usize = 8;
pub(crate) const MDOC_PRIVATE_ITEM_PRODUCT_DIGEST_ID_MAX: u32 = u32::MAX;
pub(crate) const MDOC_PRIVATE_ITEM_TS13_DIGEST_ID_MAX: u32 = u16::MAX as u32;

const MDOC_PRIVATE_ITEM_VERSION: u64 = 1;
const MDOC_PRIVATE_ITEM_DOMAIN: u64 = 0x4d44_4f43_4954_454d;
const MDOC_PRIVATE_ITEM_BLIND_ROWS: usize = 256;
const OUTER_PREFIX_BYTES: usize = 4;
const PREPROCESSED_COLS: usize = 6;
const KEY_COUNT: usize = 4;
const DIGEST_COPY_BYTES: usize = 5;
const RANDOM_BOUND_BITS: usize = 8;
const IDENTIFIER_BOUND_BITS: usize = 7;
const BIRTH_DATE_PACKED_BYTES: usize = 4;
const BIRTH_DATE_TEXT_BYTES: usize = 10;
const BIRTH_DATE_DIGITS: usize = 8;
const BIRTH_DATE_DIGIT_BITS: usize = 4;
const NATIONALITY_BYTES: usize = 2;
const NATIONALITY_COUNT_BITS: usize = 3;
const CBOR_TAG_FULL_DATE: u32 = 1004;

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
const KEY_CANONICAL_CHILD_ORDINALS: [u32; KEY_COUNT] = [0, 2, 4, 6];
const KEY_ENCODED_BYTES: usize = (1 + 6) + (1 + 8) + (1 + 12) + (1 + 17);
const TS13_ELEMENT_IDENTIFIER: &[u8] = b"age_over_18";
const TS13_CANONICAL_ELEMENT_VALUE: &[u8] = &[0xf5];
const TS13_SEMANTIC_TUPLES: usize =
    TS13_ELEMENT_IDENTIFIER.len() + TS13_CANONICAL_ELEMENT_VALUE.len();

/// One private canonical digest-ID handoff:
/// `(encoding_len, b0, b1, b2, b3, b4, value_lo16, value_hi16, is_v2)`.
///
/// The private version bit must ride in this same tuple. A separate version
/// relation would let a prover pair one item's digest with the other MSO
/// version, breaking the binder → scanner → item soundness chain.
#[cfg(test)]
pub(crate) mod digest_id_tuple {
    pub(crate) const ENCODING_LEN: usize = 0;
    pub(crate) const BYTE_0: usize = 1;
    pub(crate) const VALUE_LO16: usize = 6;
    pub(crate) const VALUE_HI16: usize = 7;
    pub(crate) const IS_V2: usize = 8;
    pub(crate) const ARITY: usize = 9;
}

relation!(MdocPrivateDigestIdRelation, 9);
relation!(MdocPrivateItemKeyRelation, 3);

pub(crate) type SharedMdocPrivateDigestIdRelation = SharedRelation<MdocPrivateDigestIdRelation>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateItemProfile {
    /// Product profile. The private MSO version selects legacy v1 versus
    /// canonical v2 key ordering without entering public shape or transcript.
    Product,
    /// Dedicated TS13 canonical profile with its published `u16` digest cap.
    Ts13,
}

impl MdocPrivateItemProfile {
    fn transcript_tag(self) -> u64 {
        match self {
            Self::Product => 0,
            Self::Ts13 => 1,
        }
    }

    fn canonical_key_order(self) -> bool {
        matches!(self, Self::Ts13)
    }

    fn digest_id_max(self) -> u32 {
        match self {
            Self::Product => MDOC_PRIVATE_ITEM_PRODUCT_DIGEST_ID_MAX,
            Self::Ts13 => MDOC_PRIVATE_ITEM_TS13_DIGEST_ID_MAX,
        }
    }
}

/// The only verifier-known semantic choice for the private `elementValue`.
///
/// Every accepted representation inside one mode is private and pays the same
/// 154-column trace. Predicate modes always emit their normalized packed
/// bytes at index zero under `MdocPrivateItemFieldIds::element_value`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateItemRequestMode {
    ValueEquality,
    BirthDate,
    Nationality,
}

impl MdocPrivateItemRequestMode {
    fn transcript_tag(self) -> u64 {
        match self {
            Self::ValueEquality => 0,
            Self::BirthDate => 1,
            Self::Nationality => 2,
        }
    }

    fn normalized_len(self) -> Option<usize> {
        match self {
            Self::ValueEquality => None,
            Self::BirthDate => Some(BIRTH_DATE_PACKED_BYTES),
            Self::Nationality => Some(NATIONALITY_BYTES),
        }
    }
}

/// Prover-only item data. Nationality arrays carry the selected member index;
/// scalar nationality and all non-nationality modes must leave it absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateItemPrivateInput {
    pub(crate) padded_item: Vec<u8>,
    pub(crate) nationality_member_index: Option<u8>,
}

impl MdocPrivateItemPrivateInput {
    pub(crate) fn new(padded_item: Vec<u8>) -> Self {
        Self {
            padded_item,
            nationality_member_index: None,
        }
    }

    pub(crate) fn with_nationality_member(
        padded_item: Vec<u8>,
        nationality_member_index: u8,
    ) -> Self {
        Self {
            padded_item,
            nationality_member_index: Some(nationality_member_index),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateItemFieldIds {
    pub(crate) outer_stream: u32,
    pub(crate) inner_stream: u32,
    /// Existing `MdocStatementAttribute::element_field_id(attribute_index)`.
    pub(crate) element_identifier: u32,
    /// Semantic value output. Use the attribute value field for
    /// `ValueEquality`, `field_id::DOB` for the packed birth-date output, and
    /// `field_id::NATIONALITY` for the numeric nationality output.
    pub(crate) element_value: u32,
}

#[derive(Clone)]
pub(crate) struct MdocPrivateItemHandles {
    /// Relation already drawn by the attribute SHA full-padded-stream provider.
    pub(crate) item_fields: SharedFieldRelation,
    pub(crate) outer_parsed: SharedParsedCborByteRelation,
    pub(crate) inner_parsed: SharedParsedCborByteRelation,
    /// Drawn by this module; consumed by the raw inner CBOR parser.
    pub(crate) inner_raw: SharedFieldRelation,
    /// Drawn by this module; consumed once by the MSO valueDigests scan.
    pub(crate) digest_id: SharedMdocPrivateDigestIdRelation,
    /// Drawn by the proof-wide fixed country-code table.
    pub(crate) country_code: SharedMdocCountryCodeRelation,
}

impl MdocPrivateItemHandles {
    pub(crate) fn fresh(
        item_fields: SharedFieldRelation,
        country_code: SharedMdocCountryCodeRelation,
    ) -> Self {
        Self {
            item_fields,
            outer_parsed: SharedParsedCborByteRelation::new(),
            inner_parsed: SharedParsedCborByteRelation::new(),
            inner_raw: SharedFieldRelation::new(),
            digest_id: SharedMdocPrivateDigestIdRelation::new(),
            country_code,
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
    AttributeIndexOutOfRange(usize),
    InvalidPaddedBucket(usize),
    PaddedBucketMismatch {
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
    InvalidCanonicalKeyOrder,
    InvalidRandom,
    InvalidDigestId,
    DigestIdOutOfRange {
        value: u64,
        max: u32,
    },
    InvalidElementIdentifier,
    InvalidElementValue,
    UnexpectedNationalityArraySelection(u8),
    MissingNationalityArraySelection,
    InvalidNationalityArraySelection {
        member_count: u8,
        selected_index: u8,
    },
    CountryCode(MdocCountryCodeError),
    Ts13RequiresValueEquality,
    TraceTooLarge {
        rows: usize,
    },
}

impl fmt::Display for MdocPrivateItemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AttributeIndexOutOfRange(index) => write!(
                f,
                "private IssuerSignedItem attribute index {index} exceeds {}",
                MDOC_PRIVATE_ITEM_MAX_ATTRIBUTES - 1
            ),
            Self::InvalidPaddedBucket(bucket) => write!(
                f,
                "private IssuerSignedItem padded length {bucket} is not one of {:?}",
                MDOC_PRIVATE_ITEM_PADDED_BUCKETS
            ),
            Self::PaddedBucketMismatch { expected, actual } => write!(
                f,
                "private IssuerSignedItem bucket is {expected} bytes but witness has {actual}"
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
            Self::InvalidCanonicalKeyOrder => {
                write!(f, "private IssuerSignedItem key order is not canonical")
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
            Self::UnexpectedNationalityArraySelection(selected_index) => write!(
                f,
                "private IssuerSignedItem scalar/non-nationality value has unexpected nationality selection {selected_index}"
            ),
            Self::MissingNationalityArraySelection => write!(
                f,
                "private IssuerSignedItem nationality array misses its private selection"
            ),
            Self::InvalidNationalityArraySelection {
                member_count,
                selected_index,
            } => write!(
                f,
                "private IssuerSignedItem nationality array selection {selected_index}/{member_count} is out of bounds"
            ),
            Self::CountryCode(error) => write!(
                f,
                "private IssuerSignedItem nationality country code is invalid: {error}"
            ),
            Self::Ts13RequiresValueEquality => write!(
                f,
                "TS13 private IssuerSignedItem requires value-equality mode"
            ),
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
            Self::CountryCode(error) => Some(error),
            _ => None,
        }
    }
}

impl From<MdocCountryCodeError> for MdocPrivateItemError {
    fn from(error: MdocCountryCodeError) -> Self {
        Self::CountryCode(error)
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

    pub(super) const IDENTIFIER_SHORT: usize = 74;
    pub(super) const IDENTIFIER_LONG: usize = 75;
    pub(super) const IDENTIFIER_LONG_ARG: usize = 76;
    pub(super) const IDENTIFIER_CONTENT_START: usize = 77;
    pub(super) const IDENTIFIER_CONTENT_ACTIVE: usize = 78;
    pub(super) const IDENTIFIER_CONTENT_END: usize = 79;
    pub(super) const IDENTIFIER_CONTENT_INDEX: usize = 80;
    pub(super) const IDENTIFIER_LEN: usize = 81;
    pub(super) const IDENTIFIER_LOWER_BITS: usize = 82;
    pub(super) const IDENTIFIER_UPPER_BITS: usize = 89;

    pub(super) const VALUE_ACTIVE: usize = 96;
    pub(super) const VALUE_END: usize = 97;
    pub(super) const VALUE_INDEX: usize = 98;
    pub(super) const VALUE_SCOPE_ACTIVE: usize = 99;
    pub(super) const VALUE_SCOPE_END: usize = 100;
    pub(super) const VALUE_ROOT_INDEX: usize = 101;
    pub(super) const VALUE_HEAD: usize = 102;
    pub(super) const VALUE_HEAD_SEEN: usize = 103;
    pub(super) const VALUE_DIRECT: usize = 104;
    pub(super) const VALUE_TAGGED: usize = 105;
    pub(super) const ARRAY_MEMBER_HEAD: usize = 106;
    pub(super) const ARRAY_MEMBER_TEXT: usize = 107;
    pub(super) const ARRAY_MEMBER_SEEN_COUNT: usize = 108;
    pub(super) const IS_V2: usize = 109;
    pub(super) const VALUE_OUTPUT_BYTE: usize = 110;
    pub(super) const NAT_MEMBER_COUNT: usize = 111;
    pub(super) const NAT_MEMBER_COUNT_MINUS_ONE_BITS: usize = 112;
    pub(super) const NAT_SELECTED_TEXT: usize = 115;
    pub(super) const NAT_CASE_FOLD_BITS: usize = 116;
    pub(super) const DATE_DIGIT_BITS: usize = 118;
    pub(super) const COUNTRY_LOOKUP_NUM_HI: usize = 150;
    pub(super) const COUNTRY_LOOKUP_NUM_LO: usize = 151;
    pub(super) const COUNTRY_LOOKUP_UPPER_0: usize = 152;
    pub(super) const COUNTRY_LOOKUP_UPPER_1: usize = 153;
    pub(super) const COUNT: usize = 154;
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

fn profile_log_size(bucket: usize) -> Result<u32, MdocPrivateItemError> {
    if !MDOC_PRIVATE_ITEM_PADDED_BUCKETS
        .map(usize::from)
        .contains(&bucket)
    {
        return Err(MdocPrivateItemError::InvalidPaddedBucket(bucket));
    }
    let max_outer = bucket - 9;
    let max_inner = max_outer - OUTER_PREFIX_BYTES;
    let rows = max_outer
        .checked_add(max_inner)
        .and_then(|rows| rows.checked_add(MDOC_PRIVATE_ITEM_BLIND_ROWS))
        .ok_or(MdocPrivateItemError::TraceTooLarge { rows: usize::MAX })?;
    Ok(rows.next_power_of_two().ilog2())
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
    let mut ids = vec![
        preprocessed_id(log_size, "first"),
        preprocessed_id(log_size, "last"),
    ];
    ids.extend(
        (0..OUTER_PREFIX_BYTES)
            .map(|index| preprocessed_id(log_size, &format!("outer_prefix_{index}"))),
    );
    ids
}

fn preprocessed_columns(log_size: u32) -> Vec<Column> {
    let rows = 1usize << log_size;
    let mut values = vec![vec![m31(0); rows]; PREPROCESSED_COLS];
    values[0][0] = m31(1);
    values[1][rows - 1] = m31(1);
    for index in 0..OUTER_PREFIX_BYTES {
        values[2 + index][index] = m31(1);
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
    TS13_ELEMENT_IDENTIFIER
        .iter()
        .copied()
        .enumerate()
        .map(move |(index, byte)| (field_ids.element_identifier, index, byte))
        .chain(
            TS13_CANONICAL_ELEMENT_VALUE
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
    identifier_len: usize,
    identifier_content_start: usize,
    value_root: usize,
    value_scope_end: usize,
    normalized_output_start: usize,
    normalized_output: Vec<u8>,
    semantic_value_head: Option<usize>,
    value_direct: bool,
    value_tagged: bool,
    array_member_heads: Vec<(usize, bool)>,
    nationality_member_count: Option<u8>,
    nationality_selected_text: bool,
    nationality_case_fold: [bool; NATIONALITY_BYTES],
    birth_date_digits: Option<[u8; BIRTH_DATE_DIGITS]>,
    country_tuple: Option<MdocCountryCodeTuple>,
    country_uses: MdocCountryCodeUses,
}

fn key_kind(bytes: &[u8]) -> Option<usize> {
    KEY_LABELS.iter().position(|label| *label == bytes)
}

fn birth_date_text(
    inner: &[u8],
    head: usize,
) -> Result<([u8; BIRTH_DATE_DIGITS], [u8; BIRTH_DATE_PACKED_BYTES]), MdocPrivateItemError> {
    let text = inner
        .get(head + 1..head + 1 + BIRTH_DATE_TEXT_BYTES)
        .ok_or(MdocPrivateItemError::InvalidElementValue)?;
    if text[4] != b'-' || text[7] != b'-' {
        return Err(MdocPrivateItemError::InvalidElementValue);
    }
    let digit_positions = [0usize, 1, 2, 3, 5, 6, 8, 9];
    let mut digits = [0u8; BIRTH_DATE_DIGITS];
    for (output, position) in digits.iter_mut().zip(digit_positions) {
        let byte = text[position];
        if !byte.is_ascii_digit() {
            return Err(MdocPrivateItemError::InvalidElementValue);
        }
        *output = byte - b'0';
    }
    let year = u16::from(digits[0]) * 1000
        + u16::from(digits[1]) * 100
        + u16::from(digits[2]) * 10
        + u16::from(digits[3]);
    let year = year.to_be_bytes();
    Ok((
        digits,
        [
            year[0],
            year[1],
            digits[4] * 10 + digits[5],
            digits[6] * 10 + digits[7],
        ],
    ))
}

fn fold_alpha2(bytes: [u8; NATIONALITY_BYTES]) -> Option<([u8; NATIONALITY_BYTES], [bool; 2])> {
    let mut upper = [0u8; NATIONALITY_BYTES];
    let mut folded = [false; NATIONALITY_BYTES];
    for index in 0..NATIONALITY_BYTES {
        match bytes[index] {
            b'A'..=b'Z' => upper[index] = bytes[index],
            b'a'..=b'z' => {
                upper[index] = bytes[index] - (b'a' - b'A');
                folded[index] = true;
            }
            _ => return None,
        }
    }
    Some((upper, folded))
}

fn analyze_inner(
    inner: &[u8],
    rows: &[MdocCborWitnessRow],
    profile: MdocPrivateItemProfile,
    is_v2: bool,
    request_mode: MdocPrivateItemRequestMode,
    nationality_member_index: Option<u8>,
) -> Result<ItemAnalysis, MdocPrivateItemError> {
    let root = rows
        .first()
        .ok_or(MdocPrivateItemError::InvalidIssuerSignedItemRoot)?;
    if !root.header || root.byte != 0xa4 || root.major != 5 || root.argument != 4 || root.depth != 0
    {
        return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
    }

    let mut spans: [Option<KeySpan>; KEY_COUNT] = [None; KEY_COUNT];
    let mut order = Vec::with_capacity(KEY_COUNT);
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
        order.push(kind);
    }
    for (kind, span) in spans.iter().enumerate() {
        if span.is_none() {
            return Err(MdocPrivateItemError::MissingKey(
                std::str::from_utf8(KEY_LABELS[kind]).expect("ASCII key"),
            ));
        }
    }
    if order.len() != KEY_COUNT {
        return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
    }
    if (profile.canonical_key_order()
        || matches!(profile, MdocPrivateItemProfile::Product) && is_v2)
        && order != [0, 1, 2, 3]
    {
        return Err(MdocPrivateItemError::InvalidCanonicalKeyOrder);
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
        0x1a => 5,
        _ => return Err(MdocPrivateItemError::InvalidDigestId),
    };
    let digest_start = digest.byte_index as usize;
    let digest_encoding = inner
        .get(digest_start..digest_start + digest_width)
        .ok_or(MdocPrivateItemError::InvalidDigestId)?
        .to_vec();
    if digest.argument > u64::from(profile.digest_id_max()) {
        return Err(MdocPrivateItemError::DigestIdOutOfRange {
            value: digest.argument,
            max: profile.digest_id_max(),
        });
    }

    let identifier = &rows[key_spans[KEY_ELEMENT_IDENTIFIER].value_start];
    let identifier_len = identifier.content_len as usize;
    if identifier.major != 3
        || !(1..=MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES).contains(&identifier_len)
    {
        return Err(MdocPrivateItemError::InvalidElementIdentifier);
    }
    let identifier_head_len = usize::from(identifier_len >= 24) + 1;
    let identifier_content_start = identifier.byte_index as usize + identifier_head_len;
    let identifier_content_end = identifier_content_start
        .checked_add(identifier_len)
        .ok_or(MdocPrivateItemError::InvalidElementIdentifier)?;
    let identifier_content = inner
        .get(identifier_content_start..identifier_content_end)
        .ok_or(MdocPrivateItemError::InvalidElementIdentifier)?;
    if matches!(profile, MdocPrivateItemProfile::Ts13)
        && identifier_content != TS13_ELEMENT_IDENTIFIER
    {
        return Err(MdocPrivateItemError::InvalidElementIdentifier);
    }

    let value_root = key_spans[KEY_ELEMENT_VALUE].value_start;
    let next_key = key_spans
        .iter()
        .map(|span| span.start)
        .filter(|start| *start > value_root)
        .min();
    let full_value_end = next_key.unwrap_or(inner.len()) - 1;
    if full_value_end < value_root
        || full_value_end - value_root + 1 > MDOC_PRIVATE_ITEM_MAX_VALUE_BYTES
    {
        return Err(MdocPrivateItemError::InvalidIssuerSignedItemRoot);
    }

    let value = &rows[value_root];
    let mut semantic_value_head = None;
    let mut value_direct = false;
    let mut value_tagged = false;
    let mut array_member_heads = Vec::new();
    let mut nationality_member_count = None;
    let mut nationality_selected_text = false;
    let mut nationality_case_fold = [false; NATIONALITY_BYTES];
    let mut birth_date_digits = None;
    let mut country_tuple = None;
    let mut country_uses = MdocCountryCodeUses::default();
    let (normalized_output_start, normalized_output) = match request_mode {
        MdocPrivateItemRequestMode::ValueEquality => {
            if let Some(selected_index) = nationality_member_index {
                return Err(MdocPrivateItemError::UnexpectedNationalityArraySelection(
                    selected_index,
                ));
            }
            (value_root, inner[value_root..=full_value_end].to_vec())
        }
        MdocPrivateItemRequestMode::BirthDate => {
            if let Some(selected_index) = nationality_member_index {
                return Err(MdocPrivateItemError::UnexpectedNationalityArraySelection(
                    selected_index,
                ));
            }
            let (head, output) = if value.major == 2
                && value.content_len as usize == BIRTH_DATE_PACKED_BYTES
                && value.byte == 0x44
            {
                let output: [u8; BIRTH_DATE_PACKED_BYTES] = inner
                    .get(value_root + 1..value_root + 1 + BIRTH_DATE_PACKED_BYTES)
                    .and_then(|bytes| bytes.try_into().ok())
                    .ok_or(MdocPrivateItemError::InvalidElementValue)?;
                (value_root, output)
            } else {
                let head = if value.major == 3
                    && value.content_len as usize == BIRTH_DATE_TEXT_BYTES
                    && value.byte == 0x6a
                {
                    value_direct = true;
                    value_root
                } else if value.major == 6
                    && value.argument == u64::from(CBOR_TAG_FULL_DATE)
                    && value.byte == 0xd9
                {
                    value_tagged = true;
                    rows.iter()
                        .filter(|row| {
                            row.header
                                && row.depth == value.depth + 1
                                && row.parent_header_index == value.byte_index
                                && row.child_ordinal == 0
                                && row.major == 3
                                && row.content_len as usize == BIRTH_DATE_TEXT_BYTES
                                && row.byte == 0x6a
                        })
                        .map(|row| row.byte_index as usize)
                        .next()
                        .ok_or(MdocPrivateItemError::InvalidElementValue)?
                } else {
                    return Err(MdocPrivateItemError::InvalidElementValue);
                };
                let (digits, output) = birth_date_text(inner, head)?;
                birth_date_digits = Some(digits);
                (head, output)
            };
            semantic_value_head = Some(head);
            (head + 1, output.to_vec())
        }
        MdocPrivateItemRequestMode::Nationality => {
            let (members, member_count, selected_index) = if matches!(value.major, 2 | 3)
                && value.content_len as usize == NATIONALITY_BYTES
                && value.byte == ((value.major << 5) | NATIONALITY_BYTES as u8)
            {
                if let Some(selected_index) = nationality_member_index {
                    return Err(MdocPrivateItemError::UnexpectedNationalityArraySelection(
                        selected_index,
                    ));
                }
                value_direct = true;
                (vec![value], 1u8, 0u8)
            } else if value.major == 4
                && (1..=MDOC_PRIVATE_ITEM_MAX_NATIONALITY_MEMBERS as u64).contains(&value.argument)
                && value.byte == 0x80 + value.argument as u8
            {
                value_tagged = true;
                let member_count = value.argument as u8;
                let selected_index = nationality_member_index
                    .ok_or(MdocPrivateItemError::MissingNationalityArraySelection)?;
                if selected_index >= member_count {
                    return Err(MdocPrivateItemError::InvalidNationalityArraySelection {
                        member_count,
                        selected_index,
                    });
                }
                let members = rows
                    .iter()
                    .filter(|row| {
                        row.header
                            && row.depth == value.depth + 1
                            && row.parent_header_index == value.byte_index
                    })
                    .collect::<Vec<_>>();
                if members.len() != usize::from(member_count)
                    || members.iter().enumerate().any(|(index, member)| {
                        member.child_ordinal != index as u32
                            || !matches!(member.major, 2 | 3)
                            || member.content_len as usize != NATIONALITY_BYTES
                            || member.byte != ((member.major << 5) | NATIONALITY_BYTES as u8)
                    })
                {
                    return Err(MdocPrivateItemError::InvalidElementValue);
                }
                (members, member_count, selected_index)
            } else {
                return Err(MdocPrivateItemError::InvalidElementValue);
            };

            array_member_heads = members
                .iter()
                .map(|member| (member.byte_index as usize, member.major == 3))
                .collect();
            nationality_member_count = Some(member_count);
            let selected = members[usize::from(selected_index)];
            let head = selected.byte_index as usize;
            let raw: [u8; NATIONALITY_BYTES] = inner
                .get(head + 1..head + 1 + NATIONALITY_BYTES)
                .and_then(|bytes| bytes.try_into().ok())
                .ok_or(MdocPrivateItemError::InvalidElementValue)?;
            let output = if selected.major == 2 {
                let tuple = mdoc_country_code_numeric_dummy_tuple();
                country_uses.record_numeric_dummy()?;
                country_tuple = Some(tuple);
                raw
            } else {
                let (upper, folded) =
                    fold_alpha2(raw).ok_or(MdocPrivateItemError::InvalidElementValue)?;
                let tuple = mdoc_country_code_alpha2_tuple(upper)?;
                country_uses.record_tuple(tuple)?;
                nationality_selected_text = true;
                nationality_case_fold = folded;
                country_tuple = Some(tuple);
                [tuple.num_hi as u8, tuple.num_lo as u8]
            };
            semantic_value_head = Some(head);
            (head + 1, output.to_vec())
        }
    };
    let normalized_output_end = normalized_output_start
        .checked_add(normalized_output.len())
        .and_then(|end| end.checked_sub(1))
        .ok_or(MdocPrivateItemError::InvalidElementValue)?;
    if normalized_output_end >= inner.len() {
        return Err(MdocPrivateItemError::InvalidElementValue);
    }
    if matches!(profile, MdocPrivateItemProfile::Ts13)
        && normalized_output != TS13_CANONICAL_ELEMENT_VALUE
    {
        return Err(MdocPrivateItemError::InvalidElementValue);
    }

    Ok(ItemAnalysis {
        key_spans,
        random_len,
        digest_encoding,
        digest_value: digest.argument,
        identifier_len,
        identifier_content_start,
        value_root,
        value_scope_end: full_value_end,
        normalized_output_start,
        normalized_output,
        semantic_value_head,
        value_direct,
        value_tagged,
        array_member_heads,
        nationality_member_count,
        nationality_selected_text,
        nationality_case_fold,
        birth_date_digits,
        country_tuple,
        country_uses,
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
    #[cfg(test)]
    country_tuple: Option<MdocCountryCodeTuple>,
    country_uses: MdocCountryCodeUses,
}

impl MdocPrivateItemWitness {
    fn new(
        private_input: MdocPrivateItemPrivateInput,
        bucket: usize,
        log_size: u32,
        profile: MdocPrivateItemProfile,
        version: MdocPrivateMsoVersion,
        request_mode: MdocPrivateItemRequestMode,
    ) -> Result<Self, MdocPrivateItemError> {
        let MdocPrivateItemPrivateInput {
            padded_item,
            nationality_member_index,
        } = private_input;
        if padded_item.len() != bucket {
            return Err(MdocPrivateItemError::PaddedBucketMismatch {
                expected: bucket,
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
        let is_v2 = matches!(version, MdocPrivateMsoVersion::V2);
        let analysis = analyze_inner(
            &inner_bytes,
            &inner.rows,
            profile,
            is_v2,
            request_mode,
            nationality_member_index,
        )?;
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
            trace_col::IDENTIFIER_SHORT,
            trace_col::IDENTIFIER_LONG,
            trace_col::IDENTIFIER_LONG_ARG,
            trace_col::IDENTIFIER_CONTENT_START,
            trace_col::IDENTIFIER_CONTENT_ACTIVE,
            trace_col::IDENTIFIER_CONTENT_END,
            trace_col::VALUE_ACTIVE,
            trace_col::VALUE_END,
            trace_col::VALUE_SCOPE_ACTIVE,
            trace_col::VALUE_SCOPE_END,
            trace_col::VALUE_HEAD,
            trace_col::VALUE_DIRECT,
            trace_col::VALUE_TAGGED,
            trace_col::ARRAY_MEMBER_HEAD,
            trace_col::ARRAY_MEMBER_TEXT,
            trace_col::NAT_SELECTED_TEXT,
        ] {
            columns[column_index].fill(m31(0));
        }
        columns[trace_col::KEY_SEEN..trace_col::KEY_SEEN + KEY_COUNT]
            .iter_mut()
            .for_each(|column| {
                column.iter_mut().for_each(|value| *value = random_bit());
            });
        columns[trace_col::VALUE_HEAD_SEEN]
            .iter_mut()
            .for_each(|value| *value = random_bit());
        columns[trace_col::IS_V2]
            .iter_mut()
            .for_each(|value| *value = random_bit());
        for index in 0..NATIONALITY_COUNT_BITS {
            columns[trace_col::NAT_MEMBER_COUNT_MINUS_ONE_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        for index in 0..NATIONALITY_BYTES {
            columns[trace_col::NAT_CASE_FOLD_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        for index in 0..BIRTH_DATE_DIGITS * BIRTH_DATE_DIGIT_BITS {
            columns[trace_col::DATE_DIGIT_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        for index in 0..RANDOM_BOUND_BITS {
            columns[trace_col::RANDOM_LOWER_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
            columns[trace_col::RANDOM_UPPER_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        for index in 0..IDENTIFIER_BOUND_BITS {
            columns[trace_col::IDENTIFIER_LOWER_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
            columns[trace_col::IDENTIFIER_UPPER_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        for index in 0..5 {
            columns[trace_col::DIGEST_SHORT_SLACK_BITS + index]
                .iter_mut()
                .for_each(|value| *value = random_bit());
        }
        columns[trace_col::INNER_LEN][..active_rows].fill(m31(inner.rows.len() as u32));
        columns[trace_col::IS_V2][..active_rows].fill(m31(u32::from(is_v2)));

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

        let identifier_header = inner_base + analysis.key_spans[KEY_ELEMENT_IDENTIFIER].value_start;
        let identifier_long = analysis.identifier_len >= 24;
        columns[if identifier_long {
            trace_col::IDENTIFIER_LONG
        } else {
            trace_col::IDENTIFIER_SHORT
        }][identifier_header] = m31(1);
        if identifier_long {
            columns[trace_col::IDENTIFIER_LONG_ARG][identifier_header + 1] = m31(1);
        }
        let identifier_content_start = inner_base + analysis.identifier_content_start;
        let identifier_content_end = identifier_content_start + analysis.identifier_len - 1;
        columns[trace_col::IDENTIFIER_LEN][identifier_header..=identifier_content_end]
            .fill(m31(analysis.identifier_len as u32));
        columns[trace_col::IDENTIFIER_CONTENT_START][identifier_content_start] = m31(1);
        columns[trace_col::IDENTIFIER_CONTENT_END][identifier_content_end] = m31(1);
        for (content_index, index) in
            (identifier_content_start..=identifier_content_end).enumerate()
        {
            columns[trace_col::IDENTIFIER_CONTENT_ACTIVE][index] = m31(1);
            columns[trace_col::IDENTIFIER_CONTENT_INDEX][index] = m31(content_index as u32);
        }
        for (offset, bit) in
            bit_values(analysis.identifier_len - 1, IDENTIFIER_BOUND_BITS).enumerate()
        {
            columns[trace_col::IDENTIFIER_LOWER_BITS + offset][identifier_header] = bit;
        }
        for (offset, bit) in bit_values(
            MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES - analysis.identifier_len,
            IDENTIFIER_BOUND_BITS,
        )
        .enumerate()
        {
            columns[trace_col::IDENTIFIER_UPPER_BITS + offset][identifier_header] = bit;
        }

        let value_scope_start = inner_base + analysis.value_root;
        let value_scope_end = inner_base + analysis.value_scope_end;
        columns[trace_col::VALUE_SCOPE_END][value_scope_end] = m31(1);
        columns[trace_col::VALUE_SCOPE_ACTIVE][value_scope_start..=value_scope_end].fill(m31(1));
        columns[trace_col::VALUE_ROOT_INDEX][value_scope_start..=value_scope_end]
            .fill(m31(analysis.value_root as u32));

        let value_start = inner_base + analysis.normalized_output_start;
        let value_end = value_start + analysis.normalized_output.len() - 1;
        columns[trace_col::VALUE_END][value_end] = m31(1);
        for (value_index, index) in (value_start..=value_end).enumerate() {
            columns[trace_col::VALUE_ACTIVE][index] = m31(1);
            columns[trace_col::VALUE_INDEX][index] = m31(value_index as u32);
            columns[trace_col::VALUE_OUTPUT_BYTE][index] =
                m31(u32::from(analysis.normalized_output[value_index]));
            if !matches!(request_mode, MdocPrivateItemRequestMode::ValueEquality) {
                for (offset, bit) in
                    bit_values(usize::from(analysis.normalized_output[value_index]), 8).enumerate()
                {
                    columns[trace_col::DATE_DIGIT_BITS + offset][index] = bit;
                }
            }
        }
        if let Some(value_head) = analysis.semantic_value_head {
            let value_head = inner_base + value_head;
            columns[trace_col::VALUE_HEAD][value_head] = m31(1);
            columns[trace_col::VALUE_HEAD_SEEN][inner_base..value_head].fill(m31(0));
            columns[trace_col::VALUE_HEAD_SEEN][value_head..active_rows].fill(m31(1));
        } else {
            columns[trace_col::VALUE_HEAD_SEEN][inner_base..active_rows].fill(m31(0));
        }
        if analysis.value_direct {
            columns[trace_col::VALUE_DIRECT][inner_base + analysis.value_root] = m31(1);
        }
        if analysis.value_tagged {
            columns[trace_col::VALUE_TAGGED][inner_base + analysis.value_root] = m31(1);
        }
        let mut members_seen = 0u32;
        for &(index, text) in &analysis.array_member_heads {
            let index = inner_base + index;
            columns[trace_col::ARRAY_MEMBER_HEAD][index] = m31(1);
            columns[trace_col::ARRAY_MEMBER_TEXT][index] = m31(u32::from(text));
        }
        for index in inner_base..active_rows {
            if columns[trace_col::ARRAY_MEMBER_HEAD][index] == m31(1) {
                members_seen += 1;
            }
            columns[trace_col::ARRAY_MEMBER_SEEN_COUNT][index] = m31(members_seen);
        }
        if let Some(member_count) = analysis.nationality_member_count {
            columns[trace_col::NAT_MEMBER_COUNT][inner_base..active_rows]
                .fill(m31(u32::from(member_count)));
            for (offset, bit) in
                bit_values(usize::from(member_count - 1), NATIONALITY_COUNT_BITS).enumerate()
            {
                columns[trace_col::NAT_MEMBER_COUNT_MINUS_ONE_BITS + offset][value_scope_start] =
                    bit;
            }
            let value_head = inner_base
                + analysis
                    .semantic_value_head
                    .expect("nationality analysis selects one member");
            columns[trace_col::NAT_SELECTED_TEXT][value_head] =
                m31(u32::from(analysis.nationality_selected_text));
            for (offset, folded) in analysis.nationality_case_fold.into_iter().enumerate() {
                columns[trace_col::NAT_CASE_FOLD_BITS + offset][value_head] =
                    m31(u32::from(folded));
            }
            let tuple = analysis
                .country_tuple
                .expect("nationality analysis emits one country tuple");
            columns[trace_col::COUNTRY_LOOKUP_NUM_HI][value_head] = m31(tuple.num_hi);
            columns[trace_col::COUNTRY_LOOKUP_NUM_LO][value_head] = m31(tuple.num_lo);
            columns[trace_col::COUNTRY_LOOKUP_UPPER_0][value_head] = m31(tuple.upper0);
            columns[trace_col::COUNTRY_LOOKUP_UPPER_1][value_head] = m31(tuple.upper1);
        }
        if let (Some(digits), Some(value_head)) =
            (analysis.birth_date_digits, analysis.semantic_value_head)
        {
            let value_head = inner_base + value_head;
            for (digit_index, digit) in digits.into_iter().enumerate() {
                for (bit_index, bit) in
                    bit_values(usize::from(digit), BIRTH_DATE_DIGIT_BITS).enumerate()
                {
                    columns[trace_col::DATE_DIGIT_BITS
                        + digit_index * BIRTH_DATE_DIGIT_BITS
                        + bit_index][value_head] = bit;
                }
            }
        }

        Ok(Self {
            columns,
            inner_bytes,
            #[cfg(test)]
            country_tuple: analysis.country_tuple,
            country_uses: analysis.country_uses,
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
    stream_index: E::F,
    byte: E::F,
    header: E::F,
    major: E::F,
    argument: &[E::F; 4],
    content_len: E::F,
    depth: E::F,
    parent: E::F,
    ordinal: E::F,
    map_key: E::F,
    map_value: E::F,
) -> [E::F; 15] {
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
    profile: MdocPrivateItemProfile,
    request_mode: MdocPrivateItemRequestMode,
    field_ids: MdocPrivateItemFieldIds,
    item_fields: FieldBytesRelation,
    outer_parsed: ParsedCborByteRelation,
    inner_parsed: ParsedCborByteRelation,
    inner_raw: FieldBytesRelation,
    digest_id: MdocPrivateDigestIdRelation,
    country_code: MdocCountryCodeRelation,
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
        let first = eval.get_preprocessed_column(preprocessed_id(self.log_size, "first"));
        let last = eval.get_preprocessed_column(preprocessed_id(self.log_size, "last"));
        let prefix: [E::F; OUTER_PREFIX_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(preprocessed_id(
                self.log_size,
                &format!("outer_prefix_{index}"),
            ))
        });
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

        let byte_window: [E::F; BIRTH_DATE_TEXT_BYTES + 1] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
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

        let identifier_short = eval.next_trace_mask();
        let identifier_long = eval.next_trace_mask();
        let [identifier_long_arg, identifier_long_arg_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [identifier_content_start, identifier_content_start_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [identifier_content_active, identifier_content_active_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let identifier_content_end = eval.next_trace_mask();
        let [identifier_content_index, identifier_content_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [identifier_len, identifier_len_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let identifier_lower_bits: [E::F; IDENTIFIER_BOUND_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let identifier_upper_bits: [E::F; IDENTIFIER_BOUND_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());

        let [element_value_active, element_value_active_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let element_value_end = eval.next_trace_mask();
        let [element_value_index, element_value_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [value_scope_active, value_scope_active_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let value_scope_end = eval.next_trace_mask();
        let [value_root_index, value_root_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [value_head, value_head_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [value_head_seen, value_head_seen_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let value_direct = eval.next_trace_mask();
        let value_tagged = eval.next_trace_mask();
        let [array_member_head, array_member_head_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let array_member_text = eval.next_trace_mask();
        let [array_member_seen_count, array_member_seen_count_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [is_v2, is_v2_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let output_byte_window: [E::F; BIRTH_DATE_PACKED_BYTES + 1] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1, 2, 3, 4]);
        let output_byte = output_byte_window[0].clone();
        let [nationality_member_count, nationality_member_count_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let nationality_count_bits: [E::F; NATIONALITY_COUNT_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let nationality_selected_text = eval.next_trace_mask();
        let nationality_case_fold: [E::F; NATIONALITY_BYTES] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let date_digit_bits: [E::F; BIRTH_DATE_DIGITS * BIRTH_DATE_DIGIT_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let country_lookup_num_hi = eval.next_trace_mask();
        let country_lookup_num_lo = eval.next_trace_mask();
        let country_lookup_upper_0 = eval.next_trace_mask();
        let country_lookup_upper_1 = eval.next_trace_mask();

        for selector in [
            active.clone(),
            outer.clone(),
            inner.clone(),
            outer_end.clone(),
            inner_start.clone(),
            inner_end.clone(),
            raw_yield.clone(),
            identifier_short.clone(),
            identifier_long.clone(),
            identifier_long_arg.clone(),
            identifier_content_start.clone(),
            identifier_content_active.clone(),
            identifier_content_end.clone(),
            element_value_active.clone(),
            element_value_end.clone(),
            value_scope_active.clone(),
            value_scope_end.clone(),
            value_head.clone(),
            value_head_seen.clone(),
            value_direct.clone(),
            value_tagged.clone(),
            array_member_head.clone(),
            array_member_text.clone(),
            is_v2.clone(),
            nationality_selected_text.clone(),
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
        .chain(identifier_lower_bits.iter().cloned())
        .chain(identifier_upper_bits.iter().cloned())
        .chain(nationality_count_bits.iter().cloned())
        .chain(nationality_case_fold.iter().cloned())
        .chain(date_digit_bits.iter().cloned())
        {
            eval.add_constraint(selector.clone() * (selector - one.clone()));
        }

        eval.add_constraint(active.clone() - outer.clone() - inner.clone());
        eval.add_constraint((active.clone() - inner_end.clone()) * (is_v2_next - is_v2.clone()));
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
            if self.profile.canonical_key_order() {
                pin(
                    &mut eval,
                    key_start[kind][0].clone(),
                    ordinal.clone(),
                    KEY_CANONICAL_CHILD_ORDINALS[kind],
                );
            } else {
                eval.add_constraint(
                    key_start[kind][0].clone()
                        * is_v2.clone()
                        * (ordinal.clone() - m31_const::<E>(KEY_CANONICAL_CHILD_ORDINALS[kind])),
                );
            }
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
        if matches!(self.profile, MdocPrivateItemProfile::Ts13) {
            eval.add_constraint(digest_start_kind[3].clone());
            pin(&mut eval, digest_start.clone(), argument[1].clone(), 0);
        }

        let identifier_start = value_start[KEY_ELEMENT_IDENTIFIER][0].clone();
        eval.add_constraint(
            identifier_short.clone() + identifier_long.clone() - identifier_start.clone(),
        );
        pin(&mut eval, identifier_start.clone(), major.clone(), 3);
        eval.add_constraint(
            identifier_short.clone()
                * (byte.clone() - m31_const::<E>(0x60) - identifier_len.clone()),
        );
        pin(&mut eval, identifier_long.clone(), byte.clone(), 0x78);
        eval.add_constraint(identifier_long_arg_next - identifier_long.clone());
        eval.add_constraint(identifier_long_arg.clone() * (byte.clone() - identifier_len.clone()));
        eval.add_constraint(identifier_long_arg.clone() * header.clone());
        eval.add_constraint(
            identifier_content_start_next.clone()
                - identifier_short.clone()
                - identifier_long_arg.clone(),
        );
        eval.add_constraint(
            identifier_content_active_next
                - identifier_content_active.clone()
                - identifier_content_start_next
                + identifier_content_end.clone(),
        );
        eval.add_constraint(
            identifier_content_start.clone() * (one.clone() - identifier_content_active.clone()),
        );
        eval.add_constraint(
            identifier_content_end.clone() * (one.clone() - identifier_content_active.clone()),
        );
        eval.add_constraint(identifier_content_start.clone() * identifier_content_index.clone());
        eval.add_constraint(
            (identifier_content_active.clone() - identifier_content_end.clone())
                * (identifier_content_index_next - identifier_content_index.clone() - one.clone()),
        );
        eval.add_constraint(
            identifier_content_end.clone()
                * (identifier_content_index.clone() + one.clone() - identifier_len.clone()),
        );
        let identifier_scope = identifier_short.clone()
            + identifier_long.clone()
            + identifier_long_arg.clone()
            + identifier_content_active.clone();
        eval.add_constraint(
            (identifier_scope - identifier_content_end.clone())
                * (identifier_len_next - identifier_len.clone()),
        );
        eval.add_constraint(
            identifier_start.clone()
                * (identifier_len.clone() - one.clone() - sum_bits::<E>(&identifier_lower_bits)),
        );
        eval.add_constraint(
            identifier_start
                * (identifier_len.clone() + sum_bits::<E>(&identifier_upper_bits)
                    - m31_const::<E>(MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES as u32)),
        );

        let element_value_start = value_start[KEY_ELEMENT_VALUE][0].clone();
        eval.add_constraint(
            value_scope_active_next
                - value_scope_active.clone()
                - value_start[KEY_ELEMENT_VALUE][1].clone()
                + value_scope_end.clone(),
        );
        eval.add_constraint(
            element_value_start.clone() * (one.clone() - value_scope_active.clone()),
        );
        eval.add_constraint(value_scope_end.clone() * (one.clone() - value_scope_active.clone()));
        eval.add_constraint(
            value_scope_end.clone()
                - value_scope_active.clone() * (inner_end.clone() + key_start_next_sum.clone()),
        );
        eval.add_constraint(
            (value_scope_active.clone() - value_scope_end.clone())
                * (value_root_index_next - value_root_index.clone()),
        );
        eval.add_constraint(
            element_value_start.clone() * (value_root_index.clone() - stream_index.clone()),
        );
        eval.add_constraint(array_member_text.clone() * (one.clone() - array_member_head.clone()));

        match self.request_mode {
            MdocPrivateItemRequestMode::ValueEquality => {
                eval.add_constraint(element_value_active.clone() - value_scope_active.clone());
                eval.add_constraint(element_value_end.clone() - value_scope_end.clone());
                eval.add_constraint(element_value_start.clone() * element_value_index.clone());
                eval.add_constraint(
                    element_value_active.clone() * (output_byte.clone() - byte.clone()),
                );
                for unused in [
                    value_head.clone(),
                    value_direct.clone(),
                    value_tagged.clone(),
                    array_member_head.clone(),
                    array_member_text.clone(),
                ] {
                    eval.add_constraint(unused);
                }
                eval.add_constraint(inner.clone() * value_head_seen.clone());
                eval.add_constraint(inner.clone() * array_member_seen_count.clone());
            }
            request_mode => {
                let normalized_len = request_mode
                    .normalized_len()
                    .expect("predicate request modes have fixed normalized lengths");
                eval.add_constraint(
                    (inner.clone() - inner_end.clone())
                        * (value_head_seen_next - value_head_seen.clone() - value_head_next),
                );
                eval.add_constraint(inner_start.clone() * value_head_seen.clone());
                eval.add_constraint(inner_end.clone() * (value_head_seen - one.clone()));
                eval.add_constraint(value_head.clone() * (one.clone() - inner.clone()));
                eval.add_constraint(
                    element_value_active_next - element_value_active.clone() - value_head.clone()
                        + element_value_end.clone(),
                );
                eval.add_constraint(value_head.clone() * element_value_active.clone());
                eval.add_constraint(value_head.clone() * element_value_index_next.clone());
                eval.add_constraint(element_value_active.clone() * header.clone());
                eval.add_constraint(
                    element_value_end.clone()
                        * (element_value_index.clone() + one.clone()
                            - m31_const::<E>(normalized_len as u32)),
                );
                eval.add_constraint(
                    element_value_active.clone()
                        * (output_byte.clone() - sum_bits::<E>(&date_digit_bits[..8])),
                );

                match request_mode {
                    MdocPrivateItemRequestMode::BirthDate => {
                        let packed = element_value_start.clone()
                            - value_direct.clone()
                            - value_tagged.clone();
                        eval.add_constraint(packed.clone() * (packed.clone() - one.clone()));
                        eval.add_constraint(
                            value_direct.clone() * (one.clone() - element_value_start.clone()),
                        );
                        eval.add_constraint(
                            value_tagged.clone() * (one.clone() - element_value_start.clone()),
                        );
                        eval.add_constraint(value_direct.clone() * value_tagged.clone());
                        eval.add_constraint(
                            (packed.clone() + value_direct.clone())
                                * (one.clone() - value_head.clone()),
                        );

                        pin(&mut eval, packed.clone(), byte.clone(), 0x44);
                        pin(&mut eval, packed.clone(), major.clone(), 2);
                        pin(
                            &mut eval,
                            packed.clone(),
                            content_len.clone(),
                            BIRTH_DATE_PACKED_BYTES as u32,
                        );

                        let text_head = value_head.clone() - packed.clone();
                        pin(&mut eval, text_head.clone(), byte.clone(), 0x6a);
                        pin(&mut eval, text_head.clone(), major.clone(), 3);
                        pin(
                            &mut eval,
                            text_head.clone(),
                            content_len.clone(),
                            BIRTH_DATE_TEXT_BYTES as u32,
                        );
                        pin(&mut eval, value_tagged.clone(), byte.clone(), 0xd9);
                        pin(&mut eval, value_tagged.clone(), major.clone(), 6);
                        pin(
                            &mut eval,
                            value_tagged.clone(),
                            argument[0].clone(),
                            CBOR_TAG_FULL_DATE,
                        );
                        for limb in &argument[1..] {
                            pin(&mut eval, value_tagged.clone(), limb.clone(), 0);
                        }
                        let nested_head = text_head.clone() - value_direct.clone();
                        pin(&mut eval, nested_head.clone(), depth.clone(), 2);
                        eval.add_constraint(
                            nested_head.clone() * (parent.clone() - value_root_index.clone()),
                        );
                        pin(&mut eval, nested_head.clone(), ordinal.clone(), 0);
                        pin(&mut eval, nested_head.clone(), map_key.clone(), 0);
                        pin(&mut eval, nested_head, map_value.clone(), 0);

                        for offset in 1..=BIRTH_DATE_PACKED_BYTES {
                            eval.add_constraint(
                                packed.clone()
                                    * (output_byte_window[offset].clone()
                                        - byte_window[offset].clone()),
                            );
                        }
                        pin(
                            &mut eval,
                            text_head.clone(),
                            byte_window[5].clone(),
                            b'-' as u32,
                        );
                        pin(
                            &mut eval,
                            text_head.clone(),
                            byte_window[8].clone(),
                            b'-' as u32,
                        );
                        let digit_positions = [1usize, 2, 3, 4, 6, 7, 9, 10];
                        let digits: [E::F; BIRTH_DATE_DIGITS] = std::array::from_fn(|index| {
                            sum_bits::<E>(
                                &date_digit_bits[index * BIRTH_DATE_DIGIT_BITS
                                    ..(index + 1) * BIRTH_DATE_DIGIT_BITS],
                            )
                        });
                        for (index, position) in digit_positions.into_iter().enumerate() {
                            eval.add_constraint(
                                text_head.clone()
                                    * (byte_window[position].clone()
                                        - m31_const::<E>(u32::from(b'0'))
                                        - digits[index].clone()),
                            );
                            let bits = &date_digit_bits[index * BIRTH_DATE_DIGIT_BITS
                                ..(index + 1) * BIRTH_DATE_DIGIT_BITS];
                            eval.add_constraint(
                                text_head.clone() * bits[3].clone() * bits[2].clone(),
                            );
                            eval.add_constraint(
                                text_head.clone() * bits[3].clone() * bits[1].clone(),
                            );
                        }
                        let year = m31_const::<E>(1000) * digits[0].clone()
                            + m31_const::<E>(100) * digits[1].clone()
                            + m31_const::<E>(10) * digits[2].clone()
                            + digits[3].clone();
                        let month = m31_const::<E>(10) * digits[4].clone() + digits[5].clone();
                        let day = m31_const::<E>(10) * digits[6].clone() + digits[7].clone();
                        eval.add_constraint(
                            text_head.clone()
                                * (m31_const::<E>(256) * output_byte_window[1].clone()
                                    + output_byte_window[2].clone()
                                    - year),
                        );
                        eval.add_constraint(
                            text_head.clone() * (output_byte_window[3].clone() - month),
                        );
                        eval.add_constraint(text_head * (output_byte_window[4].clone() - day));
                        for unused in [array_member_head.clone(), array_member_text.clone()] {
                            eval.add_constraint(unused);
                        }
                        eval.add_constraint(inner.clone() * array_member_seen_count.clone());
                    }
                    MdocPrivateItemRequestMode::Nationality => {
                        eval.add_constraint(
                            value_direct.clone() + value_tagged.clone()
                                - element_value_start.clone(),
                        );
                        eval.add_constraint(
                            (inner.clone() - inner_end.clone())
                                * (nationality_member_count_next.clone()
                                    - nationality_member_count.clone()),
                        );
                        eval.add_constraint(
                            element_value_start.clone()
                                * (nationality_member_count.clone()
                                    - one.clone()
                                    - sum_bits::<E>(&nationality_count_bits)),
                        );
                        eval.add_constraint(
                            value_direct.clone() * (nationality_member_count.clone() - one.clone()),
                        );
                        pin(&mut eval, value_tagged.clone(), major.clone(), 4);
                        eval.add_constraint(
                            value_tagged.clone()
                                * (byte.clone()
                                    - m31_const::<E>(0x80)
                                    - nationality_member_count.clone()),
                        );
                        eval.add_constraint(
                            value_tagged.clone()
                                * (argument[0].clone() - nationality_member_count.clone()),
                        );
                        for limb in &argument[1..] {
                            pin(&mut eval, value_tagged.clone(), limb.clone(), 0);
                        }

                        eval.add_constraint(
                            (inner.clone() - inner_end.clone())
                                * (array_member_seen_count_next
                                    - array_member_seen_count.clone()
                                    - array_member_head_next),
                        );
                        eval.add_constraint(inner_start.clone() * array_member_seen_count.clone());
                        eval.add_constraint(
                            inner_end.clone()
                                * (array_member_seen_count.clone()
                                    - nationality_member_count.clone()),
                        );
                        eval.add_constraint(
                            value_direct.clone() * (one.clone() - array_member_head.clone()),
                        );
                        pin(&mut eval, array_member_head.clone(), header.clone(), 1);
                        pin(
                            &mut eval,
                            array_member_head.clone(),
                            content_len.clone(),
                            NATIONALITY_BYTES as u32,
                        );
                        pin(&mut eval, array_member_head.clone(), map_key.clone(), 0);
                        eval.add_constraint(
                            array_member_head.clone() * (major.clone() - m31_const::<E>(2))
                                - array_member_text.clone(),
                        );
                        eval.add_constraint(
                            array_member_head.clone() * (byte.clone() - m31_const::<E>(0x42))
                                - m31_const::<E>(0x20) * array_member_text.clone(),
                        );
                        let array_child_head = array_member_head.clone() - value_direct.clone();
                        eval.add_constraint(
                            array_child_head.clone()
                                * (ordinal.clone() + one.clone() - array_member_seen_count.clone()),
                        );
                        pin(&mut eval, array_child_head.clone(), depth.clone(), 2);
                        eval.add_constraint(
                            array_child_head.clone() * (parent.clone() - value_root_index.clone()),
                        );
                        pin(&mut eval, array_child_head.clone(), map_value.clone(), 0);

                        eval.add_constraint(
                            value_head.clone() * (one.clone() - array_member_head.clone()),
                        );
                        eval.add_constraint(
                            nationality_selected_text.clone() * (one.clone() - value_head.clone()),
                        );
                        eval.add_constraint(
                            value_head.clone()
                                * (nationality_selected_text.clone() - array_member_text.clone()),
                        );
                        for folded in &nationality_case_fold {
                            eval.add_constraint(
                                value_head.clone()
                                    * folded.clone()
                                    * (one.clone() - nationality_selected_text.clone()),
                            );
                        }
                        let numeric_head = value_head.clone() - nationality_selected_text.clone();
                        for payload in [
                            country_lookup_num_hi.clone(),
                            country_lookup_num_lo.clone(),
                            country_lookup_upper_0.clone(),
                            country_lookup_upper_1.clone(),
                        ] {
                            eval.add_constraint(numeric_head.clone() * payload);
                        }
                        eval.add_constraint(
                            numeric_head.clone()
                                * (output_byte_window[1].clone() - byte_window[1].clone()),
                        );
                        eval.add_constraint(
                            numeric_head * (output_byte_window[2].clone() - byte_window[2].clone()),
                        );
                        eval.add_constraint(
                            nationality_selected_text.clone()
                                * (country_lookup_num_hi.clone() - output_byte_window[1].clone()),
                        );
                        eval.add_constraint(
                            nationality_selected_text.clone()
                                * (country_lookup_num_lo.clone() - output_byte_window[2].clone()),
                        );
                        eval.add_constraint(
                            nationality_selected_text.clone()
                                * (country_lookup_upper_0.clone() - byte_window[1].clone()
                                    + m31_const::<E>(32) * nationality_case_fold[0].clone()),
                        );
                        eval.add_constraint(
                            nationality_selected_text.clone()
                                * (country_lookup_upper_1.clone() - byte_window[2].clone()
                                    + m31_const::<E>(32) * nationality_case_fold[1].clone()),
                        );
                    }
                    MdocPrivateItemRequestMode::ValueEquality => {
                        unreachable!("handled above")
                    }
                }
            }
        }

        eval.add_constraint(
            element_value_end.clone() * (one.clone() - element_value_active.clone()),
        );
        eval.add_constraint(
            (element_value_active.clone() - element_value_end.clone())
                * (element_value_index_next - element_value_index.clone() - one.clone()),
        );

        let outer_tuple = parsed_tuple::<E>(
            self.field_ids.outer_stream,
            stream_index.clone(),
            byte.clone(),
            header.clone(),
            major.clone(),
            &argument,
            content_len.clone(),
            depth.clone(),
            parent.clone(),
            ordinal.clone(),
            map_key.clone(),
            map_value.clone(),
        );
        eval.add_to_relation(RelationEntry::new(
            &self.outer_parsed,
            E::EF::from(outer.clone()),
            &outer_tuple,
        ));
        let inner_tuple = parsed_tuple::<E>(
            self.field_ids.inner_stream,
            stream_index,
            byte.clone(),
            header,
            major,
            &argument,
            content_len,
            depth,
            parent,
            ordinal,
            map_key,
            map_value,
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
                is_v2,
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
                output_byte,
            ],
        ));
        if matches!(self.profile, MdocPrivateItemProfile::Ts13) {
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
        }
        if matches!(self.request_mode, MdocPrivateItemRequestMode::Nationality) {
            eval.add_to_relation(RelationEntry::new(
                &self.country_code,
                E::EF::from(value_head),
                &[
                    nationality_selected_text,
                    country_lookup_num_hi,
                    country_lookup_num_lo,
                    country_lookup_upper_0,
                    country_lookup_upper_1,
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
    profile: MdocPrivateItemProfile,
    request_mode: MdocPrivateItemRequestMode,
    field_ids: MdocPrivateItemFieldIds,
    item_fields: &FieldBytesRelation,
    outer_parsed: &ParsedCborByteRelation,
    inner_parsed: &ParsedCborByteRelation,
    inner_raw: &FieldBytesRelation,
    digest_id: &MdocPrivateDigestIdRelation,
    country_code: &SharedMdocCountryCodeRelation,
    key_relation: &MdocPrivateItemKeyRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<Column>, QM31) {
    let base = witness.trace(log_size);
    let preprocessed = preprocessed_columns(log_size);
    let packed_rows = 1usize << (log_size - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(KEY_ENCODED_BYTES + 9 + TS13_SEMANTIC_TUPLES);
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
                            -PackedQM31::from(preprocessed[0].data[row]),
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
                        base[trace_col::IS_V2].data[row],
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
            trace_col::VALUE_OUTPUT_BYTE,
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
    if matches!(profile, MdocPrivateItemProfile::Ts13) {
        for (field_id, index, byte) in ts13_semantic_tuples(field_ids) {
            sites.push(
                (0..packed_rows)
                    .map(|row| {
                        (
                            PackedQM31::from(preprocessed[0].data[row]),
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
    }
    if matches!(request_mode, MdocPrivateItemRequestMode::Nationality) {
        let country_code = country_code.get();
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    (
                        PackedQM31::from(base[trace_col::VALUE_HEAD].data[row]),
                        country_code.combine(&[
                            base[trace_col::NAT_SELECTED_TEXT].data[row],
                            base[trace_col::COUNTRY_LOOKUP_NUM_HI].data[row],
                            base[trace_col::COUNTRY_LOOKUP_NUM_LO].data[row],
                            base[trace_col::COUNTRY_LOOKUP_UPPER_0].data[row],
                            base[trace_col::COUNTRY_LOOKUP_UPPER_1].data[row],
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
/// Relation polarity is from this component's point of view:
///
/// - `outer_parsed` and `inner_parsed`: positive consumers of the two CBOR
///   parsers;
/// - `inner_raw`: negative provider for the raw inner parser;
/// - `digest_id`: negative provider for the MSO `valueDigests` scan;
/// - `item_fields`: negative provider of the identifier content plus either
///   the full encoded `elementValue` or normalized predicate bytes. TS13 also
///   provides the exact fixed positive counterparts inside this component.
/// - `country_code`: one positive dummy/alpha-2 lookup for nationality only.
///
/// The outer parser is itself fed by the SHA full-padded-stream relation.  Thus
/// the composed path binds every private SHA-padded byte without placing the
/// raw item length, random length, offsets, digest ID, or contents in tree zero.
pub(crate) struct MdocPrivateItemBind {
    attribute_index: usize,
    profile: MdocPrivateItemProfile,
    request_mode: MdocPrivateItemRequestMode,
    bucket: usize,
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
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        attribute_index: usize,
        profile: MdocPrivateItemProfile,
        version: MdocPrivateMsoVersion,
        request_mode: MdocPrivateItemRequestMode,
        bucket: usize,
        private_input: MdocPrivateItemPrivateInput,
        field_ids: MdocPrivateItemFieldIds,
        handles: MdocPrivateItemHandles,
    ) -> Result<Self, MdocPrivateItemError> {
        if attribute_index >= MDOC_PRIVATE_ITEM_MAX_ATTRIBUTES {
            return Err(MdocPrivateItemError::AttributeIndexOutOfRange(
                attribute_index,
            ));
        }
        if matches!(profile, MdocPrivateItemProfile::Ts13)
            && !matches!(request_mode, MdocPrivateItemRequestMode::ValueEquality)
        {
            return Err(MdocPrivateItemError::Ts13RequiresValueEquality);
        }
        let log_size = profile_log_size(bucket)?;
        let witness = MdocPrivateItemWitness::new(
            private_input,
            bucket,
            log_size,
            profile,
            version,
            request_mode,
        )?;
        Ok(Self {
            attribute_index,
            profile,
            request_mode,
            bucket,
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
        attribute_index: usize,
        profile: MdocPrivateItemProfile,
        request_mode: MdocPrivateItemRequestMode,
        bucket: usize,
        field_ids: MdocPrivateItemFieldIds,
        handles: MdocPrivateItemHandles,
        interaction_claim: MdocPrivateItemInteractionClaim,
    ) -> Result<Self, MdocPrivateItemError> {
        if attribute_index >= MDOC_PRIVATE_ITEM_MAX_ATTRIBUTES {
            return Err(MdocPrivateItemError::AttributeIndexOutOfRange(
                attribute_index,
            ));
        }
        if matches!(profile, MdocPrivateItemProfile::Ts13)
            && !matches!(request_mode, MdocPrivateItemRequestMode::ValueEquality)
        {
            return Err(MdocPrivateItemError::Ts13RequiresValueEquality);
        }
        let log_size = profile_log_size(bucket)?;
        Ok(Self {
            attribute_index,
            profile,
            request_mode,
            bucket,
            log_size,
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
        })
    }

    #[cfg(test)]
    pub(crate) fn attribute_index(&self) -> usize {
        self.attribute_index
    }

    #[cfg(test)]
    pub(crate) fn padded_bucket(&self) -> usize {
        self.bucket
    }

    #[cfg(test)]
    pub(crate) fn request_mode(&self) -> MdocPrivateItemRequestMode {
        self.request_mode
    }

    #[cfg(test)]
    pub(crate) fn log_size(&self) -> u32 {
        self.log_size
    }

    pub(crate) fn outer_parser_log_size(&self) -> u32 {
        parser_log_size(self.bucket).expect("validated private item bucket")
    }

    pub(crate) fn inner_parser_log_size(&self) -> u32 {
        // Every accepted inner item is below 192 bytes, and the parser adds
        // 256 blind rows with a minimum log size of nine.
        parser_log_size(MDOC_PRIVATE_ITEM_MAX_VALUE_BYTES)
            .expect("private item cap has a parser domain")
    }

    pub(crate) fn inner_bytes(&self) -> &[u8] {
        self.witness
            .as_ref()
            .expect("private item prover has a witness")
            .inner_bytes
            .as_slice()
    }

    pub(crate) fn country_code_uses(&self) -> &MdocCountryCodeUses {
        &self
            .witness
            .as_ref()
            .expect("private item prover has a witness")
            .country_uses
    }

    #[cfg(test)]
    pub(crate) fn private_country_tuple(&self) -> Option<MdocCountryCodeTuple> {
        self.witness
            .as_ref()
            .expect("private item prover has a witness")
            .country_tuple
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
        // Outer parsed, inner parsed, inner raw, key witness, 47 key constants,
        // digest tuple, identifier field, value field, the TS13 fixed semantic
        // counterparts, optional country lookup, and the final blinder.
        KEY_ENCODED_BYTES
            + 8
            + usize::from(matches!(self.profile, MdocPrivateItemProfile::Ts13))
                * TS13_SEMANTIC_TUPLES
            + usize::from(matches!(
                self.request_mode,
                MdocPrivateItemRequestMode::Nationality
            ))
    }
}

impl Air for MdocPrivateItemBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(MDOC_PRIVATE_ITEM_DOMAIN);
        channel.mix_u64(MDOC_PRIVATE_ITEM_VERSION);
        channel.mix_u64(self.profile.transcript_tag());
        channel.mix_u64(self.request_mode.transcript_tag());
        channel.mix_u64(self.attribute_index as u64);
        channel.mix_u64(self.bucket as u64);
        channel.mix_u64(u64::from(self.log_size));
        channel.mix_u64(u64::from(self.outer_parser_log_size()));
        channel.mix_u64(u64::from(self.inner_parser_log_size()));
        channel.mix_u64(MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES as u64);
        channel.mix_u64(MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES as u64);
        channel.mix_u64(MDOC_PRIVATE_ITEM_MAX_VALUE_BYTES as u64);
        channel.mix_u64(MDOC_PRIVATE_ITEM_MAX_NATIONALITY_MEMBERS as u64);
        channel.mix_u64(u64::from(self.profile.digest_id_max()));
        channel.mix_u64(u64::from(self.field_ids.outer_stream));
        channel.mix_u64(u64::from(self.field_ids.inner_stream));
        channel.mix_u64(u64::from(self.field_ids.element_identifier));
        channel.mix_u64(u64::from(self.field_ids.element_value));
        channel.mix_u64(self.main_interaction_sites() as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        if matches!(self.request_mode, MdocPrivateItemRequestMode::Nationality) {
            assert!(
                self.handles.country_code.is_set(),
                "country-code table must draw the nationality relation before the item binder"
            );
        }
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
                profile: self.profile,
                request_mode: self.request_mode,
                field_ids: self.field_ids,
                item_fields: self.item_fields(),
                outer_parsed: self.outer_parsed(),
                inner_parsed: self.inner_parsed(),
                inner_raw: self.inner_raw(),
                digest_id: self.digest_id(),
                country_code: if matches!(
                    self.request_mode,
                    MdocPrivateItemRequestMode::Nationality
                ) {
                    self.handles.country_code.get()
                } else {
                    MdocCountryCodeRelation::dummy()
                },
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
            self.profile,
            self.request_mode,
            self.field_ids,
            &self.item_fields(),
            &self.outer_parsed(),
            &self.inner_parsed(),
            &self.inner_raw(),
            &self.digest_id(),
            &self.handles.country_code,
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
    use std::collections::VecDeque;

    use crate::mdoc_country_code_table::MdocCountryCodeTable;
    use stwo::prover::ProvingError;
    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    const CANONICAL_ORDER: [usize; KEY_COUNT] = [
        KEY_RANDOM,
        KEY_DIGEST_ID,
        KEY_ELEMENT_VALUE,
        KEY_ELEMENT_IDENTIFIER,
    ];
    const LEGACY_ORDER: [usize; KEY_COUNT] = [
        KEY_ELEMENT_IDENTIFIER,
        KEY_RANDOM,
        KEY_ELEMENT_VALUE,
        KEY_DIGEST_ID,
    ];
    const TEST_IDENTIFIER: &[u8] = TS13_ELEMENT_IDENTIFIER;
    const TEST_VALUE: &[u8] = TS13_CANONICAL_ELEMENT_VALUE;

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
                _ => unreachable!("all test key kinds are covered"),
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

    #[test]
    fn tag24_wrapper_rejections_preserve_exact_token_offsets_and_reasons() {
        let cases = [
            (
                "wrong tag",
                vec![0xd8, 0x17, 0x58, 0x01, 0xa0],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 0,
                    reason: MdocPrivateTag24WrapperReason::ExpectedTag24,
                },
            ),
            (
                "declared length is short",
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
                "declared length is long",
                vec![0xd8, 0x18, 0x58, 0x02, 0xa0],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 3,
                    reason: MdocPrivateTag24WrapperReason::ByteStringLengthMismatch {
                        declared: 2,
                        actual: 1,
                    },
                },
            ),
            (
                "byte-string length is not in u8 form",
                vec![0xd8, 0x18, 0x41, 0xa0],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 2,
                    reason: MdocPrivateTag24WrapperReason::ExpectedU8ByteStringLength {
                        additional: 1,
                    },
                },
            ),
            (
                "missing u8 length",
                vec![0xd8, 0x18, 0x58],
                MdocPrivateItemError::InvalidTag24Wrapper {
                    offset: 3,
                    reason: MdocPrivateTag24WrapperReason::TruncatedToken { needed: 1 },
                },
            ),
        ];

        for (name, outer, expected) in cases {
            let padded = stwo_sha256::native::pad_message(&outer);
            let error = match extract_outer_and_inner(&padded) {
                Ok(_) => panic!("{name} unexpectedly parsed"),
                Err(error) => error,
            };
            assert_eq!(error, expected, "{name}");
        }
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

    fn test_bind_with(
        profile: MdocPrivateItemProfile,
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        test_bind_with_version(
            profile,
            MdocPrivateMsoVersion::V2,
            order,
            random_len,
            digest_id,
            identifier,
            element_value,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn test_bind_with_version(
        profile: MdocPrivateItemProfile,
        version: MdocPrivateMsoVersion,
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        test_bind_mode_with_version(
            profile,
            version,
            MdocPrivateItemRequestMode::ValueEquality,
            None,
            order,
            random_len,
            digest_id,
            identifier,
            element_value,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn test_bind_mode_with(
        profile: MdocPrivateItemProfile,
        request_mode: MdocPrivateItemRequestMode,
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        test_bind_mode_with_version(
            profile,
            MdocPrivateMsoVersion::V2,
            request_mode,
            None,
            order,
            random_len,
            digest_id,
            identifier,
            element_value,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn test_bind_mode_with_selection(
        profile: MdocPrivateItemProfile,
        request_mode: MdocPrivateItemRequestMode,
        nationality_member_index: Option<u8>,
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        test_bind_mode_with_version(
            profile,
            MdocPrivateMsoVersion::V2,
            request_mode,
            nationality_member_index,
            order,
            random_len,
            digest_id,
            identifier,
            element_value,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn test_bind_mode_with_version(
        profile: MdocPrivateItemProfile,
        version: MdocPrivateMsoVersion,
        request_mode: MdocPrivateItemRequestMode,
        nationality_member_index: Option<u8>,
        order: [usize; KEY_COUNT],
        random_len: usize,
        digest_id: u32,
        identifier: &[u8],
        element_value: &[u8],
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        let padded = padded_item(order, random_len, digest_id, identifier, element_value);
        MdocPrivateItemBind::new(
            0,
            profile,
            version,
            request_mode,
            padded.len(),
            MdocPrivateItemPrivateInput {
                padded_item: padded,
                nationality_member_index,
            },
            field_ids(),
            MdocPrivateItemHandles::fresh(
                SharedFieldRelation::new(),
                SharedMdocCountryCodeRelation::new(),
            ),
        )
    }

    fn test_bind(
        profile: MdocPrivateItemProfile,
        digest_id: u32,
    ) -> Result<MdocPrivateItemBind, MdocPrivateItemError> {
        test_bind_with(
            profile,
            CANONICAL_ORDER,
            16,
            digest_id,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
    }

    fn parsed_inner(inner: &[u8]) -> MdocCborWitness {
        MdocCborWitness::new(inner, MdocCborInputMode::Raw).unwrap()
    }

    const TEST_COUNTER_DOMAIN: u64 = 0x4d44_4f43_4954_4354;
    const TEST_ITEM_FIELDS: usize = 0;
    const TEST_OUTER_PARSED: usize = 1;
    const TEST_INNER_PARSED: usize = 2;
    const TEST_INNER_RAW: usize = 3;
    const TEST_DIGEST_ID: usize = 4;
    const TEST_COUNTER_SELECTORS: usize = 5;
    const TEST_COUNTER_VALUES: usize = 15;
    const TEST_COUNTER_COLS: usize = TEST_COUNTER_SELECTORS + TEST_COUNTER_VALUES;

    #[derive(Clone)]
    struct TestCounterRow {
        kind: usize,
        values: [M31; TEST_COUNTER_VALUES],
    }

    impl TestCounterRow {
        fn new(kind: usize, values: &[M31]) -> Self {
            let mut row = Self {
                kind,
                values: [m31(0); TEST_COUNTER_VALUES],
            };
            row.values[..values.len()].copy_from_slice(values);
            row
        }
    }

    fn test_counter_log_size(rows: usize) -> u32 {
        rows.next_power_of_two().ilog2().max(LOG_N_LANES)
    }

    fn test_counter_columns(rows: &[TestCounterRow], log_size: u32) -> Vec<Vec<M31>> {
        let mut columns = vec![vec![m31(0); 1usize << log_size]; TEST_COUNTER_COLS];
        for (row_index, row) in rows.iter().enumerate() {
            columns[row.kind][row_index] = m31(1);
            for (value_index, value) in row.values.iter().copied().enumerate() {
                columns[TEST_COUNTER_SELECTORS + value_index][row_index] = value;
            }
        }
        columns
    }

    fn test_counter_evals(rows: &[TestCounterRow], log_size: u32) -> Vec<Column> {
        test_counter_columns(rows, log_size)
            .into_iter()
            .map(|values| column(log_size, values))
            .collect()
    }

    #[derive(Clone)]
    struct TestCounterEval {
        log_size: u32,
        item_fields: FieldBytesRelation,
        outer_parsed: ParsedCborByteRelation,
        inner_parsed: ParsedCborByteRelation,
        inner_raw: FieldBytesRelation,
        digest_id: MdocPrivateDigestIdRelation,
    }

    impl FrameworkEval for TestCounterEval {
        fn log_size(&self) -> u32 {
            self.log_size
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size + 2
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let selectors: [E::F; TEST_COUNTER_SELECTORS] =
                std::array::from_fn(|_| eval.next_trace_mask());
            let values: [E::F; TEST_COUNTER_VALUES] =
                std::array::from_fn(|_| eval.next_trace_mask());
            let one = m31_const::<E>(1);
            let selector_sum = selectors
                .iter()
                .cloned()
                .fold(m31_const::<E>(0), |sum, selector| sum + selector);
            for selector in &selectors {
                eval.add_constraint(selector.clone() * (one.clone() - selector.clone()));
            }
            eval.add_constraint(selector_sum.clone() * (one - selector_sum));
            eval.add_to_relation(RelationEntry::new(
                &self.item_fields,
                E::EF::from(selectors[TEST_ITEM_FIELDS].clone()),
                &values[..3],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.outer_parsed,
                -E::EF::from(selectors[TEST_OUTER_PARSED].clone()),
                &values,
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.inner_parsed,
                -E::EF::from(selectors[TEST_INNER_PARSED].clone()),
                &values,
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.inner_raw,
                E::EF::from(selectors[TEST_INNER_RAW].clone()),
                &values[..3],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.digest_id,
                E::EF::from(selectors[TEST_DIGEST_ID].clone()),
                &values[..digest_id_tuple::ARITY],
            ));
            eval.finalize_logup_in_pairs();
            eval
        }
    }

    fn test_counter_interaction(
        rows: &[TestCounterRow],
        log_size: u32,
        handles: &MdocPrivateItemHandles,
    ) -> (Vec<Column>, QM31) {
        let trace = test_counter_evals(rows, log_size);
        let packed_rows = 1usize << (log_size - LOG_N_LANES);
        let values = |row: usize| -> [PackedM31; TEST_COUNTER_VALUES] {
            std::array::from_fn(|index| trace[TEST_COUNTER_SELECTORS + index].data[row])
        };
        let mut sites = Vec::with_capacity(TEST_COUNTER_SELECTORS);
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        PackedQM31::from(trace[TEST_ITEM_FIELDS].data[row]),
                        handles.item_fields.get().combine(&values[..3]),
                    )
                })
                .collect::<Vec<_>>(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        -PackedQM31::from(trace[TEST_OUTER_PARSED].data[row]),
                        handles.outer_parsed.get().combine(&values),
                    )
                })
                .collect::<Vec<_>>(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        -PackedQM31::from(trace[TEST_INNER_PARSED].data[row]),
                        handles.inner_parsed.get().combine(&values),
                    )
                })
                .collect::<Vec<_>>(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        PackedQM31::from(trace[TEST_INNER_RAW].data[row]),
                        handles.inner_raw.get().combine(&values[..3]),
                    )
                })
                .collect::<Vec<_>>(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        PackedQM31::from(trace[TEST_DIGEST_ID].data[row]),
                        handles
                            .digest_id
                            .get()
                            .combine(&values[..digest_id_tuple::ARITY]),
                    )
                })
                .collect::<Vec<_>>(),
        );

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
        logup.col_from_iter((0..packed_rows).map(|row| sites[site][row]));
        logup.finalize_last()
    }

    struct TestRelationCounter {
        rows: Vec<TestCounterRow>,
        log_size: u32,
        handles: MdocPrivateItemHandles,
        component: Option<FrameworkComponent<TestCounterEval>>,
    }

    impl TestRelationCounter {
        fn new(rows: Vec<TestCounterRow>, handles: MdocPrivateItemHandles) -> Self {
            Self {
                log_size: test_counter_log_size(rows.len()),
                rows,
                handles,
                component: None,
            }
        }

        fn interaction(&self) -> (Vec<Column>, QM31) {
            test_counter_interaction(&self.rows, self.log_size, &self.handles)
        }
    }

    impl Air for TestRelationCounter {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_u64(TEST_COUNTER_DOMAIN);
            channel.mix_u64(u64::from(self.log_size));
            channel.mix_u64(self.rows.len() as u64);
        }

        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            assert!(!self.handles.item_fields.is_set());
            assert!(!self.handles.outer_parsed.is_set());
            assert!(!self.handles.inner_parsed.is_set());
            self.handles
                .item_fields
                .set(FieldBytesRelation::draw(channel));
            self.handles
                .outer_parsed
                .set(ParsedCborByteRelation::draw(channel));
            self.handles
                .inner_parsed
                .set(ParsedCborByteRelation::draw(channel));
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: Vec::new(),
                trace: vec![self.log_size; TEST_COUNTER_COLS],
                interaction: vec![
                    self.log_size;
                    TEST_COUNTER_SELECTORS.div_ceil(2) * SECURE_EXTENSION_DEGREE
                ],
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
                    item_fields: self.handles.item_fields.get(),
                    outer_parsed: self.handles.outer_parsed.get(),
                    inner_parsed: self.handles.inner_parsed.get(),
                    inner_raw: self.handles.inner_raw.get(),
                    digest_id: self.handles.digest_id.get(),
                },
                self.interaction().1,
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().unwrap()]
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

        fn write_preprocessed(&mut self, _tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

        fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
            Vec::new()
        }

        fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tree.extend_evals(test_counter_evals(&self.rows, self.log_size));
        }

        fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tree.extend_evals(self.interaction().0);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self.component.as_ref().unwrap()]
        }
    }

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn for_row(witness: &MdocPrivateItemWitness, log_size: u32, row: usize) -> Self {
            let rows = 1usize << log_size;
            let at = |column: usize, offset: usize| witness.columns[column][(row + offset) % rows];
            let mut eval = Self::default();
            eval.preprocessed.push_back(vec![m31(u32::from(row == 0))]);
            eval.preprocessed
                .push_back(vec![m31(u32::from(row + 1 == rows))]);
            for prefix in 0..OUTER_PREFIX_BYTES {
                eval.preprocessed
                    .push_back(vec![m31(u32::from(row == prefix))]);
            }

            let pair_columns = [
                trace_col::ACTIVE,
                trace_col::OUTER,
                trace_col::INNER,
                trace_col::INNER_START,
                trace_col::STREAM_INDEX,
                trace_col::INNER_LEN,
                trace_col::KEY_ACTIVE,
                trace_col::KEY_ACTIVE + 1,
                trace_col::KEY_ACTIVE + 2,
                trace_col::KEY_ACTIVE + 3,
                trace_col::KEY_START,
                trace_col::KEY_START + 1,
                trace_col::KEY_START + 2,
                trace_col::KEY_START + 3,
                trace_col::KEY_SEEN,
                trace_col::KEY_SEEN + 1,
                trace_col::KEY_SEEN + 2,
                trace_col::KEY_SEEN + 3,
                trace_col::KEY_INDEX,
                trace_col::VALUE_START,
                trace_col::VALUE_START + 1,
                trace_col::VALUE_START + 2,
                trace_col::VALUE_START + 3,
                trace_col::IDENTIFIER_LONG_ARG,
                trace_col::IDENTIFIER_CONTENT_START,
                trace_col::IDENTIFIER_CONTENT_ACTIVE,
                trace_col::IDENTIFIER_CONTENT_INDEX,
                trace_col::IDENTIFIER_LEN,
                trace_col::VALUE_ACTIVE,
                trace_col::VALUE_INDEX,
                trace_col::VALUE_SCOPE_ACTIVE,
                trace_col::VALUE_ROOT_INDEX,
                trace_col::VALUE_HEAD,
                trace_col::VALUE_HEAD_SEEN,
                trace_col::ARRAY_MEMBER_HEAD,
                trace_col::ARRAY_MEMBER_SEEN_COUNT,
                trace_col::IS_V2,
                trace_col::NAT_MEMBER_COUNT,
            ];
            for column in 0..trace_col::COUNT {
                let values = if column == trace_col::BYTE {
                    (0..=BIRTH_DATE_TEXT_BYTES)
                        .map(|offset| at(column, offset))
                        .collect()
                } else if column == trace_col::VALUE_OUTPUT_BYTE {
                    (0..=BIRTH_DATE_PACKED_BYTES)
                        .map(|offset| at(column, offset))
                        .collect()
                } else if pair_columns.contains(&column) {
                    vec![at(column, 0), at(column, 1)]
                } else {
                    vec![at(column, 0)]
                };
                eval.original.push_back(values);
            }
            eval
        }

        fn nonzero_constraints(&self) -> Vec<(usize, QM31)> {
            self.constraints
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| *value != QM31::from_u32_unchecked(0, 0, 0, 0))
                .collect()
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
                _ => panic!("unexpected interaction index {interaction}"),
            };
            let values = queue
                .pop_front()
                .unwrap_or_else(|| panic!("missing mask for interaction {interaction}"));
            assert_eq!(values.len(), N, "mask arity mismatch");
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

    fn test_eval(bind: &MdocPrivateItemBind) -> MdocPrivateItemEval {
        MdocPrivateItemEval {
            log_size: bind.log_size,
            profile: bind.profile,
            request_mode: bind.request_mode,
            field_ids: bind.field_ids,
            item_fields: FieldBytesRelation::dummy(),
            outer_parsed: ParsedCborByteRelation::dummy(),
            inner_parsed: ParsedCborByteRelation::dummy(),
            inner_raw: FieldBytesRelation::dummy(),
            digest_id: MdocPrivateDigestIdRelation::dummy(),
            country_code: MdocCountryCodeRelation::dummy(),
            key_relation: MdocPrivateItemKeyRelation::dummy(),
            blinder_relation: ClaimedSumBlinderRelation::dummy(),
            blinder_v: qm31(7),
            blinder_m: qm31(11),
        }
    }

    fn assert_witness_satisfies_air(bind: &MdocPrivateItemBind) {
        let witness = bind.witness.as_ref().unwrap();
        for row in 0..1usize << bind.log_size {
            let evaluated = test_eval(bind).evaluate(RowEval::for_row(witness, bind.log_size, row));
            let nonzero = evaluated.nonzero_constraints();
            assert!(
                nonzero.is_empty(),
                "honest row {row} violates constraints: {nonzero:?}"
            );
        }
    }

    fn assert_mutated_row_rejected(
        bind: &MdocPrivateItemBind,
        witness: &MdocPrivateItemWitness,
        row: usize,
    ) {
        let evaluated = test_eval(bind).evaluate(RowEval::for_row(witness, bind.log_size, row));
        assert!(
            !evaluated.nonzero_constraints().is_empty(),
            "mutated row {row} unexpectedly satisfies the AIR"
        );
    }

    #[test]
    fn constructors_enforce_public_shape_and_profile_order() {
        let canonical = test_bind(MdocPrivateItemProfile::Product, 7).unwrap();
        assert_eq!(canonical.attribute_index(), 0);
        assert_eq!(canonical.padded_bucket(), 128);
        assert_eq!(canonical.log_size(), 9);
        assert_eq!(canonical.outer_parser_log_size(), 9);
        assert_eq!(canonical.inner_parser_log_size(), 9);

        assert!(test_bind_with_version(
            MdocPrivateItemProfile::Product,
            MdocPrivateMsoVersion::V1,
            LEGACY_ORDER,
            16,
            7,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
        .is_ok());
        assert_eq!(
            test_bind_with(
                MdocPrivateItemProfile::Product,
                LEGACY_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                TEST_VALUE,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidCanonicalKeyOrder)
        );

        let handles = MdocPrivateItemHandles::fresh(
            SharedFieldRelation::new(),
            SharedMdocCountryCodeRelation::new(),
        );
        assert_eq!(
            MdocPrivateItemBind::verifier(
                MDOC_PRIVATE_ITEM_MAX_ATTRIBUTES,
                MdocPrivateItemProfile::Ts13,
                MdocPrivateItemRequestMode::ValueEquality,
                128,
                field_ids(),
                handles.clone(),
                test_claim(),
            )
            .err(),
            Some(MdocPrivateItemError::AttributeIndexOutOfRange(
                MDOC_PRIVATE_ITEM_MAX_ATTRIBUTES
            ))
        );
        assert_eq!(
            MdocPrivateItemBind::verifier(
                0,
                MdocPrivateItemProfile::Ts13,
                MdocPrivateItemRequestMode::ValueEquality,
                96,
                field_ids(),
                handles,
                test_claim(),
            )
            .err(),
            Some(MdocPrivateItemError::InvalidPaddedBucket(96))
        );
        assert_eq!(
            profile_log_size(usize::from(u16::MAX) + 65),
            Err(MdocPrivateItemError::InvalidPaddedBucket(
                usize::from(u16::MAX) + 65
            ))
        );

        for (bucket, expected_log) in [(64, 9), (128, 9), (192, 10)] {
            let verifier = MdocPrivateItemBind::verifier(
                3,
                MdocPrivateItemProfile::Ts13,
                MdocPrivateItemRequestMode::ValueEquality,
                bucket,
                field_ids(),
                MdocPrivateItemHandles::fresh(
                    SharedFieldRelation::new(),
                    SharedMdocCountryCodeRelation::new(),
                ),
                test_claim(),
            )
            .unwrap();
            assert_eq!(verifier.padded_bucket(), bucket);
            assert_eq!(verifier.log_size(), expected_log);
        }
    }

    #[test]
    fn digest_id_canonical_boundaries_and_profile_caps_are_exact() {
        for digest_id in [0, 23, 24, 255, 256, u16::MAX as u32, u32::MAX] {
            test_bind(MdocPrivateItemProfile::Product, digest_id)
                .unwrap_or_else(|error| panic!("product digest ID {digest_id} failed: {error}"));
        }
        for digest_id in [0, 23, 24, 255, 256, u16::MAX as u32] {
            test_bind(MdocPrivateItemProfile::Ts13, digest_id)
                .unwrap_or_else(|error| panic!("TS13 digest ID {digest_id} failed: {error}"));
        }
        assert_eq!(
            test_bind(MdocPrivateItemProfile::Ts13, u16::MAX as u32 + 1).err(),
            Some(MdocPrivateItemError::DigestIdOutOfRange {
                value: u16::MAX as u64 + 1,
                max: u16::MAX as u32,
            })
        );

        let inner = inner_item_with_digest_encoding(
            CANONICAL_ORDER,
            16,
            &[0x18, 0x07],
            TEST_IDENTIFIER,
            TEST_VALUE,
        );
        let padded = wrap_and_pad(&inner);
        assert!(matches!(
            MdocPrivateItemBind::new(
                0,
                MdocPrivateItemProfile::Product,
                MdocPrivateMsoVersion::V2,
                MdocPrivateItemRequestMode::ValueEquality,
                padded.len(),
                MdocPrivateItemPrivateInput::new(padded),
                field_ids(),
                MdocPrivateItemHandles::fresh(
                    SharedFieldRelation::new(),
                    SharedMdocCountryCodeRelation::new(),
                ),
            ),
            Err(MdocPrivateItemError::InnerParser(_))
        ));
    }

    #[test]
    fn semantic_bounds_and_shifted_key_are_rejected() {
        assert_eq!(
            test_bind_with(
                MdocPrivateItemProfile::Product,
                CANONICAL_ORDER,
                15,
                7,
                TEST_IDENTIFIER,
                TEST_VALUE,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidRandom)
        );
        assert_eq!(
            test_bind_with(
                MdocPrivateItemProfile::Product,
                CANONICAL_ORDER,
                16,
                7,
                b"",
                TEST_VALUE,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidElementIdentifier)
        );

        let oversized_identifier = vec![b'x'; MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES + 1];
        assert_eq!(
            test_bind_with(
                MdocPrivateItemProfile::Product,
                CANONICAL_ORDER,
                16,
                7,
                &oversized_identifier,
                TEST_VALUE,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidElementIdentifier)
        );

        let mut shifted = inner_item(CANONICAL_ORDER, 16, 7, TEST_IDENTIFIER, TEST_VALUE);
        let digest_key = shifted
            .windows(KEY_LABELS[KEY_DIGEST_ID].len())
            .position(|window| window == KEY_LABELS[KEY_DIGEST_ID])
            .expect("fixture contains digestID");
        shifted[digest_key] = b'D';
        let witness = parsed_inner(&shifted);
        assert_eq!(
            analyze_inner(
                &shifted,
                &witness.rows,
                MdocPrivateItemProfile::Product,
                true,
                MdocPrivateItemRequestMode::ValueEquality,
                None,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidIssuerSignedItemRoot)
        );
    }

    #[test]
    fn random_and_identifier_caps_hold_at_host_analysis_boundaries() {
        for random_len in [16, MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES] {
            let inner = inner_item(CANONICAL_ORDER, random_len, 7, TEST_IDENTIFIER, TEST_VALUE);
            let witness = parsed_inner(&inner);
            assert!(analyze_inner(
                &inner,
                &witness.rows,
                MdocPrivateItemProfile::Product,
                true,
                MdocPrivateItemRequestMode::ValueEquality,
                None,
            )
            .is_ok());
        }
        for random_len in [15, MDOC_PRIVATE_ITEM_MAX_RANDOM_BYTES + 1] {
            let inner = inner_item(CANONICAL_ORDER, random_len, 7, TEST_IDENTIFIER, TEST_VALUE);
            let witness = parsed_inner(&inner);
            assert_eq!(
                analyze_inner(
                    &inner,
                    &witness.rows,
                    MdocPrivateItemProfile::Product,
                    true,
                    MdocPrivateItemRequestMode::ValueEquality,
                    None,
                )
                .err(),
                Some(MdocPrivateItemError::InvalidRandom)
            );
        }

        for identifier_len in [1, MDOC_PRIVATE_ITEM_MAX_IDENTIFIER_BYTES] {
            let identifier = vec![b'a'; identifier_len];
            let inner = inner_item(CANONICAL_ORDER, 16, 7, &identifier, TEST_VALUE);
            let witness = parsed_inner(&inner);
            assert!(analyze_inner(
                &inner,
                &witness.rows,
                MdocPrivateItemProfile::Product,
                true,
                MdocPrivateItemRequestMode::ValueEquality,
                None,
            )
            .is_ok());
        }
    }

    fn normalized_output(bind: &MdocPrivateItemBind) -> Vec<u8> {
        let witness = bind.witness.as_ref().unwrap();
        (0..1usize << bind.log_size)
            .filter(|&row| witness.columns[trace_col::VALUE_ACTIVE][row] == m31(1))
            .map(|row| witness.columns[trace_col::VALUE_OUTPUT_BYTE][row].0 as u8)
            .collect()
    }

    fn text_date(tagged: bool) -> Vec<u8> {
        let mut value = if tagged {
            vec![0xd9, 0x03, 0xec, 0x6a]
        } else {
            vec![0x6a]
        };
        value.extend_from_slice(b"2026-07-29");
        value
    }

    #[test]
    fn predicate_forms_normalize_to_one_packed_output_and_satisfy_every_air_row() {
        let nationality_array = vec![0x83, 0x62, b'U', b'S', 0x42, 0x01, 0xfa, 0x62, b'd', b'e'];
        let cases = [
            (
                MdocPrivateItemRequestMode::BirthDate,
                None,
                vec![0x44, 0x07, 0xea, 7, 29],
                vec![0x07, 0xea, 7, 29],
            ),
            (
                MdocPrivateItemRequestMode::BirthDate,
                None,
                text_date(false),
                vec![0x07, 0xea, 7, 29],
            ),
            (
                MdocPrivateItemRequestMode::BirthDate,
                None,
                text_date(true),
                vec![0x07, 0xea, 7, 29],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x42, 0x01, 0xfa],
                vec![0x01, 0xfa],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x62, b'D', b'E'],
                vec![0x01, 0x14],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x62, b'd', b'E'],
                vec![0x01, 0x14],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                Some(1),
                nationality_array.clone(),
                vec![0x01, 0xfa],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                Some(2),
                nationality_array,
                vec![0x01, 0x14],
            ),
        ];

        for (request_mode, selection, encoded, expected) in cases {
            let bind = test_bind_mode_with_selection(
                MdocPrivateItemProfile::Product,
                request_mode,
                selection,
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                &encoded,
            )
            .unwrap_or_else(|error| panic!("{request_mode:?}/{selection:?} failed: {error}"));
            assert_eq!(bind.request_mode(), request_mode);
            assert_eq!(normalized_output(&bind), expected);
            let witness = bind.witness.as_ref().unwrap();
            let indexes = (0..1usize << bind.log_size)
                .filter(|&row| witness.columns[trace_col::VALUE_ACTIVE][row] == m31(1))
                .map(|row| witness.columns[trace_col::VALUE_INDEX][row].0)
                .collect::<Vec<_>>();
            assert_eq!(
                indexes,
                (0..expected.len() as u32).collect::<Vec<_>>(),
                "normalized output must restart at relation index zero"
            );
            assert_eq!(
                bind.country_code_uses().total_uses(),
                u64::from(matches!(
                    request_mode,
                    MdocPrivateItemRequestMode::Nationality
                ))
            );
            assert_eq!(
                bind.private_country_tuple().is_some(),
                matches!(request_mode, MdocPrivateItemRequestMode::Nationality)
            );
            assert_witness_satisfies_air(&bind);
        }
    }

    #[test]
    fn typed_host_validation_rejects_private_form_cardinality_selection_and_mapping_faults() {
        let mut malformed_date = text_date(false);
        malformed_date[4] = b'x';
        assert_eq!(
            test_bind_mode_with(
                MdocPrivateItemProfile::Product,
                MdocPrivateItemRequestMode::BirthDate,
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                &malformed_date,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidElementValue)
        );
        assert!(matches!(
            test_bind_mode_with(
                MdocPrivateItemProfile::Product,
                MdocPrivateItemRequestMode::Nationality,
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                &[0x62, b'Z', b'Z'],
            ),
            Err(MdocPrivateItemError::CountryCode(
                MdocCountryCodeError::UnknownAlpha2(_)
            ))
        ));

        let array = [0x82, 0x62, b'U', b'S', 0x62, b'D', b'E'];
        assert_eq!(
            test_bind_mode_with(
                MdocPrivateItemProfile::Product,
                MdocPrivateItemRequestMode::Nationality,
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                &array,
            )
            .err(),
            Some(MdocPrivateItemError::MissingNationalityArraySelection)
        );
        assert_eq!(
            test_bind_mode_with_selection(
                MdocPrivateItemProfile::Product,
                MdocPrivateItemRequestMode::Nationality,
                Some(2),
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                &array,
            )
            .err(),
            Some(MdocPrivateItemError::InvalidNationalityArraySelection {
                member_count: 2,
                selected_index: 2,
            })
        );
        assert_eq!(
            test_bind_mode_with_selection(
                MdocPrivateItemProfile::Product,
                MdocPrivateItemRequestMode::Nationality,
                Some(0),
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                &[0x62, b'D', b'E'],
            )
            .err(),
            Some(MdocPrivateItemError::UnexpectedNationalityArraySelection(0))
        );

        for malformed in [
            vec![0x82, 0x62, b'U', b'S', 0x01],
            vec![0x82, 0x63, b'U', b'S', b'A', 0x62, b'D', b'E'],
            vec![0x80],
            vec![0x89],
        ] {
            assert!(matches!(
                test_bind_mode_with_selection(
                    MdocPrivateItemProfile::Product,
                    MdocPrivateItemRequestMode::Nationality,
                    Some(0),
                    CANONICAL_ORDER,
                    16,
                    7,
                    TEST_IDENTIFIER,
                    &malformed,
                ),
                Err(MdocPrivateItemError::InvalidElementValue)
                    | Err(MdocPrivateItemError::InnerParser(_))
            ));
        }
    }

    #[test]
    fn isolated_air_rejects_form_digit_output_count_selection_and_mapping_mutations() {
        let date = test_bind_mode_with(
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::BirthDate,
            CANONICAL_ORDER,
            16,
            7,
            b"birth_date",
            &text_date(false),
        )
        .unwrap();
        let date_head = date.witness.as_ref().unwrap().columns[trace_col::VALUE_HEAD]
            .iter()
            .position(|value| *value == m31(1))
            .unwrap();
        for (column, row) in [
            (trace_col::VALUE_DIRECT, date_head),
            (trace_col::DATE_DIGIT_BITS, date_head),
            (trace_col::VALUE_OUTPUT_BYTE, date_head + 1),
        ] {
            let mut wrong = date.witness.as_ref().unwrap().clone();
            wrong.columns[column][row] += m31(1);
            assert_mutated_row_rejected(&date, &wrong, row);
        }

        let array = [0x82, 0x62, b'U', b'S', 0x62, b'd', b'e'];
        let nationality = test_bind_mode_with_selection(
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::Nationality,
            Some(1),
            CANONICAL_ORDER,
            16,
            7,
            b"nationality",
            &array,
        )
        .unwrap();
        let witness = nationality.witness.as_ref().unwrap();
        let head = witness.columns[trace_col::VALUE_HEAD]
            .iter()
            .position(|value| *value == m31(1))
            .unwrap();
        let root = witness.columns[trace_col::VALUE_TAGGED]
            .iter()
            .position(|value| *value == m31(1))
            .unwrap();
        for (column, row) in [
            (trace_col::NAT_MEMBER_COUNT, root),
            (trace_col::VALUE_HEAD, head),
            (trace_col::NAT_CASE_FOLD_BITS, head),
            (trace_col::COUNTRY_LOOKUP_NUM_LO, head),
        ] {
            let mut wrong = witness.clone();
            wrong.columns[column][row] += m31(1);
            assert_mutated_row_rejected(&nationality, &wrong, row);
        }
    }

    #[test]
    fn ts13_rejects_predicate_requests_and_keeps_value_equality() {
        let padded = padded_item(CANONICAL_ORDER, 16, 7, TEST_IDENTIFIER, &[0x42, b'D', b'E']);
        assert_eq!(
            MdocPrivateItemBind::new(
                0,
                MdocPrivateItemProfile::Ts13,
                MdocPrivateMsoVersion::V2,
                MdocPrivateItemRequestMode::Nationality,
                padded.len(),
                MdocPrivateItemPrivateInput::new(padded),
                field_ids(),
                MdocPrivateItemHandles::fresh(
                    SharedFieldRelation::new(),
                    SharedMdocCountryCodeRelation::new(),
                ),
            )
            .err(),
            Some(MdocPrivateItemError::Ts13RequiresValueEquality)
        );
    }

    #[test]
    fn ts13_host_analysis_accepts_only_the_frozen_identifier_and_canonical_true() {
        for (name, identifier) in [
            ("wrong byte", b"age_over_19".as_slice()),
            ("short identifier", b"age_over_1".as_slice()),
            ("long identifier", b"age_over_18x".as_slice()),
        ] {
            assert_eq!(
                test_bind_with(
                    MdocPrivateItemProfile::Ts13,
                    CANONICAL_ORDER,
                    16,
                    7,
                    identifier,
                    TS13_CANONICAL_ELEMENT_VALUE,
                )
                .err(),
                Some(MdocPrivateItemError::InvalidElementIdentifier),
                "{name}"
            );
        }

        assert_eq!(
            test_bind_with(
                MdocPrivateItemProfile::Ts13,
                CANONICAL_ORDER,
                16,
                7,
                TS13_ELEMENT_IDENTIFIER,
                &[0xf4],
            )
            .err(),
            Some(MdocPrivateItemError::InvalidElementValue),
            "false"
        );
        assert_eq!(
            test_bind_with(
                MdocPrivateItemProfile::Ts13,
                CANONICAL_ORDER,
                16,
                7,
                TS13_ELEMENT_IDENTIFIER,
                &[0xc0, 0xf5],
            )
            .err(),
            Some(MdocPrivateItemError::InvalidElementValue),
            "tagged true"
        );
        for (name, value) in [
            ("noncanonical true", [0xf8, 0x15]),
            ("trailing value", [0xf5, 0x00]),
        ] {
            assert!(
                test_bind_with(
                    MdocPrivateItemProfile::Ts13,
                    CANONICAL_ORDER,
                    16,
                    7,
                    TS13_ELEMENT_IDENTIFIER,
                    &value,
                )
                .is_err(),
                "{name} unexpectedly passed host analysis"
            );
        }

        assert!(
            test_bind(MdocPrivateItemProfile::Ts13, 7).is_ok(),
            "the exact frozen TS13 semantic pair must remain accepted"
        );
    }

    #[test]
    fn digest_tuple_copies_canonical_cells_and_rejects_wrong_or_shifted_witnesses() {
        let bind = test_bind(MdocPrivateItemProfile::Product, 65_536).unwrap();
        let witness = bind.witness.as_ref().unwrap();
        let digest_row = (0..1usize << bind.log_size)
            .find(|&row| {
                (0..4)
                    .any(|kind| witness.columns[trace_col::DIGEST_START_KIND + kind][row] == m31(1))
            })
            .unwrap();
        assert_eq!(
            witness.columns[trace_col::DIGEST_START_KIND + 3][digest_row],
            m31(1)
        );
        assert_eq!(
            (0..DIGEST_COPY_BYTES)
                .map(|offset| witness.columns[trace_col::DIGEST_COPY + offset][digest_row].0 as u8)
                .collect::<Vec<_>>(),
            canonical_uint(65_536)
        );
        assert_eq!(witness.columns[trace_col::ARGUMENT][digest_row], m31(0));
        assert_eq!(witness.columns[trace_col::ARGUMENT + 1][digest_row], m31(1));

        let mut wrong_id = witness.clone();
        wrong_id.columns[trace_col::DIGEST_COPY + 2][digest_row] = m31(2);
        assert_mutated_row_rejected(&bind, &wrong_id, digest_row);

        let mut shifted = witness.clone();
        shifted.columns[trace_col::DIGEST_START_KIND + 3][digest_row] = m31(0);
        shifted.columns[trace_col::DIGEST_START_KIND + 3][digest_row + 1] = m31(1);
        assert_mutated_row_rejected(&bind, &shifted, digest_row);
        assert_mutated_row_rejected(&bind, &shifted, digest_row + 1);
    }

    #[test]
    fn changing_only_the_digest_handoff_changes_the_interaction_claim() {
        let bind = test_bind(MdocPrivateItemProfile::Product, 7).unwrap();
        let honest = bind.witness.as_ref().unwrap();
        let mut wrong = honest.clone();
        let digest_row = (0..1usize << bind.log_size)
            .find(|&row| wrong.columns[trace_col::DIGEST_START_KIND][row] == m31(1))
            .unwrap();
        wrong.columns[trace_col::DIGEST_COPY][digest_row] = m31(8);

        let mut channel = Blake2sChannel::default();
        let item_fields = FieldBytesRelation::draw(&mut channel);
        let outer_parsed = ParsedCborByteRelation::draw(&mut channel);
        let inner_parsed = ParsedCborByteRelation::draw(&mut channel);
        let inner_raw = FieldBytesRelation::draw(&mut channel);
        let digest_id = MdocPrivateDigestIdRelation::draw(&mut channel);
        let key_relation = MdocPrivateItemKeyRelation::draw(&mut channel);
        let blinder_relation = ClaimedSumBlinderRelation::draw(&mut channel);
        let country_code = SharedMdocCountryCodeRelation::new();
        let claim_for = |witness| {
            interaction_trace(
                witness,
                bind.log_size,
                bind.profile,
                bind.request_mode,
                bind.field_ids,
                &item_fields,
                &outer_parsed,
                &inner_parsed,
                &inner_raw,
                &digest_id,
                &country_code,
                &key_relation,
                &blinder_relation,
                qm31(17),
                qm31(19),
            )
            .1
        };
        assert_ne!(claim_for(honest), claim_for(&wrong));
    }

    #[test]
    fn equal_bucket_items_hide_all_private_lengths_and_contents_from_tree_zero() {
        let mut first = test_bind_with(
            MdocPrivateItemProfile::Product,
            CANONICAL_ORDER,
            16,
            7,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
        .unwrap();
        let mut second = test_bind_with(
            MdocPrivateItemProfile::Product,
            CANONICAL_ORDER,
            31,
            65_535,
            b"resident_address",
            &[0x63, b'L', b'e', b'e'],
        )
        .unwrap();
        assert_eq!(first.padded_bucket(), second.padded_bucket());
        assert_ne!(first.inner_bytes().len(), second.inner_bytes().len());
        assert_ne!(first.inner_bytes(), second.inner_bytes());
        assert_eq!(
            first.preprocessed_column_ids(),
            second.preprocessed_column_ids()
        );
        assert_eq!(
            first.preprocessed_column_fingerprints(),
            second.preprocessed_column_fingerprints()
        );

        let mut first_channel = Blake2sChannel::default();
        let mut second_channel = Blake2sChannel::default();
        first.mix_public(&mut first_channel);
        second.mix_public(&mut second_channel);
        assert_eq!(
            FieldBytesRelation::draw(&mut first_channel),
            FieldBytesRelation::draw(&mut second_channel),
            "public transcript must contain the bucket and caps, not hidden lengths or bytes"
        );
    }

    #[test]
    fn all_birth_date_forms_share_public_layout_transcript_and_tree_zero() {
        let mut packed = test_bind_mode_with(
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::BirthDate,
            CANONICAL_ORDER,
            16,
            7,
            b"birth_date",
            &[0x44, 0x07, 0xea, 7, 29],
        )
        .unwrap();
        let mut direct = test_bind_mode_with(
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::BirthDate,
            CANONICAL_ORDER,
            16,
            7,
            b"birth_date",
            &text_date(false),
        )
        .unwrap();
        let mut tagged = test_bind_mode_with(
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::BirthDate,
            CANONICAL_ORDER,
            19,
            8,
            b"birth_date",
            &text_date(true),
        )
        .unwrap();
        assert_eq!(packed.padded_bucket(), direct.padded_bucket());
        assert_eq!(direct.padded_bucket(), tagged.padded_bucket());
        assert_ne!(direct.inner_bytes().len(), tagged.inner_bytes().len());
        let packed_layout = packed.layout();
        let direct_layout = direct.layout();
        let tagged_layout = tagged.layout();
        assert_eq!(packed_layout.preprocessed, direct_layout.preprocessed);
        assert_eq!(packed_layout.trace, direct_layout.trace);
        assert_eq!(packed_layout.interaction, direct_layout.interaction);
        assert_eq!(packed_layout.preprocessed, tagged_layout.preprocessed);
        assert_eq!(packed_layout.trace, tagged_layout.trace);
        assert_eq!(packed_layout.interaction, tagged_layout.interaction);
        let fingerprints = packed.preprocessed_column_fingerprints();
        assert_eq!(fingerprints, direct.preprocessed_column_fingerprints());
        assert_eq!(fingerprints, tagged.preprocessed_column_fingerprints());

        let transcript_marker = |bind: &MdocPrivateItemBind| {
            let mut channel = Blake2sChannel::default();
            bind.mix_public(&mut channel);
            FieldBytesRelation::draw(&mut channel)
        };
        assert_eq!(transcript_marker(&packed), transcript_marker(&direct));
        assert_eq!(transcript_marker(&packed), transcript_marker(&tagged));

        let config = crate::mdoc::mdoc_production_pcs_config();
        let packed_root =
            air_core::compute_canonical_preprocessed_root(&mut [&mut packed], config).unwrap();
        let direct_root =
            air_core::compute_canonical_preprocessed_root(&mut [&mut direct], config).unwrap();
        let tagged_root =
            air_core::compute_canonical_preprocessed_root(&mut [&mut tagged], config).unwrap();
        assert_eq!(packed_root, direct_root);
        assert_eq!(packed_root, tagged_root);
    }

    fn nationality_array(member_count: u8) -> Vec<u8> {
        let mut value = vec![0x80 + member_count];
        for index in 0..member_count {
            if index % 2 == 0 {
                value.extend_from_slice(&[0x62, b'd', b'e']);
            } else {
                value.extend_from_slice(&[0x42, 0x01, 0xfa]);
            }
        }
        value
    }

    #[test]
    fn nationality_scalar_case_and_arrays_one_through_eight_share_maximal_public_shape() {
        let mut binds = Vec::new();
        for scalar in [
            vec![0x42, 0x01, 0xfa],
            vec![0x62, b'D', b'E'],
            vec![0x62, b'd', b'E'],
            vec![0x62, b'D', b'e'],
        ] {
            binds.push(
                test_bind_mode_with(
                    MdocPrivateItemProfile::Product,
                    MdocPrivateItemRequestMode::Nationality,
                    CANONICAL_ORDER,
                    16,
                    7,
                    b"nationality",
                    &scalar,
                )
                .unwrap(),
            );
        }
        for member_count in 1..=MDOC_PRIVATE_ITEM_MAX_NATIONALITY_MEMBERS as u8 {
            let selected_index = member_count - 1;
            binds.push(
                test_bind_mode_with_selection(
                    MdocPrivateItemProfile::Product,
                    MdocPrivateItemRequestMode::Nationality,
                    Some(selected_index),
                    CANONICAL_ORDER,
                    16,
                    7,
                    b"nationality",
                    &nationality_array(member_count),
                )
                .unwrap_or_else(|error| {
                    panic!("nationality array {member_count}/{selected_index} failed: {error}")
                }),
            );
        }

        let expected_layout = binds[0].layout();
        let mut expected_channel = Blake2sChannel::default();
        binds[0].mix_public(&mut expected_channel);
        let expected_transcript = FieldBytesRelation::draw(&mut expected_channel);
        let mut expected_root = None;
        for bind in &mut binds {
            assert_eq!(bind.padded_bucket(), 128);
            let layout = bind.layout();
            assert_eq!(layout.preprocessed, expected_layout.preprocessed);
            assert_eq!(layout.trace, expected_layout.trace);
            assert_eq!(layout.interaction, expected_layout.interaction);
            assert_eq!(layout.trace.len(), 154);
            assert_eq!(layout.interaction.len(), 29 * SECURE_EXTENSION_DEGREE);
            let mut channel = Blake2sChannel::default();
            bind.mix_public(&mut channel);
            assert_eq!(FieldBytesRelation::draw(&mut channel), expected_transcript);
            assert_eq!(bind.country_code_uses().total_uses(), 1);
            assert_witness_satisfies_air(bind);
            let mut country = MdocCountryCodeTable::prover(
                &[bind.country_code_uses().clone()],
                bind.handles.country_code.clone(),
            )
            .unwrap();
            let root = air_core::compute_canonical_preprocessed_root(
                &mut [&mut country, bind],
                crate::mdoc::mdoc_production_pcs_config(),
            )
            .unwrap();
            if let Some(expected) = &expected_root {
                assert_eq!(&root, expected);
            } else {
                expected_root = Some(root);
            }
        }
    }

    #[test]
    fn inactive_private_metadata_cells_are_fresh() {
        let first = test_bind(MdocPrivateItemProfile::Product, 7).unwrap();
        let second = test_bind(MdocPrivateItemProfile::Product, 7).unwrap();
        let first = first.witness.as_ref().unwrap();
        let second = second.witness.as_ref().unwrap();
        let inactive_start = first.columns[trace_col::ACTIVE]
            .iter()
            .position(|value| *value == m31(0))
            .unwrap();
        for column in [
            trace_col::INNER_LEN,
            trace_col::IDENTIFIER_LEN,
            trace_col::VALUE_ROOT_INDEX,
            trace_col::KEY_SEEN,
            trace_col::VALUE_HEAD_SEEN,
            trace_col::ARRAY_MEMBER_SEEN_COUNT,
            trace_col::VALUE_OUTPUT_BYTE,
            trace_col::NAT_MEMBER_COUNT,
            trace_col::DATE_DIGIT_BITS,
            trace_col::COUNTRY_LOOKUP_NUM_HI,
        ] {
            assert_ne!(
                &first.columns[column][inactive_start..],
                &second.columns[column][inactive_start..],
                "inactive private state column {column} must be freshly blinded"
            );
        }
    }

    #[test]
    fn bucket_192_uses_log_ten_without_exposing_actual_inner_length() {
        let first = test_bind_with(
            MdocPrivateItemProfile::Product,
            CANONICAL_ORDER,
            64,
            7,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
        .unwrap();
        let second = test_bind_with(
            MdocPrivateItemProfile::Product,
            CANONICAL_ORDER,
            75,
            8,
            b"portrait",
            TEST_VALUE,
        )
        .unwrap();
        assert_eq!(first.padded_bucket(), 192);
        assert_eq!(second.padded_bucket(), 192);
        assert_eq!(first.log_size(), 10);
        assert_eq!(second.log_size(), 10);
        assert_eq!(first.inner_parser_log_size(), 9);
        assert_ne!(first.inner_bytes().len(), second.inner_bytes().len());
    }

    #[test]
    fn all_items_from_each_of_the_three_frozen_real_vectors_are_accepted() {
        let vectors = crate::mdoc_real_vectors::real_mdoc_vectors();
        assert_eq!(vectors.len(), 3);
        for vector in vectors {
            assert!(
                !vector.items.is_empty(),
                "{} must contain at least one item",
                vector.source
            );
            for item in vector.items {
                let padded = stwo_sha256::native::pad_message(&item.outer);
                let bind = MdocPrivateItemBind::new(
                    0,
                    MdocPrivateItemProfile::Product,
                    MdocPrivateMsoVersion::V1,
                    MdocPrivateItemRequestMode::ValueEquality,
                    padded.len(),
                    MdocPrivateItemPrivateInput::new(padded),
                    field_ids(),
                    MdocPrivateItemHandles::fresh(
                        SharedFieldRelation::new(),
                        SharedMdocCountryCodeRelation::new(),
                    ),
                )
                .unwrap_or_else(|error| {
                    panic!(
                        "{} namespace {} digest {} failed strict item binding: {error}",
                        vector.source, item.namespace, item.digest_id
                    )
                });
                assert_eq!(bind.inner_bytes(), item.inner);
                assert_witness_satisfies_air(&bind);
            }
        }
    }

    #[test]
    fn honest_full_encoding_witness_satisfies_every_air_row() {
        for digest_id in [65_536, u32::MAX] {
            let bind = test_bind(MdocPrivateItemProfile::Product, digest_id).unwrap();
            assert_witness_satisfies_air(&bind);
        }
        let product_v1 = test_bind_with_version(
            MdocPrivateItemProfile::Product,
            MdocPrivateMsoVersion::V1,
            LEGACY_ORDER,
            16,
            7,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
        .unwrap();
        assert_witness_satisfies_air(&product_v1);
        let ts13 = test_bind(MdocPrivateItemProfile::Ts13, u16::MAX as u32).unwrap();
        assert_witness_satisfies_air(&ts13);
    }

    #[test]
    fn product_v1_and_v2_share_public_shape_while_version_stays_constant_in_trace() {
        let mut v1 = test_bind_with_version(
            MdocPrivateItemProfile::Product,
            MdocPrivateMsoVersion::V1,
            LEGACY_ORDER,
            16,
            7,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
        .unwrap();
        let mut v2 = test_bind_with_version(
            MdocPrivateItemProfile::Product,
            MdocPrivateMsoVersion::V2,
            CANONICAL_ORDER,
            16,
            7,
            TEST_IDENTIFIER,
            TEST_VALUE,
        )
        .unwrap();
        assert_eq!(v1.padded_bucket(), v2.padded_bucket());
        assert_eq!(
            v1.preprocessed_column_fingerprints(),
            v2.preprocessed_column_fingerprints()
        );
        let mut v1_channel = Blake2sChannel::default();
        let mut v2_channel = Blake2sChannel::default();
        v1.mix_public(&mut v1_channel);
        v2.mix_public(&mut v2_channel);
        assert_eq!(
            FieldBytesRelation::draw(&mut v1_channel),
            FieldBytesRelation::draw(&mut v2_channel),
            "product v1/v2 is private and must not alter the public transcript"
        );

        let witness = v2.witness.as_ref().unwrap();
        let changed_row = witness.columns[trace_col::ACTIVE]
            .iter()
            .enumerate()
            .skip(1)
            .find_map(|(row, &active)| (active == m31(1)).then_some(row))
            .unwrap();
        let mut wrong_version = witness.clone();
        wrong_version.columns[trace_col::IS_V2][changed_row] = m31(0);
        assert_mutated_row_rejected(&v2, &wrong_version, changed_row - 1);
    }

    struct TestComposedItemProof {
        stark: stwo::core::proof::StarkProof<air_core::Hasher>,
        bind_claim: MdocPrivateItemInteractionClaim,
        country_claim: Option<QM31>,
        counter_rows: Vec<TestCounterRow>,
        attribute_index: usize,
        profile: MdocPrivateItemProfile,
        request_mode: MdocPrivateItemRequestMode,
        bucket: usize,
        field_ids: MdocPrivateItemFieldIds,
    }

    fn parsed_counter_row(
        kind: usize,
        stream_id: u32,
        witness: &MdocPrivateItemWitness,
        row: usize,
    ) -> TestCounterRow {
        let mut values = [m31(0); TEST_COUNTER_VALUES];
        values[0] = m31(stream_id);
        values[1] = witness.columns[trace_col::STREAM_INDEX][row];
        for offset in 0..13 {
            values[offset + 2] = witness.columns[trace_col::BYTE + offset][row];
        }
        TestCounterRow::new(kind, &values)
    }

    fn honest_counter_rows(bind: &MdocPrivateItemBind) -> Vec<TestCounterRow> {
        let witness = bind.witness.as_ref().unwrap();
        let mut rows = Vec::new();
        for row in 0..1usize << bind.log_size {
            if witness.columns[trace_col::OUTER][row] == m31(1) {
                rows.push(parsed_counter_row(
                    TEST_OUTER_PARSED,
                    bind.field_ids.outer_stream,
                    witness,
                    row,
                ));
            }
            if witness.columns[trace_col::INNER][row] == m31(1) {
                rows.push(parsed_counter_row(
                    TEST_INNER_PARSED,
                    bind.field_ids.inner_stream,
                    witness,
                    row,
                ));
            }
            if witness.columns[trace_col::RAW_YIELD][row] == m31(1) {
                rows.push(TestCounterRow::new(
                    TEST_INNER_RAW,
                    &[
                        m31(bind.field_ids.inner_stream),
                        witness.columns[trace_col::RAW_INDEX][row],
                        witness.columns[trace_col::BYTE][row],
                    ],
                ));
            }

            let digest_kind = (0..4)
                .find(|kind| witness.columns[trace_col::DIGEST_START_KIND + kind][row] == m31(1));
            if let Some(digest_kind) = digest_kind {
                let mut values = [m31(0); digest_id_tuple::ARITY];
                values[digest_id_tuple::ENCODING_LEN] = m31([1, 2, 3, 5][digest_kind]);
                for index in 0..DIGEST_COPY_BYTES {
                    values[digest_id_tuple::BYTE_0 + index] =
                        witness.columns[trace_col::DIGEST_COPY + index][row];
                }
                values[digest_id_tuple::VALUE_LO16] = witness.columns[trace_col::ARGUMENT][row];
                values[digest_id_tuple::VALUE_HI16] = witness.columns[trace_col::ARGUMENT + 1][row];
                values[digest_id_tuple::IS_V2] = witness.columns[trace_col::IS_V2][row];
                rows.push(TestCounterRow::new(TEST_DIGEST_ID, &values));
            }
            if matches!(bind.profile, MdocPrivateItemProfile::Product) {
                for (selector, field_id, index_column, byte_column) in [
                    (
                        trace_col::IDENTIFIER_CONTENT_ACTIVE,
                        bind.field_ids.element_identifier,
                        trace_col::IDENTIFIER_CONTENT_INDEX,
                        trace_col::BYTE,
                    ),
                    (
                        trace_col::VALUE_ACTIVE,
                        bind.field_ids.element_value,
                        trace_col::VALUE_INDEX,
                        trace_col::VALUE_OUTPUT_BYTE,
                    ),
                ] {
                    if witness.columns[selector][row] == m31(1) {
                        rows.push(TestCounterRow::new(
                            TEST_ITEM_FIELDS,
                            &[
                                m31(field_id),
                                witness.columns[index_column][row],
                                witness.columns[byte_column][row],
                            ],
                        ));
                    }
                }
            }
        }
        rows
    }

    fn prove_composed_item() -> TestComposedItemProof {
        let mut bind = test_bind(MdocPrivateItemProfile::Product, 65_536).unwrap();
        prove_composed_bind(&mut bind, None)
    }

    fn prove_composed_bind(
        bind: &mut MdocPrivateItemBind,
        country_uses_override: Option<MdocCountryCodeUses>,
    ) -> TestComposedItemProof {
        let counter_rows = honest_counter_rows(&bind);
        let mut counter = TestRelationCounter::new(counter_rows.clone(), bind.handles.clone());
        let (stark, country_claim) =
            if matches!(bind.request_mode, MdocPrivateItemRequestMode::Nationality) {
                let uses =
                    country_uses_override.unwrap_or_else(|| bind.country_code_uses().clone());
                let mut country =
                    MdocCountryCodeTable::prover(&[uses], bind.handles.country_code.clone())
                        .unwrap();
                let stark = air_core::prove(
                    &mut [&mut counter, &mut country, bind],
                    crate::mdoc::mdoc_production_pcs_config(),
                )
                .expect("locally evaluable nationality item proof");
                (stark, Some(country.claimed_sum()))
            } else {
                let stark = air_core::prove(
                    &mut [&mut counter, bind],
                    crate::mdoc::mdoc_production_pcs_config(),
                )
                .expect("locally evaluable private item proof");
                (stark, None)
            };
        TestComposedItemProof {
            stark,
            bind_claim: bind.claim().clone(),
            country_claim,
            counter_rows,
            attribute_index: bind.attribute_index,
            profile: bind.profile,
            request_mode: bind.request_mode,
            bucket: bind.bucket,
            field_ids: bind.field_ids,
        }
    }

    fn assert_composed_prover_rejects(bind: &mut MdocPrivateItemBind, name: &str) {
        let counter_rows = honest_counter_rows(bind);
        let mut counter = TestRelationCounter::new(counter_rows, bind.handles.clone());
        let result = if matches!(bind.request_mode, MdocPrivateItemRequestMode::Nationality) {
            let mut country = MdocCountryCodeTable::prover(
                &[bind.country_code_uses().clone()],
                bind.handles.country_code.clone(),
            )
            .unwrap();
            air_core::prove(
                &mut [&mut counter, &mut country, bind],
                crate::mdoc::mdoc_production_pcs_config(),
            )
        } else {
            air_core::prove(
                &mut [&mut counter, bind],
                crate::mdoc::mdoc_production_pcs_config(),
            )
        };
        let Err(error) = result else {
            panic!("{name} unexpectedly produced a proof");
        };
        assert!(
            matches!(error, ProvingError::ConstraintsNotSatisfied),
            "{name} failed with the wrong prover error: {error}"
        );
    }

    fn verify_composed_item(
        fixture: &TestComposedItemProof,
        counter_rows: Vec<TestCounterRow>,
    ) -> Result<(), air_core::VerifyError> {
        let handles = MdocPrivateItemHandles::fresh(
            SharedFieldRelation::new(),
            SharedMdocCountryCodeRelation::new(),
        );
        let mut counter = TestRelationCounter::new(counter_rows, handles.clone());
        let mut bind = MdocPrivateItemBind::verifier(
            fixture.attribute_index,
            fixture.profile,
            fixture.request_mode,
            fixture.bucket,
            fixture.field_ids,
            handles.clone(),
            fixture.bind_claim.clone(),
        )
        .unwrap();
        if let Some(country_claim) = fixture.country_claim {
            let mut country =
                MdocCountryCodeTable::verifier(country_claim, handles.country_code.clone());
            let expected_root = air_core::compute_canonical_preprocessed_root(
                &mut [&mut counter, &mut country, &mut bind],
                fixture.stark.config,
            )
            .expect("canonical item/country preprocessing");
            air_core::verify_with_expected_preprocessed_root(
                &mut [&mut counter, &mut country, &mut bind],
                &fixture.stark,
                Some(expected_root),
            )
        } else {
            let expected_root = air_core::compute_canonical_preprocessed_root(
                &mut [&mut counter, &mut bind],
                fixture.stark.config,
            )
            .expect("canonical item preprocessing");
            air_core::verify_with_expected_preprocessed_root(
                &mut [&mut counter, &mut bind],
                &fixture.stark,
                Some(expected_root),
            )
        }
    }

    fn assert_counter_mutation_rejects(
        fixture: &TestComposedItemProof,
        name: &str,
        kind: usize,
        value_index: usize,
    ) {
        let mut rows = fixture.counter_rows.clone();
        rows.iter_mut().find(|row| row.kind == kind).unwrap().values[value_index] += m31(1);
        match verify_composed_item(fixture, rows)
            .expect_err("mutated relation counterpart must not verify")
        {
            air_core::VerifyError::Stark(
                stwo::core::verifier::VerificationError::InvalidStructure(reason),
            ) => assert_eq!(reason, "LogUp claimed sums do not cancel", "{name}"),
            other => panic!("{name}: expected global LogUp rejection, got {other:?}"),
        }
    }

    fn assert_composed_rejects(fixture: &TestComposedItemProof, name: &str) {
        assert!(
            verify_composed_item(fixture, fixture.counter_rows.clone()).is_err(),
            "{name} unexpectedly verified"
        );
    }

    fn assert_composed_logup_rejects(fixture: &TestComposedItemProof, name: &str) {
        match verify_composed_item(fixture, fixture.counter_rows.clone())
            .expect_err("mismatched composed lookup must not verify")
        {
            air_core::VerifyError::Stark(
                stwo::core::verifier::VerificationError::InvalidStructure(reason),
            ) => assert_eq!(reason, "LogUp claimed sums do not cancel", "{name}"),
            other => panic!("{name}: expected global LogUp rejection, got {other:?}"),
        }
    }

    fn predicate_bind(
        request_mode: MdocPrivateItemRequestMode,
        selection: Option<u8>,
        identifier: &[u8],
        value: &[u8],
    ) -> MdocPrivateItemBind {
        test_bind_mode_with_selection(
            MdocPrivateItemProfile::Product,
            request_mode,
            selection,
            CANONICAL_ORDER,
            16,
            7,
            identifier,
            value,
        )
        .unwrap()
    }

    #[test]
    fn production_pcs_composed_proofs_accept_every_normalization_branch() {
        for mut bind in [
            test_bind_with_version(
                MdocPrivateItemProfile::Product,
                MdocPrivateMsoVersion::V1,
                LEGACY_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                TEST_VALUE,
            )
            .unwrap(),
            test_bind_with_version(
                MdocPrivateItemProfile::Product,
                MdocPrivateMsoVersion::V2,
                CANONICAL_ORDER,
                16,
                7,
                TEST_IDENTIFIER,
                TEST_VALUE,
            )
            .unwrap(),
        ] {
            let fixture = prove_composed_bind(&mut bind, None);
            verify_composed_item(&fixture, fixture.counter_rows.clone())
                .expect("A-734 private v1/v2 composed item proof verifies");
        }

        let mut cases = vec![
            (
                MdocPrivateItemRequestMode::BirthDate,
                None,
                vec![0x44, 0x07, 0xea, 7, 29],
            ),
            (
                MdocPrivateItemRequestMode::BirthDate,
                None,
                text_date(false),
            ),
            (MdocPrivateItemRequestMode::BirthDate, None, text_date(true)),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x42, 0xff, 0xff],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x62, b'd', b'E'],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x62, b'D', b'E'],
            ),
            (
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x62, b'd', b'e'],
            ),
        ];
        for member_count in 1..=MDOC_PRIVATE_ITEM_MAX_NATIONALITY_MEMBERS as u8 {
            cases.push((
                MdocPrivateItemRequestMode::Nationality,
                Some(member_count - 1),
                nationality_array(member_count),
            ));
        }
        let mut normalization_prove_ms = Vec::with_capacity(cases.len());
        for (request_mode, selection, value) in cases {
            let identifier = if matches!(request_mode, MdocPrivateItemRequestMode::BirthDate) {
                b"birth_date".as_slice()
            } else {
                b"nationality".as_slice()
            };
            let mut bind = predicate_bind(request_mode, selection, identifier, &value);
            let prove_started = std::time::Instant::now();
            let fixture = prove_composed_bind(&mut bind, None);
            normalization_prove_ms.push(prove_started.elapsed().as_millis());
            verify_composed_item(&fixture, fixture.counter_rows.clone()).unwrap_or_else(|error| {
                panic!(
                    "production proof for {request_mode:?}/{selection:?} failed verification: {error:?}"
                )
            });
        }
        normalization_prove_ms.sort_unstable();
        eprintln!(
            "u3_normalization_prove_ms={} samples={}",
            normalization_prove_ms[normalization_prove_ms.len() / 2],
            normalization_prove_ms.len()
        );
    }

    #[test]
    fn production_pcs_proofs_reject_form_date_output_cardinality_selection_and_mapping_faults() {
        type MutationCase = (
            &'static str,
            MdocPrivateItemRequestMode,
            Option<u8>,
            Vec<u8>,
            fn(&mut MdocPrivateItemWitness),
        );
        let mutation_cases: [MutationCase; 8] = [
            (
                "private birth form",
                MdocPrivateItemRequestMode::BirthDate,
                None,
                text_date(false),
                |witness| {
                    let row = witness.columns[trace_col::VALUE_DIRECT]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::VALUE_DIRECT][row] = m31(0);
                },
            ),
            (
                "date digit",
                MdocPrivateItemRequestMode::BirthDate,
                None,
                text_date(false),
                |witness| {
                    let row = witness.columns[trace_col::VALUE_HEAD]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::DATE_DIGIT_BITS][row] += m31(1);
                },
            ),
            (
                "date decomposition",
                MdocPrivateItemRequestMode::BirthDate,
                None,
                text_date(false),
                |witness| {
                    let row = witness.columns[trace_col::VALUE_HEAD]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::VALUE_OUTPUT_BYTE][row + 2] += m31(1);
                },
            ),
            (
                "normalized output",
                MdocPrivateItemRequestMode::BirthDate,
                None,
                vec![0x44, 0x07, 0xea, 7, 29],
                |witness| {
                    let row = witness.columns[trace_col::VALUE_ACTIVE]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::VALUE_OUTPUT_BYTE][row] += m31(1);
                },
            ),
            (
                "private nationality form",
                MdocPrivateItemRequestMode::Nationality,
                Some(1),
                nationality_array(2),
                |witness| {
                    let row = witness.columns[trace_col::VALUE_TAGGED]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::VALUE_TAGGED][row] = m31(0);
                },
            ),
            (
                "array cardinality",
                MdocPrivateItemRequestMode::Nationality,
                Some(1),
                nationality_array(2),
                |witness| {
                    let row = witness.columns[trace_col::VALUE_TAGGED]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::NAT_MEMBER_COUNT][row] += m31(1);
                },
            ),
            (
                "array selection",
                MdocPrivateItemRequestMode::Nationality,
                Some(1),
                nationality_array(2),
                |witness| {
                    let row = witness.columns[trace_col::VALUE_HEAD]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::VALUE_HEAD][row] = m31(0);
                },
            ),
            (
                "alpha mapping",
                MdocPrivateItemRequestMode::Nationality,
                None,
                vec![0x62, b'D', b'E'],
                |witness| {
                    let row = witness.columns[trace_col::VALUE_HEAD]
                        .iter()
                        .position(|value| *value == m31(1))
                        .unwrap();
                    witness.columns[trace_col::COUNTRY_LOOKUP_NUM_LO][row] += m31(1);
                },
            ),
        ];

        for (name, request_mode, selection, value, mutate) in mutation_cases {
            let identifier = if matches!(request_mode, MdocPrivateItemRequestMode::BirthDate) {
                b"birth_date".as_slice()
            } else {
                b"nationality".as_slice()
            };
            let mut bind = predicate_bind(request_mode, selection, identifier, &value);
            mutate(bind.witness.as_mut().unwrap());
            assert_composed_prover_rejects(&mut bind, name);
        }
    }

    #[test]
    fn production_pcs_country_relation_rejects_branch_mapping_multiplicity_and_claim_faults() {
        let germany = |count: usize| {
            let mut uses = MdocCountryCodeUses::default();
            for _ in 0..count {
                uses.record_alpha2(*b"DE").unwrap();
            }
            uses
        };
        let france = || {
            let mut uses = MdocCountryCodeUses::default();
            uses.record_alpha2(*b"FR").unwrap();
            uses
        };
        let numeric = || {
            let mut uses = MdocCountryCodeUses::default();
            uses.record_numeric_dummy().unwrap();
            uses
        };

        let mismatch_cases = [
            (
                "numeric consumer against real row",
                vec![0x42, 0x01, 0xfa],
                germany(1),
            ),
            (
                "alpha consumer against dummy row",
                vec![0x62, b'D', b'E'],
                numeric(),
            ),
            ("wrong alpha mapping", vec![0x62, b'D', b'E'], france()),
            ("country multiplicity", vec![0x62, b'D', b'E'], germany(2)),
        ];
        for (name, value, uses) in mismatch_cases {
            let mut bind = predicate_bind(
                MdocPrivateItemRequestMode::Nationality,
                None,
                b"nationality",
                &value,
            );
            let fixture = prove_composed_bind(&mut bind, Some(uses));
            assert_composed_rejects(&fixture, name);
        }

        let mut unknown = predicate_bind(
            MdocPrivateItemRequestMode::Nationality,
            None,
            b"nationality",
            &[0x62, b'D', b'E'],
        );
        {
            let witness = unknown.witness.as_mut().unwrap();
            let head = witness.columns[trace_col::VALUE_HEAD]
                .iter()
                .position(|value| *value == m31(1))
                .unwrap();
            for offset in 1..=NATIONALITY_BYTES {
                witness.columns[trace_col::BYTE][head + offset] = m31(u32::from(b'Z'));
                witness.columns[trace_col::VALUE_OUTPUT_BYTE][head + offset] = m31(0);
                for bit in 0..8 {
                    witness.columns[trace_col::DATE_DIGIT_BITS + bit][head + offset] = m31(0);
                }
            }
            witness.columns[trace_col::NAT_CASE_FOLD_BITS][head] = m31(0);
            witness.columns[trace_col::NAT_CASE_FOLD_BITS + 1][head] = m31(0);
            witness.columns[trace_col::COUNTRY_LOOKUP_NUM_HI][head] = m31(0);
            witness.columns[trace_col::COUNTRY_LOOKUP_NUM_LO][head] = m31(0);
            witness.columns[trace_col::COUNTRY_LOOKUP_UPPER_0][head] = m31(u32::from(b'Z'));
            witness.columns[trace_col::COUNTRY_LOOKUP_UPPER_1][head] = m31(u32::from(b'Z'));
        }
        assert_witness_satisfies_air(&unknown);
        let unknown_fixture =
            prove_composed_bind(&mut unknown, Some(MdocCountryCodeUses::default()));
        assert_composed_rejects(&unknown_fixture, "unknown alpha-2 tuple");

        let mut bind = predicate_bind(
            MdocPrivateItemRequestMode::Nationality,
            None,
            b"nationality",
            &[0x62, b'D', b'E'],
        );
        let mut fixture = prove_composed_bind(&mut bind, None);
        verify_composed_item(&fixture, fixture.counter_rows.clone())
            .expect("honest country claim verifies");
        fixture.country_claim = Some(fixture.country_claim.unwrap() + qm31(1));
        assert_composed_rejects(&fixture, "country claimed sum");
    }

    #[test]
    fn composed_proof_verifies_and_rejects_every_private_item_relation_seam_mutation() {
        let fixture = prove_composed_item();
        verify_composed_item(&fixture, fixture.counter_rows.clone())
            .expect("private item relation composition must verify");
        for (name, kind, value_index) in [
            ("item field byte", TEST_ITEM_FIELDS, 2),
            ("outer parsed byte", TEST_OUTER_PARSED, 2),
            ("inner parsed byte", TEST_INNER_PARSED, 2),
            ("inner raw byte", TEST_INNER_RAW, 2),
            ("digest encoding", TEST_DIGEST_ID, 1),
            ("digest version", TEST_DIGEST_ID, digest_id_tuple::IS_V2),
        ] {
            assert_counter_mutation_rejects(&fixture, name, kind, value_index);
        }
    }

    #[test]
    fn ts13_semantics_balance_inside_the_item_slot_and_reject_forged_private_values() {
        let mut honest = test_bind(MdocPrivateItemProfile::Ts13, 7).unwrap();
        let fixture = prove_composed_bind(&mut honest, None);
        assert!(
            fixture
                .counter_rows
                .iter()
                .all(|row| row.kind != TEST_ITEM_FIELDS),
            "TS13 must not rely on an external semantic window counterpart"
        );
        verify_composed_item(&fixture, fixture.counter_rows.clone())
            .expect("exact TS13 semantics balance within the item-binder slot");

        let mut false_trace = test_bind(MdocPrivateItemProfile::Ts13, 7).unwrap();
        {
            let witness = false_trace.witness.as_mut().unwrap();
            let row = witness.columns[trace_col::VALUE_ACTIVE]
                .iter()
                .position(|value| *value == m31(1))
                .expect("TS13 fixture has one active value byte");
            witness.columns[trace_col::BYTE][row] = m31(0xf4);
            witness.columns[trace_col::ARGUMENT][row] = m31(20);
            witness.columns[trace_col::VALUE_OUTPUT_BYTE][row] = m31(0xf4);
        }
        assert_witness_satisfies_air(&false_trace);
        let false_fixture = prove_composed_bind(&mut false_trace, None);
        assert_composed_logup_rejects(&false_fixture, "AIR-level true-to-false mutation");

        for (name, identifier, value) in [
            (
                "wrong identifier byte",
                b"age_over_19".as_slice(),
                TS13_CANONICAL_ELEMENT_VALUE,
            ),
            (
                "wrong identifier length",
                b"age_over_1".as_slice(),
                TS13_CANONICAL_ELEMENT_VALUE,
            ),
            ("false", TS13_ELEMENT_IDENTIFIER, &[0xf4]),
            ("tagged true", TS13_ELEMENT_IDENTIFIER, &[0xc0, 0xf5]),
        ] {
            // Construct under the generic product profile to model a malicious
            // prover bypassing TS13's host-side witness validation, then prove
            // the same trace under the TS13 AIR and transcript.
            let mut forged = test_bind_with(
                MdocPrivateItemProfile::Product,
                CANONICAL_ORDER,
                16,
                7,
                identifier,
                value,
            )
            .unwrap_or_else(|error| panic!("{name} fixture is not structurally valid: {error}"));
            forged.profile = MdocPrivateItemProfile::Ts13;
            let forged_fixture = prove_composed_bind(&mut forged, None);
            assert!(
                forged_fixture
                    .counter_rows
                    .iter()
                    .all(|row| row.kind != TEST_ITEM_FIELDS),
                "{name}: forged proof unexpectedly gained an external semantic counterpart"
            );
            assert_composed_logup_rejects(&forged_fixture, name);
        }
    }

    #[test]
    fn layout_claim_components_and_degree_budget_are_fixed() {
        let expected_claim = test_claim();
        let encoded = bincode::serialize(&expected_claim).unwrap();
        let decoded: MdocPrivateItemInteractionClaim = bincode::deserialize(&encoded).unwrap();
        assert_eq!(decoded, expected_claim);

        let item_fields = SharedFieldRelation::new();
        let handles = MdocPrivateItemHandles::fresh(
            item_fields.clone(),
            SharedMdocCountryCodeRelation::new(),
        );
        let mut channel = Blake2sChannel::default();
        item_fields.set(FieldBytesRelation::draw(&mut channel));
        handles
            .outer_parsed
            .set(ParsedCborByteRelation::draw(&mut channel));
        handles
            .inner_parsed
            .set(ParsedCborByteRelation::draw(&mut channel));
        let mut verifier = MdocPrivateItemBind::verifier(
            2,
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::ValueEquality,
            192,
            field_ids(),
            handles.clone(),
            decoded,
        )
        .unwrap();
        assert_eq!(verifier.claimed_sums(), vec![qm31(1), qm31(4)]);
        let layout = verifier.layout();
        assert_eq!(layout.preprocessed, vec![10; PREPROCESSED_COLS]);
        assert_eq!(layout.trace, vec![10; trace_col::COUNT]);
        assert_eq!(layout.trace.len(), 154);
        assert_eq!(layout.interaction, vec![10; 29 * SECURE_EXTENSION_DEGREE]);
        assert_eq!(verifier.main_interaction_sites(), 55);
        let nationality = MdocPrivateItemBind::verifier(
            2,
            MdocPrivateItemProfile::Product,
            MdocPrivateItemRequestMode::Nationality,
            192,
            field_ids(),
            MdocPrivateItemHandles::fresh(
                SharedFieldRelation::new(),
                SharedMdocCountryCodeRelation::new(),
            ),
            test_claim(),
        )
        .unwrap();
        assert_eq!(nationality.main_interaction_sites(), 56);
        let nationality_layout = nationality.layout();
        assert_eq!(nationality_layout.preprocessed, layout.preprocessed);
        assert_eq!(nationality_layout.trace, layout.trace);
        assert_eq!(nationality_layout.interaction, layout.interaction);
        let ts13 = MdocPrivateItemBind::verifier(
            0,
            MdocPrivateItemProfile::Ts13,
            MdocPrivateItemRequestMode::ValueEquality,
            128,
            field_ids(),
            MdocPrivateItemHandles::fresh(
                SharedFieldRelation::new(),
                SharedMdocCountryCodeRelation::new(),
            ),
            test_claim(),
        )
        .unwrap();
        assert_eq!(ts13.main_interaction_sites(), 67);
        assert_eq!(
            ts13.layout().interaction,
            vec![9; 35 * SECURE_EXTENSION_DEGREE]
        );
        assert_eq!(trace_col::VALUE_OUTPUT_BYTE, 110);
        assert_eq!(trace_col::COUNTRY_LOOKUP_UPPER_1, 153);
        assert_eq!((trace_col::COUNT - 110) * (1usize << 9), 22_528);
        assert_eq!((trace_col::COUNT - 110) * (1usize << 10), 45_056);
        assert_eq!(digest_id_tuple::ARITY, 9);

        verifier.draw_relations(&mut channel);
        assert!(handles.inner_raw.is_set());
        assert!(handles.digest_id.is_set());
        let ids = verifier.preprocessed_column_ids();
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids.as_slice());
        verifier.build_components(&mut allocator);
        assert_eq!(
            verifier.components().len(),
            2,
            "main item binder must be followed immediately by its blinder counterpart"
        );

        let prover = test_bind(MdocPrivateItemProfile::Product, 7).unwrap();
        assert_eq!(
            FrameworkEval::max_constraint_log_degree_bound(&test_eval(&prover)),
            prover.log_size + 2
        );
        assert_eq!(
            AirProver::max_constraint_log_degree_bound(&prover),
            prover.log_size + 2
        );
        assert!(prover.store_polynomial_coefficients());
    }
}
