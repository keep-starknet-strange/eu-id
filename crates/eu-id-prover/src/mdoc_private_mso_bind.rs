//! Private MobileSecurityObject fact binding for unlinkable mdoc proofs.
//!
//! The issuer `Sig_structure` is provided by
//! `mdoc_private_message::MdocPrivateMessageProvider`. This component consumes
//! positive `(HOSTED_MSG_FIELD_ID, absolute_index, byte)` tuples at private,
//! range-checked offsets and proves the public MSO facts which used to be
//! recovered by parsing a public issuer message.
//!
//! `valueDigests` deliberately is not handled here. Its namespace-scoped map
//! scan is a separate component sharing [`SharedMdocMsoStartRelation`].
//!
//! # Relation polarity
//!
//! | relation | provider | sign | consumer | sign |
//! |---|---|---:|---|---:|
//! | issuer hosted message | private-message provider | `-` | this binder | `+` |
//! | full padded MSO SHA stream | SHA-256 AIR | `-` | this binder | `+` |
//! | private `mso_start` | this binder | `-` | valueDigests scanner | `+` |
//!
//! The optional `mso_start` site follows the 32 issuer sites and optional 32
//! SHA-stream sites. The claimed-sum blinder is always the final site.

use std::fmt;

use air_core::relations::{FieldBytesRelation, SharedFieldRelation, SharedRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use predicates::Date;
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
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};

pub(crate) const MDOC_PRIVATE_MSO_BIND_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_PRIVATE_MSO_BIND_ROWS: usize = 1usize << MDOC_PRIVATE_MSO_BIND_LOG_SIZE;
pub(crate) const MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS: usize = 256;
pub(crate) const MDOC_PRIVATE_MSO_MIN_BLIND_ROWS: usize = 256;
pub(crate) const MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES: usize = 1_987;
pub(crate) const MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES: usize = 23;

const BIND_VERSION: u64 = 1;
const BIND_DOMAIN: u64 = 0x4d44_4f43_4d53_4f42; // "MDOCMSOB"
const CHUNK_BYTES: usize = 32;
const DOC_TYPE_CHUNKS: usize = 1;
const DEVICE_KEY_INFO_CHUNKS: usize = MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES.div_ceil(CHUNK_BYTES);
const OFFSET_BITS: usize = 13;
const TDATE_BYTES: usize = 20;
const TDATE_DIGITS: usize = 14;
const DIGIT_BITS: usize = 4;
const DATE_SLACK_BITS: usize = 23;
const MONTH_RANGE_BITS: usize = 4;
const DAY_RANGE_BITS: usize = 5;
const HOUR_RANGE_BITS: usize = 5;
const MINUTE_RANGE_BITS: usize = 6;
const SECOND_RANGE_BITS: usize = 6;
const RANGE_BITS: usize = 2 * MONTH_RANGE_BITS
    + 2 * DAY_RANGE_BITS
    + HOUR_RANGE_BITS
    + MINUTE_RANGE_BITS
    + SECOND_RANGE_BITS;
const M31_MODULUS: u32 = 2_147_483_647;

const VERSION_PREFIX: &[u8] = b"\x67version\x63";
const DIGEST_ALGORITHM_RUN: &[u8] = b"\x6fdigestAlgorithm\x67SHA-256";
const DOC_TYPE_KEY: &[u8] = b"\x67docType";
const VALID_FROM_ANCHOR: &[u8] = b"\x69validFrom\xc0\x74";
const VALID_UNTIL_ANCHOR: &[u8] = b"\x6avalidUntil\xc0\x74";
const DEVICE_KEY_INFO_PREFIX: &[u8; 35] =
    b"\x6ddeviceKeyInfo\xa1\x69deviceKey\xa3\x01\x07\x03\x38\x30\x20\x59\x07\xa0";

relation!(MdocMsoStartRelation, 2);

/// Private `(mso_start,is_v2)` handoff to the namespace-scoped scanner.
///
/// The version bit must ride in the same tuple as the anchor: a separate
/// relation would let a prover pair a v1 anchor with a v2 bit or vice versa.
/// This binder emits exactly one negative tuple and the scanner consumes one
/// positive tuple.
pub(crate) type SharedMdocMsoStartRelation = SharedRelation<MdocMsoStartRelation>;

type MdocPrivateMsoColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocPrivateMsoComponent = FrameworkComponent<MdocPrivateMsoEval>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateMsoVersion {
    V1,
    V2,
}

impl MdocPrivateMsoVersion {
    fn selector(self) -> u32 {
        u32::from(matches!(self, Self::V2))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoShaStreamSpec {
    pub(crate) field_id: u32,
    pub(crate) padded_len: usize,
}

/// Verifier-known shape and constants. No private MSO byte, offset, version,
/// tdate, or multiplicity is carried here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoBindSpec {
    pub(crate) issuer_message_len: usize,
    pub(crate) mso_len: usize,
    pub(crate) doc_type: String,
    pub(crate) device_public_key: Vec<u8>,
    pub(crate) policy_date: Date,
    pub(crate) sha_stream: Option<MdocPrivateMsoShaStreamSpec>,
}

/// Prover-only values. Every offset except `payload_anchor_offset` is relative
/// to the first MSO payload byte.
#[derive(Clone, Debug)]
pub(crate) struct MdocPrivateMsoBindWitness {
    pub(crate) issuer_message: Vec<u8>,
    pub(crate) payload_anchor_offset: usize,
    pub(crate) version_offset: usize,
    pub(crate) digest_algorithm_offset: usize,
    pub(crate) doc_type_offset: usize,
    pub(crate) device_key_info_offset: usize,
    pub(crate) valid_from_offset: usize,
    pub(crate) valid_until_offset: usize,
    pub(crate) version: MdocPrivateMsoVersion,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoUseCensus {
    /// Additional positive hosted-message consumers contributed by this
    /// binder, indexed by the issuer message position.
    pub(crate) issuer_position_uses: Vec<u32>,
    pub(crate) issuer_uses_total: usize,
    pub(crate) sha_stream_uses: usize,
    pub(crate) mso_start_uses: usize,
    pub(crate) active_rows: usize,
    pub(crate) blind_rows: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateMsoBindError {
    EmptyIssuerMessage,
    IssuerMessageTooLong {
        length: usize,
        max: usize,
    },
    EmptyMso,
    MsoTooLong {
        length: usize,
        max: usize,
    },
    MsoCannotFitIssuerMessage {
        issuer_message_len: usize,
        mso_len: usize,
        anchor_len: usize,
    },
    DevicePublicKeyLength {
        length: usize,
        expected: usize,
    },
    EmptyDocType,
    DocTypeTooLong {
        length: usize,
        max: usize,
    },
    InvalidPolicyDate {
        year: u32,
        month: u32,
        day: u32,
    },
    ShaStreamHandleMismatch {
        spec_present: bool,
        handle_present: bool,
    },
    ShaFieldIdOutOfRange {
        field_id: u32,
    },
    ShaPaddedLengthMismatch {
        expected: usize,
        actual: usize,
    },
    IssuerMessageLengthMismatch {
        expected: usize,
        actual: usize,
    },
    MsoBytesLengthMismatch {
        expected: usize,
        actual: usize,
    },
    CanonicalAnchorMissing {
        anchor: &'static str,
    },
    CanonicalAnchorAmbiguous {
        anchor: &'static str,
    },
    PayloadOffsetOverflow {
        offset: usize,
        anchor_len: usize,
    },
    PayloadOutOfBounds {
        mso_start: usize,
        mso_len: usize,
        issuer_message_len: usize,
    },
    WindowOffsetOverflow {
        window: &'static str,
        offset: usize,
        len: usize,
    },
    WindowOutOfBounds {
        window: &'static str,
        offset: usize,
        len: usize,
        mso_len: usize,
    },
    ScheduleTooLarge {
        active_rows: usize,
        max: usize,
    },
    UseCountOverflow {
        issuer_index: usize,
    },
}

impl fmt::Display for MdocPrivateMsoBindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyIssuerMessage => write!(f, "private issuer message is empty"),
            Self::IssuerMessageTooLong { length, max } => {
                write!(f, "private issuer message length {length} exceeds the {max}-byte cap")
            }
            Self::EmptyMso => write!(f, "private MSO payload is empty"),
            Self::MsoTooLong { length, max } => {
                write!(f, "private MSO payload length {length} exceeds the {max}-byte cap")
            }
            Self::MsoCannotFitIssuerMessage {
                issuer_message_len,
                mso_len,
                anchor_len,
            } => write!(
                f,
                "{mso_len}-byte MSO plus {anchor_len}-byte payload anchor cannot fit the {issuer_message_len}-byte issuer message"
            ),
            Self::DevicePublicKeyLength { length, expected } => write!(
                f,
                "device ML-DSA public key has {length} bytes; expected {expected}"
            ),
            Self::EmptyDocType => write!(f, "public docType is empty"),
            Self::DocTypeTooLong { length, max } => write!(
                f,
                "public docType has {length} bytes; the supported canonical one-chunk profile allows at most {max}"
            ),
            Self::InvalidPolicyDate { year, month, day } => {
                write!(f, "invalid policy date {year:04}-{month:02}-{day:02}")
            }
            Self::ShaStreamHandleMismatch {
                spec_present,
                handle_present,
            } => write!(
                f,
                "MSO SHA stream spec/handle mismatch (spec={spec_present}, handle={handle_present})"
            ),
            Self::ShaFieldIdOutOfRange { field_id } => write!(
                f,
                "MSO SHA stream field id {field_id} is not canonical in M31"
            ),
            Self::ShaPaddedLengthMismatch { expected, actual } => write!(
                f,
                "MSO SHA padded length is {actual}; canonical length is {expected}"
            ),
            Self::IssuerMessageLengthMismatch { expected, actual } => write!(
                f,
                "private issuer message has {actual} bytes; public shape requires {expected}"
            ),
            Self::MsoBytesLengthMismatch { expected, actual } => write!(
                f,
                "private MSO has {actual} bytes; public shape requires {expected}"
            ),
            Self::CanonicalAnchorMissing { anchor } => {
                write!(f, "canonical {anchor} anchor is missing")
            }
            Self::CanonicalAnchorAmbiguous { anchor } => {
                write!(f, "canonical {anchor} anchor occurs more than once")
            }
            Self::PayloadOffsetOverflow { offset, anchor_len } => write!(
                f,
                "payload anchor offset {offset} plus {anchor_len} bytes overflows"
            ),
            Self::PayloadOutOfBounds {
                mso_start,
                mso_len,
                issuer_message_len,
            } => write!(
                f,
                "private MSO [{mso_start}, {}) exceeds the {issuer_message_len}-byte issuer message",
                mso_start.saturating_add(*mso_len)
            ),
            Self::WindowOffsetOverflow {
                window,
                offset,
                len,
            } => write!(f, "{window} offset {offset} plus {len} bytes overflows"),
            Self::WindowOutOfBounds {
                window,
                offset,
                len,
                mso_len,
            } => write!(
                f,
                "{window} window [{offset}, {}) exceeds the {mso_len}-byte MSO",
                offset.saturating_add(*len)
            ),
            Self::ScheduleTooLarge { active_rows, max } => write!(
                f,
                "private MSO bind needs {active_rows} active rows; fixed log-9 profile permits {max}"
            ),
            Self::UseCountOverflow { issuer_index } => write!(
                f,
                "issuer-message use count overflows at byte {issuer_index}"
            ),
        }
    }
}

impl std::error::Error for MdocPrivateMsoBindError {}

fn unique_subslice(
    haystack: &[u8],
    needle: &[u8],
    anchor: &'static str,
) -> Result<usize, MdocPrivateMsoBindError> {
    let mut matches = haystack
        .windows(needle.len())
        .enumerate()
        .filter_map(|(index, window)| (window == needle).then_some(index));
    let first = matches
        .next()
        .ok_or(MdocPrivateMsoBindError::CanonicalAnchorMissing { anchor })?;
    if matches.next().is_some() {
        return Err(MdocPrivateMsoBindError::CanonicalAnchorAmbiguous { anchor });
    }
    Ok(first)
}

impl MdocPrivateMsoBindWitness {
    /// Absolute issuer-message position of the first private MSO byte.
    ///
    /// The valueDigests scanner consumes this same private start through
    /// [`MdocMsoStartRelation`]; callers must not rediscover it with an
    /// independent byte search.
    pub(crate) fn mso_start(&self, mso_len: usize) -> Result<usize, MdocPrivateMsoBindError> {
        let anchor_len = payload_anchor(mso_len).len();
        self.payload_anchor_offset.checked_add(anchor_len).ok_or(
            MdocPrivateMsoBindError::PayloadOffsetOverflow {
                offset: self.payload_anchor_offset,
                anchor_len,
            },
        )
    }

    /// Derive every private offset from canonical bytes rather than accepting
    /// legacy statement-supplied offsets.
    ///
    /// The complete `empty external_aad || bstr-head || mso_bytes` occurrence
    /// and every supported fact anchor must be unique. This is the deliberate
    /// trusted-canonical-issuer boundary of U2.
    ///
    /// ponytail: if non-canonical or adversarial issuers become supported,
    /// replace these unique anchors with a full private Sig_structure/MSO CBOR
    /// parser rather than adding more search heuristics.
    pub(crate) fn from_canonical_issuer_message(
        spec: &MdocPrivateMsoBindSpec,
        issuer_message: Vec<u8>,
        mso_bytes: &[u8],
        version: MdocPrivateMsoVersion,
    ) -> Result<Self, MdocPrivateMsoBindError> {
        // Validate all public caps before constructing the anchored-payload
        // search needle. Relation-handle presence is immaterial to this
        // canonical witness helper, so mirror the spec's own mode.
        validate_spec(spec, spec.sha_stream.is_some())?;
        if issuer_message.len() != spec.issuer_message_len {
            return Err(MdocPrivateMsoBindError::IssuerMessageLengthMismatch {
                expected: spec.issuer_message_len,
                actual: issuer_message.len(),
            });
        }
        if mso_bytes.len() != spec.mso_len {
            return Err(MdocPrivateMsoBindError::MsoBytesLengthMismatch {
                expected: spec.mso_len,
                actual: mso_bytes.len(),
            });
        }
        let anchor = payload_anchor(spec.mso_len);
        let mut anchored_payload = Vec::with_capacity(anchor.len() + mso_bytes.len());
        anchored_payload.extend_from_slice(&anchor);
        anchored_payload.extend_from_slice(mso_bytes);
        let payload_anchor_offset =
            unique_subslice(&issuer_message, &anchored_payload, "Sig_structure payload")?;

        let mut version_run = Vec::with_capacity(VERSION_PREFIX.len() + 3);
        version_run.extend_from_slice(VERSION_PREFIX);
        version_run.extend_from_slice(match version {
            MdocPrivateMsoVersion::V1 => b"1.0",
            MdocPrivateMsoVersion::V2 => b"2.0",
        });
        let version_offset = unique_subslice(mso_bytes, &version_run, "MSO version")?;
        let digest_algorithm_offset =
            unique_subslice(mso_bytes, DIGEST_ALGORITHM_RUN, "MSO digestAlgorithm")?;
        let doc_type_offset = unique_subslice(
            mso_bytes,
            &canonical_doc_type_run(&spec.doc_type),
            "MSO docType",
        )?;
        let device_key_info_offset = unique_subslice(
            mso_bytes,
            &canonical_device_key_info_run(&spec.device_public_key),
            "MSO deviceKeyInfo",
        )?;
        let valid_from_offset = unique_subslice(mso_bytes, VALID_FROM_ANCHOR, "MSO validFrom")?;
        checked_window_end(
            WindowKind::ValidFrom,
            valid_from_offset,
            VALID_FROM_ANCHOR.len() + TDATE_BYTES,
            spec.mso_len,
        )?;
        let valid_until_offset = unique_subslice(mso_bytes, VALID_UNTIL_ANCHOR, "MSO validUntil")?;
        checked_window_end(
            WindowKind::ValidUntil,
            valid_until_offset,
            VALID_UNTIL_ANCHOR.len() + TDATE_BYTES,
            spec.mso_len,
        )?;
        Ok(Self {
            issuer_message,
            payload_anchor_offset,
            version_offset,
            digest_algorithm_offset,
            doc_type_offset,
            device_key_info_offset,
            valid_from_offset,
            valid_until_offset,
            version,
        })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WindowKind {
    PayloadAnchor,
    Version,
    DigestAlgorithm,
    DocType,
    DeviceKeyInfo,
    ValidFrom,
    ValidUntil,
    MsoMirror,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EvalConstantKind {
    DocType,
    DeviceKeyInfo,
}

impl WindowKind {
    fn name(self) -> &'static str {
        match self {
            Self::PayloadAnchor => "Sig_structure payload anchor",
            Self::Version => "MSO version",
            Self::DigestAlgorithm => "MSO digestAlgorithm",
            Self::DocType => "MSO docType",
            Self::DeviceKeyInfo => "MSO deviceKeyInfo",
            Self::ValidFrom => "MSO validFrom",
            Self::ValidUntil => "MSO validUntil",
            Self::MsoMirror => "full MSO mirror",
        }
    }
}

#[derive(Clone)]
struct PublicRow {
    kind: WindowKind,
    window_len: usize,
    chunk_relative: usize,
    byte_len: usize,
    continuation: bool,
    expected_active: [bool; CHUNK_BYTES],
    expected: [u8; CHUNK_BYTES],
    eval_constant: Option<(EvalConstantKind, usize)>,
    issuer_active: [bool; CHUNK_BYTES],
    version_row: bool,
    valid_from_date_row: bool,
    valid_until_date_row: bool,
    mirror_row: bool,
}

impl PublicRow {
    fn new(
        kind: WindowKind,
        window_len: usize,
        chunk_relative: usize,
        byte_len: usize,
        continuation: bool,
    ) -> Self {
        Self {
            kind,
            window_len,
            chunk_relative,
            byte_len,
            continuation,
            expected_active: [false; CHUNK_BYTES],
            expected: [0; CHUNK_BYTES],
            eval_constant: None,
            issuer_active: [false; CHUNK_BYTES],
            version_row: false,
            valid_from_date_row: false,
            valid_until_date_row: false,
            mirror_row: false,
        }
    }

    fn mso_window(&self) -> bool {
        self.kind != WindowKind::PayloadAnchor
    }
}

#[derive(Clone)]
struct PublicShape {
    payload_anchor: Vec<u8>,
    rows: Vec<PublicRow>,
}

fn checked_sha_padded_len(message_len: usize) -> Option<usize> {
    message_len
        .checked_add(9)?
        .checked_add(63)
        .map(|length| length / 64 * 64)
}

fn canonical_bstr_head(length: usize) -> Vec<u8> {
    match length {
        0..=23 => vec![0x40 | length as u8],
        24..=0xff => vec![0x58, length as u8],
        _ => {
            let bytes = (length as u16).to_be_bytes();
            vec![0x59, bytes[0], bytes[1]]
        }
    }
}

fn canonical_text_head(length: usize) -> Vec<u8> {
    match length {
        0..=23 => vec![0x60 | length as u8],
        24..=0xff => vec![0x78, length as u8],
        _ => {
            let bytes = (length as u16).to_be_bytes();
            vec![0x79, bytes[0], bytes[1]]
        }
    }
}

fn payload_anchor(mso_len: usize) -> Vec<u8> {
    let mut anchor = vec![0x40]; // canonical empty external_aad bstr
    anchor.extend_from_slice(&canonical_bstr_head(mso_len));
    anchor
}

fn canonical_doc_type_run(doc_type: &str) -> Vec<u8> {
    let mut run = Vec::with_capacity(DOC_TYPE_KEY.len() + 3 + doc_type.len());
    run.extend_from_slice(DOC_TYPE_KEY);
    run.extend_from_slice(&canonical_text_head(doc_type.len()));
    run.extend_from_slice(doc_type.as_bytes());
    run
}

fn canonical_device_key_info_run(public_key: &[u8]) -> Vec<u8> {
    let mut run = Vec::with_capacity(MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES);
    run.extend_from_slice(DEVICE_KEY_INFO_PREFIX);
    run.extend_from_slice(public_key);
    debug_assert_eq!(run.len(), MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES);
    run
}

fn push_constant_window(rows: &mut Vec<PublicRow>, kind: WindowKind, bytes: &[u8]) {
    for (chunk_index, chunk) in bytes.chunks(CHUNK_BYTES).enumerate() {
        let chunk_relative = chunk_index * CHUNK_BYTES;
        let mut row = PublicRow::new(
            kind,
            bytes.len(),
            chunk_relative,
            chunk.len(),
            chunk_index != 0,
        );
        row.expected_active[..chunk.len()].fill(true);
        row.expected[..chunk.len()].copy_from_slice(chunk);
        row.issuer_active[..chunk.len()].fill(true);
        rows.push(row);
    }
}

fn push_eval_constant_window(
    rows: &mut Vec<PublicRow>,
    kind: WindowKind,
    eval_kind: EvalConstantKind,
    bytes_len: usize,
) {
    for (chunk_index, chunk_relative) in (0..bytes_len).step_by(CHUNK_BYTES).enumerate() {
        let chunk_len = (bytes_len - chunk_relative).min(CHUNK_BYTES);
        let mut row = PublicRow::new(kind, bytes_len, chunk_relative, chunk_len, chunk_index != 0);
        row.eval_constant = Some((eval_kind, chunk_index));
        row.issuer_active[..chunk_len].fill(true);
        rows.push(row);
    }
}

fn push_version_window(rows: &mut Vec<PublicRow>) {
    let mut row = PublicRow::new(
        WindowKind::Version,
        VERSION_PREFIX.len() + 3,
        0,
        VERSION_PREFIX.len() + 3,
        false,
    );
    row.expected_active[..VERSION_PREFIX.len()].fill(true);
    row.expected[..VERSION_PREFIX.len()].copy_from_slice(VERSION_PREFIX);
    row.issuer_active[..row.byte_len].fill(true);
    row.version_row = true;
    rows.push(row);
}

fn push_tdate_window(rows: &mut Vec<PublicRow>, kind: WindowKind, anchor: &[u8], valid_from: bool) {
    let window_len = anchor.len() + TDATE_BYTES;
    let mut anchor_row = PublicRow::new(kind, window_len, 0, anchor.len(), false);
    anchor_row.expected_active[..anchor.len()].fill(true);
    anchor_row.expected[..anchor.len()].copy_from_slice(anchor);
    anchor_row.issuer_active[..anchor.len()].fill(true);
    rows.push(anchor_row);

    let mut date_row = PublicRow::new(kind, window_len, anchor.len(), TDATE_BYTES, true);
    date_row.issuer_active[..TDATE_BYTES].fill(true);
    date_row.valid_from_date_row = valid_from;
    date_row.valid_until_date_row = !valid_from;
    rows.push(date_row);
}

fn canonical_padding_byte(mso_len: usize, padded_len: usize, index: usize) -> u8 {
    if index == mso_len {
        return 0x80;
    }
    if index < padded_len - 8 {
        return 0;
    }
    let length_bytes = ((mso_len as u64) * 8).to_be_bytes();
    length_bytes[index - (padded_len - 8)]
}

fn push_mirror_rows(rows: &mut Vec<PublicRow>, mso_len: usize, padded_len: usize) {
    for chunk_relative in (0..padded_len).step_by(CHUNK_BYTES) {
        let mut row = PublicRow::new(
            WindowKind::MsoMirror,
            mso_len,
            chunk_relative,
            CHUNK_BYTES,
            chunk_relative != 0,
        );
        row.mirror_row = true;
        for byte_idx in 0..CHUNK_BYTES {
            let index = chunk_relative + byte_idx;
            if index < mso_len {
                row.issuer_active[byte_idx] = true;
            } else {
                row.expected_active[byte_idx] = true;
                row.expected[byte_idx] = canonical_padding_byte(mso_len, padded_len, index);
            }
        }
        rows.push(row);
    }
}

fn validate_spec(
    spec: &MdocPrivateMsoBindSpec,
    sha_handle_present: bool,
) -> Result<PublicShape, MdocPrivateMsoBindError> {
    if spec.issuer_message_len == 0 {
        return Err(MdocPrivateMsoBindError::EmptyIssuerMessage);
    }
    if spec.issuer_message_len > crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES {
        return Err(MdocPrivateMsoBindError::IssuerMessageTooLong {
            length: spec.issuer_message_len,
            max: crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES,
        });
    }
    if spec.mso_len == 0 {
        return Err(MdocPrivateMsoBindError::EmptyMso);
    }
    if spec.mso_len > crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES {
        return Err(MdocPrivateMsoBindError::MsoTooLong {
            length: spec.mso_len,
            max: crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES,
        });
    }
    if spec.device_public_key.len() != stwo_mldsa::constants::PK_BYTES {
        return Err(MdocPrivateMsoBindError::DevicePublicKeyLength {
            length: spec.device_public_key.len(),
            expected: stwo_mldsa::constants::PK_BYTES,
        });
    }
    if spec.doc_type.is_empty() {
        return Err(MdocPrivateMsoBindError::EmptyDocType);
    }
    if spec.doc_type.len() > MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES {
        return Err(MdocPrivateMsoBindError::DocTypeTooLong {
            length: spec.doc_type.len(),
            max: MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES,
        });
    }
    if spec.policy_date.year > 9_999
        || !(1..=12).contains(&spec.policy_date.month)
        || !(1..=31).contains(&spec.policy_date.day)
    {
        return Err(MdocPrivateMsoBindError::InvalidPolicyDate {
            year: spec.policy_date.year,
            month: spec.policy_date.month,
            day: spec.policy_date.day,
        });
    }
    if spec.sha_stream.is_some() != sha_handle_present {
        return Err(MdocPrivateMsoBindError::ShaStreamHandleMismatch {
            spec_present: spec.sha_stream.is_some(),
            handle_present: sha_handle_present,
        });
    }
    let payload_anchor = payload_anchor(spec.mso_len);
    if payload_anchor.len() + spec.mso_len > spec.issuer_message_len {
        return Err(MdocPrivateMsoBindError::MsoCannotFitIssuerMessage {
            issuer_message_len: spec.issuer_message_len,
            mso_len: spec.mso_len,
            anchor_len: payload_anchor.len(),
        });
    }
    if let Some(sha) = &spec.sha_stream {
        if sha.field_id >= M31_MODULUS {
            return Err(MdocPrivateMsoBindError::ShaFieldIdOutOfRange {
                field_id: sha.field_id,
            });
        }
        let expected = checked_sha_padded_len(spec.mso_len)
            .expect("bounded MSO length cannot overflow SHA padding");
        if sha.padded_len != expected {
            return Err(MdocPrivateMsoBindError::ShaPaddedLengthMismatch {
                expected,
                actual: sha.padded_len,
            });
        }
    }

    let mut rows = Vec::with_capacity(MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS);
    let mut anchor_row =
        PublicRow::new(WindowKind::PayloadAnchor, 0, 0, payload_anchor.len(), false);
    anchor_row.expected_active[..payload_anchor.len()].fill(true);
    anchor_row.expected[..payload_anchor.len()].copy_from_slice(&payload_anchor);
    anchor_row.issuer_active[..payload_anchor.len()].fill(true);
    rows.push(anchor_row);

    push_version_window(&mut rows);
    push_constant_window(&mut rows, WindowKind::DigestAlgorithm, DIGEST_ALGORITHM_RUN);
    push_eval_constant_window(
        &mut rows,
        WindowKind::DocType,
        EvalConstantKind::DocType,
        canonical_doc_type_run(&spec.doc_type).len(),
    );
    push_eval_constant_window(
        &mut rows,
        WindowKind::DeviceKeyInfo,
        EvalConstantKind::DeviceKeyInfo,
        MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES,
    );
    push_tdate_window(&mut rows, WindowKind::ValidFrom, VALID_FROM_ANCHOR, true);
    push_tdate_window(&mut rows, WindowKind::ValidUntil, VALID_UNTIL_ANCHOR, false);
    if let Some(sha) = &spec.sha_stream {
        push_mirror_rows(&mut rows, spec.mso_len, sha.padded_len);
    }
    if rows.len() > MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS {
        return Err(MdocPrivateMsoBindError::ScheduleTooLarge {
            active_rows: rows.len(),
            max: MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS,
        });
    }
    debug_assert!(MDOC_PRIVATE_MSO_BIND_ROWS - rows.len() >= MDOC_PRIVATE_MSO_MIN_BLIND_ROWS);
    Ok(PublicShape {
        payload_anchor,
        rows,
    })
}

const PP_ACTIVE: usize = 0;
const PP_MSO_WINDOW: usize = 1;
const PP_WINDOW_START: usize = 2;
const PP_CONTINUATION: usize = 3;
const PP_WINDOW_LEN: usize = 4;
const PP_CHUNK_RELATIVE: usize = 5;
const PP_VERSION_ROW: usize = 6;
const PP_VALID_FROM_DATE_ROW: usize = 7;
const PP_VALID_UNTIL_DATE_ROW: usize = 8;
const PP_MIRROR_ROW: usize = 9;
const PP_ANCHOR_ROW: usize = 10;
const PP_SAME_PAYLOAD_PREV: usize = 11;
const PP_BYTE_ACTIVE_START: usize = 12;
const PP_ISSUER_ACTIVE_START: usize = PP_BYTE_ACTIVE_START + CHUNK_BYTES;
const PP_EXPECTED_ACTIVE_START: usize = PP_ISSUER_ACTIVE_START + CHUNK_BYTES;
const PP_EXPECTED_START: usize = PP_EXPECTED_ACTIVE_START + CHUNK_BYTES;
const PP_DOC_TYPE_CHUNK_START: usize = PP_EXPECTED_START + CHUNK_BYTES;
const PP_DEVICE_KEY_INFO_CHUNK_START: usize = PP_DOC_TYPE_CHUNK_START + DOC_TYPE_CHUNKS;
const PREPROCESSED_COLS: usize = PP_DEVICE_KEY_INFO_CHUNK_START + DEVICE_KEY_INFO_CHUNKS;

const TRACE_BYTE_START: usize = 0;
const TRACE_PAYLOAD_OFFSET: usize = TRACE_BYTE_START + CHUNK_BYTES;
const TRACE_PAYLOAD_OFFSET_BITS: usize = TRACE_PAYLOAD_OFFSET + 1;
const TRACE_PAYLOAD_SLACK: usize = TRACE_PAYLOAD_OFFSET_BITS + OFFSET_BITS;
const TRACE_PAYLOAD_SLACK_BITS: usize = TRACE_PAYLOAD_SLACK + 1;
const TRACE_WINDOW_OFFSET: usize = TRACE_PAYLOAD_SLACK_BITS + OFFSET_BITS;
const TRACE_WINDOW_OFFSET_BITS: usize = TRACE_WINDOW_OFFSET + 1;
const TRACE_WINDOW_SLACK: usize = TRACE_WINDOW_OFFSET_BITS + OFFSET_BITS;
const TRACE_WINDOW_SLACK_BITS: usize = TRACE_WINDOW_SLACK + 1;
const TRACE_VERSION_SELECTOR: usize = TRACE_WINDOW_SLACK_BITS + OFFSET_BITS;
const TRACE_DIGIT_BITS: usize = TRACE_VERSION_SELECTOR + 1;
const TRACE_DATE_SLACK_BITS: usize = TRACE_DIGIT_BITS + TDATE_DIGITS * DIGIT_BITS;
const TRACE_RANGE_BITS: usize = TRACE_DATE_SLACK_BITS + DATE_SLACK_BITS;
const TRACE_COLS: usize = TRACE_RANGE_BITS + RANGE_BITS;

fn m31(value: usize) -> M31 {
    M31::from_u32_unchecked(value as u32)
}

fn m31_u32(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return M31::from_u32_unchecked(candidate);
        }
    }
}

fn random_bit() -> M31 {
    M31::from_u32_unchecked(rand::thread_rng().next_u32() & 1)
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn column_eval(values: Vec<M31>) -> MdocPrivateMsoColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(MDOC_PRIVATE_MSO_BIND_LOG_SIZE).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(
            MDOC_PRIVATE_MSO_BIND_LOG_SIZE,
            values,
        )),
    )
}

fn col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/private_mso_bind/v{BIND_VERSION}/{name}"),
    }
}

fn preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    let mut ids = vec![
        col_id("active"),
        col_id("mso_window"),
        col_id("window_start"),
        col_id("continuation"),
        col_id("window_len"),
        col_id("chunk_relative"),
        col_id("version_row"),
        col_id("valid_from_date_row"),
        col_id("valid_until_date_row"),
        col_id("mirror_row"),
        col_id("anchor_row"),
        col_id("same_payload_prev"),
    ];
    ids.extend((0..CHUNK_BYTES).map(|index| col_id(&format!("byte_active_{index}"))));
    ids.extend((0..CHUNK_BYTES).map(|index| col_id(&format!("issuer_active_{index}"))));
    ids.extend((0..CHUNK_BYTES).map(|index| col_id(&format!("expected_active_{index}"))));
    ids.extend((0..CHUNK_BYTES).map(|index| col_id(&format!("expected_{index}"))));
    ids.extend((0..DOC_TYPE_CHUNKS).map(|index| col_id(&format!("doc_type_chunk_{index}"))));
    ids.extend(
        (0..DEVICE_KEY_INFO_CHUNKS).map(|index| col_id(&format!("device_key_info_chunk_{index}"))),
    );
    debug_assert_eq!(ids.len(), PREPROCESSED_COLS);
    ids
}

fn preprocessed_columns(shape: &PublicShape) -> Vec<MdocPrivateMsoColumnEval> {
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); MDOC_PRIVATE_MSO_BIND_ROWS]; PREPROCESSED_COLS];
    for (row_index, row) in shape.rows.iter().enumerate() {
        columns[PP_ACTIVE][row_index] = m31_u32(1);
        columns[PP_MSO_WINDOW][row_index] = m31_u32(u32::from(row.mso_window()));
        columns[PP_WINDOW_START][row_index] =
            m31_u32(u32::from(row.mso_window() && !row.continuation));
        columns[PP_CONTINUATION][row_index] = m31_u32(u32::from(row.continuation));
        columns[PP_WINDOW_LEN][row_index] = m31(row.window_len);
        columns[PP_CHUNK_RELATIVE][row_index] = m31(row.chunk_relative);
        columns[PP_VERSION_ROW][row_index] = m31_u32(u32::from(row.version_row));
        columns[PP_VALID_FROM_DATE_ROW][row_index] = m31_u32(u32::from(row.valid_from_date_row));
        columns[PP_VALID_UNTIL_DATE_ROW][row_index] = m31_u32(u32::from(row.valid_until_date_row));
        columns[PP_MIRROR_ROW][row_index] = m31_u32(u32::from(row.mirror_row));
        columns[PP_ANCHOR_ROW][row_index] =
            m31_u32(u32::from(row.kind == WindowKind::PayloadAnchor));
        columns[PP_SAME_PAYLOAD_PREV][row_index] = m31_u32(u32::from(row_index != 0));
        for byte_index in 0..CHUNK_BYTES {
            columns[PP_BYTE_ACTIVE_START + byte_index][row_index] =
                m31_u32(u32::from(byte_index < row.byte_len));
            columns[PP_ISSUER_ACTIVE_START + byte_index][row_index] =
                m31_u32(u32::from(row.issuer_active[byte_index]));
            columns[PP_EXPECTED_ACTIVE_START + byte_index][row_index] =
                m31_u32(u32::from(row.expected_active[byte_index]));
            columns[PP_EXPECTED_START + byte_index][row_index] =
                m31_u32(u32::from(row.expected[byte_index]));
        }
        if let Some((kind, chunk_index)) = row.eval_constant {
            let column = match kind {
                EvalConstantKind::DocType => PP_DOC_TYPE_CHUNK_START + chunk_index,
                EvalConstantKind::DeviceKeyInfo => PP_DEVICE_KEY_INFO_CHUNK_START + chunk_index,
            };
            columns[column][row_index] = m31_u32(1);
        }
    }
    columns.into_iter().map(column_eval).collect()
}

fn bits_for(value: usize, count: usize) -> impl Iterator<Item = M31> {
    (0..count).map(move |bit| m31_u32(((value >> bit) & 1) as u32))
}

fn write_bits(columns: &mut [Vec<M31>], start: usize, row: usize, value: usize, count: usize) {
    for (column, bit) in columns[start..start + count]
        .iter_mut()
        .zip(bits_for(value, count))
    {
        column[row] = bit;
    }
}

fn write_digit_bits(columns: &mut [Vec<M31>], row: usize, digits: &[u8; TDATE_DIGITS]) {
    for (digit_index, digit) in digits.iter().enumerate() {
        write_bits(
            columns,
            TRACE_DIGIT_BITS + digit_index * DIGIT_BITS,
            row,
            usize::from(*digit),
            DIGIT_BITS,
        );
    }
}

fn randomize_globally_constrained_cells(columns: &mut [Vec<M31>]) {
    for row in 0..MDOC_PRIVATE_MSO_BIND_ROWS {
        for start in [
            TRACE_PAYLOAD_OFFSET_BITS,
            TRACE_PAYLOAD_SLACK_BITS,
            TRACE_WINDOW_OFFSET_BITS,
            TRACE_WINDOW_SLACK_BITS,
            TRACE_DATE_SLACK_BITS,
            TRACE_RANGE_BITS,
        ] {
            let count = match start {
                TRACE_DATE_SLACK_BITS => DATE_SLACK_BITS,
                TRACE_RANGE_BITS => RANGE_BITS,
                _ => OFFSET_BITS,
            };
            for column in &mut columns[start..start + count] {
                column[row] = random_bit();
            }
        }
        columns[TRACE_VERSION_SELECTOR][row] = random_bit();
        let digits = std::array::from_fn(|_| (rand::thread_rng().next_u32() % 10) as u8);
        write_digit_bits(columns, row, &digits);
    }
}

#[derive(Clone, Copy)]
struct ParsedTdate {
    digits: [u8; TDATE_DIGITS],
    year: usize,
    month: usize,
    day: usize,
    hour: usize,
    minute: usize,
    second: usize,
}

fn parse_tdate_for_trace(bytes: &[u8]) -> ParsedTdate {
    const POSITIONS: [usize; TDATE_DIGITS] = [0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18];
    let digits = std::array::from_fn(|index| {
        bytes
            .get(POSITIONS[index])
            .copied()
            .and_then(|byte| byte.checked_sub(b'0'))
            .filter(|digit| *digit <= 9)
            .unwrap_or(0)
    });
    let pair = |index: usize| usize::from(digits[index]) * 10 + usize::from(digits[index + 1]);
    ParsedTdate {
        digits,
        year: usize::from(digits[0]) * 1000
            + usize::from(digits[1]) * 100
            + usize::from(digits[2]) * 10
            + usize::from(digits[3]),
        month: pair(4),
        day: pair(6),
        hour: pair(8),
        minute: pair(10),
        second: pair(12),
    }
}

fn date_key(year: usize, month: usize, day: usize) -> usize {
    year * 512 + month * 32 + day
}

fn policy_date_key(policy: Date) -> usize {
    date_key(
        policy.year as usize,
        policy.month as usize,
        policy.day as usize,
    )
}

fn range_slacks(date: ParsedTdate) -> [usize; 7] {
    [
        date.month.saturating_sub(1),
        12usize.saturating_sub(date.month),
        date.day.saturating_sub(1),
        31usize.saturating_sub(date.day),
        23usize.saturating_sub(date.hour),
        59usize.saturating_sub(date.minute),
        59usize.saturating_sub(date.second),
    ]
}

fn write_tdate_aux(
    columns: &mut [Vec<M31>],
    row: usize,
    bytes: &[u8],
    policy: Date,
    valid_from: bool,
) {
    let date = parse_tdate_for_trace(bytes);
    write_digit_bits(columns, row, &date.digits);
    let credential_key = date_key(date.year, date.month, date.day);
    let public_key = policy_date_key(policy);
    let compare_slack = if valid_from {
        public_key.saturating_sub(credential_key)
    } else {
        credential_key.saturating_sub(public_key)
    };
    write_bits(
        columns,
        TRACE_DATE_SLACK_BITS,
        row,
        compare_slack,
        DATE_SLACK_BITS,
    );
    let slacks = range_slacks(date);
    let widths = [
        MONTH_RANGE_BITS,
        MONTH_RANGE_BITS,
        DAY_RANGE_BITS,
        DAY_RANGE_BITS,
        HOUR_RANGE_BITS,
        MINUTE_RANGE_BITS,
        SECOND_RANGE_BITS,
    ];
    let mut start = TRACE_RANGE_BITS;
    for (slack, width) in slacks.into_iter().zip(widths) {
        write_bits(columns, start, row, slack, width);
        start += width;
    }
    debug_assert_eq!(start, TRACE_COLS);
}

fn mso_window_offset(witness: &MdocPrivateMsoBindWitness, kind: WindowKind) -> usize {
    match kind {
        WindowKind::PayloadAnchor | WindowKind::MsoMirror => 0,
        WindowKind::Version => witness.version_offset,
        WindowKind::DigestAlgorithm => witness.digest_algorithm_offset,
        WindowKind::DocType => witness.doc_type_offset,
        WindowKind::DeviceKeyInfo => witness.device_key_info_offset,
        WindowKind::ValidFrom => witness.valid_from_offset,
        WindowKind::ValidUntil => witness.valid_until_offset,
    }
}

fn checked_window_end(
    kind: WindowKind,
    offset: usize,
    len: usize,
    mso_len: usize,
) -> Result<usize, MdocPrivateMsoBindError> {
    let end = offset
        .checked_add(len)
        .ok_or(MdocPrivateMsoBindError::WindowOffsetOverflow {
            window: kind.name(),
            offset,
            len,
        })?;
    if end > mso_len {
        return Err(MdocPrivateMsoBindError::WindowOutOfBounds {
            window: kind.name(),
            offset,
            len,
            mso_len,
        });
    }
    Ok(end)
}

fn padded_mso(raw: &[u8], padded_len: usize) -> Vec<u8> {
    let mut padded = Vec::with_capacity(padded_len);
    padded.extend_from_slice(raw);
    padded.push(0x80);
    padded.resize(padded_len - 8, 0);
    padded.extend_from_slice(&((raw.len() as u64) * 8).to_be_bytes());
    debug_assert_eq!(padded.len(), padded_len);
    padded
}

#[derive(Clone)]
struct MdocPrivateMsoTrace {
    columns: Vec<Vec<M31>>,
}

impl MdocPrivateMsoTrace {
    fn column_evals(&self) -> Vec<MdocPrivateMsoColumnEval> {
        self.columns.iter().cloned().map(column_eval).collect()
    }
}

fn private_trace(
    spec: &MdocPrivateMsoBindSpec,
    shape: &PublicShape,
    witness: &MdocPrivateMsoBindWitness,
    use_mso_start: bool,
) -> Result<(MdocPrivateMsoTrace, MdocPrivateMsoUseCensus), MdocPrivateMsoBindError> {
    if witness.issuer_message.len() != spec.issuer_message_len {
        return Err(MdocPrivateMsoBindError::IssuerMessageLengthMismatch {
            expected: spec.issuer_message_len,
            actual: witness.issuer_message.len(),
        });
    }
    let mso_start = witness
        .payload_anchor_offset
        .checked_add(shape.payload_anchor.len())
        .ok_or(MdocPrivateMsoBindError::PayloadOffsetOverflow {
            offset: witness.payload_anchor_offset,
            anchor_len: shape.payload_anchor.len(),
        })?;
    let mso_end =
        mso_start
            .checked_add(spec.mso_len)
            .ok_or(MdocPrivateMsoBindError::PayloadOutOfBounds {
                mso_start,
                mso_len: spec.mso_len,
                issuer_message_len: spec.issuer_message_len,
            })?;
    if mso_end > spec.issuer_message_len {
        return Err(MdocPrivateMsoBindError::PayloadOutOfBounds {
            mso_start,
            mso_len: spec.mso_len,
            issuer_message_len: spec.issuer_message_len,
        });
    }
    let payload_slack = spec.issuer_message_len - mso_end;

    for row in &shape.rows {
        if row.mso_window() {
            checked_window_end(
                row.kind,
                mso_window_offset(witness, row.kind),
                row.window_len,
                spec.mso_len,
            )?;
        }
    }

    let raw_mso = &witness.issuer_message[mso_start..mso_end];
    let padded = spec
        .sha_stream
        .as_ref()
        .map(|sha| padded_mso(raw_mso, sha.padded_len));
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); MDOC_PRIVATE_MSO_BIND_ROWS]; TRACE_COLS];
    for column in &mut columns {
        for value in column.iter_mut() {
            *value = random_m31_cell();
        }
    }
    randomize_globally_constrained_cells(&mut columns);

    let mut issuer_position_uses = vec![0u32; spec.issuer_message_len];
    let mut issuer_uses_total = 0usize;
    for (row_index, row) in shape.rows.iter().enumerate() {
        let offset = mso_window_offset(witness, row.kind);
        let window_slack = if row.mso_window() {
            spec.mso_len - offset - row.window_len
        } else {
            0
        };
        columns[TRACE_PAYLOAD_OFFSET][row_index] = m31(witness.payload_anchor_offset);
        write_bits(
            &mut columns,
            TRACE_PAYLOAD_OFFSET_BITS,
            row_index,
            witness.payload_anchor_offset,
            OFFSET_BITS,
        );
        columns[TRACE_PAYLOAD_SLACK][row_index] = m31(payload_slack);
        write_bits(
            &mut columns,
            TRACE_PAYLOAD_SLACK_BITS,
            row_index,
            payload_slack,
            OFFSET_BITS,
        );
        if row.mso_window() {
            columns[TRACE_WINDOW_OFFSET][row_index] = m31(offset);
            write_bits(
                &mut columns,
                TRACE_WINDOW_OFFSET_BITS,
                row_index,
                offset,
                OFFSET_BITS,
            );
            columns[TRACE_WINDOW_SLACK][row_index] = m31(window_slack);
            write_bits(
                &mut columns,
                TRACE_WINDOW_SLACK_BITS,
                row_index,
                window_slack,
                OFFSET_BITS,
            );
        } else {
            // Keep the active payload-anchor row on the linear issuer-index
            // path. Inactive rows retain their random window-offset cells.
            columns[TRACE_WINDOW_OFFSET][row_index] = m31(0);
        }
        columns[TRACE_VERSION_SELECTOR][row_index] = m31_u32(witness.version.selector());

        let source: &[u8] = if row.kind == WindowKind::PayloadAnchor {
            let start = witness.payload_anchor_offset + row.chunk_relative;
            &witness.issuer_message[start..start + row.byte_len]
        } else if row.kind == WindowKind::MsoMirror {
            let padded = padded
                .as_ref()
                .expect("mirror rows exist only with a SHA stream spec");
            &padded[row.chunk_relative..row.chunk_relative + row.byte_len]
        } else {
            let start = mso_start + offset + row.chunk_relative;
            &witness.issuer_message[start..start + row.byte_len]
        };
        for (byte_index, &byte) in source.iter().enumerate() {
            columns[TRACE_BYTE_START + byte_index][row_index] = m31_u32(u32::from(byte));
            if row.issuer_active[byte_index] {
                let issuer_index = if row.kind == WindowKind::PayloadAnchor {
                    witness.payload_anchor_offset + row.chunk_relative + byte_index
                } else {
                    mso_start + offset + row.chunk_relative + byte_index
                };
                issuer_position_uses[issuer_index] = issuer_position_uses[issuer_index]
                    .checked_add(1)
                    .ok_or(MdocPrivateMsoBindError::UseCountOverflow { issuer_index })?;
                issuer_uses_total += 1;
            }
        }
        if row.valid_from_date_row || row.valid_until_date_row {
            write_tdate_aux(
                &mut columns,
                row_index,
                source,
                spec.policy_date,
                row.valid_from_date_row,
            );
        }
    }
    let active_rows = shape.rows.len();
    Ok((
        MdocPrivateMsoTrace { columns },
        MdocPrivateMsoUseCensus {
            issuer_position_uses,
            issuer_uses_total,
            sha_stream_uses: spec.sha_stream.as_ref().map_or(0, |sha| sha.padded_len),
            mso_start_uses: usize::from(use_mso_start),
            active_rows,
            blind_rows: MDOC_PRIVATE_MSO_BIND_ROWS - active_rows,
        },
    ))
}

#[derive(Clone)]
struct MdocPrivateMsoEval {
    spec: MdocPrivateMsoBindSpec,
    payload_anchor_len: usize,
    issuer_relation: FieldBytesRelation,
    sha_relation: Option<FieldBytesRelation>,
    mso_start_relation: Option<MdocMsoStartRelation>,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

fn m31_const<E: EvalAtRow>(value: usize) -> E::F {
    E::F::from(M31::from_u32_unchecked(value as u32))
}

fn bit_sum<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |sum, (index, bit)| {
            sum + m31_const::<E>(1usize << index) * bit.clone()
        })
}

fn add_boolean<E: EvalAtRow>(eval: &mut E, value: E::F, one: &E::F) {
    eval.add_constraint(value.clone() * (value - one.clone()));
}

fn issuer_absolute_index<T>(
    payload_offset: T,
    chunk_relative: T,
    byte_index: T,
    mso_window: T,
    payload_anchor_len: T,
    window_offset: T,
) -> T
where
    T: std::ops::Add<Output = T> + std::ops::Mul<Output = T>,
{
    payload_offset + chunk_relative + byte_index + mso_window * payload_anchor_len + window_offset
}

struct MdocPrivateMsoInteractionInputs<'a> {
    issuer_relation: &'a FieldBytesRelation,
    sha_relation: Option<&'a FieldBytesRelation>,
    mso_start_relation: Option<&'a MdocMsoStartRelation>,
    blinder_relation: &'a ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

fn private_mso_interaction_trace(
    spec: &MdocPrivateMsoBindSpec,
    shape: &PublicShape,
    trace: &MdocPrivateMsoTrace,
    inputs: MdocPrivateMsoInteractionInputs<'_>,
) -> (Vec<MdocPrivateMsoColumnEval>, QM31) {
    let public = preprocessed_columns(shape);
    let private = trace.column_evals();
    let n_vec_rows = 1usize << (MDOC_PRIVATE_MSO_BIND_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(
        CHUNK_BYTES
            + usize::from(inputs.sha_relation.is_some()) * CHUNK_BYTES
            + usize::from(inputs.mso_start_relation.is_some())
            + 1,
    );

    // Fixed sites 0..32: hosted issuer-message consumers.
    for byte_index in 0..CHUNK_BYTES {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator =
                        PackedQM31::from(public[PP_ISSUER_ACTIVE_START + byte_index].data[vec_row]);
                    let absolute_index = issuer_absolute_index(
                        private[TRACE_PAYLOAD_OFFSET].data[vec_row],
                        public[PP_CHUNK_RELATIVE].data[vec_row],
                        PackedM31::broadcast(m31(byte_index)),
                        public[PP_MSO_WINDOW].data[vec_row],
                        PackedM31::broadcast(m31(shape.payload_anchor.len())),
                        private[TRACE_WINDOW_OFFSET].data[vec_row],
                    );
                    let denominator = inputs.issuer_relation.combine(&[
                        PackedM31::broadcast(m31_u32(HOSTED_MSG_FIELD_ID)),
                        absolute_index,
                        private[TRACE_BYTE_START + byte_index].data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    // Optional fixed sites 32..64: complete canonical padded MSO stream.
    if let (Some(sha), Some(relation)) = (&spec.sha_stream, inputs.sha_relation) {
        for byte_index in 0..CHUNK_BYTES {
            sites.push(
                (0..n_vec_rows)
                    .map(|vec_row| {
                        let numerator = PackedQM31::from(
                            public[PP_MIRROR_ROW].data[vec_row]
                                * public[PP_BYTE_ACTIVE_START + byte_index].data[vec_row],
                        );
                        let denominator = relation.combine(&[
                            PackedM31::broadcast(m31_u32(sha.field_id)),
                            public[PP_CHUNK_RELATIVE].data[vec_row]
                                + PackedM31::broadcast(m31(byte_index)),
                            private[TRACE_BYTE_START + byte_index].data[vec_row],
                        ]);
                        (numerator, denominator)
                    })
                    .collect(),
            );
        }
    }

    // Optional Q-732 handoff: binder provider (-), map scanner consumer (+).
    if let Some(relation) = inputs.mso_start_relation {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = -PackedQM31::from(public[PP_ANCHOR_ROW].data[vec_row]);
                    let denominator = relation.combine(&[
                        private[TRACE_PAYLOAD_OFFSET].data[vec_row]
                            + PackedM31::broadcast(m31(shape.payload_anchor.len())),
                        private[TRACE_VERSION_SELECTOR].data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    // Claimed-sum blinder is always the final main-component site.
    let blinder_numerator = PackedQM31::broadcast(inputs.blinder_m);
    let blinder_denominator = blinder_denominator(inputs.blinder_relation, inputs.blinder_v);
    sites.push(vec![(blinder_numerator, blinder_denominator); n_vec_rows]);

    let mut logup = LogupTraceGenerator::new(MDOC_PRIVATE_MSO_BIND_LOG_SIZE);
    let mut site_index = 0usize;
    while site_index + 1 < sites.len() {
        let left = &sites[site_index];
        let right = &sites[site_index + 1];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let (left_numerator, left_denominator) = left[vec_row];
            let (right_numerator, right_denominator) = right[vec_row];
            (
                left_numerator * right_denominator + right_numerator * left_denominator,
                left_denominator * right_denominator,
            )
        }));
        site_index += 2;
    }
    if site_index < sites.len() {
        let last = &sites[site_index];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| last[vec_row]));
    }
    logup.finalize_last()
}

impl FrameworkEval for MdocPrivateMsoEval {
    fn log_size(&self) -> u32 {
        MDOC_PRIVATE_MSO_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Absolute issuer indices stay linear: non-MSO active rows constrain
        // window_offset to zero before it is added unconditionally. Paired
        // LogUp denominators and quadratic selector numerators are cubic.
        MDOC_PRIVATE_MSO_BIND_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(col_id("active"));
        let mso_window = eval.get_preprocessed_column(col_id("mso_window"));
        let window_start = eval.get_preprocessed_column(col_id("window_start"));
        let continuation = eval.get_preprocessed_column(col_id("continuation"));
        let window_len = eval.get_preprocessed_column(col_id("window_len"));
        let chunk_relative = eval.get_preprocessed_column(col_id("chunk_relative"));
        let version_row = eval.get_preprocessed_column(col_id("version_row"));
        let valid_from_date_row = eval.get_preprocessed_column(col_id("valid_from_date_row"));
        let valid_until_date_row = eval.get_preprocessed_column(col_id("valid_until_date_row"));
        let mirror_row = eval.get_preprocessed_column(col_id("mirror_row"));
        let anchor_row = eval.get_preprocessed_column(col_id("anchor_row"));
        let same_payload_prev = eval.get_preprocessed_column(col_id("same_payload_prev"));
        let byte_active: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("byte_active_{index}")))
        });
        let issuer_active: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("issuer_active_{index}")))
        });
        let expected_active: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("expected_active_{index}")))
        });
        let expected: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("expected_{index}")))
        });
        let doc_type_chunks: [E::F; DOC_TYPE_CHUNKS] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("doc_type_chunk_{index}")))
        });
        let device_key_info_chunks: [E::F; DEVICE_KEY_INFO_CHUNKS] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("device_key_info_chunk_{index}")))
        });

        let bytes: [E::F; CHUNK_BYTES] = std::array::from_fn(|_| eval.next_trace_mask());
        let [payload_offset, payload_offset_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let payload_offset_bits: [E::F; OFFSET_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let payload_slack = eval.next_trace_mask();
        let payload_slack_bits: [E::F; OFFSET_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let [window_offset, window_offset_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let window_offset_bits: [E::F; OFFSET_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let window_slack = eval.next_trace_mask();
        let window_slack_bits: [E::F; OFFSET_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let [version_selector, version_selector_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let digit_bits: [[E::F; DIGIT_BITS]; TDATE_DIGITS] =
            std::array::from_fn(|_| std::array::from_fn(|_| eval.next_trace_mask()));
        let date_slack_bits: [E::F; DATE_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let range_bits: [E::F; RANGE_BITS] = std::array::from_fn(|_| eval.next_trace_mask());

        let one = m31_const::<E>(1);
        for selector in [
            active.clone(),
            mso_window.clone(),
            window_start.clone(),
            continuation.clone(),
            version_row.clone(),
            valid_from_date_row.clone(),
            valid_until_date_row.clone(),
            mirror_row.clone(),
            anchor_row.clone(),
            same_payload_prev.clone(),
        ] {
            add_boolean(&mut eval, selector, &one);
        }
        eval.add_constraint(window_start.clone() + continuation.clone() - mso_window.clone());
        eval.add_constraint(anchor_row.clone() * (active.clone() - one.clone()));
        eval.add_constraint(mirror_row.clone() * (mso_window.clone() - one.clone()));
        eval.add_constraint(
            (valid_from_date_row.clone() + valid_until_date_row.clone())
                * (mso_window.clone() - one.clone()),
        );
        for index in 0..CHUNK_BYTES {
            add_boolean(&mut eval, byte_active[index].clone(), &one);
            add_boolean(&mut eval, issuer_active[index].clone(), &one);
            add_boolean(&mut eval, expected_active[index].clone(), &one);
            eval.add_constraint(
                issuer_active[index].clone() * (one.clone() - byte_active[index].clone()),
            );
            eval.add_constraint(
                expected_active[index].clone() * (one.clone() - byte_active[index].clone()),
            );
        }
        for selector in doc_type_chunks.iter().chain(device_key_info_chunks.iter()) {
            add_boolean(&mut eval, selector.clone(), &one);
            eval.add_constraint(selector.clone() * (active.clone() - one.clone()));
        }

        // All private selector/decomposition bits are boolean on every row.
        // Inactive rows therefore receive fresh valid bits rather than zeros.
        for bit in payload_offset_bits
            .iter()
            .chain(payload_slack_bits.iter())
            .chain(window_offset_bits.iter())
            .chain(window_slack_bits.iter())
            .chain(date_slack_bits.iter())
            .chain(range_bits.iter())
            .chain(digit_bits.iter().flatten())
        {
            add_boolean(&mut eval, bit.clone(), &one);
        }
        add_boolean(&mut eval, version_selector.clone(), &one);
        for bits in &digit_bits {
            // Four boolean bits plus these two quadratic exclusions encode 0..9.
            eval.add_constraint(bits[3].clone() * bits[2].clone());
            eval.add_constraint(bits[3].clone() * bits[1].clone());
        }

        // One payload anchor and one private profile selector are common to
        // every active row. Continuation rows retain one logical-window offset.
        eval.add_constraint(
            same_payload_prev.clone() * (payload_offset.clone() - payload_offset_prev),
        );
        eval.add_constraint(same_payload_prev * (version_selector.clone() - version_selector_prev));
        eval.add_constraint(continuation.clone() * (window_offset.clone() - window_offset_prev));

        // Four globally-boolean 13-bit decompositions prevent M31 wraparound.
        eval.add_constraint(
            active.clone() * (payload_offset.clone() - bit_sum::<E>(&payload_offset_bits)),
        );
        eval.add_constraint(
            active.clone() * (payload_slack.clone() - bit_sum::<E>(&payload_slack_bits)),
        );
        eval.add_constraint(
            active.clone()
                * (payload_offset.clone()
                    + m31_const::<E>(self.payload_anchor_len)
                    + m31_const::<E>(self.spec.mso_len)
                    + payload_slack
                    - m31_const::<E>(self.spec.issuer_message_len)),
        );
        eval.add_constraint(
            mso_window.clone() * (window_offset.clone() - bit_sum::<E>(&window_offset_bits)),
        );
        eval.add_constraint(
            mso_window.clone() * (window_slack.clone() - bit_sum::<E>(&window_slack_bits)),
        );
        eval.add_constraint(
            mso_window.clone()
                * (window_offset.clone() + window_len + window_slack
                    - m31_const::<E>(self.spec.mso_len)),
        );
        eval.add_constraint((active.clone() - mso_window.clone()) * window_offset.clone());
        eval.add_constraint(mirror_row.clone() * window_offset.clone());

        // Protocol-invariant anchors and canonical padding are safe in tree
        // zero. Credential/request-varying public values stay out of
        // preprocessing: content-independent chunk selectors pick their
        // bytes from public Eval constants instead.
        for index in 0..CHUNK_BYTES {
            eval.add_constraint(
                expected_active[index].clone() * (bytes[index].clone() - expected[index].clone()),
            );
        }
        let doc_type = canonical_doc_type_run(&self.spec.doc_type);
        for (chunk_index, selector) in doc_type_chunks.iter().enumerate() {
            let chunk_start = chunk_index * CHUNK_BYTES;
            for (byte_index, expected_byte) in
                doc_type[chunk_start..].iter().take(CHUNK_BYTES).enumerate()
            {
                eval.add_constraint(
                    selector.clone()
                        * (bytes[byte_index].clone() - m31_const::<E>(usize::from(*expected_byte))),
                );
            }
        }
        let device_key_info = canonical_device_key_info_run(&self.spec.device_public_key);
        for (chunk_index, selector) in device_key_info_chunks.iter().enumerate() {
            let chunk_start = chunk_index * CHUNK_BYTES;
            for (byte_index, expected_byte) in device_key_info[chunk_start..]
                .iter()
                .take(CHUNK_BYTES)
                .enumerate()
            {
                eval.add_constraint(
                    selector.clone()
                        * (bytes[byte_index].clone() - m31_const::<E>(usize::from(*expected_byte))),
                );
            }
        }

        // Private supported profile: selector 0 => "1.0", 1 => "2.0".
        for (index, (&v1, &v2)) in b"1.0".iter().zip(b"2.0").enumerate() {
            let byte_index = VERSION_PREFIX.len() + index;
            let selected = (one.clone() - version_selector.clone())
                * m31_const::<E>(usize::from(v1))
                + version_selector.clone() * m31_const::<E>(usize::from(v2));
            eval.add_constraint(version_row.clone() * (bytes[byte_index].clone() - selected));
        }

        let date_active = valid_from_date_row.clone() + valid_until_date_row.clone();
        const DIGIT_POSITIONS: [usize; TDATE_DIGITS] =
            [0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18];
        let digits: [E::F; TDATE_DIGITS] =
            std::array::from_fn(|index| bit_sum::<E>(&digit_bits[index]));
        for (digit_index, byte_index) in DIGIT_POSITIONS.into_iter().enumerate() {
            eval.add_constraint(
                date_active.clone()
                    * (bytes[byte_index].clone()
                        - m31_const::<E>(b'0' as usize)
                        - digits[digit_index].clone()),
            );
        }
        for (index, byte) in [
            (4usize, b'-'),
            (7, b'-'),
            (10, b'T'),
            (13, b':'),
            (16, b':'),
            (19, b'Z'),
        ] {
            eval.add_constraint(
                date_active.clone() * (bytes[index].clone() - m31_const::<E>(byte as usize)),
            );
        }

        let year = m31_const::<E>(1000) * digits[0].clone()
            + m31_const::<E>(100) * digits[1].clone()
            + m31_const::<E>(10) * digits[2].clone()
            + digits[3].clone();
        let month = m31_const::<E>(10) * digits[4].clone() + digits[5].clone();
        let day = m31_const::<E>(10) * digits[6].clone() + digits[7].clone();
        let hour = m31_const::<E>(10) * digits[8].clone() + digits[9].clone();
        let minute = m31_const::<E>(10) * digits[10].clone() + digits[11].clone();
        let second = m31_const::<E>(10) * digits[12].clone() + digits[13].clone();
        let date_key =
            m31_const::<E>(512) * year + m31_const::<E>(32) * month.clone() + day.clone();

        let mut range_cursor = 0usize;
        let month_lower = bit_sum::<E>(&range_bits[range_cursor..range_cursor + MONTH_RANGE_BITS]);
        range_cursor += MONTH_RANGE_BITS;
        let month_upper = bit_sum::<E>(&range_bits[range_cursor..range_cursor + MONTH_RANGE_BITS]);
        range_cursor += MONTH_RANGE_BITS;
        let day_lower = bit_sum::<E>(&range_bits[range_cursor..range_cursor + DAY_RANGE_BITS]);
        range_cursor += DAY_RANGE_BITS;
        let day_upper = bit_sum::<E>(&range_bits[range_cursor..range_cursor + DAY_RANGE_BITS]);
        range_cursor += DAY_RANGE_BITS;
        let hour_upper = bit_sum::<E>(&range_bits[range_cursor..range_cursor + HOUR_RANGE_BITS]);
        range_cursor += HOUR_RANGE_BITS;
        let minute_upper =
            bit_sum::<E>(&range_bits[range_cursor..range_cursor + MINUTE_RANGE_BITS]);
        range_cursor += MINUTE_RANGE_BITS;
        let second_upper =
            bit_sum::<E>(&range_bits[range_cursor..range_cursor + SECOND_RANGE_BITS]);
        range_cursor += SECOND_RANGE_BITS;
        debug_assert_eq!(range_cursor, RANGE_BITS);

        eval.add_constraint(date_active.clone() * (month.clone() - one.clone() - month_lower));
        eval.add_constraint(date_active.clone() * (m31_const::<E>(12) - month - month_upper));
        eval.add_constraint(date_active.clone() * (day.clone() - one.clone() - day_lower));
        eval.add_constraint(date_active.clone() * (m31_const::<E>(31) - day - day_upper));
        eval.add_constraint(date_active.clone() * (m31_const::<E>(23) - hour - hour_upper));
        eval.add_constraint(date_active.clone() * (m31_const::<E>(59) - minute - minute_upper));
        eval.add_constraint(date_active.clone() * (m31_const::<E>(59) - second - second_upper));
        let compare_slack = bit_sum::<E>(&date_slack_bits);
        let policy_key = m31_const::<E>(policy_date_key(self.spec.policy_date));
        eval.add_constraint(
            valid_from_date_row * (policy_key.clone() - date_key.clone() - compare_slack.clone()),
        );
        eval.add_constraint(valid_until_date_row * (date_key - policy_key - compare_slack));

        // Fixed relation-site order: 32 issuer, optional 32 SHA, optional
        // mso_start, blinder last.
        for index in 0..CHUNK_BYTES {
            let absolute_index = issuer_absolute_index(
                payload_offset.clone(),
                chunk_relative.clone(),
                m31_const::<E>(index),
                mso_window.clone(),
                m31_const::<E>(self.payload_anchor_len),
                window_offset.clone(),
            );
            eval.add_to_relation(RelationEntry::new(
                &self.issuer_relation,
                E::EF::from(issuer_active[index].clone()),
                &[
                    m31_const::<E>(HOSTED_MSG_FIELD_ID as usize),
                    absolute_index,
                    bytes[index].clone(),
                ],
            ));
        }
        if let (Some(sha), Some(relation)) = (&self.spec.sha_stream, &self.sha_relation) {
            for index in 0..CHUNK_BYTES {
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    E::EF::from(mirror_row.clone() * byte_active[index].clone()),
                    &[
                        m31_const::<E>(sha.field_id as usize),
                        chunk_relative.clone() + m31_const::<E>(index),
                        bytes[index].clone(),
                    ],
                ));
            }
        }
        if let Some(relation) = &self.mso_start_relation {
            eval.add_to_relation(RelationEntry::new(
                relation,
                -E::EF::from(anchor_row),
                &[
                    payload_offset + m31_const::<E>(self.payload_anchor_len),
                    version_selector,
                ],
            ));
        }
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

pub(crate) struct MdocPrivateMsoBind {
    spec: MdocPrivateMsoBindSpec,
    shape: PublicShape,
    trace: Option<MdocPrivateMsoTrace>,
    issuer_handle: SharedFieldRelation,
    sha_handle: Option<SharedFieldRelation>,
    mso_start_handle: Option<SharedMdocMsoStartRelation>,
    mso_start_relation: Option<MdocMsoStartRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocPrivateMsoInteractionClaim>,
    component: Option<MdocPrivateMsoComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocPrivateMsoBind {
    #[allow(clippy::type_complexity)]
    pub(crate) fn prover(
        spec: MdocPrivateMsoBindSpec,
        witness: MdocPrivateMsoBindWitness,
        issuer_handle: SharedFieldRelation,
        sha_handle: Option<SharedFieldRelation>,
        mso_start_handle: Option<SharedMdocMsoStartRelation>,
    ) -> Result<(Self, MdocPrivateMsoUseCensus), MdocPrivateMsoBindError> {
        let shape = validate_spec(&spec, sha_handle.is_some())?;
        let (trace, census) = private_trace(&spec, &shape, &witness, mso_start_handle.is_some())?;
        Ok((
            Self {
                spec,
                shape,
                trace: Some(trace),
                issuer_handle,
                sha_handle,
                mso_start_handle,
                mso_start_relation: None,
                blinder_relation: None,
                interaction_claim: None,
                component: None,
                blinder_component: None,
            },
            census,
        ))
    }

    pub(crate) fn verifier(
        spec: MdocPrivateMsoBindSpec,
        issuer_handle: SharedFieldRelation,
        sha_handle: Option<SharedFieldRelation>,
        mso_start_handle: Option<SharedMdocMsoStartRelation>,
        interaction_claim: MdocPrivateMsoInteractionClaim,
    ) -> Result<Self, MdocPrivateMsoBindError> {
        let shape = validate_spec(&spec, sha_handle.is_some())?;
        Ok(Self {
            spec,
            shape,
            trace: None,
            issuer_handle,
            sha_handle,
            mso_start_handle,
            mso_start_relation: None,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        })
    }

    pub(crate) fn interaction_claim(&self) -> &MdocPrivateMsoInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("private MSO bind interaction claim is set")
    }

    #[cfg(test)]
    pub(crate) fn active_rows(&self) -> usize {
        self.shape.rows.len()
    }

    fn issuer_relation(&self) -> FieldBytesRelation {
        self.issuer_handle.get()
    }

    fn sha_relation(&self) -> Option<FieldBytesRelation> {
        self.sha_handle.as_ref().map(SharedFieldRelation::get)
    }

    fn n_main_sites(&self) -> usize {
        CHUNK_BYTES
            + usize::from(self.spec.sha_stream.is_some()) * CHUNK_BYTES
            + usize::from(self.mso_start_handle.is_some())
            + 1 // blinder, last
    }

    fn interaction_columns(&self) -> usize {
        // Main paired LogUp columns plus one blinder-counterpart column.
        (self.n_main_sites().div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE
    }
}

impl Air for MdocPrivateMsoBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(BIND_DOMAIN);
        channel.mix_u64(BIND_VERSION);
        channel.mix_u64(self.spec.issuer_message_len as u64);
        channel.mix_u64(self.spec.mso_len as u64);
        channel.mix_u64(self.shape.payload_anchor.len() as u64);
        channel.mix_u64(self.shape.rows.len() as u64);
        channel.mix_u64(PREPROCESSED_COLS as u64);
        channel.mix_u64(TRACE_COLS as u64);
        channel.mix_u64(self.interaction_columns() as u64);
        channel.mix_u64(self.spec.policy_date.year as u64);
        channel.mix_u64(self.spec.policy_date.month as u64);
        channel.mix_u64(self.spec.policy_date.day as u64);
        channel.mix_u64(self.spec.doc_type.len() as u64);
        for &byte in self.spec.doc_type.as_bytes() {
            channel.mix_u64(u64::from(byte));
        }
        channel.mix_u64(self.spec.device_public_key.len() as u64);
        for &byte in &self.spec.device_public_key {
            channel.mix_u64(u64::from(byte));
        }
        match &self.spec.sha_stream {
            Some(sha) => {
                channel.mix_u64(1);
                channel.mix_u64(u64::from(sha.field_id));
                channel.mix_u64(sha.padded_len as u64);
            }
            None => channel.mix_u64(0),
        }
        channel.mix_u64(u64::from(self.mso_start_handle.is_some()));
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        if let Some(handle) = &self.mso_start_handle {
            assert!(
                !handle.is_set(),
                "private MSO binder needs a fresh mso_start relation handle"
            );
            let relation = MdocMsoStartRelation::draw(channel);
            handle.set(relation.clone());
            self.mso_start_relation = Some(relation);
        }
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; PREPROCESSED_COLS],
            trace: vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; TRACE_COLS],
            interaction: vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; self.interaction_columns()],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns(&self.shape))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private MSO binder blinder relation is drawn");
        self.component = Some(MdocPrivateMsoComponent::new(
            allocator,
            MdocPrivateMsoEval {
                spec: self.spec.clone(),
                payload_anchor_len: self.shape.payload_anchor.len(),
                issuer_relation: self.issuer_relation(),
                sha_relation: self.sha_relation(),
                mso_start_relation: self.mso_start_relation.clone(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_PRIVATE_MSO_BIND_LOG_SIZE,
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
                .expect("private MSO bind component is built"),
            self.blinder_component
                .as_ref()
                .expect("private MSO bind blinder component is built"),
        ]
    }
}

impl AirProver for MdocPrivateMsoBind {
    fn max_log_size(&self) -> u32 {
        MDOC_PRIVATE_MSO_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_PRIVATE_MSO_BIND_LOG_SIZE + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_private_mso_bind::MdocPrivateMsoBind",
            &preprocessed_column_ids(),
            &preprocessed_columns(&self.shape),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = preprocessed_column_ids();
        let all_columns = preprocessed_columns(&self.shape);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected private MSO bind preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let trace = self
            .trace
            .as_ref()
            .expect("private MSO bind prover has a witness");
        tb.extend_evals(trace.column_evals());
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let trace = self
            .trace
            .as_ref()
            .expect("private MSO bind prover has a witness");
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private MSO binder blinder relation is drawn");
        let issuer_relation = self.issuer_relation();
        let sha_relation = self.sha_relation();
        let (interaction, claimed_sum) = private_mso_interaction_trace(
            &self.spec,
            &self.shape,
            trace,
            MdocPrivateMsoInteractionInputs {
                issuer_relation: &issuer_relation,
                sha_relation: sha_relation.as_ref(),
                mso_start_relation: self.mso_start_relation.as_ref(),
                blinder_relation: &blinder_relation,
                blinder_v,
                blinder_m,
            },
        );
        tb.extend_evals(interaction);
        let (blinder_trace, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_PRIVATE_MSO_BIND_LOG_SIZE,
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocPrivateMsoInteractionClaim {
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
                .expect("private MSO bind component is built"),
            self.blinder_component
                .as_ref()
                .expect("private MSO bind blinder component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use stwo::core::verifier::VerificationError;
    use stwo::prover::backend::Column as _;
    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    const PID: &str = "eu.europa.ec.eudi.pid.1";
    const TEST_COUNTER_DOMAIN: u64 = 0x4d44_4f43_4d53_4f54; // "MDOCMSOT"
    const PAYLOAD_OFFSET: usize = 20;
    const VERSION_OFFSET: usize = 0;
    const ALGORITHM_OFFSET: usize = 16;
    const DOC_TYPE_OFFSET: usize = 64;
    const DEVICE_KEY_OFFSET: usize = 128;
    const VALID_FROM_OFFSET: usize = 2_200;
    const VALID_UNTIL_OFFSET: usize = 2_300;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct PolynomialDegree(u32);

    impl std::ops::Add for PolynomialDegree {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            Self(self.0.max(rhs.0))
        }
    }

    // Multiplication adds polynomial degrees; the arithmetic is intentional.
    #[allow(clippy::suspicious_arithmetic_impl)]
    impl std::ops::Mul for PolynomialDegree {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            Self(self.0 + rhs.0)
        }
    }

    fn qm31(value: u32) -> QM31 {
        QM31::from(M31::from_u32_unchecked(value))
    }

    fn test_claim() -> MdocPrivateMsoInteractionClaim {
        MdocPrivateMsoInteractionClaim {
            claimed_sum: qm31(1),
            blinder_v: qm31(2),
            blinder_m: qm31(3),
            blinder_claimed_sum: qm31(4),
        }
    }

    fn test_spec(with_sha: bool) -> MdocPrivateMsoBindSpec {
        MdocPrivateMsoBindSpec {
            issuer_message_len: crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES,
            mso_len: crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES,
            doc_type: PID.to_string(),
            device_public_key: vec![0; stwo_mldsa::constants::PK_BYTES],
            policy_date: Date {
                year: 2026,
                month: 7,
                day: 29,
            },
            sha_stream: with_sha.then_some(MdocPrivateMsoShaStreamSpec {
                field_id: 91,
                padded_len: 4_160,
            }),
        }
    }

    fn write_at(target: &mut [u8], offset: usize, bytes: &[u8]) {
        target[offset..offset + bytes.len()].copy_from_slice(bytes);
    }

    fn test_parts_for_spec(
        spec: MdocPrivateMsoBindSpec,
    ) -> (MdocPrivateMsoBindSpec, Vec<u8>, Vec<u8>) {
        let mut mso = vec![0x55; spec.mso_len];

        let mut version = VERSION_PREFIX.to_vec();
        version.extend_from_slice(b"1.0");
        write_at(&mut mso, VERSION_OFFSET, &version);
        write_at(&mut mso, ALGORITHM_OFFSET, DIGEST_ALGORITHM_RUN);
        write_at(
            &mut mso,
            DOC_TYPE_OFFSET,
            &canonical_doc_type_run(&spec.doc_type),
        );
        write_at(
            &mut mso,
            DEVICE_KEY_OFFSET,
            &canonical_device_key_info_run(&spec.device_public_key),
        );
        let mut valid_from = VALID_FROM_ANCHOR.to_vec();
        valid_from.extend_from_slice(b"2020-01-01T00:00:00Z");
        write_at(&mut mso, VALID_FROM_OFFSET, &valid_from);
        let mut valid_until = VALID_UNTIL_ANCHOR.to_vec();
        valid_until.extend_from_slice(b"2030-12-31T23:59:59Z");
        write_at(&mut mso, VALID_UNTIL_OFFSET, &valid_until);

        let anchor = payload_anchor(spec.mso_len);
        let mut issuer_message = vec![0xaa; spec.issuer_message_len];
        write_at(&mut issuer_message, PAYLOAD_OFFSET, &anchor);
        write_at(&mut issuer_message, PAYLOAD_OFFSET + anchor.len(), &mso);
        (spec, issuer_message, mso)
    }

    fn test_parts(with_sha: bool) -> (MdocPrivateMsoBindSpec, Vec<u8>, Vec<u8>) {
        test_parts_for_spec(test_spec(with_sha))
    }

    fn test_witness(
        spec: &MdocPrivateMsoBindSpec,
        issuer_message: Vec<u8>,
        mso: &[u8],
    ) -> MdocPrivateMsoBindWitness {
        MdocPrivateMsoBindWitness::from_canonical_issuer_message(
            spec,
            issuer_message,
            mso,
            MdocPrivateMsoVersion::V1,
        )
        .unwrap()
    }

    fn test_binder(
        with_sha: bool,
        with_mso_start: bool,
    ) -> (MdocPrivateMsoBind, MdocPrivateMsoUseCensus) {
        let (spec, issuer_message, mso) = test_parts(with_sha);
        let witness = test_witness(&spec, issuer_message, &mso);
        MdocPrivateMsoBind::prover(
            spec,
            witness,
            SharedFieldRelation::new(),
            with_sha.then(SharedFieldRelation::new),
            with_mso_start.then(SharedMdocMsoStartRelation::new),
        )
        .unwrap()
    }

    fn logical_value(column: &MdocPrivateMsoColumnEval, index: usize) -> M31 {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(index, MDOC_PRIVATE_MSO_BIND_LOG_SIZE),
            MDOC_PRIVATE_MSO_BIND_LOG_SIZE,
        );
        column.values.at(row)
    }

    #[derive(Clone, Copy)]
    struct TestCounterRow {
        issuer: u32,
        sha: u32,
        start: u32,
        field_id: u32,
        index: u32,
        byte: u32,
    }

    impl TestCounterRow {
        fn issuer(index: usize, byte: u8) -> Self {
            Self {
                issuer: 1,
                sha: 0,
                start: 0,
                field_id: HOSTED_MSG_FIELD_ID,
                index: index as u32,
                byte: u32::from(byte),
            }
        }

        fn sha(field_id: u32, index: usize, byte: u8) -> Self {
            Self {
                issuer: 0,
                sha: 1,
                start: 0,
                field_id,
                index: index as u32,
                byte: u32::from(byte),
            }
        }

        fn start(index: usize, is_v2: bool, active: bool) -> Self {
            Self {
                issuer: 0,
                sha: 0,
                start: u32::from(active),
                field_id: 0,
                index: index as u32,
                byte: u32::from(is_v2),
            }
        }
    }

    const TEST_COUNTER_COLS: usize = 6;
    const TEST_ISSUER: usize = 0;
    const TEST_SHA: usize = 1;
    const TEST_START: usize = 2;
    const TEST_FIELD_ID: usize = 3;
    const TEST_INDEX: usize = 4;
    const TEST_BYTE: usize = 5;

    fn test_counter_log_size(rows: usize) -> u32 {
        rows.next_power_of_two().ilog2().max(LOG_N_LANES)
    }

    fn test_counter_columns(rows: &[TestCounterRow], log_size: u32) -> Vec<Vec<M31>> {
        let mut columns = vec![vec![m31_u32(0); 1usize << log_size]; TEST_COUNTER_COLS];
        for (index, row) in rows.iter().enumerate() {
            for (column, value) in [
                row.issuer,
                row.sha,
                row.start,
                row.field_id,
                row.index,
                row.byte,
            ]
            .into_iter()
            .enumerate()
            {
                columns[column][index] = m31_u32(value);
            }
        }
        columns
    }

    fn test_counter_evals(rows: &[TestCounterRow], log_size: u32) -> Vec<MdocPrivateMsoColumnEval> {
        test_counter_columns(rows, log_size)
            .into_iter()
            .map(|values| {
                CircleEvaluation::new(
                    CanonicCoset::new(log_size).circle_domain(),
                    BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, values)),
                )
            })
            .collect()
    }

    #[derive(Clone)]
    struct TestCounterEval {
        log_size: u32,
        issuer: FieldBytesRelation,
        sha: FieldBytesRelation,
        start: MdocMsoStartRelation,
    }

    impl FrameworkEval for TestCounterEval {
        fn log_size(&self) -> u32 {
            self.log_size
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            self.log_size + 2
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let issuer = eval.next_trace_mask();
            let sha = eval.next_trace_mask();
            let start = eval.next_trace_mask();
            let field_id = eval.next_trace_mask();
            let index = eval.next_trace_mask();
            let byte = eval.next_trace_mask();
            let one = E::F::from(m31_u32(1));
            for selector in [&issuer, &sha, &start] {
                eval.add_constraint(selector.clone() * (one.clone() - selector.clone()));
            }
            eval.add_to_relation(RelationEntry::new(
                &self.issuer,
                -E::EF::from(issuer),
                &[field_id.clone(), index.clone(), byte.clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.sha,
                -E::EF::from(sha),
                &[field_id, index.clone(), byte.clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.start,
                E::EF::from(start),
                &[index, byte],
            ));
            eval.finalize_logup_in_pairs();
            eval
        }
    }

    fn test_counter_interaction(
        rows: &[TestCounterRow],
        log_size: u32,
        issuer_relation: &FieldBytesRelation,
        sha_relation: &FieldBytesRelation,
        start_relation: &MdocMsoStartRelation,
    ) -> (Vec<MdocPrivateMsoColumnEval>, QM31) {
        let trace = test_counter_evals(rows, log_size);
        let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
        let mut logup = LogupTraceGenerator::new(log_size);
        logup.col_from_fn(|vec_row| {
            let tuple: [PackedM31; 3] = [
                trace[TEST_FIELD_ID].data[vec_row],
                trace[TEST_INDEX].data[vec_row],
                trace[TEST_BYTE].data[vec_row],
            ];
            let issuer_denominator: PackedQM31 = issuer_relation.combine(&tuple);
            let sha_denominator: PackedQM31 = sha_relation.combine(&tuple);
            let issuer_numerator = -PackedQM31::from(trace[TEST_ISSUER].data[vec_row]);
            let sha_numerator = -PackedQM31::from(trace[TEST_SHA].data[vec_row]);
            (
                issuer_numerator * sha_denominator + sha_numerator * issuer_denominator,
                issuer_denominator * sha_denominator,
            )
        });
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            (
                PackedQM31::from(trace[TEST_START].data[vec_row]),
                start_relation.combine(&[
                    trace[TEST_INDEX].data[vec_row],
                    trace[TEST_BYTE].data[vec_row],
                ]),
            )
        }));
        logup.finalize_last()
    }

    struct TestRelationCounter {
        rows: Vec<TestCounterRow>,
        log_size: u32,
        issuer_handle: SharedFieldRelation,
        sha_handle: SharedFieldRelation,
        start_handle: SharedMdocMsoStartRelation,
        component: Option<FrameworkComponent<TestCounterEval>>,
    }

    impl TestRelationCounter {
        fn new(
            rows: Vec<TestCounterRow>,
            issuer_handle: SharedFieldRelation,
            sha_handle: SharedFieldRelation,
            start_handle: SharedMdocMsoStartRelation,
        ) -> Self {
            Self {
                log_size: test_counter_log_size(rows.len()),
                rows,
                issuer_handle,
                sha_handle,
                start_handle,
                component: None,
            }
        }

        fn interaction(&self) -> (Vec<MdocPrivateMsoColumnEval>, QM31) {
            test_counter_interaction(
                &self.rows,
                self.log_size,
                &self.issuer_handle.get(),
                &self.sha_handle.get(),
                &self.start_handle.get(),
            )
        }
    }

    impl Air for TestRelationCounter {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            // Counter tuples model private provider witnesses. Only their fixed
            // shape is public; the tests mutate their proof claim after tree 1.
            channel.mix_u64(TEST_COUNTER_DOMAIN);
            channel.mix_u64(self.log_size as u64);
            channel.mix_u64(self.rows.len() as u64);
        }

        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            assert!(!self.issuer_handle.is_set());
            assert!(!self.sha_handle.is_set());
            self.issuer_handle.set(FieldBytesRelation::draw(channel));
            self.sha_handle.set(FieldBytesRelation::draw(channel));
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: Vec::new(),
                trace: vec![self.log_size; TEST_COUNTER_COLS],
                interaction: vec![self.log_size; 2 * SECURE_EXTENSION_DEGREE],
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
                    sha: self.sha_handle.get(),
                    start: self.start_handle.get(),
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
        fn for_row(shape: &PublicShape, trace: &MdocPrivateMsoTrace, row: usize) -> Self {
            let previous = if row == 0 {
                MDOC_PRIVATE_MSO_BIND_ROWS - 1
            } else {
                row - 1
            };
            let mut eval = Self::default();
            for column in preprocessed_columns(shape) {
                eval.preprocessed
                    .push_back(vec![logical_value(&column, row)]);
            }
            for (index, column) in trace.columns.iter().enumerate() {
                if matches!(
                    index,
                    TRACE_PAYLOAD_OFFSET | TRACE_WINDOW_OFFSET | TRACE_VERSION_SELECTOR
                ) {
                    eval.original.push_back(vec![column[row], column[previous]]);
                } else {
                    eval.original.push_back(vec![column[row]]);
                }
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

    fn test_eval(spec: &MdocPrivateMsoBindSpec, shape: &PublicShape) -> MdocPrivateMsoEval {
        MdocPrivateMsoEval {
            spec: spec.clone(),
            payload_anchor_len: shape.payload_anchor.len(),
            issuer_relation: FieldBytesRelation::dummy(),
            sha_relation: spec
                .sha_stream
                .as_ref()
                .map(|_| FieldBytesRelation::dummy()),
            mso_start_relation: Some(MdocMsoStartRelation::dummy()),
            blinder_relation: ClaimedSumBlinderRelation::dummy(),
            blinder_v: qm31(7),
            blinder_m: qm31(11),
        }
    }

    fn assert_row_satisfies(
        spec: &MdocPrivateMsoBindSpec,
        shape: &PublicShape,
        trace: &MdocPrivateMsoTrace,
        row: usize,
    ) {
        let evaluated = test_eval(spec, shape).evaluate(RowEval::for_row(shape, trace, row));
        let nonzero = evaluated.nonzero_constraints();
        assert!(
            nonzero.is_empty(),
            "row {row} violates constraints: {nonzero:?}"
        );
    }

    fn assert_row_rejects(
        spec: &MdocPrivateMsoBindSpec,
        shape: &PublicShape,
        trace: &MdocPrivateMsoTrace,
        row: usize,
    ) {
        let evaluated = test_eval(spec, shape).evaluate(RowEval::for_row(shape, trace, row));
        assert!(
            !evaluated.nonzero_constraints().is_empty(),
            "mutated row {row} unexpectedly satisfies the AIR"
        );
    }

    struct TestComposedMsoProof {
        stark: stwo::core::proof::StarkProof<air_core::Hasher>,
        bind_claim: MdocPrivateMsoInteractionClaim,
        spec: MdocPrivateMsoBindSpec,
        counter_rows: Vec<TestCounterRow>,
    }

    fn honest_counter_rows(
        spec: &MdocPrivateMsoBindSpec,
        issuer_message: &[u8],
        mso_start: usize,
        census: &MdocPrivateMsoUseCensus,
    ) -> Vec<TestCounterRow> {
        let sha = spec.sha_stream.as_ref().unwrap();
        let raw_mso = &issuer_message[mso_start..mso_start + spec.mso_len];
        let padded = padded_mso(raw_mso, sha.padded_len);
        census
            .issuer_position_uses
            .iter()
            .enumerate()
            .filter(|(_, uses)| **uses != 0)
            .flat_map(|(index, &uses)| {
                std::iter::repeat_n(
                    TestCounterRow::issuer(index, issuer_message[index]),
                    uses as usize,
                )
            })
            .chain(
                padded
                    .into_iter()
                    .enumerate()
                    .map(|(index, byte)| TestCounterRow::sha(sha.field_id, index, byte)),
            )
            .chain([
                TestCounterRow::start(mso_start, false, true),
                TestCounterRow::start(mso_start, false, false),
            ])
            .collect()
    }

    fn prove_composed_mso(config: stwo::core::pcs::PcsConfig) -> TestComposedMsoProof {
        let (spec, issuer_message, mso) = test_parts(true);
        let witness = test_witness(&spec, issuer_message.clone(), &mso);
        let mso_start = witness.payload_anchor_offset + payload_anchor(spec.mso_len).len();
        let issuer_handle = SharedFieldRelation::new();
        let sha_handle = SharedFieldRelation::new();
        let start_handle = SharedMdocMsoStartRelation::new();
        let (mut binder, census) = MdocPrivateMsoBind::prover(
            spec.clone(),
            witness,
            issuer_handle.clone(),
            Some(sha_handle.clone()),
            Some(start_handle.clone()),
        )
        .unwrap();
        let counter_rows = honest_counter_rows(&spec, &issuer_message, mso_start, &census);
        let mut counter = TestRelationCounter::new(
            counter_rows.clone(),
            issuer_handle,
            sha_handle,
            start_handle,
        );
        let stark = air_core::prove(&mut [&mut counter, &mut binder], config)
            .expect("honest private MSO relation composition proves");
        TestComposedMsoProof {
            stark,
            bind_claim: binder.interaction_claim().clone(),
            spec,
            counter_rows,
        }
    }

    fn verify_composed_mso(
        fixture: &TestComposedMsoProof,
        counter_rows: Vec<TestCounterRow>,
    ) -> Result<(), air_core::VerifyError> {
        let issuer_handle = SharedFieldRelation::new();
        let sha_handle = SharedFieldRelation::new();
        let start_handle = SharedMdocMsoStartRelation::new();
        let mut counter = TestRelationCounter::new(
            counter_rows,
            issuer_handle.clone(),
            sha_handle.clone(),
            start_handle.clone(),
        );
        let mut binder = MdocPrivateMsoBind::verifier(
            fixture.spec.clone(),
            issuer_handle,
            Some(sha_handle),
            Some(start_handle),
            fixture.bind_claim.clone(),
        )
        .unwrap();
        air_core::verify_with_expected_preprocessed_root(
            &mut [&mut counter, &mut binder],
            &fixture.stark,
            None,
        )
    }

    fn assert_counter_mutation_rejects(
        fixture: &TestComposedMsoProof,
        name: &str,
        mutate: impl FnOnce(&mut [TestCounterRow]),
    ) {
        let mut rows = fixture.counter_rows.clone();
        mutate(&mut rows);
        match verify_composed_mso(fixture, rows)
            .expect_err("mutated relation counterpart must not verify")
        {
            air_core::VerifyError::Stark(VerificationError::InvalidStructure(reason)) => {
                assert_eq!(reason, "LogUp claimed sums do not cancel", "{name}")
            }
            other => panic!("{name}: expected global LogUp rejection, got {other:?}"),
        }
    }

    #[test]
    fn composed_proof_rejects_every_private_mso_relation_seam_mutation() {
        let fixture = prove_composed_mso(crate::mdoc::mdoc_production_pcs_config());
        verify_composed_mso(&fixture, fixture.counter_rows.clone())
            .expect("full-profile private MSO relation composition must verify");

        assert_counter_mutation_rejects(&fixture, "shifted payload anchor", |rows| {
            rows.iter_mut()
                .find(|row| row.issuer == 1 && row.index == PAYLOAD_OFFSET as u32)
                .unwrap()
                .index += 1;
        });
        assert_counter_mutation_rejects(&fixture, "shifted mso_start", |rows| {
            rows.iter_mut().find(|row| row.start == 1).unwrap().index += 1;
        });
        assert_counter_mutation_rejects(&fixture, "mso_start version bit", |rows| {
            rows.iter_mut().find(|row| row.start == 1).unwrap().byte ^= 1;
        });
        assert_counter_mutation_rejects(&fixture, "raw MSO mirror byte", |rows| {
            rows.iter_mut()
                .find(|row| row.sha == 1 && row.index == 123)
                .unwrap()
                .byte ^= 1;
        });
        for (name, index) in [
            ("SHA padding marker", fixture.spec.mso_len),
            ("SHA padding zero", fixture.spec.mso_len + 1),
            (
                "SHA padding bit length",
                fixture.spec.sha_stream.as_ref().unwrap().padded_len - 1,
            ),
        ] {
            assert_counter_mutation_rejects(&fixture, name, |rows| {
                rows.iter_mut()
                    .find(|row| row.sha == 1 && row.index == index as u32)
                    .unwrap()
                    .byte ^= 1;
            });
        }
        assert_counter_mutation_rejects(&fixture, "missing mso_start use", |rows| {
            rows.iter_mut().find(|row| row.start == 1).unwrap().start = 0;
        });
        let mso_start = PAYLOAD_OFFSET + payload_anchor(fixture.spec.mso_len).len();
        assert_counter_mutation_rejects(&fixture, "extra mso_start use", |rows| {
            rows.iter_mut()
                .rev()
                .find(|row| row.field_id == 0 && row.index as usize == mso_start)
                .unwrap()
                .start = 1;
        });
    }

    #[test]
    fn minimum_blowup_proves_the_linearized_mso_degree_bound() {
        let fixture = prove_composed_mso(stwo::core::pcs::PcsConfig::default());
        verify_composed_mso(&fixture, fixture.counter_rows.clone())
            .expect("coefficient-backed minimum-blowup MSO proof must verify");
    }

    #[test]
    fn canonical_constructor_derives_unique_offsets_and_rejects_ambiguity() {
        let (spec, mut issuer_message, mut mso) = test_parts(true);
        let witness = test_witness(&spec, issuer_message.clone(), &mso);
        assert_eq!(witness.payload_anchor_offset, PAYLOAD_OFFSET);
        assert_eq!(
            witness.mso_start(spec.mso_len).unwrap(),
            PAYLOAD_OFFSET + payload_anchor(spec.mso_len).len()
        );
        assert_eq!(witness.version_offset, VERSION_OFFSET);
        assert_eq!(witness.digest_algorithm_offset, ALGORITHM_OFFSET);
        assert_eq!(witness.doc_type_offset, DOC_TYPE_OFFSET);
        assert_eq!(witness.device_key_info_offset, DEVICE_KEY_OFFSET);
        assert_eq!(witness.valid_from_offset, VALID_FROM_OFFSET);
        assert_eq!(witness.valid_until_offset, VALID_UNTIL_OFFSET);

        let mut anchored = payload_anchor(spec.mso_len);
        anchored.extend_from_slice(&mso);
        assert_eq!(
            issuer_message
                .windows(anchored.len())
                .filter(|window| *window == anchored)
                .count(),
            1,
            "honest fixture must have exactly one payload anchor occurrence"
        );

        let mut duplicate_version = VERSION_PREFIX.to_vec();
        duplicate_version.extend_from_slice(b"1.0");
        write_at(&mut mso, 3_000, &duplicate_version);
        write_at(
            &mut issuer_message,
            PAYLOAD_OFFSET + payload_anchor(spec.mso_len).len(),
            &mso,
        );
        assert_eq!(
            MdocPrivateMsoBindWitness::from_canonical_issuer_message(
                &spec,
                issuer_message,
                &mso,
                MdocPrivateMsoVersion::V1,
            )
            .unwrap_err(),
            MdocPrivateMsoBindError::CanonicalAnchorAmbiguous {
                anchor: "MSO version"
            }
        );
    }

    #[test]
    fn fixed_log9_full_profile_census_is_exact() {
        let (binder, census) = test_binder(true, true);
        assert_eq!(PREPROCESSED_COLS, 204);
        assert_eq!(TRACE_COLS, 203);
        assert_eq!(DEVICE_KEY_INFO_CHUNKS, 63);
        assert_eq!(binder.active_rows(), 201);
        assert_eq!(census.active_rows, 201);
        assert_eq!(census.blind_rows, 311);
        assert_eq!(census.issuer_uses_total, 6_220);
        assert_eq!(census.sha_stream_uses, 4_160);
        assert_eq!(census.mso_start_uses, 1);
        assert_eq!(
            census
                .issuer_position_uses
                .iter()
                .map(|&count| count as usize)
                .sum::<usize>(),
            census.issuer_uses_total
        );
        assert_eq!(census.issuer_position_uses[PAYLOAD_OFFSET], 1);
        assert!(
            census.issuer_position_uses[PAYLOAD_OFFSET + payload_anchor(4_096).len() + 3_000] >= 1
        );

        let (without_sha, census) = test_binder(false, false);
        assert_eq!(without_sha.active_rows(), 71);
        assert_eq!(census.blind_rows, 441);
        assert_eq!(census.issuer_uses_total, 2_124);
        assert_eq!(census.sha_stream_uses, 0);
        assert_eq!(census.mso_start_uses, 0);
    }

    #[test]
    fn precise_public_shape_and_private_offset_errors_reject_before_trace_allocation() {
        let mut spec = test_spec(true);
        spec.issuer_message_len = crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES + 1;
        assert!(matches!(
            validate_spec(&spec, true),
            Err(MdocPrivateMsoBindError::IssuerMessageTooLong { .. })
        ));

        let mut spec = test_spec(true);
        spec.device_public_key.pop();
        assert!(matches!(
            validate_spec(&spec, true),
            Err(MdocPrivateMsoBindError::DevicePublicKeyLength { .. })
        ));

        let mut spec = test_spec(true);
        spec.sha_stream.as_mut().unwrap().padded_len -= 64;
        assert!(matches!(
            validate_spec(&spec, true),
            Err(MdocPrivateMsoBindError::ShaPaddedLengthMismatch { .. })
        ));
        assert!(matches!(
            validate_spec(&test_spec(true), false),
            Err(MdocPrivateMsoBindError::ShaStreamHandleMismatch { .. })
        ));

        let mut spec = test_spec(true);
        spec.doc_type = "x".repeat(MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES + 1);
        assert!(matches!(
            validate_spec(&spec, true),
            Err(MdocPrivateMsoBindError::DocTypeTooLong { .. })
        ));

        let (spec, issuer_message, mso) = test_parts(true);
        let mut witness = test_witness(&spec, issuer_message, &mso);
        witness.version_offset = spec.mso_len - 1;
        let shape = validate_spec(&spec, true).unwrap();
        assert!(matches!(
            private_trace(&spec, &shape, &witness, false),
            Err(MdocPrivateMsoBindError::WindowOutOfBounds {
                window: "MSO version",
                ..
            })
        ));
    }

    #[test]
    fn issuer_absolute_index_stays_linear() {
        const CONSTANT: PolynomialDegree = PolynomialDegree(0);
        const COLUMN: PolynomialDegree = PolynomialDegree(1);
        assert_eq!(
            issuer_absolute_index(COLUMN, COLUMN, CONSTANT, COLUMN, CONSTANT, COLUMN),
            COLUMN,
            "pairing two issuer denominators must remain cubic, not quintic"
        );
    }

    #[test]
    fn all_honest_active_and_inactive_rows_satisfy_constraints_and_cubic_logup_bound() {
        let (binder, _) = test_binder(true, true);
        let trace = binder.trace.as_ref().unwrap();
        let anchor_row = binder
            .shape
            .rows
            .iter()
            .position(|row| row.kind == WindowKind::PayloadAnchor)
            .unwrap();
        assert_eq!(
            trace.columns[TRACE_WINDOW_OFFSET][anchor_row],
            m31_u32(0),
            "the active non-MSO row must keep the linear issuer index exact"
        );
        for row in 0..binder.active_rows() {
            assert_row_satisfies(&binder.spec, &binder.shape, trace, row);
        }
        assert_row_satisfies(&binder.spec, &binder.shape, trace, binder.active_rows());
        let eval = test_eval(&binder.spec, &binder.shape);
        assert_eq!(
            FrameworkEval::max_constraint_log_degree_bound(&eval),
            MDOC_PRIVATE_MSO_BIND_LOG_SIZE + 2
        );
        assert_eq!(
            AirProver::max_constraint_log_degree_bound(&binder),
            MDOC_PRIVATE_MSO_BIND_LOG_SIZE + 2
        );
        assert!(binder.store_polynomial_coefficients());
    }

    #[test]
    fn anchor_offsets_profile_constants_device_key_tdates_and_padding_mutations_reject() {
        let (binder, _) = test_binder(true, true);
        let honest = binder.trace.as_ref().unwrap();
        let anchor_row = binder
            .shape
            .rows
            .iter()
            .position(|row| row.kind == WindowKind::PayloadAnchor)
            .unwrap();

        let mut anchor_window_offset = honest.clone();
        anchor_window_offset.columns[TRACE_WINDOW_OFFSET][anchor_row] += m31_u32(1);
        assert_row_rejects(
            &binder.spec,
            &binder.shape,
            &anchor_window_offset,
            anchor_row,
        );

        let mut anchor = honest.clone();
        anchor.columns[TRACE_BYTE_START][0] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &anchor, 0);

        let mut payload_bits = honest.clone();
        payload_bits.columns[TRACE_PAYLOAD_OFFSET_BITS][0] =
            m31_u32(1) - payload_bits.columns[TRACE_PAYLOAD_OFFSET_BITS][0];
        assert_row_rejects(&binder.spec, &binder.shape, &payload_bits, 0);

        let mut shifted_window = honest.clone();
        shifted_window.columns[TRACE_WINDOW_OFFSET][2] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &shifted_window, 2);

        let mut version = honest.clone();
        version.columns[TRACE_BYTE_START + VERSION_PREFIX.len()][1] = m31_u32(b'9' as u32);
        assert_row_rejects(&binder.spec, &binder.shape, &version, 1);

        let mut algorithm = honest.clone();
        algorithm.columns[TRACE_BYTE_START][2] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &algorithm, 2);

        let mut doc_type = honest.clone();
        doc_type.columns[TRACE_BYTE_START + DOC_TYPE_KEY.len() + 1][3] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &doc_type, 3);

        let device_first_row = 4;
        let mut device = honest.clone();
        device.columns[TRACE_BYTE_START][device_first_row] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &device, device_first_row);

        let mut device_public_key = honest.clone();
        device_public_key.columns[TRACE_BYTE_START + 3][device_first_row + 1] += m31_u32(1);
        assert_row_rejects(
            &binder.spec,
            &binder.shape,
            &device_public_key,
            device_first_row + 1,
        );

        let valid_from_date_row = 68;
        let mut bad_time = honest.clone();
        bad_time.columns[TRACE_BYTE_START + 11][valid_from_date_row] = m31_u32(b'2' as u32);
        bad_time.columns[TRACE_BYTE_START + 12][valid_from_date_row] = m31_u32(b'4' as u32);
        assert_row_rejects(&binder.spec, &binder.shape, &bad_time, valid_from_date_row);

        let padding_marker_row = 199;
        let mut padding = honest.clone();
        padding.columns[TRACE_BYTE_START][padding_marker_row] = m31_u32(0);
        assert_row_rejects(&binder.spec, &binder.shape, &padding, padding_marker_row);
    }

    #[test]
    fn relation_claim_changes_for_raw_byte_and_fully_shifted_payload_mutations() {
        let (binder, _) = test_binder(true, true);
        let mut channel = Blake2sChannel::default();
        let issuer = FieldBytesRelation::draw(&mut channel);
        let sha = FieldBytesRelation::draw(&mut channel);
        let start = MdocMsoStartRelation::draw(&mut channel);
        let blinder = ClaimedSumBlinderRelation::draw(&mut channel);
        let v = qm31(17);
        let m = qm31(19);
        let claim = |trace: &MdocPrivateMsoTrace| {
            private_mso_interaction_trace(
                &binder.spec,
                &binder.shape,
                trace,
                MdocPrivateMsoInteractionInputs {
                    issuer_relation: &issuer,
                    sha_relation: Some(&sha),
                    mso_start_relation: Some(&start),
                    blinder_relation: &blinder,
                    blinder_v: v,
                    blinder_m: m,
                },
            )
            .1
        };
        let honest = binder.trace.as_ref().unwrap();
        let honest_claim = claim(honest);

        let mut raw = honest.clone();
        raw.columns[TRACE_BYTE_START + 7][71] += m31_u32(1);
        assert_ne!(claim(&raw), honest_claim);

        let mut shifted = honest.clone();
        for row in 0..binder.active_rows() {
            shifted.columns[TRACE_PAYLOAD_OFFSET][row] += m31_u32(1);
            let offset = (logical_u32(&shifted.columns[TRACE_PAYLOAD_OFFSET][row]) as usize)
                & ((1 << OFFSET_BITS) - 1);
            write_bits(
                &mut shifted.columns,
                TRACE_PAYLOAD_OFFSET_BITS,
                row,
                offset,
                OFFSET_BITS,
            );
            shifted.columns[TRACE_PAYLOAD_SLACK][row] -= m31_u32(1);
            let slack = logical_u32(&shifted.columns[TRACE_PAYLOAD_SLACK][row]) as usize;
            write_bits(
                &mut shifted.columns,
                TRACE_PAYLOAD_SLACK_BITS,
                row,
                slack,
                OFFSET_BITS,
            );
        }
        assert_ne!(claim(&shifted), honest_claim);
    }

    fn logical_u32(value: &M31) -> u32 {
        value.0
    }

    #[test]
    fn private_content_does_not_change_preprocessing_or_public_mixing() {
        let (spec, issuer_message, mso) = test_parts(true);
        let first_witness = test_witness(&spec, issuer_message.clone(), &mso);
        let mut changed_message = issuer_message;
        let mut changed_mso = mso;
        let mso_start = PAYLOAD_OFFSET + payload_anchor(spec.mso_len).len();
        changed_message[mso_start + 3_500] ^= 1;
        changed_mso[3_500] ^= 1;
        let second_witness = test_witness(&spec, changed_message, &changed_mso);
        let (mut first, _) = MdocPrivateMsoBind::prover(
            spec.clone(),
            first_witness,
            SharedFieldRelation::new(),
            Some(SharedFieldRelation::new()),
            None,
        )
        .unwrap();
        let (mut second, _) = MdocPrivateMsoBind::prover(
            spec,
            second_witness,
            SharedFieldRelation::new(),
            Some(SharedFieldRelation::new()),
            None,
        )
        .unwrap();
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
            FieldBytesRelation::draw(&mut second_channel)
        );
        assert_ne!(
            first.trace.as_ref().unwrap().columns,
            second.trace.as_ref().unwrap().columns
        );
    }

    #[test]
    fn same_shape_public_content_does_not_change_tree_zero_material() {
        let (first_spec, first_message, first_mso) = test_parts(true);
        let mut second_spec = first_spec.clone();
        second_spec.doc_type = "a".repeat(first_spec.doc_type.len());
        second_spec.device_public_key = vec![0x3c; stwo_mldsa::constants::PK_BYTES];
        let (second_spec, mut second_message, mut second_mso) = test_parts_for_spec(second_spec);
        let second_mso_start = PAYLOAD_OFFSET + payload_anchor(second_spec.mso_len).len();
        second_mso[3_500] ^= 1;
        second_message[second_mso_start + 3_500] = second_mso[3_500];

        let first_witness = test_witness(&first_spec, first_message, &first_mso);
        let second_witness = test_witness(&second_spec, second_message, &second_mso);
        let (mut first, _) = MdocPrivateMsoBind::prover(
            first_spec,
            first_witness,
            SharedFieldRelation::new(),
            Some(SharedFieldRelation::new()),
            None,
        )
        .unwrap();
        let (mut second, _) = MdocPrivateMsoBind::prover(
            second_spec,
            second_witness,
            SharedFieldRelation::new(),
            Some(SharedFieldRelation::new()),
            None,
        )
        .unwrap();

        assert_eq!(
            first.preprocessed_column_ids(),
            second.preprocessed_column_ids()
        );
        assert_eq!(
            first.preprocessed_column_fingerprints(),
            second.preprocessed_column_fingerprints(),
            "tree-zero fingerprints must depend on shape, never public credential content"
        );
        let first_root = air_core::compute_preprocessed_root_uncached(
            &mut [&mut first],
            stwo::core::pcs::PcsConfig::default(),
        );
        let second_root = air_core::compute_preprocessed_root_uncached(
            &mut [&mut second],
            stwo::core::pcs::PcsConfig::default(),
        );
        assert_eq!(
            first_root, second_root,
            "same-shape credentials must produce byte-identical tree-zero root material"
        );

        let mut first_channel = Blake2sChannel::default();
        let mut second_channel = Blake2sChannel::default();
        first.mix_public(&mut first_channel);
        second.mix_public(&mut second_channel);
        assert_ne!(
            FieldBytesRelation::draw(&mut first_channel),
            FieldBytesRelation::draw(&mut second_channel),
            "Eval constants remain transcript-bound even though tree zero is reusable"
        );
    }

    #[test]
    fn inactive_bits_and_digits_are_fresh_and_globally_valid() {
        let (first, _) = test_binder(true, false);
        let (second, _) = test_binder(true, false);
        let first = first.trace.as_ref().unwrap();
        let second = second.trace.as_ref().unwrap();
        let inactive = 201;
        assert_ne!(
            first
                .columns
                .iter()
                .map(|column| column[inactive])
                .collect::<Vec<_>>(),
            second
                .columns
                .iter()
                .map(|column| column[inactive])
                .collect::<Vec<_>>()
        );
        for row in inactive..MDOC_PRIVATE_MSO_BIND_ROWS {
            for start in [
                TRACE_PAYLOAD_OFFSET_BITS,
                TRACE_PAYLOAD_SLACK_BITS,
                TRACE_WINDOW_OFFSET_BITS,
                TRACE_WINDOW_SLACK_BITS,
                TRACE_DATE_SLACK_BITS,
                TRACE_RANGE_BITS,
            ] {
                let count = match start {
                    TRACE_DATE_SLACK_BITS => DATE_SLACK_BITS,
                    TRACE_RANGE_BITS => RANGE_BITS,
                    _ => OFFSET_BITS,
                };
                assert!(first.columns[start..start + count]
                    .iter()
                    .all(|column| matches!(column[row].0, 0 | 1)));
            }
            for digit in 0..TDATE_DIGITS {
                let value = (0..DIGIT_BITS)
                    .map(|bit| {
                        (first.columns[TRACE_DIGIT_BITS + digit * DIGIT_BITS + bit][row].0 as usize)
                            << bit
                    })
                    .sum::<usize>();
                assert!(value <= 9);
            }
        }
    }

    #[test]
    fn layout_claim_shape_site_order_and_component_order_are_fixed() {
        let spec = test_spec(true);
        let issuer_handle = SharedFieldRelation::new();
        let sha_handle = SharedFieldRelation::new();
        let start_handle = SharedMdocMsoStartRelation::new();
        let mut channel = Blake2sChannel::default();
        issuer_handle.set(FieldBytesRelation::draw(&mut channel));
        sha_handle.set(FieldBytesRelation::draw(&mut channel));
        let claim = test_claim();
        let encoded = bincode::serialize(&claim).unwrap();
        let decoded: MdocPrivateMsoInteractionClaim = bincode::deserialize(&encoded).unwrap();
        assert_eq!(decoded, claim);

        let mut verifier = MdocPrivateMsoBind::verifier(
            spec,
            issuer_handle,
            Some(sha_handle),
            Some(start_handle.clone()),
            decoded,
        )
        .unwrap();
        assert_eq!(verifier.n_main_sites(), 66);
        assert_eq!(
            verifier.layout().preprocessed,
            vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; PREPROCESSED_COLS]
        );
        assert_eq!(
            verifier.layout().trace,
            vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; TRACE_COLS]
        );
        assert_eq!(
            verifier.layout().interaction,
            vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; 34 * SECURE_EXTENSION_DEGREE]
        );
        assert_eq!(verifier.claimed_sums(), vec![qm31(1), qm31(4)]);

        verifier.draw_relations(&mut channel);
        assert!(start_handle.is_set());
        let ids = verifier.preprocessed_column_ids();
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(ids.as_slice());
        verifier.build_components(&mut allocator);
        assert_eq!(
            verifier.components().len(),
            2,
            "main binder must be followed immediately by its blinder counterpart"
        );
    }
}
