//! Private canonical `valueDigests` scanner for the TS13 identity proof.
//!
//! ## Guarantees
//!
//! The scanner consumes canonical bytes from the private issuer message.
//! It proves that the requested namespace occurs exactly once.
//! It binds each selected digest ID and SHA-256 digest.
//! It does not add either value to the clear public inputs.
//! Extra canonical namespaces remain accepted.
//!
//! ## Relation polarity
//!
//! | relation | provider | sign | consumer | sign |
//! |---|---|---:|---|---:|
//! | issuer hosted message | private-message provider | `-` | this scanner | `+` |
//! | MSO start | private-MSO binder | `-` | this scanner | `+` |
//! | private digest ID | private item binder | `-` | this scanner | `+` |
//! | item SHA digest | SHA-256 AIR | `-` | this scanner | `+` |
//! | raw/sorted `(namespace,id)` | this scanner | `+` | this scanner | `-` |

use std::collections::HashSet;
use std::fmt;

use air_core::relations::{
    DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
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
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};
use crate::mdoc_private_item_bind::{
    MdocPrivateDigestIdRelation, SharedMdocPrivateDigestIdRelation, MDOC_PRIVATE_ITEM_DIGEST_ID_MAX,
};
use crate::mdoc_private_mso_bind::{MdocMsoStartRelation, SharedMdocMsoStartRelation};
use crate::randomness::{random_bit, random_m31};

pub(crate) const MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_VALUE_DIGESTS_SCAN_ROWS: usize = 1usize << MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE;
pub(crate) const MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS: usize = 255;
pub(crate) const MDOC_MAX_PUBLIC_NAMESPACE_BYTES: usize = 32;

const SCAN_VERSION: u64 = 1;
const SCAN_DOMAIN: u64 = 0x4d44_4f43_5644_5343; // "MDOCVDSC"
const SCAN_TRANSCRIPT_TAG: u64 = 1;
const TS13_SELECTED_ATTRIBUTE_COUNT: usize = 1;
const DIGEST_ID_ENCODING_BYTES: usize = 3;
const DIGEST_BSTR_HEAD_END: usize = DIGEST_ID_ENCODING_BYTES + 1;
const DIGEST_BYTES_START: usize = DIGEST_ID_ENCODING_BYTES + 2;
const BYTE_SITES: usize = DIGEST_BYTES_START + 32;
const NAMESPACE_BYTE_SITES: usize = 32;
const COUNT_BITS: usize = 8;
const OFFSET_BITS: usize = 13;
const ROW_LEN_BITS: usize = 6;
const NAMESPACE_LEN_BITS: usize = 6;
const MAP_SLACK_BITS: usize = 8;
const DIGEST_CANONICAL_SLACK_BITS: usize = 8;
const SORTED_DIFF_BITS: usize = 16;
const NAMESPACE_PACK_BYTES: usize = 3;
const NAMESPACE_PACKS: usize = MDOC_MAX_PUBLIC_NAMESPACE_BYTES.div_ceil(NAMESPACE_PACK_BYTES);
const NAMESPACE_MISMATCHES: usize = 1 + NAMESPACE_PACKS;
pub(crate) const MDOC_VALUE_DIGESTS_SCAN_PREPROCESSED_COLS: usize = 4;
pub(crate) const MDOC_VALUE_DIGESTS_SCAN_TRACE_COLS: usize = 305;
pub(crate) const MDOC_VALUE_DIGESTS_SCAN_RELATION_SITES: usize = BYTE_SITES
    + 1 // MSO start handoff
    + 2 // raw/sorted private ID multiset
    + 1 // private item digest ID
    + 1 // SHA digest
    + 1; // claimed-sum blinder
/// Degree-recounted safe at +2: every numerator among the RELATION_SITES fractions is
/// degree <=1, so batch-4 folding over degree-1 denominators tops out at D5.
const LOGUP_BATCH: usize = 4;
pub(crate) const MDOC_VALUE_DIGESTS_SCAN_INTERACTION_COLS: usize =
    (MDOC_VALUE_DIGESTS_SCAN_RELATION_SITES.div_ceil(LOGUP_BATCH) + 1) * SECURE_EXTENSION_DEGREE;
const PREPROCESSED_COLS: usize = MDOC_VALUE_DIGESTS_SCAN_PREPROCESSED_COLS;
const TRACE_COLS: usize = MDOC_VALUE_DIGESTS_SCAN_TRACE_COLS;
const MAIN_RELATION_SITES: usize = MDOC_VALUE_DIGESTS_SCAN_RELATION_SITES;
const INTERACTION_COLS: usize = MDOC_VALUE_DIGESTS_SCAN_INTERACTION_COLS;
const VALUE_DIGESTS_KEY: &[u8] = b"\x6cvalueDigests";
relation!(MdocValueDigestIdMultisetRelation, 3);

type Column = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type ScanComponent = FrameworkComponent<MdocValueDigestsScanEval>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocValueDigestsScanSpec {
    pub(crate) issuer_message_len: usize,
    pub(crate) mso_len: usize,
    pub(crate) namespace: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocSelectedValueDigest {
    pub(crate) digest_id: u32,
    pub(crate) digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub(crate) struct MdocValueDigestsScanWitness {
    pub(crate) issuer_message: Vec<u8>,
    pub(crate) mso_start: usize,
    pub(crate) selected_digest: MdocSelectedValueDigest,
}

#[derive(Clone)]
pub(crate) struct MdocValueDigestItemHandles {
    pub(crate) digest_id: SharedMdocPrivateDigestIdRelation,
    pub(crate) digest: SharedDigestRelation,
}

#[derive(Clone)]
pub(crate) struct MdocValueDigestsScanHandles {
    pub(crate) issuer_message: SharedFieldRelation,
    pub(crate) mso_start: SharedMdocMsoStartRelation,
    pub(crate) item: MdocValueDigestItemHandles,
}

/// Why one MSO `valueDigests` map is not canonical.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MsoValueDigestsCanonicalityReason {
    /// The `valueDigests` key is missing.
    MissingValueDigests,
    /// The `valueDigests` key occurs more than once.
    AmbiguousValueDigests,
    /// A token ends before its declared length.
    Truncated(&'static str),
    /// The map is not a minimally encoded definite map.
    ExpectedDefiniteMap,
    /// A namespace key is not a minimally encoded definite text string.
    ExpectedDefiniteText,
    /// A namespace key is not valid UTF-8.
    InvalidUtf8,
    /// A namespace exceeds the length cap.
    NamespaceTooLong {
        /// The observed namespace length in bytes.
        length: usize,
        /// The maximum namespace length in bytes.
        max: usize,
    },
    /// A namespace occurs more than once.
    DuplicateNamespace,
    /// A digest ID is not a minimally encoded canonical integer.
    ExpectedCanonicalDigestId,
    /// A digest ID exceeds the maximum.
    DigestIdOutOfRange {
        /// The decoded digest ID value.
        value: u64,
        /// The maximum digest ID value.
        max: u32,
    },
    /// A digest is not a canonical 32-byte string.
    ExpectedDigestBstr32,
    /// A digest ID occurs more than once in one namespace.
    DuplicateDigestId,
}

impl fmt::Display for MsoValueDigestsCanonicalityReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingValueDigests => write!(f, "valueDigests key is missing"),
            Self::AmbiguousValueDigests => write!(f, "valueDigests key occurs more than once"),
            Self::Truncated(token) => write!(f, "truncated {token}"),
            Self::ExpectedDefiniteMap => write!(f, "expected a minimally encoded definite map"),
            Self::ExpectedDefiniteText => {
                write!(f, "expected a minimally encoded definite text key")
            }
            Self::InvalidUtf8 => write!(f, "namespace key is not valid UTF-8"),
            Self::NamespaceTooLong { length, max } => {
                write!(f, "namespace has {length} bytes; maximum is {max}")
            }
            Self::DuplicateNamespace => write!(f, "duplicate valueDigests namespace"),
            Self::ExpectedCanonicalDigestId => {
                write!(f, "expected a minimally encoded canonical digest ID")
            }
            Self::DigestIdOutOfRange { value, max } => {
                write!(f, "digest ID {value} exceeds maximum {max}")
            }
            Self::ExpectedDigestBstr32 => write!(f, "expected canonical bstr(32) digest"),
            Self::DuplicateDigestId => write!(f, "duplicate digest ID in namespace"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocValueDigestsScanError {
    EmptyIssuerMessage,
    IssuerMessageTooLong {
        length: usize,
        max: usize,
    },
    IssuerMessageLengthMismatch {
        expected: usize,
        actual: usize,
    },
    EmptyMso,
    MsoTooLong {
        length: usize,
        max: usize,
    },
    MsoOutOfBounds {
        start: usize,
        length: usize,
        issuer_message_len: usize,
    },
    EmptyPublicNamespace,
    PublicNamespaceTooLong {
        length: usize,
        max: usize,
    },
    ScanItemCapExceeded {
        items: usize,
        max: usize,
    },
    MsoValueDigestsNotCanonical {
        offset: usize,
        reason: MsoValueDigestsCanonicalityReason,
    },
    RequestedNamespaceMissing,
    RequestedNamespaceDuplicate,
    RequestedDigestMissing,
    IssuerUseCountOverflow {
        issuer_index: usize,
    },
}

impl fmt::Display for MdocValueDigestsScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyIssuerMessage => write!(f, "private issuer message is empty"),
            Self::IssuerMessageTooLong { length, max } => {
                write!(f, "private issuer message length {length} exceeds {max}")
            }
            Self::IssuerMessageLengthMismatch { expected, actual } => write!(
                f,
                "private issuer message length is {actual}, expected {expected}"
            ),
            Self::EmptyMso => write!(f, "private MSO is empty"),
            Self::MsoTooLong { length, max } => {
                write!(f, "private MSO length {length} exceeds {max}")
            }
            Self::MsoOutOfBounds {
                start,
                length,
                issuer_message_len,
            } => write!(
                f,
                "private MSO [{start}, {}) exceeds issuer message length {issuer_message_len}",
                start.saturating_add(*length)
            ),
            Self::EmptyPublicNamespace => write!(f, "public namespace is empty"),
            Self::PublicNamespaceTooLong { length, max } => {
                write!(f, "public namespace has {length} bytes; maximum is {max}")
            }
            Self::ScanItemCapExceeded { items, max } => {
                write!(f, "valueDigests scan has {items} items; maximum is {max}")
            }
            Self::MsoValueDigestsNotCanonical { offset, reason } => {
                write!(
                    f,
                    "MSO valueDigests is not canonical at byte {offset}: {reason}"
                )
            }
            Self::RequestedNamespaceMissing => write!(f, "requested namespace is missing"),
            Self::RequestedNamespaceDuplicate => {
                write!(f, "requested namespace occurs more than once")
            }
            Self::RequestedDigestMissing => write!(f, "selected digest is missing"),
            Self::IssuerUseCountOverflow { issuer_index } => {
                write!(f, "issuer byte-use count overflows at index {issuer_index}")
            }
        }
    }
}

impl std::error::Error for MdocValueDigestsScanError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocValueDigestsUseCensus {
    pub(crate) issuer_position_uses: Vec<u32>,
    pub(crate) issuer_uses_total: usize,
    pub(crate) active_rows: usize,
    pub(crate) blind_rows: usize,
    pub(crate) namespaces: usize,
    pub(crate) digest_entries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocValueDigestsInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

fn canonical_error(
    offset: usize,
    reason: MsoValueDigestsCanonicalityReason,
) -> MdocValueDigestsScanError {
    MdocValueDigestsScanError::MsoValueDigestsNotCanonical { offset, reason }
}

fn read_argument(
    bytes: &[u8],
    offset: usize,
    expected_major: u8,
    token: &'static str,
) -> Result<(u64, usize), MdocValueDigestsScanError> {
    let first = *bytes.get(offset).ok_or_else(|| {
        canonical_error(offset, MsoValueDigestsCanonicalityReason::Truncated(token))
    })?;
    if first >> 5 != expected_major {
        return Err(canonical_error(
            offset,
            match expected_major {
                3 => MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
                _ => MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            },
        ));
    }
    let additional = first & 0x1f;
    let (value, width) = match additional {
        value @ 0..=23 => (u64::from(value), 1),
        24 => {
            let value = *bytes.get(offset + 1).ok_or_else(|| {
                canonical_error(
                    offset + 1,
                    MsoValueDigestsCanonicalityReason::Truncated(token),
                )
            })?;
            if value < 24 {
                return Err(canonical_error(
                    offset,
                    match expected_major {
                        3 => MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
                        _ => MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
                    },
                ));
            }
            (u64::from(value), 2)
        }
        25 => {
            let tail = bytes.get(offset + 1..offset + 3).ok_or_else(|| {
                canonical_error(
                    offset + 1,
                    MsoValueDigestsCanonicalityReason::Truncated(token),
                )
            })?;
            let value = u64::from(u16::from_be_bytes([tail[0], tail[1]]));
            if value <= u64::from(u8::MAX) {
                return Err(canonical_error(
                    offset,
                    match expected_major {
                        3 => MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
                        _ => MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
                    },
                ));
            }
            (value, 3)
        }
        26 => {
            let tail = bytes.get(offset + 1..offset + 5).ok_or_else(|| {
                canonical_error(
                    offset + 1,
                    MsoValueDigestsCanonicalityReason::Truncated(token),
                )
            })?;
            let value = u64::from(u32::from_be_bytes([tail[0], tail[1], tail[2], tail[3]]));
            if value <= u64::from(u16::MAX) {
                return Err(canonical_error(
                    offset,
                    match expected_major {
                        3 => MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
                        _ => MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
                    },
                ));
            }
            (value, 5)
        }
        _ => {
            return Err(canonical_error(
                offset,
                match expected_major {
                    3 => MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
                    _ => MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
                },
            ));
        }
    };
    Ok((value, width))
}

fn read_map_count(
    bytes: &[u8],
    offset: usize,
) -> Result<(usize, usize), MdocValueDigestsScanError> {
    let (value, width) = read_argument(bytes, offset, 5, "map head")?;
    usize::try_from(value)
        .map(|value| (value, width))
        .map_err(|_| {
            canonical_error(
                offset,
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            )
        })
}

fn read_text(bytes: &[u8], offset: usize) -> Result<(&[u8], usize), MdocValueDigestsScanError> {
    let (length, head_len) = read_argument(bytes, offset, 3, "namespace text")?;
    let length = usize::try_from(length).map_err(|_| {
        canonical_error(
            offset,
            MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
        )
    })?;
    if length > MDOC_MAX_PUBLIC_NAMESPACE_BYTES {
        return Err(canonical_error(
            offset,
            MsoValueDigestsCanonicalityReason::NamespaceTooLong {
                length,
                max: MDOC_MAX_PUBLIC_NAMESPACE_BYTES,
            },
        ));
    }
    let start = offset.checked_add(head_len).ok_or_else(|| {
        canonical_error(
            offset,
            MsoValueDigestsCanonicalityReason::Truncated("namespace text"),
        )
    })?;
    let end = start.checked_add(length).ok_or_else(|| {
        canonical_error(
            start,
            MsoValueDigestsCanonicalityReason::Truncated("namespace text"),
        )
    })?;
    let text = bytes.get(start..end).ok_or_else(|| {
        canonical_error(
            start,
            MsoValueDigestsCanonicalityReason::Truncated("namespace text"),
        )
    })?;
    std::str::from_utf8(text).map_err(|error| {
        canonical_error(
            start + error.valid_up_to(),
            MsoValueDigestsCanonicalityReason::InvalidUtf8,
        )
    })?;
    Ok((text, head_len))
}

fn read_digest_id(
    bytes: &[u8],
    offset: usize,
) -> Result<(u32, usize, [u8; DIGEST_ID_ENCODING_BYTES]), MdocValueDigestsScanError> {
    let first = *bytes.get(offset).ok_or_else(|| {
        canonical_error(
            offset,
            MsoValueDigestsCanonicalityReason::Truncated("digest ID"),
        )
    })?;
    if first >> 5 != 0 {
        return Err(canonical_error(
            offset,
            MsoValueDigestsCanonicalityReason::ExpectedCanonicalDigestId,
        ));
    }
    let additional = first & 0x1f;
    let (value, width) = match additional {
        value @ 0..=23 => (u64::from(value), 1),
        24 => {
            let value = *bytes.get(offset + 1).ok_or_else(|| {
                canonical_error(
                    offset + 1,
                    MsoValueDigestsCanonicalityReason::Truncated("digest ID"),
                )
            })?;
            if value < 24 {
                return Err(canonical_error(
                    offset,
                    MsoValueDigestsCanonicalityReason::ExpectedCanonicalDigestId,
                ));
            }
            (u64::from(value), 2)
        }
        25 => {
            let tail = bytes.get(offset + 1..offset + 3).ok_or_else(|| {
                canonical_error(
                    offset + 1,
                    MsoValueDigestsCanonicalityReason::Truncated("digest ID"),
                )
            })?;
            let value = u64::from(u16::from_be_bytes([tail[0], tail[1]]));
            if value <= u64::from(u8::MAX) {
                return Err(canonical_error(
                    offset,
                    MsoValueDigestsCanonicalityReason::ExpectedCanonicalDigestId,
                ));
            }
            (value, 3)
        }
        26 => {
            let tail = bytes.get(offset + 1..offset + 5).ok_or_else(|| {
                canonical_error(
                    offset + 1,
                    MsoValueDigestsCanonicalityReason::Truncated("digest ID"),
                )
            })?;
            let value = u64::from(u32::from_be_bytes([tail[0], tail[1], tail[2], tail[3]]));
            if value <= u64::from(u16::MAX) {
                return Err(canonical_error(
                    offset,
                    MsoValueDigestsCanonicalityReason::ExpectedCanonicalDigestId,
                ));
            }
            (value, 5)
        }
        _ => {
            return Err(canonical_error(
                offset,
                MsoValueDigestsCanonicalityReason::ExpectedCanonicalDigestId,
            ));
        }
    };
    if value > u64::from(MDOC_PRIVATE_ITEM_DIGEST_ID_MAX) {
        return Err(canonical_error(
            offset,
            MsoValueDigestsCanonicalityReason::DigestIdOutOfRange {
                value,
                max: MDOC_PRIVATE_ITEM_DIGEST_ID_MAX,
            },
        ));
    }
    let mut encoded = [0u8; DIGEST_ID_ENCODING_BYTES];
    encoded[..width].copy_from_slice(&bytes[offset..offset + width]);
    Ok((value as u32, width, encoded))
}

#[derive(Clone, Debug)]
struct ParsedDigest {
    id: u32,
    encoding_len: usize,
    encoding: [u8; DIGEST_ID_ENCODING_BYTES],
    digest: [u8; 32],
    offset: usize,
}

#[derive(Clone, Debug)]
struct ParsedNamespace {
    name: Vec<u8>,
    head_len: usize,
    offset: usize,
    map_head_len: usize,
    digests: Vec<ParsedDigest>,
}

#[derive(Clone, Debug)]
struct ParsedValueDigests {
    offset: usize,
    namespaces: Vec<ParsedNamespace>,
    digest_entries: usize,
}

fn parse_value_digests_at(
    mso: &[u8],
    offset: usize,
) -> Result<ParsedValueDigests, MdocValueDigestsScanError> {
    let map_offset = offset + VALUE_DIGESTS_KEY.len();
    let (namespace_count, map_head_len) = read_map_count(mso, map_offset)?;
    if namespace_count > MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS {
        return Err(MdocValueDigestsScanError::ScanItemCapExceeded {
            items: namespace_count,
            max: MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS,
        });
    }

    // Check the limit before allocation.
    // Reject a declared 256th scan item before schedule allocation.
    let mut namespaces = Vec::with_capacity(namespace_count);
    let mut seen_namespaces = HashSet::with_capacity(namespace_count);
    let mut cursor = map_offset + map_head_len;
    let mut scan_items = namespace_count;
    let mut digest_entries = 0usize;
    for _ in 0..namespace_count {
        let namespace_offset = cursor;
        let (name, head_len) = read_text(mso, cursor)?;
        cursor += head_len + name.len();
        if !seen_namespaces.insert(name.to_vec()) {
            return Err(canonical_error(
                namespace_offset,
                MsoValueDigestsCanonicalityReason::DuplicateNamespace,
            ));
        }
        let (digest_count, map_head_len) = read_map_count(mso, cursor)?;
        let prospective_items = scan_items.checked_add(digest_count).ok_or(
            MdocValueDigestsScanError::ScanItemCapExceeded {
                items: usize::MAX,
                max: MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS,
            },
        )?;
        if prospective_items > MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS {
            return Err(MdocValueDigestsScanError::ScanItemCapExceeded {
                items: prospective_items,
                max: MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS,
            });
        }
        scan_items = prospective_items;
        cursor += map_head_len;

        let mut digests = Vec::with_capacity(digest_count);
        let mut seen_ids = HashSet::with_capacity(digest_count);
        for _ in 0..digest_count {
            let digest_offset = cursor;
            let (id, encoding_len, encoding) = read_digest_id(mso, cursor)?;
            cursor += encoding_len;
            if !seen_ids.insert(id) {
                return Err(canonical_error(
                    digest_offset,
                    MsoValueDigestsCanonicalityReason::DuplicateDigestId,
                ));
            }
            if mso.get(cursor..cursor + 2) != Some(&[0x58, 0x20]) {
                return Err(canonical_error(
                    cursor,
                    MsoValueDigestsCanonicalityReason::ExpectedDigestBstr32,
                ));
            }
            cursor += 2;
            let digest_slice = mso.get(cursor..cursor + 32).ok_or_else(|| {
                canonical_error(
                    cursor,
                    MsoValueDigestsCanonicalityReason::Truncated("digest bytes"),
                )
            })?;
            let mut digest = [0u8; 32];
            digest.copy_from_slice(digest_slice);
            cursor += 32;
            digests.push(ParsedDigest {
                id,
                encoding_len,
                encoding,
                digest,
                offset: digest_offset,
            });
            digest_entries += 1;
        }
        namespaces.push(ParsedNamespace {
            name: name.to_vec(),
            head_len,
            offset: namespace_offset,
            map_head_len,
            digests,
        });
    }
    Ok(ParsedValueDigests {
        offset,
        namespaces,
        digest_entries,
    })
}

fn select_value_digests(
    mso: &[u8],
    requested_namespace: &[u8],
    selected_digest: &MdocSelectedValueDigest,
) -> Result<(ParsedValueDigests, Vec<ScanRow>), MdocValueDigestsScanError> {
    let offsets = mso
        .windows(VALUE_DIGESTS_KEY.len())
        .enumerate()
        .filter_map(|(offset, bytes)| (bytes == VALUE_DIGESTS_KEY).then_some(offset))
        .collect::<Vec<_>>();
    if offsets.is_empty() {
        return Err(canonical_error(
            0,
            MsoValueDigestsCanonicalityReason::MissingValueDigests,
        ));
    }

    let mut selected = None;
    let mut first_semantic_error = None;
    for &offset in &offsets {
        let candidate = parse_value_digests_at(mso, offset).and_then(|parsed| {
            build_rows(&parsed, requested_namespace, selected_digest).map(|rows| (parsed, rows))
        });
        match candidate {
            Ok(candidate) if selected.is_some() => {
                return Err(canonical_error(
                    offset,
                    MsoValueDigestsCanonicalityReason::AmbiguousValueDigests,
                ));
            }
            Ok(candidate) => selected = Some(candidate),
            Err(error) if offsets.len() == 1 => return Err(error),
            Err(error @ MdocValueDigestsScanError::RequestedNamespaceMissing)
            | Err(error @ MdocValueDigestsScanError::RequestedNamespaceDuplicate)
            | Err(error @ MdocValueDigestsScanError::RequestedDigestMissing) => {
                first_semantic_error.get_or_insert(error);
            }
            Err(_) => {}
        }
    }
    selected.ok_or_else(|| {
        first_semantic_error.unwrap_or_else(|| {
            canonical_error(0, MsoValueDigestsCanonicalityReason::MissingValueDigests)
        })
    })
}

mod trace_col {
    pub(super) const ACTIVE: usize = 0;
    pub(super) const HEAD: usize = 1;
    pub(super) const NAMESPACE: usize = 2;
    pub(super) const DIGEST: usize = 3;
    pub(super) const ROW_LEN: usize = 4;
    pub(super) const CURSOR: usize = 5;
    pub(super) const MSO_START: usize = 6;
    pub(super) const OUTER_REMAINING: usize = 7;
    pub(super) const INNER_REMAINING: usize = 8;
    pub(super) const OUTER_ONE: usize = 9;
    pub(super) const OUTER_MORE: usize = 10;
    pub(super) const INNER_ZERO: usize = 11;
    pub(super) const INNER_ONE: usize = 12;
    pub(super) const INNER_MORE: usize = 13;
    pub(super) const NS_EMPTY_ONE: usize = 14;
    pub(super) const NS_EMPTY_MORE: usize = 15;
    pub(super) const DIGEST_LAST_ONE: usize = 16;
    pub(super) const DIGEST_LAST_MORE: usize = 17;
    pub(super) const NS_MATCH: usize = 18;
    pub(super) const REQUESTED_SCOPE: usize = 19;
    pub(super) const REQUESTED_COUNT: usize = 20;
    pub(super) const SELECTED: usize = 21;
    pub(super) const SELECTED_COUNT: usize = 22;
    pub(super) const NAMESPACE_INDEX: usize = 23;
    pub(super) const SORTED_ACTIVE: usize = 24;
    pub(super) const SORTED_NAMESPACE: usize = 25;
    pub(super) const SORTED_ID: usize = 26;
    pub(super) const SORTED_NAMESPACE_GT: usize = 27;
    pub(super) const SORTED_NAMESPACE_EQ: usize = 28;
    pub(super) const OUTER_NONZERO_INV: usize = 29;
    pub(super) const OUTER_ONE_INV: usize = 30;
    pub(super) const INNER_ZERO_INV: usize = 31;
    pub(super) const INNER_ONE_INV: usize = 32;

    pub(super) const BYTE: usize = 33;
    pub(super) const BYTE_ACTIVE: usize = BYTE + super::BYTE_SITES;
    pub(super) const BYTE_OFFSET: usize = BYTE_ACTIVE + super::BYTE_SITES;
    pub(super) const CURSOR_BITS: usize = BYTE_OFFSET + super::BYTE_SITES;
    pub(super) const ROW_LEN_BITS: usize = CURSOR_BITS + super::OFFSET_BITS;
    pub(super) const END_SLACK_BITS: usize = ROW_LEN_BITS + super::ROW_LEN_BITS;
    pub(super) const OUTER_BITS: usize = END_SLACK_BITS + super::OFFSET_BITS;
    pub(super) const INNER_BITS: usize = OUTER_BITS + super::COUNT_BITS;
    pub(super) const NAMESPACE_LONG: usize = INNER_BITS + super::COUNT_BITS;
    pub(super) const NAMESPACE_LEN: usize = NAMESPACE_LONG + 1;
    pub(super) const NAMESPACE_LEN_BITS: usize = NAMESPACE_LEN + 1;
    pub(super) const NAMESPACE_CONTENT_ACTIVE: usize =
        NAMESPACE_LEN_BITS + super::NAMESPACE_LEN_BITS;
    pub(super) const NAMESPACE_MISMATCH_INV: usize =
        NAMESPACE_CONTENT_ACTIVE + super::NAMESPACE_BYTE_SITES;
    pub(super) const OUTER_LONG: usize = NAMESPACE_MISMATCH_INV + super::NAMESPACE_MISMATCHES;
    pub(super) const INNER_LONG: usize = OUTER_LONG + 1;
    pub(super) const OUTER_MAP_SLACK_BITS: usize = INNER_LONG + 1;
    pub(super) const INNER_MAP_SLACK_BITS: usize = OUTER_MAP_SLACK_BITS + super::MAP_SLACK_BITS;
    pub(super) const DIGEST_KIND: usize = INNER_MAP_SLACK_BITS + super::MAP_SLACK_BITS;
    pub(super) const DIGEST_ENCODING_LEN: usize = DIGEST_KIND + 3;
    pub(super) const DIGEST_ID_LO: usize = DIGEST_ENCODING_LEN + 1;
    pub(super) const DIGEST_CANONICAL_SLACK_BITS: usize = DIGEST_ID_LO + 1;
    pub(super) const SORTED_NAMESPACE_DIFF_BITS: usize =
        DIGEST_CANONICAL_SLACK_BITS + super::DIGEST_CANONICAL_SLACK_BITS;
    pub(super) const SORTED_ID_DIFF_BITS: usize = SORTED_NAMESPACE_DIFF_BITS + super::COUNT_BITS;
    pub(super) const NAMESPACE_UPPER_SLACK_BITS: usize =
        SORTED_ID_DIFF_BITS + super::SORTED_DIFF_BITS;
    pub(super) const COUNT: usize = NAMESPACE_UPPER_SLACK_BITS + super::NAMESPACE_LEN_BITS;
}

const _: [(); TRACE_COLS] = [(); trace_col::COUNT];
const _: [(); 43] = [(); MAIN_RELATION_SITES];
const _: [(); 48] = [(); INTERACTION_COLS];

fn m31(value: usize) -> M31 {
    M31::from_u32_unchecked(value as u32)
}

fn m31_u32(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn inverse(value: M31) -> M31 {
    if value == m31(0) {
        m31(0)
    } else {
        value.inverse()
    }
}

fn bits(value: usize, count: usize) -> impl Iterator<Item = M31> {
    (0..count).map(move |bit| m31((value >> bit) & 1))
}

fn write_bits(columns: &mut [Vec<M31>], start: usize, row: usize, value: usize, count: usize) {
    for (column, bit) in columns[start..start + count]
        .iter_mut()
        .zip(bits(value, count))
    {
        column[row] = bit;
    }
}

fn coset_order_to_circle_domain_order(values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![m31(0); MDOC_VALUE_DIGESTS_SCAN_ROWS];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE),
            MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE,
        );
        ordered[row] = value;
    }
    ordered
}

fn column(values: Vec<M31>) -> Column {
    CircleEvaluation::new(
        CanonicCoset::new(MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(values)),
    )
}

fn namespace_tag(namespace: &str) -> String {
    namespace
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn preprocessed_id(spec: &MdocValueDigestsScanSpec, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!(
            "mdoc/value_digests_scan/v{SCAN_VERSION}/attribute_{}/ns_{}/{name}",
            TS13_SELECTED_ATTRIBUTE_COUNT,
            namespace_tag(&spec.namespace)
        ),
    }
}

fn preprocessed_ids(spec: &MdocValueDigestsScanSpec) -> Vec<PreProcessedColumnId> {
    ["first", "last", "capacity", "namespace_material"]
        .map(|name| preprocessed_id(spec, name))
        .into()
}

fn namespace_material(namespace: &[u8]) -> Vec<M31> {
    let mut values = vec![m31(0); MDOC_VALUE_DIGESTS_SCAN_ROWS];
    values[0] = m31(namespace.len());
    for (chunk_index, chunk) in namespace.chunks(NAMESPACE_PACK_BYTES).enumerate() {
        let packed = chunk
            .iter()
            .fold(0usize, |value, byte| value * 256 + usize::from(*byte));
        values[1 + chunk_index] = m31(packed);
    }
    values
}

fn preprocessed_columns(spec: &MdocValueDigestsScanSpec) -> Vec<Column> {
    let mut first = vec![m31(0); MDOC_VALUE_DIGESTS_SCAN_ROWS];
    first[0] = m31(1);
    let mut last = vec![m31(0); MDOC_VALUE_DIGESTS_SCAN_ROWS];
    last[MDOC_VALUE_DIGESTS_SCAN_ROWS - 1] = m31(1);
    let capacity = (0..MDOC_VALUE_DIGESTS_SCAN_ROWS)
        .map(|row| m31(usize::from(row <= MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS)))
        .collect();
    vec![
        column(first),
        column(last),
        column(capacity),
        column(namespace_material(spec.namespace.as_bytes())),
    ]
}

#[derive(Clone, Debug)]
enum RowKind {
    Head,
    Namespace {
        name: Vec<u8>,
        head_len: usize,
        digest_count: usize,
        map_head_len: usize,
        requested: bool,
    },
    Digest {
        id: u32,
        encoding_len: usize,
        encoding: [u8; DIGEST_ID_ENCODING_BYTES],
        digest: [u8; 32],
        selected: bool,
        requested_scope: bool,
    },
}

#[derive(Clone, Debug)]
struct ScanRow {
    kind: RowKind,
    cursor: usize,
    outer_remaining: usize,
    inner_remaining: usize,
    namespace_index: usize,
}

impl ScanRow {
    fn bytes(&self) -> ([u8; BYTE_SITES], [bool; BYTE_SITES], [usize; BYTE_SITES]) {
        let mut bytes = [0u8; BYTE_SITES];
        let mut active = [false; BYTE_SITES];
        let mut offsets = [0usize; BYTE_SITES];
        match &self.kind {
            RowKind::Head => {
                bytes[..VALUE_DIGESTS_KEY.len()].copy_from_slice(VALUE_DIGESTS_KEY);
                active[..VALUE_DIGESTS_KEY.len()].fill(true);
                for (index, offset) in offsets[..VALUE_DIGESTS_KEY.len()].iter_mut().enumerate() {
                    *offset = index;
                }
                let count = self.outer_remaining;
                let head = VALUE_DIGESTS_KEY.len();
                active[head] = true;
                offsets[head] = head;
                if count <= 23 {
                    bytes[head] = 0xa0 | count as u8;
                } else {
                    bytes[head] = 0xb8;
                    bytes[head + 1] = count as u8;
                    active[head + 1] = true;
                    offsets[head + 1] = head + 1;
                }
            }
            RowKind::Namespace {
                name,
                head_len,
                digest_count,
                map_head_len,
                ..
            } => {
                active[0] = true;
                offsets[0] = 0;
                if *head_len == 1 {
                    bytes[0] = 0x60 | name.len() as u8;
                } else {
                    bytes[0] = 0x78;
                    bytes[1] = name.len() as u8;
                    active[1] = true;
                    offsets[1] = 1;
                }
                for (index, &byte) in name.iter().enumerate() {
                    let site = 2 + index;
                    bytes[site] = byte;
                    active[site] = true;
                    offsets[site] = 1 + usize::from(*head_len == 2) + index;
                }
                let map_site = 34;
                let map_offset = head_len + name.len();
                active[map_site] = true;
                offsets[map_site] = map_offset;
                if *map_head_len == 1 {
                    bytes[map_site] = 0xa0 | *digest_count as u8;
                } else {
                    bytes[map_site] = 0xb8;
                    bytes[map_site + 1] = *digest_count as u8;
                    active[map_site + 1] = true;
                    offsets[map_site + 1] = map_offset + 1;
                }
            }
            RowKind::Digest {
                encoding_len,
                encoding,
                digest,
                ..
            } => {
                for index in 0..*encoding_len {
                    bytes[index] = encoding[index];
                    active[index] = true;
                    offsets[index] = index;
                }
                bytes[DIGEST_ID_ENCODING_BYTES] = 0x58;
                bytes[DIGEST_ID_ENCODING_BYTES + 1] = 0x20;
                active[DIGEST_ID_ENCODING_BYTES] = true;
                active[DIGEST_ID_ENCODING_BYTES + 1] = true;
                offsets[DIGEST_ID_ENCODING_BYTES] = *encoding_len;
                offsets[DIGEST_ID_ENCODING_BYTES + 1] = *encoding_len + 1;
                for (index, &byte) in digest.iter().enumerate() {
                    let site = DIGEST_BYTES_START + index;
                    bytes[site] = byte;
                    active[site] = true;
                    offsets[site] = *encoding_len + 2 + index;
                }
            }
        }
        (bytes, active, offsets)
    }

    fn row_len(&self) -> usize {
        match &self.kind {
            RowKind::Head => VALUE_DIGESTS_KEY.len() + 1 + usize::from(self.outer_remaining > 23),
            RowKind::Namespace {
                name,
                head_len,
                map_head_len,
                ..
            } => head_len + name.len() + map_head_len,
            RowKind::Digest { encoding_len, .. } => encoding_len + 2 + 32,
        }
    }
}

#[derive(Clone)]
struct MdocValueDigestsWitnessTrace {
    columns: Vec<Vec<M31>>,
    #[cfg(test)]
    rows: Vec<ScanRow>,
}

impl MdocValueDigestsWitnessTrace {
    fn trace(&self) -> Vec<Column> {
        self.columns.iter().cloned().map(column).collect()
    }
}

fn validate_spec(spec: &MdocValueDigestsScanSpec) -> Result<(), MdocValueDigestsScanError> {
    if spec.issuer_message_len == 0 {
        return Err(MdocValueDigestsScanError::EmptyIssuerMessage);
    }
    let max_message = crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES;
    if spec.issuer_message_len > max_message {
        return Err(MdocValueDigestsScanError::IssuerMessageTooLong {
            length: spec.issuer_message_len,
            max: max_message,
        });
    }
    if spec.mso_len == 0 {
        return Err(MdocValueDigestsScanError::EmptyMso);
    }
    let max_mso = crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES;
    if spec.mso_len > max_mso {
        return Err(MdocValueDigestsScanError::MsoTooLong {
            length: spec.mso_len,
            max: max_mso,
        });
    }
    if spec.namespace.is_empty() {
        return Err(MdocValueDigestsScanError::EmptyPublicNamespace);
    }
    if spec.namespace.len() > MDOC_MAX_PUBLIC_NAMESPACE_BYTES {
        return Err(MdocValueDigestsScanError::PublicNamespaceTooLong {
            length: spec.namespace.len(),
            max: MDOC_MAX_PUBLIC_NAMESPACE_BYTES,
        });
    }
    Ok(())
}

fn build_rows(
    parsed: &ParsedValueDigests,
    requested_namespace: &[u8],
    selected_digest: &MdocSelectedValueDigest,
) -> Result<Vec<ScanRow>, MdocValueDigestsScanError> {
    let requested = parsed
        .namespaces
        .iter()
        .enumerate()
        .filter_map(|(index, namespace)| {
            (namespace.name.as_slice() == requested_namespace).then_some(index)
        })
        .collect::<Vec<_>>();
    match requested.as_slice() {
        [] => Err(MdocValueDigestsScanError::RequestedNamespaceMissing),
        [index] => {
            let requested_namespace = &parsed.namespaces[*index];
            let selected_index = requested_namespace
                .digests
                .iter()
                .position(|digest| {
                    digest.id == selected_digest.digest_id
                        && digest.digest == selected_digest.digest
                })
                .ok_or(MdocValueDigestsScanError::RequestedDigestMissing)?;

            let mut rows = Vec::with_capacity(1 + parsed.namespaces.len() + parsed.digest_entries);
            rows.push(ScanRow {
                kind: RowKind::Head,
                cursor: parsed.offset,
                outer_remaining: parsed.namespaces.len(),
                inner_remaining: 0,
                namespace_index: 0,
            });
            for (namespace_index, namespace) in parsed.namespaces.iter().enumerate() {
                let requested_scope = namespace_index == *index;
                let outer_remaining = parsed.namespaces.len() - namespace_index;
                rows.push(ScanRow {
                    kind: RowKind::Namespace {
                        name: namespace.name.clone(),
                        head_len: namespace.head_len,
                        digest_count: namespace.digests.len(),
                        map_head_len: namespace.map_head_len,
                        requested: requested_scope,
                    },
                    cursor: namespace.offset,
                    outer_remaining,
                    inner_remaining: namespace.digests.len(),
                    namespace_index,
                });
                for (digest_index, digest) in namespace.digests.iter().enumerate() {
                    rows.push(ScanRow {
                        kind: RowKind::Digest {
                            id: digest.id,
                            encoding_len: digest.encoding_len,
                            encoding: digest.encoding,
                            digest: digest.digest,
                            selected: requested_scope && digest_index == selected_index,
                            requested_scope,
                        },
                        cursor: digest.offset,
                        outer_remaining,
                        inner_remaining: namespace.digests.len() - digest_index,
                        namespace_index,
                    });
                }
            }
            Ok(rows)
        }
        _ => Err(MdocValueDigestsScanError::RequestedNamespaceDuplicate),
    }
}

fn write_random_bits(columns: &mut [Vec<M31>], start: usize, count: usize, rng: &mut impl RngCore) {
    for column in &mut columns[start..start + count] {
        column.iter_mut().for_each(|value| *value = random_bit(rng));
    }
}

fn namespace_mismatches(row: &ScanRow, requested_namespace: &[u8]) -> [M31; NAMESPACE_MISMATCHES] {
    let mut differences = [m31(0); NAMESPACE_MISMATCHES];
    let RowKind::Namespace { name, .. } = &row.kind else {
        return differences;
    };
    differences[0] = m31(name.len()) - m31(requested_namespace.len());
    for chunk_index in 0..NAMESPACE_PACKS {
        let start = chunk_index * NAMESPACE_PACK_BYTES;
        let mut actual = 0usize;
        let mut expected = 0usize;
        for index in start..(start + NAMESPACE_PACK_BYTES).min(MDOC_MAX_PUBLIC_NAMESPACE_BYTES) {
            actual = actual * 256 + usize::from(name.get(index).copied().unwrap_or(0));
            expected =
                expected * 256 + usize::from(requested_namespace.get(index).copied().unwrap_or(0));
        }
        differences[1 + chunk_index] = m31(actual) - m31(expected);
    }
    differences
}

fn build_trace(
    spec: &MdocValueDigestsScanSpec,
    witness: &MdocValueDigestsScanWitness,
    rows: Vec<ScanRow>,
) -> Result<(MdocValueDigestsWitnessTrace, MdocValueDigestsUseCensus), MdocValueDigestsScanError> {
    let mut columns = vec![vec![m31(0); MDOC_VALUE_DIGESTS_SCAN_ROWS]; TRACE_COLS];
    let mut rng = rand::thread_rng();
    for column in &mut columns[trace_col::BYTE..trace_col::BYTE + BYTE_SITES] {
        column
            .iter_mut()
            .for_each(|value| *value = random_m31(&mut rng));
    }
    for column in &mut columns[trace_col::BYTE_OFFSET..trace_col::BYTE_OFFSET + BYTE_SITES] {
        column
            .iter_mut()
            .for_each(|value| *value = random_m31(&mut rng));
    }
    for (start, count) in [
        (trace_col::CURSOR_BITS, OFFSET_BITS),
        (trace_col::ROW_LEN_BITS, ROW_LEN_BITS),
        (trace_col::END_SLACK_BITS, OFFSET_BITS),
        (trace_col::OUTER_BITS, COUNT_BITS),
        (trace_col::INNER_BITS, COUNT_BITS),
        (trace_col::NAMESPACE_LEN_BITS, NAMESPACE_LEN_BITS),
        (trace_col::OUTER_MAP_SLACK_BITS, MAP_SLACK_BITS),
        (trace_col::INNER_MAP_SLACK_BITS, MAP_SLACK_BITS),
        (
            trace_col::DIGEST_CANONICAL_SLACK_BITS,
            DIGEST_CANONICAL_SLACK_BITS,
        ),
        (trace_col::SORTED_NAMESPACE_DIFF_BITS, COUNT_BITS),
        (trace_col::SORTED_ID_DIFF_BITS, SORTED_DIFF_BITS),
        (trace_col::NAMESPACE_UPPER_SLACK_BITS, NAMESPACE_LEN_BITS),
    ] {
        write_random_bits(&mut columns, start, count, &mut rng);
    }
    let mut requested_count = 0usize;
    let mut selected_count = 0usize;
    let mut issuer_position_uses = vec![0u32; spec.issuer_message_len];
    let mut issuer_uses_total = 0usize;
    for (row_index, row) in rows.iter().enumerate() {
        let row_len = row.row_len();
        let row_end =
            row.cursor
                .checked_add(row_len)
                .ok_or(MdocValueDigestsScanError::MsoOutOfBounds {
                    start: row.cursor,
                    length: row_len,
                    issuer_message_len: spec.mso_len,
                })?;
        if row_end > spec.mso_len {
            return Err(MdocValueDigestsScanError::MsoOutOfBounds {
                start: row.cursor,
                length: row_len,
                issuer_message_len: spec.mso_len,
            });
        }
        columns[trace_col::ACTIVE][row_index] = m31(1);
        columns[trace_col::ROW_LEN][row_index] = m31(row_len);
        columns[trace_col::CURSOR][row_index] = m31(row.cursor);
        columns[trace_col::MSO_START][row_index] = m31(witness.mso_start);
        columns[trace_col::OUTER_REMAINING][row_index] = m31(row.outer_remaining);
        columns[trace_col::INNER_REMAINING][row_index] = m31(row.inner_remaining);
        columns[trace_col::NAMESPACE_INDEX][row_index] = m31(row.namespace_index);
        write_bits(
            &mut columns,
            trace_col::CURSOR_BITS,
            row_index,
            row.cursor,
            OFFSET_BITS,
        );
        write_bits(
            &mut columns,
            trace_col::ROW_LEN_BITS,
            row_index,
            row_len,
            ROW_LEN_BITS,
        );
        write_bits(
            &mut columns,
            trace_col::END_SLACK_BITS,
            row_index,
            spec.mso_len - row_end,
            OFFSET_BITS,
        );
        write_bits(
            &mut columns,
            trace_col::OUTER_BITS,
            row_index,
            row.outer_remaining,
            COUNT_BITS,
        );
        write_bits(
            &mut columns,
            trace_col::INNER_BITS,
            row_index,
            row.inner_remaining,
            COUNT_BITS,
        );
        columns[trace_col::OUTER_ONE][row_index] = m31(usize::from(row.outer_remaining == 1));
        columns[trace_col::OUTER_MORE][row_index] = m31(usize::from(row.outer_remaining > 1));
        columns[trace_col::OUTER_NONZERO_INV][row_index] = inverse(m31(row.outer_remaining));
        columns[trace_col::OUTER_ONE_INV][row_index] = inverse(m31(row.outer_remaining) - m31(1));

        let inner_context = !matches!(row.kind, RowKind::Head);
        columns[trace_col::INNER_ZERO][row_index] =
            m31(usize::from(inner_context && row.inner_remaining == 0));
        columns[trace_col::INNER_ONE][row_index] =
            m31(usize::from(inner_context && row.inner_remaining == 1));
        columns[trace_col::INNER_MORE][row_index] =
            m31(usize::from(inner_context && row.inner_remaining > 1));
        if inner_context {
            columns[trace_col::INNER_ZERO_INV][row_index] = inverse(m31(row.inner_remaining));
            columns[trace_col::INNER_ONE_INV][row_index] =
                inverse(m31(row.inner_remaining) - m31(1));
        }

        let (bytes, byte_active, byte_offsets) = row.bytes();
        for site in 0..BYTE_SITES {
            columns[trace_col::BYTE + site][row_index] = m31_u32(u32::from(bytes[site]));
            columns[trace_col::BYTE_ACTIVE + site][row_index] = m31(usize::from(byte_active[site]));
            columns[trace_col::BYTE_OFFSET + site][row_index] = m31(byte_offsets[site]);
            if byte_active[site] {
                let issuer_index = witness
                    .mso_start
                    .checked_add(row.cursor)
                    .and_then(|value| value.checked_add(byte_offsets[site]))
                    .ok_or(MdocValueDigestsScanError::MsoOutOfBounds {
                        start: witness.mso_start,
                        length: spec.mso_len,
                        issuer_message_len: spec.issuer_message_len,
                    })?;
                if issuer_index >= spec.issuer_message_len {
                    return Err(MdocValueDigestsScanError::MsoOutOfBounds {
                        start: witness.mso_start,
                        length: spec.mso_len,
                        issuer_message_len: spec.issuer_message_len,
                    });
                }
                issuer_position_uses[issuer_index] = issuer_position_uses[issuer_index]
                    .checked_add(1)
                    .ok_or(MdocValueDigestsScanError::IssuerUseCountOverflow { issuer_index })?;
                issuer_uses_total += 1;
            }
        }

        match &row.kind {
            RowKind::Head => {
                columns[trace_col::HEAD][row_index] = m31(1);
                let long = usize::from(row.outer_remaining > 23);
                columns[trace_col::OUTER_LONG][row_index] = m31(long);
                let slack = if long == 0 {
                    23 - row.outer_remaining
                } else {
                    row.outer_remaining - 24
                };
                write_bits(
                    &mut columns,
                    trace_col::OUTER_MAP_SLACK_BITS,
                    row_index,
                    slack,
                    MAP_SLACK_BITS,
                );
            }
            RowKind::Namespace {
                name,
                head_len,
                digest_count,
                map_head_len,
                requested,
            } => {
                columns[trace_col::NAMESPACE][row_index] = m31(1);
                columns[trace_col::NAMESPACE_LONG][row_index] = m31(usize::from(*head_len == 2));
                columns[trace_col::NAMESPACE_LEN][row_index] = m31(name.len());
                write_bits(
                    &mut columns,
                    trace_col::NAMESPACE_LEN_BITS,
                    row_index,
                    name.len(),
                    NAMESPACE_LEN_BITS,
                );
                write_bits(
                    &mut columns,
                    trace_col::NAMESPACE_UPPER_SLACK_BITS,
                    row_index,
                    MDOC_MAX_PUBLIC_NAMESPACE_BYTES - name.len(),
                    NAMESPACE_LEN_BITS,
                );
                for index in 0..name.len() {
                    columns[trace_col::NAMESPACE_CONTENT_ACTIVE + index][row_index] = m31(1);
                }
                let namespace_slack = if *head_len == 1 {
                    23 - name.len()
                } else {
                    name.len() - 24
                };
                write_bits(
                    &mut columns,
                    trace_col::OUTER_MAP_SLACK_BITS,
                    row_index,
                    namespace_slack,
                    MAP_SLACK_BITS,
                );
                columns[trace_col::INNER_LONG][row_index] = m31(usize::from(*map_head_len == 2));
                let map_slack = if *map_head_len == 1 {
                    23 - digest_count
                } else {
                    digest_count - 24
                };
                write_bits(
                    &mut columns,
                    trace_col::INNER_MAP_SLACK_BITS,
                    row_index,
                    map_slack,
                    MAP_SLACK_BITS,
                );
                columns[trace_col::NS_MATCH][row_index] = m31(usize::from(*requested));
                if *requested {
                    requested_count += 1;
                }
                let differences = namespace_mismatches(row, spec.namespace.as_bytes());
                if let Some((index, difference)) = differences
                    .iter()
                    .copied()
                    .enumerate()
                    .find(|(_, difference)| *difference != m31(0))
                {
                    columns[trace_col::NAMESPACE_MISMATCH_INV + index][row_index] =
                        difference.inverse();
                }
                if *digest_count == 0 {
                    let branch = if row.outer_remaining == 1 {
                        trace_col::NS_EMPTY_ONE
                    } else {
                        trace_col::NS_EMPTY_MORE
                    };
                    columns[branch][row_index] = m31(1);
                }
            }
            RowKind::Digest {
                id,
                encoding_len,
                encoding,
                selected,
                requested_scope,
                ..
            } => {
                columns[trace_col::DIGEST][row_index] = m31(1);
                columns[trace_col::REQUESTED_SCOPE][row_index] = m31(usize::from(*requested_scope));
                let kind = match encoding_len {
                    1 => 0,
                    2 => 1,
                    3 => 2,
                    _ => unreachable!("canonical digest ID width"),
                };
                columns[trace_col::DIGEST_KIND + kind][row_index] = m31(1);
                columns[trace_col::DIGEST_ENCODING_LEN][row_index] = m31(*encoding_len);
                columns[trace_col::DIGEST_ID_LO][row_index] = m31_u32(*id & 0xffff);
                let canonical_slack = match kind {
                    0 => 23 - usize::from(encoding[0]),
                    1 => usize::from(encoding[1]) - 24,
                    2 => usize::from(encoding[1]) - 1,
                    _ => unreachable!(),
                };
                write_bits(
                    &mut columns,
                    trace_col::DIGEST_CANONICAL_SLACK_BITS,
                    row_index,
                    canonical_slack,
                    DIGEST_CANONICAL_SLACK_BITS,
                );
                if *selected {
                    columns[trace_col::SELECTED][row_index] = m31(1);
                    selected_count += 1;
                }
                if row.inner_remaining == 1 {
                    let branch = if row.outer_remaining == 1 {
                        trace_col::DIGEST_LAST_ONE
                    } else {
                        trace_col::DIGEST_LAST_MORE
                    };
                    columns[branch][row_index] = m31(1);
                }
            }
        }
        columns[trace_col::REQUESTED_COUNT][row_index] = m31(requested_count);
        columns[trace_col::SELECTED_COUNT][row_index] = m31(selected_count);
    }

    let active_rows = rows.len();
    let namespaces = rows
        .iter()
        .filter(|row| matches!(row.kind, RowKind::Namespace { .. }))
        .count();
    let mut sorted = rows
        .iter()
        .filter_map(|row| match row.kind {
            RowKind::Digest { id, .. } => Some((row.namespace_index, id)),
            _ => None,
        })
        .collect::<Vec<_>>();
    sorted.sort_unstable();
    for (row, &(namespace, id)) in sorted.iter().enumerate() {
        columns[trace_col::SORTED_ACTIVE][row] = m31(1);
        columns[trace_col::SORTED_NAMESPACE][row] = m31(namespace);
        columns[trace_col::SORTED_ID][row] = m31_u32(id);
        if row == 0 {
            continue;
        }
        let (previous_namespace, previous_id) = sorted[row - 1];
        if namespace > previous_namespace {
            columns[trace_col::SORTED_NAMESPACE_GT][row] = m31(1);
            write_bits(
                &mut columns,
                trace_col::SORTED_NAMESPACE_DIFF_BITS,
                row,
                namespace - previous_namespace - 1,
                COUNT_BITS,
            );
        } else {
            columns[trace_col::SORTED_NAMESPACE_EQ][row] = m31(1);
            write_bits(
                &mut columns,
                trace_col::SORTED_ID_DIFF_BITS,
                row,
                (id - previous_id - 1) as usize,
                SORTED_DIFF_BITS,
            );
        }
    }

    Ok((
        MdocValueDigestsWitnessTrace {
            columns,
            #[cfg(test)]
            rows,
        },
        MdocValueDigestsUseCensus {
            issuer_position_uses,
            issuer_uses_total,
            active_rows,
            blind_rows: MDOC_VALUE_DIGESTS_SCAN_ROWS - active_rows,
            namespaces,
            digest_entries: sorted.len(),
        },
    ))
}

fn m31_const<E: EvalAtRow>(value: usize) -> E::F {
    E::F::from(m31(value))
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

#[derive(Clone)]
struct MdocValueDigestsScanEval {
    spec: MdocValueDigestsScanSpec,
    issuer_relation: FieldBytesRelation,
    mso_start_relation: MdocMsoStartRelation,
    id_multiset_relation: MdocValueDigestIdMultisetRelation,
    item_id_relation: MdocPrivateDigestIdRelation,
    digest_relation: DigestBytesRelation,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

impl FrameworkEval for MdocValueDigestsScanEval {
    fn log_size(&self) -> u32 {
        MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Base constraints and the paired linear-denominator LogUp recurrence
        // both reach cubic degree.
        MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let first = eval.get_preprocessed_column(preprocessed_id(&self.spec, "first"));
        let last = eval.get_preprocessed_column(preprocessed_id(&self.spec, "last"));
        let capacity = eval.get_preprocessed_column(preprocessed_id(&self.spec, "capacity"));
        let namespace_material =
            eval.get_preprocessed_column(preprocessed_id(&self.spec, "namespace_material"));

        let [active, active_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let head = eval.next_trace_mask();
        let [namespace, namespace_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [digest, digest_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [row_len, _row_len_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [cursor, cursor_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [mso_start, mso_start_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [outer_remaining, outer_remaining_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [inner_remaining, inner_remaining_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let outer_one = eval.next_trace_mask();
        let outer_more = eval.next_trace_mask();
        let inner_zero = eval.next_trace_mask();
        let inner_one = eval.next_trace_mask();
        let inner_more = eval.next_trace_mask();
        let ns_empty_one = eval.next_trace_mask();
        let ns_empty_more = eval.next_trace_mask();
        let digest_last_one = eval.next_trace_mask();
        let digest_last_more = eval.next_trace_mask();
        let [ns_match, ns_match_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [requested_scope, requested_scope_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [requested_count, requested_count_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [selected, selected_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [selected_count, selected_count_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [namespace_index, namespace_index_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [sorted_active, sorted_active_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [sorted_namespace, sorted_namespace_prev] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [sorted_id, sorted_id_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let sorted_namespace_gt = eval.next_trace_mask();
        let sorted_namespace_eq = eval.next_trace_mask();
        let outer_nonzero_inv = eval.next_trace_mask();
        let outer_one_inv = eval.next_trace_mask();
        let inner_zero_inv = eval.next_trace_mask();
        let inner_one_inv = eval.next_trace_mask();
        let bytes: [E::F; BYTE_SITES] = std::array::from_fn(|_| eval.next_trace_mask());
        let byte_active: [E::F; BYTE_SITES] = std::array::from_fn(|_| eval.next_trace_mask());
        let byte_offset: [E::F; BYTE_SITES] = std::array::from_fn(|_| eval.next_trace_mask());
        let cursor_bits: [E::F; OFFSET_BITS] = std::array::from_fn(|_| eval.next_trace_mask());
        let row_len_bits: [E::F; ROW_LEN_BITS] = std::array::from_fn(|_| eval.next_trace_mask());
        let end_slack_bits: [E::F; OFFSET_BITS] = std::array::from_fn(|_| eval.next_trace_mask());
        let outer_bits: [E::F; COUNT_BITS] = std::array::from_fn(|_| eval.next_trace_mask());
        let inner_bits: [E::F; COUNT_BITS] = std::array::from_fn(|_| eval.next_trace_mask());
        let namespace_long = eval.next_trace_mask();
        let namespace_len = eval.next_trace_mask();
        let namespace_len_bits: [E::F; NAMESPACE_LEN_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let namespace_content_active: [E::F; NAMESPACE_BYTE_SITES] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let namespace_mismatch_inv: [E::F; NAMESPACE_MISMATCHES] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let outer_long = eval.next_trace_mask();
        let inner_long = eval.next_trace_mask();
        let outer_map_slack_bits: [E::F; MAP_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let inner_map_slack_bits: [E::F; MAP_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let digest_kind: [E::F; 3] = std::array::from_fn(|_| eval.next_trace_mask());
        let digest_encoding_len = eval.next_trace_mask();
        let digest_id_lo = eval.next_trace_mask();
        let digest_canonical_slack_bits: [E::F; DIGEST_CANONICAL_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let sorted_namespace_diff_bits: [E::F; COUNT_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let sorted_id_diff_bits: [E::F; SORTED_DIFF_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let namespace_upper_slack_bits: [E::F; NAMESPACE_LEN_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());

        let one = m31_const::<E>(1);
        let zero = m31_const::<E>(0);
        for selector in [
            active.clone(),
            head.clone(),
            namespace.clone(),
            digest.clone(),
            outer_one.clone(),
            outer_more.clone(),
            inner_zero.clone(),
            inner_one.clone(),
            inner_more.clone(),
            ns_empty_one.clone(),
            ns_empty_more.clone(),
            digest_last_one.clone(),
            digest_last_more.clone(),
            ns_match.clone(),
            requested_scope.clone(),
            selected.clone(),
            sorted_active.clone(),
            sorted_namespace_gt.clone(),
            sorted_namespace_eq.clone(),
            namespace_long.clone(),
            outer_long.clone(),
            inner_long.clone(),
        ]
        .into_iter()
        .chain(byte_active.iter().cloned())
        .chain(namespace_content_active.iter().cloned())
        .chain(digest_kind.iter().cloned())
        .chain(cursor_bits.iter().cloned())
        .chain(row_len_bits.iter().cloned())
        .chain(end_slack_bits.iter().cloned())
        .chain(outer_bits.iter().cloned())
        .chain(inner_bits.iter().cloned())
        .chain(namespace_len_bits.iter().cloned())
        .chain(outer_map_slack_bits.iter().cloned())
        .chain(inner_map_slack_bits.iter().cloned())
        .chain(digest_canonical_slack_bits.iter().cloned())
        .chain(sorted_namespace_diff_bits.iter().cloned())
        .chain(sorted_id_diff_bits.iter().cloned())
        .chain(namespace_upper_slack_bits.iter().cloned())
        {
            add_boolean(&mut eval, selector, &one);
        }

        eval.add_constraint(active.clone() - head.clone() - namespace.clone() - digest.clone());
        eval.add_constraint(head.clone() - first.clone());
        eval.add_constraint(active.clone() * (one.clone() - capacity.clone()));
        eval.add_constraint(sorted_active.clone() * (one.clone() - capacity));
        eval.add_constraint(last.clone() * active.clone());
        eval.add_constraint(last.clone() * sorted_active.clone());
        eval.add_constraint(
            first.clone() * (namespace_material - m31_const::<E>(self.spec.namespace.len())),
        );

        let ns_nonempty = namespace.clone() - ns_empty_one.clone() - ns_empty_more.clone();
        let digest_more = digest.clone() - digest_last_one.clone() - digest_last_more.clone();
        let terminal = ns_empty_one.clone() + digest_last_one.clone();
        let continue_active = head.clone()
            + ns_nonempty.clone()
            + ns_empty_more.clone()
            + digest_more.clone()
            + digest_last_more.clone();
        eval.add_constraint(
            (one.clone() - last.clone()) * (active_next.clone() - continue_active.clone()),
        );
        eval.add_constraint(
            (one.clone() - last.clone())
                * (namespace_next.clone()
                    - head.clone()
                    - ns_empty_more.clone()
                    - digest_last_more.clone()),
        );
        eval.add_constraint(
            (one.clone() - last.clone())
                * (digest_next.clone() - ns_nonempty.clone() - digest_more.clone()),
        );
        eval.add_constraint(terminal.clone() * active_next.clone());

        eval.add_constraint(outer_one.clone() + outer_more.clone() - active.clone());
        eval.add_constraint(outer_remaining.clone() * outer_nonzero_inv - active.clone());
        eval.add_constraint(outer_one.clone() * (outer_remaining.clone() - one.clone()));
        eval.add_constraint(
            (outer_remaining.clone() - one.clone()) * outer_one_inv - active.clone()
                + outer_one.clone(),
        );
        let inner_context = namespace.clone() + digest.clone();
        eval.add_constraint(
            inner_zero.clone() + inner_one.clone() + inner_more.clone() - inner_context.clone(),
        );
        eval.add_constraint(inner_zero.clone() * inner_remaining.clone());
        eval.add_constraint(
            inner_remaining.clone() * inner_zero_inv - inner_context.clone() + inner_zero.clone(),
        );
        eval.add_constraint(inner_one.clone() * (inner_remaining.clone() - one.clone()));
        eval.add_constraint(
            (inner_remaining.clone() - one.clone()) * inner_one_inv - inner_context.clone()
                + inner_one.clone(),
        );
        eval.add_constraint(digest.clone() * inner_zero.clone());
        eval.add_constraint(
            ns_empty_one.clone() + ns_empty_more.clone() - namespace.clone() * inner_zero.clone(),
        );
        eval.add_constraint(ns_empty_one.clone() * outer_more.clone());
        eval.add_constraint(ns_empty_more.clone() * outer_one.clone());
        eval.add_constraint(
            digest_last_one.clone() + digest_last_more.clone() - digest.clone() * inner_one.clone(),
        );
        eval.add_constraint(digest_last_one.clone() * outer_more.clone());
        eval.add_constraint(digest_last_more.clone() * outer_one.clone());

        eval.add_constraint(active.clone() * (cursor.clone() - bit_sum::<E>(&cursor_bits)));
        eval.add_constraint(active.clone() * (row_len.clone() - bit_sum::<E>(&row_len_bits)));
        eval.add_constraint(
            active.clone()
                * (cursor.clone() + row_len.clone() + bit_sum::<E>(&end_slack_bits)
                    - m31_const::<E>(self.spec.mso_len)),
        );
        eval.add_constraint(active.clone() * (outer_remaining.clone() - bit_sum::<E>(&outer_bits)));
        eval.add_constraint(
            inner_context.clone() * (inner_remaining.clone() - bit_sum::<E>(&inner_bits)),
        );
        eval.add_constraint(
            continue_active.clone() * (cursor_next - cursor.clone() - row_len.clone()),
        );
        eval.add_constraint(continue_active.clone() * (mso_start_next - mso_start.clone()));

        let same_outer = head.clone() + ns_nonempty.clone() + digest_more.clone();
        let next_namespace = ns_empty_more.clone() + digest_last_more.clone();
        eval.add_constraint(
            same_outer.clone() * (outer_remaining_next.clone() - outer_remaining.clone()),
        );
        eval.add_constraint(
            next_namespace.clone() * (outer_remaining_next - outer_remaining.clone() + one.clone()),
        );
        eval.add_constraint(
            ns_nonempty.clone() * (inner_remaining_next.clone() - inner_remaining.clone()),
        );
        eval.add_constraint(
            digest_more.clone() * (inner_remaining_next - inner_remaining.clone() + one.clone()),
        );
        eval.add_constraint(head.clone() * namespace_index.clone());
        eval.add_constraint(head.clone() * namespace_index_next.clone());
        eval.add_constraint(
            (ns_nonempty.clone() + digest_more.clone())
                * (namespace_index_next.clone() - namespace_index.clone()),
        );
        eval.add_constraint(
            next_namespace * (namespace_index_next - namespace_index.clone() - one.clone()),
        );

        eval.add_constraint((head.clone() + namespace.clone()) * requested_scope.clone());
        eval.add_constraint(
            ns_nonempty.clone() * (requested_scope_next.clone() - ns_match.clone()),
        );
        eval.add_constraint(digest_more.clone() * (requested_scope_next - requested_scope.clone()));
        eval.add_constraint(ns_match.clone() * (one.clone() - namespace.clone()));
        eval.add_constraint(first.clone() * requested_count.clone());
        eval.add_constraint(
            continue_active.clone()
                * (requested_count_next - requested_count.clone() - ns_match_next),
        );
        eval.add_constraint(terminal.clone() * (requested_count - one.clone()));

        eval.add_constraint(selected.clone() * (one.clone() - digest.clone()));
        eval.add_constraint(selected.clone() * (one.clone() - requested_scope.clone()));
        eval.add_constraint(first.clone() * selected_count.clone());
        eval.add_constraint(
            continue_active.clone()
                * (selected_count_next - selected_count.clone() - selected_next),
        );
        eval.add_constraint(terminal.clone() * (selected_count - one.clone()));

        let outer_short = head.clone() - outer_long.clone();
        eval.add_constraint(outer_long.clone() * (one.clone() - head.clone()));
        let outer_map_slack = bit_sum::<E>(&outer_map_slack_bits);
        eval.add_constraint(
            outer_short.clone()
                * (outer_remaining.clone() + outer_map_slack.clone() - m31_const::<E>(23)),
        );
        eval.add_constraint(
            outer_long.clone()
                * (outer_remaining.clone() - m31_const::<E>(24) - outer_map_slack.clone()),
        );
        let namespace_short = namespace.clone() - namespace_long.clone();
        eval.add_constraint(namespace_long.clone() * (one.clone() - namespace.clone()));
        eval.add_constraint(
            namespace.clone() * (namespace_len.clone() - bit_sum::<E>(&namespace_len_bits)),
        );
        eval.add_constraint(
            namespace.clone()
                * (namespace_len.clone() + bit_sum::<E>(&namespace_upper_slack_bits)
                    - m31_const::<E>(MDOC_MAX_PUBLIC_NAMESPACE_BYTES)),
        );
        eval.add_constraint(
            namespace_short.clone()
                * (namespace_len.clone() + outer_map_slack.clone() - m31_const::<E>(23)),
        );
        eval.add_constraint(
            namespace_long.clone() * (namespace_len.clone() - m31_const::<E>(24) - outer_map_slack),
        );
        let namespace_active_sum = namespace_content_active
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, value| sum + value);
        eval.add_constraint(namespace_active_sum - namespace_len.clone());
        for index in 0..NAMESPACE_BYTE_SITES {
            eval.add_constraint(
                namespace_content_active[index].clone() * (one.clone() - namespace.clone()),
            );
            eval.add_constraint(
                (namespace.clone() - namespace_content_active[index].clone())
                    * bytes[2 + index].clone(),
            );
            if index + 1 < NAMESPACE_BYTE_SITES {
                eval.add_constraint(
                    namespace_content_active[index + 1].clone()
                        * (one.clone() - namespace_content_active[index].clone()),
                );
            }
        }
        let inner_short = namespace.clone() - inner_long.clone();
        eval.add_constraint(inner_long.clone() * (one.clone() - namespace.clone()));
        let inner_map_slack = bit_sum::<E>(&inner_map_slack_bits);
        eval.add_constraint(
            inner_short.clone()
                * (inner_remaining.clone() + inner_map_slack.clone() - m31_const::<E>(23)),
        );
        eval.add_constraint(
            inner_long.clone() * (inner_remaining.clone() - m31_const::<E>(24) - inner_map_slack),
        );

        let expected_row_len = m31_const::<E>(14) * head.clone()
            + outer_long.clone()
            + m31_const::<E>(2) * namespace.clone()
            + namespace_long.clone()
            + namespace_len.clone()
            + inner_long.clone()
            + m31_const::<E>(34) * digest.clone()
            + digest_encoding_len.clone();
        eval.add_constraint(row_len - expected_row_len);

        for site in 0..BYTE_SITES {
            let mut expected_active = zero.clone();
            if site < VALUE_DIGESTS_KEY.len() + 1 {
                expected_active += head.clone();
            } else if site == VALUE_DIGESTS_KEY.len() + 1 {
                expected_active += outer_long.clone();
            }
            match site {
                0 => expected_active += namespace.clone(),
                1 => expected_active += namespace_long.clone(),
                2..=33 => expected_active += namespace_content_active[site - 2].clone(),
                34 => expected_active += namespace.clone(),
                35 => expected_active += inner_long.clone(),
                _ => {}
            }
            if site < DIGEST_ID_ENCODING_BYTES {
                for (kind, len) in [1usize, 2, 3].into_iter().enumerate() {
                    if site < len {
                        expected_active += digest_kind[kind].clone();
                    }
                }
            } else if site >= DIGEST_ID_ENCODING_BYTES {
                expected_active += digest.clone();
            }
            eval.add_constraint(byte_active[site].clone() - expected_active);

            if site < VALUE_DIGESTS_KEY.len() + 2 {
                eval.add_constraint(
                    (if site == VALUE_DIGESTS_KEY.len() + 1 {
                        outer_long.clone()
                    } else {
                        head.clone()
                    }) * (byte_offset[site].clone() - m31_const::<E>(site)),
                );
            }
            let namespace_offset = match site {
                0 => Some(zero.clone()),
                1 => Some(one.clone()),
                2..=33 => Some(one.clone() + namespace_long.clone() + m31_const::<E>(site - 2)),
                34 => Some(one.clone() + namespace_long.clone() + namespace_len.clone()),
                35 => Some(m31_const::<E>(2) + namespace_long.clone() + namespace_len.clone()),
                _ => None,
            };
            if let Some(expected) = namespace_offset {
                let gate = match site {
                    0 | 34 => namespace.clone(),
                    1 => namespace_long.clone(),
                    2..=33 => namespace_content_active[site - 2].clone(),
                    35 => inner_long.clone(),
                    _ => unreachable!(),
                };
                eval.add_constraint(gate * (byte_offset[site].clone() - expected));
            }
            let digest_offset = match site {
                0..DIGEST_ID_ENCODING_BYTES => m31_const::<E>(site),
                DIGEST_ID_ENCODING_BYTES => digest_encoding_len.clone(),
                DIGEST_BSTR_HEAD_END => digest_encoding_len.clone() + one.clone(),
                DIGEST_BYTES_START..BYTE_SITES => {
                    digest_encoding_len.clone() + m31_const::<E>(site - DIGEST_ID_ENCODING_BYTES)
                }
                _ => unreachable!(),
            };
            let digest_gate = if site < DIGEST_ID_ENCODING_BYTES {
                byte_active[site].clone()
                    - head.clone()
                    - match site {
                        0 => namespace.clone(),
                        1 => namespace_long.clone(),
                        2 => namespace_content_active[0].clone(),
                        _ => zero.clone(),
                    }
            } else {
                digest.clone()
            };
            eval.add_constraint(digest_gate * (byte_offset[site].clone() - digest_offset));
        }

        for (site, &expected) in VALUE_DIGESTS_KEY.iter().enumerate() {
            eval.add_constraint(
                head.clone() * (bytes[site].clone() - m31_const::<E>(usize::from(expected))),
            );
        }
        eval.add_constraint(
            outer_short.clone()
                * (bytes[VALUE_DIGESTS_KEY.len()].clone()
                    - m31_const::<E>(0xa0)
                    - outer_remaining.clone()),
        );
        eval.add_constraint(
            outer_long.clone() * (bytes[VALUE_DIGESTS_KEY.len()].clone() - m31_const::<E>(0xb8)),
        );
        eval.add_constraint(
            outer_long.clone()
                * (bytes[VALUE_DIGESTS_KEY.len() + 1].clone() - outer_remaining.clone()),
        );
        eval.add_constraint(
            namespace_short.clone()
                * (bytes[0].clone() - m31_const::<E>(0x60) - namespace_len.clone()),
        );
        eval.add_constraint(namespace_long.clone() * (bytes[0].clone() - m31_const::<E>(0x78)));
        eval.add_constraint(namespace_long.clone() * (bytes[1].clone() - namespace_len.clone()));
        eval.add_constraint(
            inner_short.clone()
                * (bytes[34].clone() - m31_const::<E>(0xa0) - inner_remaining.clone()),
        );
        eval.add_constraint(inner_long.clone() * (bytes[34].clone() - m31_const::<E>(0xb8)));
        eval.add_constraint(inner_long.clone() * (bytes[35].clone() - inner_remaining.clone()));

        let mut mismatches = Vec::with_capacity(NAMESPACE_MISMATCHES);
        mismatches.push(namespace_len.clone() - m31_const::<E>(self.spec.namespace.len()));
        for chunk_index in 0..NAMESPACE_PACKS {
            let start = chunk_index * NAMESPACE_PACK_BYTES;
            let mut actual = zero.clone();
            let mut expected = 0usize;
            for byte_index in
                start..(start + NAMESPACE_PACK_BYTES).min(MDOC_MAX_PUBLIC_NAMESPACE_BYTES)
            {
                actual = actual * m31_const::<E>(256) + bytes[2 + byte_index].clone();
                expected = expected * 256
                    + usize::from(
                        self.spec
                            .namespace
                            .as_bytes()
                            .get(byte_index)
                            .copied()
                            .unwrap_or(0),
                    );
            }
            mismatches.push(actual - m31_const::<E>(expected));
        }
        let mut mismatch_witness = zero.clone();
        for (difference, inverse) in mismatches.iter().zip(&namespace_mismatch_inv) {
            eval.add_constraint(ns_match.clone() * difference.clone());
            mismatch_witness += difference.clone() * inverse.clone();
        }
        eval.add_constraint(mismatch_witness - namespace.clone() + ns_match.clone());

        let digest_kind_sum = digest_kind
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, value| sum + value);
        eval.add_constraint(digest_kind_sum - digest.clone());
        let encoding_len_expected = digest_kind
            .iter()
            .zip([1usize, 2, 3])
            .fold(zero.clone(), |sum, (selector, len)| {
                sum + m31_const::<E>(len) * selector.clone()
            });
        eval.add_constraint(digest_encoding_len.clone() - encoding_len_expected);
        eval.add_constraint(
            digest.clone() * (bytes[DIGEST_ID_ENCODING_BYTES].clone() - m31_const::<E>(0x58)),
        );
        eval.add_constraint(
            digest.clone() * (bytes[DIGEST_ID_ENCODING_BYTES + 1].clone() - m31_const::<E>(0x20)),
        );
        let digest_slack = bit_sum::<E>(&digest_canonical_slack_bits);
        eval.add_constraint(
            digest_kind[0].clone() * (bytes[0].clone() + digest_slack.clone() - m31_const::<E>(23)),
        );
        eval.add_constraint(digest_kind[0].clone() * (digest_id_lo.clone() - bytes[0].clone()));
        eval.add_constraint(digest_kind[1].clone() * (bytes[0].clone() - m31_const::<E>(0x18)));
        eval.add_constraint(
            digest_kind[1].clone() * (bytes[1].clone() - m31_const::<E>(24) - digest_slack.clone()),
        );
        eval.add_constraint(digest_kind[1].clone() * (digest_id_lo.clone() - bytes[1].clone()));
        eval.add_constraint(digest_kind[2].clone() * (bytes[0].clone() - m31_const::<E>(0x19)));
        eval.add_constraint(
            digest_kind[2].clone() * (bytes[1].clone() - one.clone() - digest_slack.clone()),
        );
        eval.add_constraint(
            digest_kind[2].clone()
                * (digest_id_lo.clone()
                    - m31_const::<E>(256) * bytes[1].clone()
                    - bytes[2].clone()),
        );
        for (kind, len) in [1usize, 2, 3].into_iter().enumerate() {
            for byte in bytes.iter().take(DIGEST_ID_ENCODING_BYTES).skip(len) {
                eval.add_constraint(digest_kind[kind].clone() * byte.clone());
            }
        }

        eval.add_constraint(first.clone() * (sorted_active.clone() - one.clone()));
        eval.add_constraint(
            (one.clone() - last)
                * sorted_active_next.clone()
                * (one.clone() - sorted_active.clone()),
        );
        let sorted_nonfirst = sorted_active.clone() - first.clone();
        eval.add_constraint(
            sorted_namespace_gt.clone() + sorted_namespace_eq.clone() - sorted_nonfirst,
        );
        let namespace_diff = bit_sum::<E>(&sorted_namespace_diff_bits);
        eval.add_constraint(
            sorted_namespace_gt.clone()
                * (sorted_namespace.clone()
                    - sorted_namespace_prev.clone()
                    - one.clone()
                    - namespace_diff),
        );
        eval.add_constraint(
            sorted_namespace_eq.clone() * (sorted_namespace.clone() - sorted_namespace_prev),
        );
        let id_diff = bit_sum::<E>(&sorted_id_diff_bits);
        eval.add_constraint(
            sorted_namespace_eq * (sorted_id.clone() - sorted_id_prev - one.clone() - id_diff),
        );

        for site in 0..BYTE_SITES {
            eval.add_to_relation(RelationEntry::new(
                &self.issuer_relation,
                E::EF::from(byte_active[site].clone()),
                &[
                    m31_const::<E>(HOSTED_MSG_FIELD_ID as usize),
                    mso_start.clone() + cursor.clone() + byte_offset[site].clone(),
                    bytes[site].clone(),
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::new(
            &self.mso_start_relation,
            E::EF::from(head.clone()),
            &[mso_start],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.id_multiset_relation,
            E::EF::from(digest.clone()),
            &[namespace_index, digest_id_lo.clone(), zero.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.id_multiset_relation,
            -E::EF::from(sorted_active),
            &[sorted_namespace, sorted_id, zero.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.item_id_relation,
            E::EF::from(selected.clone()),
            // The fixed profile sets both unused bytes and the high limb to zero.
            &[
                digest_encoding_len,
                bytes[0].clone(),
                bytes[1].clone(),
                bytes[2].clone(),
                zero.clone(),
                zero,
                digest_id_lo,
                m31_const::<E>(0),
            ],
        ));
        let digest_values: [E::F; 32] =
            std::array::from_fn(|index| bytes[DIGEST_BYTES_START + index].clone());
        eval.add_to_relation(RelationEntry::new(
            &self.digest_relation,
            E::EF::from(selected),
            &digest_values,
        ));
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

struct ScanInteractionInputs<'a> {
    issuer_relation: &'a FieldBytesRelation,
    mso_start_relation: &'a MdocMsoStartRelation,
    id_multiset_relation: &'a MdocValueDigestIdMultisetRelation,
    item_id_relation: &'a MdocPrivateDigestIdRelation,
    digest_relation: &'a DigestBytesRelation,
    blinder_relation: &'a ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

fn interaction_trace(
    witness: &MdocValueDigestsWitnessTrace,
    inputs: ScanInteractionInputs<'_>,
) -> (Vec<Column>, QM31) {
    let base = witness.trace();
    let packed_rows = 1usize << (MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(MAIN_RELATION_SITES);
    for site in 0..BYTE_SITES {
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    (
                        PackedQM31::from(base[trace_col::BYTE_ACTIVE + site].data[row]),
                        inputs.issuer_relation.combine(&[
                            PackedM31::broadcast(m31_u32(HOSTED_MSG_FIELD_ID)),
                            base[trace_col::MSO_START].data[row]
                                + base[trace_col::CURSOR].data[row]
                                + base[trace_col::BYTE_OFFSET + site].data[row],
                            base[trace_col::BYTE + site].data[row],
                        ]),
                    )
                })
                .collect(),
        );
    }
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    PackedQM31::from(base[trace_col::HEAD].data[row]),
                    inputs
                        .mso_start_relation
                        .combine(&[base[trace_col::MSO_START].data[row]]),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    PackedQM31::from(base[trace_col::DIGEST].data[row]),
                    inputs.id_multiset_relation.combine(&[
                        base[trace_col::NAMESPACE_INDEX].data[row],
                        base[trace_col::DIGEST_ID_LO].data[row],
                        PackedM31::broadcast(m31(0)),
                    ]),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    -PackedQM31::from(base[trace_col::SORTED_ACTIVE].data[row]),
                    inputs.id_multiset_relation.combine(&[
                        base[trace_col::SORTED_NAMESPACE].data[row],
                        base[trace_col::SORTED_ID].data[row],
                        PackedM31::broadcast(m31(0)),
                    ]),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                (
                    PackedQM31::from(base[trace_col::SELECTED].data[row]),
                    inputs.item_id_relation.combine(&[
                        base[trace_col::DIGEST_ENCODING_LEN].data[row],
                        base[trace_col::BYTE].data[row],
                        base[trace_col::BYTE + 1].data[row],
                        base[trace_col::BYTE + 2].data[row],
                        PackedM31::broadcast(m31(0)),
                        PackedM31::broadcast(m31(0)),
                        base[trace_col::DIGEST_ID_LO].data[row],
                        PackedM31::broadcast(m31(0)),
                    ]),
                )
            })
            .collect(),
    );
    sites.push(
        (0..packed_rows)
            .map(|row| {
                let values: [PackedM31; 32] = std::array::from_fn(|index| {
                    base[trace_col::BYTE + DIGEST_BYTES_START + index].data[row]
                });
                (
                    PackedQM31::from(base[trace_col::SELECTED].data[row]),
                    inputs.digest_relation.combine(&values),
                )
            })
            .collect(),
    );
    let blinder_numerator = PackedQM31::broadcast(inputs.blinder_m);
    let blinder_denominator = blinder_denominator(inputs.blinder_relation, inputs.blinder_v);
    sites.push(vec![(blinder_numerator, blinder_denominator); packed_rows]);
    debug_assert_eq!(sites.len(), MAIN_RELATION_SITES);

    // Mirrors `finalize_logup_batched(LOGUP_BATCH)`'s recursive fraction fold exactly
    // (`num = num*d + n*den; den = den*d`, left-to-right over the chunk).
    let mut logup = LogupTraceGenerator::new(MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE);
    let mut site = 0usize;
    while site < sites.len() {
        let end = (site + LOGUP_BATCH).min(sites.len());
        let chunk = &sites[site..end];
        logup.col_from_iter((0..packed_rows).map(|row| {
            let mut iter = chunk.iter().map(|s| s[row]);
            let (mut num, mut den) = iter.next().unwrap();
            for (n, d) in iter {
                num = num * d + n * den;
                den *= d;
            }
            (num, den)
        }));
        site = end;
    }
    logup.finalize_last()
}

pub(crate) struct MdocValueDigestsScan {
    spec: MdocValueDigestsScanSpec,
    handles: MdocValueDigestsScanHandles,
    witness: Option<MdocValueDigestsWitnessTrace>,
    id_multiset_relation: Option<MdocValueDigestIdMultisetRelation>,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocValueDigestsInteractionClaim>,
    component: Option<ScanComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocValueDigestsScan {
    pub(crate) fn prover(
        spec: MdocValueDigestsScanSpec,
        witness: MdocValueDigestsScanWitness,
        handles: MdocValueDigestsScanHandles,
    ) -> Result<(Self, MdocValueDigestsUseCensus), MdocValueDigestsScanError> {
        validate_spec(&spec)?;
        if witness.issuer_message.len() != spec.issuer_message_len {
            return Err(MdocValueDigestsScanError::IssuerMessageLengthMismatch {
                expected: spec.issuer_message_len,
                actual: witness.issuer_message.len(),
            });
        }
        let mso_end = witness.mso_start.checked_add(spec.mso_len).ok_or(
            MdocValueDigestsScanError::MsoOutOfBounds {
                start: witness.mso_start,
                length: spec.mso_len,
                issuer_message_len: spec.issuer_message_len,
            },
        )?;
        let mso = witness
            .issuer_message
            .get(witness.mso_start..mso_end)
            .ok_or(MdocValueDigestsScanError::MsoOutOfBounds {
                start: witness.mso_start,
                length: spec.mso_len,
                issuer_message_len: spec.issuer_message_len,
            })?;
        let (parsed, rows) =
            select_value_digests(mso, spec.namespace.as_bytes(), &witness.selected_digest)?;
        debug_assert_eq!(
            rows.len(),
            1 + parsed.namespaces.len() + parsed.digest_entries
        );
        let (trace, census) = build_trace(&spec, &witness, rows)?;
        Ok((
            Self {
                spec,
                handles,
                witness: Some(trace),
                id_multiset_relation: None,
                blinder_relation: None,
                interaction_claim: None,
                component: None,
                blinder_component: None,
            },
            census,
        ))
    }

    pub(crate) fn verifier(
        spec: MdocValueDigestsScanSpec,
        handles: MdocValueDigestsScanHandles,
        interaction_claim: MdocValueDigestsInteractionClaim,
    ) -> Result<Self, MdocValueDigestsScanError> {
        validate_spec(&spec)?;
        Ok(Self {
            spec,
            handles,
            witness: None,
            id_multiset_relation: None,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        })
    }

    pub(crate) fn claim(&self) -> &MdocValueDigestsInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("valueDigests scanner interaction claim is set")
    }

    fn issuer_relation(&self) -> FieldBytesRelation {
        self.handles.issuer_message.get()
    }

    fn mso_start_relation(&self) -> MdocMsoStartRelation {
        self.handles.mso_start.get()
    }

    fn item_id_relation(&self) -> MdocPrivateDigestIdRelation {
        self.handles.item.digest_id.get()
    }

    fn digest_relation(&self) -> DigestBytesRelation {
        self.handles.item.digest.get()
    }

    fn id_multiset_relation(&self) -> MdocValueDigestIdMultisetRelation {
        self.id_multiset_relation
            .clone()
            .expect("valueDigests scanner ID multiset relation is drawn")
    }
}

impl Air for MdocValueDigestsScan {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(SCAN_DOMAIN);
        channel.mix_u64(SCAN_VERSION);
        channel.mix_u64(SCAN_TRANSCRIPT_TAG);
        channel.mix_u64(self.spec.issuer_message_len as u64);
        channel.mix_u64(self.spec.mso_len as u64);
        channel.mix_u64(TS13_SELECTED_ATTRIBUTE_COUNT as u64);
        channel.mix_u64(self.spec.namespace.len() as u64);
        for &byte in self.spec.namespace.as_bytes() {
            channel.mix_u64(u64::from(byte));
        }
        channel.mix_u64(MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE as u64);
        channel.mix_u64(MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS as u64);
        channel.mix_u64(MDOC_MAX_PUBLIC_NAMESPACE_BYTES as u64);
        channel.mix_u64(PREPROCESSED_COLS as u64);
        channel.mix_u64(TRACE_COLS as u64);
        channel.mix_u64(MAIN_RELATION_SITES as u64);
        channel.mix_u64(INTERACTION_COLS as u64);
        channel.mix_u64(u64::from(MDOC_PRIVATE_ITEM_DIGEST_ID_MAX));
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.id_multiset_relation = Some(MdocValueDigestIdMultisetRelation::draw(channel));
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE; PREPROCESSED_COLS],
            trace: vec![MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE; TRACE_COLS],
            interaction: vec![MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE; INTERACTION_COLS],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(&self.spec)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns(&self.spec))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("valueDigests scanner blinder relation is drawn");
        self.component = Some(ScanComponent::new(
            allocator,
            MdocValueDigestsScanEval {
                spec: self.spec.clone(),
                issuer_relation: self.issuer_relation(),
                mso_start_relation: self.mso_start_relation(),
                id_multiset_relation: self.id_multiset_relation(),
                item_id_relation: self.item_id_relation(),
                digest_relation: self.digest_relation(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE,
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
                .expect("valueDigests scanner component is built"),
            self.blinder_component
                .as_ref()
                .expect("valueDigests scanner blinder component is built"),
        ]
    }
}

impl AirProver for MdocValueDigestsScan {
    fn max_log_size(&self) -> u32 {
        MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
    }

    fn write_preprocessed(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tree, &preprocessed_ids(&self.spec));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_value_digests_scan::MdocValueDigestsScan",
            &preprocessed_ids(&self.spec),
            &preprocessed_columns(&self.spec),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tree: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let ids = preprocessed_ids(&self.spec);
        let columns = preprocessed_columns(&self.spec);
        tree.extend_evals(
            selected_ids
                .iter()
                .map(|id| {
                    ids.iter()
                        .position(|candidate| candidate == id)
                        .map(|index| columns[index].clone())
                        .expect("unexpected valueDigests scanner preprocessed selection")
                })
                .collect(),
        );
    }

    fn write_trace(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tree.extend_evals(
            self.witness
                .as_ref()
                .expect("valueDigests scanner prover has a witness")
                .trace(),
        );
    }

    fn write_interaction(&mut self, tree: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("valueDigests scanner blinder relation is drawn");
        let issuer_relation = self.issuer_relation();
        let mso_start_relation = self.mso_start_relation();
        let id_multiset_relation = self.id_multiset_relation();
        let item_id_relation = self.item_id_relation();
        let digest_relation = self.digest_relation();
        let (interaction, claimed_sum) = interaction_trace(
            self.witness
                .as_ref()
                .expect("valueDigests scanner prover has a witness"),
            ScanInteractionInputs {
                issuer_relation: &issuer_relation,
                mso_start_relation: &mso_start_relation,
                id_multiset_relation: &id_multiset_relation,
                item_id_relation: &item_id_relation,
                digest_relation: &digest_relation,
                blinder_relation: &blinder_relation,
                blinder_v,
                blinder_m,
            },
        );
        tree.extend_evals(interaction);
        let (blinder_trace, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_VALUE_DIGESTS_SCAN_LOG_SIZE,
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tree.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocValueDigestsInteractionClaim {
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
                .expect("valueDigests scanner component is built"),
            self.blinder_component
                .as_ref()
                .expect("valueDigests scanner blinder component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use crate::mdoc_real_vectors::real_mdoc_vectors;
    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    const REQUESTED_NAMESPACE: &str = "org.iso.18013.5.1";

    fn qm31(value: u32) -> QM31 {
        QM31::from(m31_u32(value))
    }

    fn digest(seed: u8) -> [u8; 32] {
        std::array::from_fn(|index| seed.wrapping_add(index as u8))
    }

    fn push_head(output: &mut Vec<u8>, major: u8, value: usize) {
        match value {
            0..=23 => output.push((major << 5) | value as u8),
            24..=255 => {
                output.push((major << 5) | 24);
                output.push(value as u8);
            }
            256..=65_535 => {
                output.push((major << 5) | 25);
                output.extend_from_slice(&(value as u16).to_be_bytes());
            }
            _ => panic!("test CBOR argument {value} is unsupported"),
        }
    }

    fn push_text(output: &mut Vec<u8>, value: &[u8]) {
        push_head(output, 3, value.len());
        output.extend_from_slice(value);
    }

    fn push_uint(output: &mut Vec<u8>, value: u32) {
        match value {
            0..=23 => output.push(value as u8),
            24..=0xff => output.extend_from_slice(&[0x18, value as u8]),
            0x100..=0xffff => {
                output.push(0x19);
                output.extend_from_slice(&(value as u16).to_be_bytes());
            }
            _ => {
                output.push(0x1a);
                output.extend_from_slice(&value.to_be_bytes());
            }
        }
    }

    fn push_entry(output: &mut Vec<u8>, id: u32, value: &[u8; 32]) {
        push_uint(output, id);
        output.extend_from_slice(&[0x58, 0x20]);
        output.extend_from_slice(value);
    }

    type TestNamespaceDigests = (Vec<u8>, Vec<(u32, [u8; 32])>);

    fn encode_value_digests(namespaces: &[TestNamespaceDigests]) -> Vec<u8> {
        // The leading map head makes the anchor look like its canonical MSO
        // key position while remaining irrelevant to the narrow scanner.
        let mut output = vec![0xa1];
        output.extend_from_slice(VALUE_DIGESTS_KEY);
        push_head(&mut output, 5, namespaces.len());
        for (namespace, entries) in namespaces {
            push_text(&mut output, namespace);
            push_head(&mut output, 5, entries.len());
            for (id, value) in entries {
                push_entry(&mut output, *id, value);
            }
        }
        output
    }

    fn encode_single_namespace_with_heads(
        outer_map_head: &[u8],
        namespace_text_head: &[u8],
        inner_map_head: &[u8],
    ) -> Vec<u8> {
        let mut output = vec![0xa1];
        output.extend_from_slice(VALUE_DIGESTS_KEY);
        output.extend_from_slice(outer_map_head);
        output.extend_from_slice(namespace_text_head);
        output.extend_from_slice(REQUESTED_NAMESPACE.as_bytes());
        output.extend_from_slice(inner_map_head);
        push_entry(&mut output, 7, &digest(0x20));
        output
    }

    fn with_value_digests_tail(tail: &[u8]) -> Vec<u8> {
        let mut output = vec![0xa1];
        output.extend_from_slice(VALUE_DIGESTS_KEY);
        output.extend_from_slice(tail);
        output
    }

    fn parse_value_digests(mso: &[u8]) -> Result<ParsedValueDigests, MdocValueDigestsScanError> {
        let offset = mso
            .windows(VALUE_DIGESTS_KEY.len())
            .position(|bytes| bytes == VALUE_DIGESTS_KEY)
            .ok_or_else(|| {
                canonical_error(0, MsoValueDigestsCanonicalityReason::MissingValueDigests)
            })?;
        parse_value_digests_at(mso, offset)
    }

    fn handles() -> MdocValueDigestsScanHandles {
        MdocValueDigestsScanHandles {
            issuer_message: SharedFieldRelation::new(),
            mso_start: SharedMdocMsoStartRelation::new(),
            item: MdocValueDigestItemHandles {
                digest_id: SharedMdocPrivateDigestIdRelation::new(),
                digest: SharedDigestRelation::new(),
            },
        }
    }

    fn scanner_for_mso(
        mso: Vec<u8>,
        namespace: &str,
        selected_digest: MdocSelectedValueDigest,
    ) -> Result<(MdocValueDigestsScan, MdocValueDigestsUseCensus), MdocValueDigestsScanError> {
        let mso_start = 3;
        let mut issuer_message = vec![0x55; mso_start];
        issuer_message.extend_from_slice(&mso);
        let spec = MdocValueDigestsScanSpec {
            issuer_message_len: issuer_message.len(),
            mso_len: mso.len(),
            namespace: namespace.to_owned(),
        };
        MdocValueDigestsScan::prover(
            spec,
            MdocValueDigestsScanWitness {
                issuer_message,
                mso_start,
                selected_digest,
            },
            handles(),
        )
    }

    fn fixture() -> (
        MdocValueDigestsScan,
        MdocValueDigestsUseCensus,
        MdocValueDigestsScanWitness,
    ) {
        let requested_first = digest(0x20);
        let requested_second = digest(0x60);
        let mso = encode_value_digests(&[
            (b"org.example.extra".to_vec(), vec![(7, digest(0xa0))]),
            (
                REQUESTED_NAMESPACE.as_bytes().to_vec(),
                vec![(7, requested_first), (u16::MAX as u32, requested_second)],
            ),
        ]);
        let mso_start = 5;
        let mut issuer_message = vec![0x55; mso_start];
        issuer_message.extend_from_slice(&mso);
        issuer_message.extend_from_slice(&[0xaa; 3]);
        let selected_digest = MdocSelectedValueDigest {
            digest_id: u16::MAX as u32,
            digest: requested_second,
        };
        let spec = MdocValueDigestsScanSpec {
            issuer_message_len: issuer_message.len(),
            mso_len: mso.len(),
            namespace: REQUESTED_NAMESPACE.to_owned(),
        };
        let witness = MdocValueDigestsScanWitness {
            issuer_message,
            mso_start,
            selected_digest,
        };
        let (scan, census) =
            MdocValueDigestsScan::prover(spec, witness.clone(), handles()).unwrap();
        (scan, census, witness)
    }

    fn canonical_reason(error: MdocValueDigestsScanError) -> MsoValueDigestsCanonicalityReason {
        match error {
            MdocValueDigestsScanError::MsoValueDigestsNotCanonical { reason, .. } => reason,
            other => panic!("expected canonicality error, got {other:?}"),
        }
    }

    fn scanner_error(
        result: Result<
            (MdocValueDigestsScan, MdocValueDigestsUseCensus),
            MdocValueDigestsScanError,
        >,
    ) -> MdocValueDigestsScanError {
        match result {
            Ok(_) => panic!("expected valueDigests scanner construction to fail"),
            Err(error) => error,
        }
    }

    #[test]
    fn canonical_multi_namespace_scan_selects_only_the_requested_namespace() {
        let (scan, census, witness) = fixture();
        assert_eq!(census.active_rows, 6);
        assert_eq!(census.blind_rows, MDOC_VALUE_DIGESTS_SCAN_ROWS - 6);
        assert_eq!(census.namespaces, 2);
        assert_eq!(census.digest_entries, 3);
        assert_eq!(
            census.issuer_uses_total,
            census
                .issuer_position_uses
                .iter()
                .map(|&uses| uses as usize)
                .sum::<usize>()
        );
        assert!(census.issuer_position_uses[..witness.mso_start]
            .iter()
            .all(|&uses| uses == 0));
        let trace = scan.witness.as_ref().unwrap();
        let selected_rows = (0..MDOC_VALUE_DIGESTS_SCAN_ROWS)
            .filter(|&row| trace.columns[trace_col::SELECTED][row] == m31(1))
            .collect::<Vec<_>>();
        assert_eq!(selected_rows.len(), 1);
        assert!(selected_rows
            .iter()
            .all(|&row| trace.columns[trace_col::NAMESPACE_INDEX][row] == m31(1)));
    }

    #[test]
    fn viable_candidate_selection_ignores_inert_and_wrong_namespace_decoys() {
        let selected_digest_bytes = digest(0x20);
        let selected_digest = MdocSelectedValueDigest {
            digest_id: 7,
            digest: selected_digest_bytes,
        };
        let actual = encode_value_digests(&[(
            REQUESTED_NAMESPACE.as_bytes().to_vec(),
            vec![(7, selected_digest_bytes)],
        )]);

        let mut inert_then_actual = VALUE_DIGESTS_KEY.to_vec();
        inert_then_actual.push(0xff);
        let actual_offset = inert_then_actual.len() + 1;
        inert_then_actual.extend_from_slice(&actual);
        let (scan, _) = scanner_for_mso(
            inert_then_actual,
            REQUESTED_NAMESPACE,
            selected_digest.clone(),
        )
        .unwrap();
        assert_eq!(scan.witness.as_ref().unwrap().rows[0].cursor, actual_offset);
        assert_trace_satisfies_air(&scan);

        let wrong = encode_value_digests(&[(
            b"org.example.wrong".to_vec(),
            vec![(7, selected_digest_bytes)],
        )]);
        let actual_offset = wrong.len() + 1;
        let mut wrong_then_actual = wrong;
        wrong_then_actual.extend_from_slice(&actual);
        let (scan, _) =
            scanner_for_mso(wrong_then_actual, REQUESTED_NAMESPACE, selected_digest).unwrap();
        assert_eq!(scan.witness.as_ref().unwrap().rows[0].cursor, actual_offset);
        assert_trace_satisfies_air(&scan);
    }

    #[test]
    fn viable_candidate_selection_rejects_a_second_viable_subtree() {
        let selected_digest = digest(0x20);
        let actual = encode_value_digests(&[(
            REQUESTED_NAMESPACE.as_bytes().to_vec(),
            vec![(7, selected_digest)],
        )]);
        let second_offset = actual.len() + 1;
        let mut two_viable = actual.clone();
        two_viable.extend_from_slice(&actual);
        assert_eq!(
            scanner_error(scanner_for_mso(
                two_viable,
                REQUESTED_NAMESPACE,
                MdocSelectedValueDigest {
                    digest_id: 7,
                    digest: selected_digest,
                },
            )),
            canonical_error(
                second_offset,
                MsoValueDigestsCanonicalityReason::AmbiguousValueDigests,
            )
        );
    }

    #[test]
    fn candidate_selection_preserves_missing_and_single_malformed_errors() {
        let selected_digest = MdocSelectedValueDigest {
            digest_id: 7,
            digest: digest(0x20),
        };
        assert_eq!(
            scanner_error(scanner_for_mso(
                vec![0xa0],
                REQUESTED_NAMESPACE,
                selected_digest.clone(),
            )),
            canonical_error(0, MsoValueDigestsCanonicalityReason::MissingValueDigests)
        );

        let mut malformed = vec![0xaa, 0xbb];
        malformed.extend_from_slice(VALUE_DIGESTS_KEY);
        malformed.push(0xbf);
        assert_eq!(
            scanner_error(scanner_for_mso(
                malformed,
                REQUESTED_NAMESPACE,
                selected_digest,
            )),
            canonical_error(
                2 + VALUE_DIGESTS_KEY.len(),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            )
        );
    }

    #[test]
    fn prover_rejects_missing_namespace_and_noncanonical_heads_or_keys() {
        let selected_digest = MdocSelectedValueDigest {
            digest_id: 7,
            digest: digest(0x20),
        };
        let wrong_namespace = encode_value_digests(&[(
            b"org.example.wrong".to_vec(),
            vec![(7, selected_digest.digest)],
        )]);
        assert_eq!(
            scanner_error(scanner_for_mso(
                wrong_namespace.clone(),
                REQUESTED_NAMESPACE,
                selected_digest.clone(),
            )),
            MdocValueDigestsScanError::RequestedNamespaceMissing
        );

        let mut inert_then_wrong = VALUE_DIGESTS_KEY.to_vec();
        inert_then_wrong.push(0xff);
        inert_then_wrong.extend_from_slice(&wrong_namespace);
        assert_eq!(
            scanner_error(scanner_for_mso(
                inert_then_wrong,
                REQUESTED_NAMESPACE,
                selected_digest.clone(),
            )),
            MdocValueDigestsScanError::RequestedNamespaceMissing,
            "an inert malformed decoy must not mask the first semantic candidate error"
        );

        let mut nonminimal_value_digests_key = vec![0xa1, 0x78, 0x0c];
        nonminimal_value_digests_key.extend_from_slice(b"valueDigests");
        nonminimal_value_digests_key.push(0xa0);
        let mut indefinite_value_digests_key = vec![0xa1, 0x7f];
        indefinite_value_digests_key.extend_from_slice(VALUE_DIGESTS_KEY);
        indefinite_value_digests_key.extend_from_slice(&[0xff, 0xa0]);
        for (mso, expected) in [
            (
                nonminimal_value_digests_key,
                MsoValueDigestsCanonicalityReason::MissingValueDigests,
            ),
            (
                indefinite_value_digests_key,
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                encode_single_namespace_with_heads(
                    &[0xbf],
                    &[0x60 + REQUESTED_NAMESPACE.len() as u8],
                    &[0xa1],
                ),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                encode_single_namespace_with_heads(
                    &[0xb8, 0x01],
                    &[0x60 + REQUESTED_NAMESPACE.len() as u8],
                    &[0xa1],
                ),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                encode_single_namespace_with_heads(&[0xa1], &[0x7f], &[0xa1]),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
            ),
            (
                encode_single_namespace_with_heads(
                    &[0xa1],
                    &[0x78, REQUESTED_NAMESPACE.len() as u8],
                    &[0xa1],
                ),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
            ),
            (
                encode_single_namespace_with_heads(
                    &[0xa1],
                    &[0x60 + REQUESTED_NAMESPACE.len() as u8],
                    &[0xbf],
                ),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                encode_single_namespace_with_heads(
                    &[0xa1],
                    &[0x60 + REQUESTED_NAMESPACE.len() as u8],
                    &[0xb8, 0x01],
                ),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
        ] {
            assert_eq!(
                canonical_reason(scanner_error(scanner_for_mso(
                    mso,
                    REQUESTED_NAMESPACE,
                    selected_digest.clone(),
                ))),
                expected
            );
        }
    }

    #[test]
    fn canonicality_rejection_matrix_is_typed() {
        let mut digest_bytes = vec![0x58, 0x20];
        digest_bytes.extend_from_slice(&digest(1));

        let cases = [
            (
                with_value_digests_tail(&[0xbf]),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                with_value_digests_tail(&[0xb8, 0x01, 0x61, b'a', 0xa0]),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                with_value_digests_tail(&[0xa1, 0x01, 0xa0]),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
            ),
            (
                with_value_digests_tail(&[0xa1, 0x78, 0x01, b'a', 0xa0]),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteText,
            ),
            (
                with_value_digests_tail(&[0xa1, 0x61, 0xff, 0xa0]),
                MsoValueDigestsCanonicalityReason::InvalidUtf8,
            ),
            (
                with_value_digests_tail(&[0xa2, 0x61, b'a', 0xa0, 0x61, b'a', 0xa0]),
                MsoValueDigestsCanonicalityReason::DuplicateNamespace,
            ),
            (
                with_value_digests_tail(&[0xa1, 0x61, b'a', 0xbf]),
                MsoValueDigestsCanonicalityReason::ExpectedDefiniteMap,
            ),
            (
                {
                    let mut tail = vec![0xa1, 0x61, b'a', 0xa1, 0x18, 0x01];
                    tail.extend_from_slice(&digest_bytes);
                    with_value_digests_tail(&tail)
                },
                MsoValueDigestsCanonicalityReason::ExpectedCanonicalDigestId,
            ),
            (
                with_value_digests_tail(&[0xa1, 0x61, b'a', 0xa1, 0x00, 0x40]),
                MsoValueDigestsCanonicalityReason::ExpectedDigestBstr32,
            ),
            (
                {
                    let mut tail = vec![0xa1, 0x61, b'a', 0xa2];
                    push_entry(&mut tail, 7, &digest(1));
                    push_entry(&mut tail, 7, &digest(2));
                    with_value_digests_tail(&tail)
                },
                MsoValueDigestsCanonicalityReason::DuplicateDigestId,
            ),
            (
                {
                    let mut tail = vec![0xa1, 0x78, 33];
                    tail.extend_from_slice(&[b'x'; 33]);
                    tail.push(0xa0);
                    with_value_digests_tail(&tail)
                },
                MsoValueDigestsCanonicalityReason::NamespaceTooLong {
                    length: 33,
                    max: MDOC_MAX_PUBLIC_NAMESPACE_BYTES,
                },
            ),
        ];
        for (mso, expected) in cases {
            assert_eq!(
                canonical_reason(parse_value_digests(&mso).unwrap_err()),
                expected
            );
        }
    }

    #[test]
    fn digest_and_scan_item_caps_are_exact() {
        let at_digest_cap =
            encode_value_digests(&[(b"a".to_vec(), vec![(u16::MAX as u32, digest(1))])]);
        assert_eq!(
            parse_value_digests(&at_digest_cap).unwrap().namespaces[0].digests[0].id,
            u16::MAX as u32
        );

        let too_large =
            encode_value_digests(&[(b"a".to_vec(), vec![(u16::MAX as u32 + 1, digest(1))])]);
        assert_eq!(
            canonical_reason(parse_value_digests(&too_large).unwrap_err()),
            MsoValueDigestsCanonicalityReason::DigestIdOutOfRange {
                value: u16::MAX as u64 + 1,
                max: u16::MAX as u32,
            }
        );

        let namespaces = (0..MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS)
            .map(|index| (format!("n{index:03}").into_bytes(), Vec::new()))
            .collect::<Vec<_>>();
        let at_cap = encode_value_digests(&namespaces);
        let parsed = parse_value_digests(&at_cap).unwrap();
        assert_eq!(parsed.namespaces.len(), MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS);
        assert_eq!(parsed.digest_entries, 0);

        let over_cap = with_value_digests_tail(&[0xb9, 0x01, 0x00]);
        assert_eq!(
            parse_value_digests(&over_cap).unwrap_err(),
            MdocValueDigestsScanError::ScanItemCapExceeded {
                items: MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS + 1,
                max: MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS,
            }
        );
    }

    #[test]
    fn requested_namespace_and_selected_digest_are_bound_exactly() {
        let target_digest = digest(4);
        let extra_digest = digest(8);
        let mso = encode_value_digests(&[
            (b"extra".to_vec(), vec![(9, extra_digest)]),
            (
                REQUESTED_NAMESPACE.as_bytes().to_vec(),
                vec![(9, target_digest)],
            ),
        ]);
        let parsed = parse_value_digests(&mso).unwrap();
        build_rows(
            &parsed,
            REQUESTED_NAMESPACE.as_bytes(),
            &MdocSelectedValueDigest {
                digest_id: 9,
                digest: target_digest,
            },
        )
        .expect("same ID in an extra namespace must not collide");
        assert_eq!(
            build_rows(
                &parsed,
                REQUESTED_NAMESPACE.as_bytes(),
                &MdocSelectedValueDigest {
                    digest_id: 9,
                    digest: extra_digest,
                },
            )
            .unwrap_err(),
            MdocValueDigestsScanError::RequestedDigestMissing
        );
        assert_eq!(
            build_rows(
                &parsed,
                b"missing.namespace",
                &MdocSelectedValueDigest {
                    digest_id: 9,
                    digest: target_digest,
                },
            )
            .unwrap_err(),
            MdocValueDigestsScanError::RequestedNamespaceMissing
        );
    }

    #[test]
    fn every_fixed_real_mso_namespace_is_accepted() {
        for vector in real_mdoc_vectors() {
            let parsed = parse_value_digests(&vector.mso)
                .unwrap_or_else(|error| panic!("{}: {error}", vector.source));
            assert_eq!(
                parsed
                    .namespaces
                    .iter()
                    .map(|namespace| (namespace.name.as_slice(), namespace.digests.len()))
                    .collect::<Vec<_>>(),
                vector
                    .namespaces
                    .iter()
                    .map(|namespace| (namespace.name.as_bytes(), namespace.digest_count))
                    .collect::<Vec<_>>(),
                "{}",
                vector.source
            );
            for namespace in &parsed.namespaces {
                let selected = namespace
                    .digests
                    .first()
                    .unwrap_or_else(|| panic!("{}: empty real namespace", vector.source));
                let mso_start = 3;
                let mut issuer_message = vec![0x55; mso_start];
                issuer_message.extend_from_slice(&vector.mso);
                let spec = MdocValueDigestsScanSpec {
                    issuer_message_len: issuer_message.len(),
                    mso_len: vector.mso.len(),
                    namespace: std::str::from_utf8(&namespace.name).unwrap().to_owned(),
                };
                let witness = MdocValueDigestsScanWitness {
                    issuer_message,
                    mso_start,
                    selected_digest: MdocSelectedValueDigest {
                        digest_id: selected.id,
                        digest: selected.digest,
                    },
                };
                let (scan, census) = MdocValueDigestsScan::prover(spec, witness, handles())
                    .unwrap_or_else(|error| {
                        panic!(
                            "{} namespace {:?}: {error}",
                            vector.source,
                            String::from_utf8_lossy(&namespace.name)
                        )
                    });
                assert_eq!(census.namespaces, vector.namespaces.len());
                assert_eq!(
                    census.digest_entries,
                    vector
                        .namespaces
                        .iter()
                        .map(|namespace| namespace.digest_count)
                        .sum::<usize>()
                );
                assert_trace_satisfies_air(&scan);
            }
        }
    }

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn for_row(
            trace: &MdocValueDigestsWitnessTrace,
            spec: &MdocValueDigestsScanSpec,
            row: usize,
        ) -> Self {
            let next = (row + 1) % MDOC_VALUE_DIGESTS_SCAN_ROWS;
            let previous = (row + MDOC_VALUE_DIGESTS_SCAN_ROWS - 1) % MDOC_VALUE_DIGESTS_SCAN_ROWS;
            let mut eval = Self::default();
            eval.preprocessed
                .push_back(vec![m31(usize::from(row == 0))]);
            eval.preprocessed.push_back(vec![m31(usize::from(
                row + 1 == MDOC_VALUE_DIGESTS_SCAN_ROWS,
            ))]);
            eval.preprocessed.push_back(vec![m31(usize::from(
                row <= MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS,
            ))]);
            eval.preprocessed
                .push_back(vec![namespace_material(spec.namespace.as_bytes())[row]]);

            let next_columns = [
                trace_col::ACTIVE,
                trace_col::NAMESPACE,
                trace_col::DIGEST,
                trace_col::ROW_LEN,
                trace_col::CURSOR,
                trace_col::MSO_START,
                trace_col::OUTER_REMAINING,
                trace_col::INNER_REMAINING,
                trace_col::NS_MATCH,
                trace_col::REQUESTED_SCOPE,
                trace_col::REQUESTED_COUNT,
                trace_col::SELECTED,
                trace_col::SELECTED_COUNT,
                trace_col::NAMESPACE_INDEX,
                trace_col::SORTED_ACTIVE,
            ];
            let previous_columns = [trace_col::SORTED_NAMESPACE, trace_col::SORTED_ID];
            for column in 0..trace_col::COUNT {
                let values = if next_columns.contains(&column) {
                    vec![trace.columns[column][row], trace.columns[column][next]]
                } else if previous_columns.contains(&column) {
                    vec![trace.columns[column][row], trace.columns[column][previous]]
                } else {
                    vec![trace.columns[column][row]]
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
                .filter(|(_, value)| *value != qm31(0))
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

        fn finalize_logup_batched(&mut self, _batch_size: usize) {}
    }

    fn test_eval(scan: &MdocValueDigestsScan) -> MdocValueDigestsScanEval {
        MdocValueDigestsScanEval {
            spec: scan.spec.clone(),
            issuer_relation: FieldBytesRelation::dummy(),
            mso_start_relation: MdocMsoStartRelation::dummy(),
            id_multiset_relation: MdocValueDigestIdMultisetRelation::dummy(),
            item_id_relation: MdocPrivateDigestIdRelation::dummy(),
            digest_relation: DigestBytesRelation::dummy(),
            blinder_relation: ClaimedSumBlinderRelation::dummy(),
            blinder_v: qm31(7),
            blinder_m: qm31(11),
        }
    }

    fn assert_trace_satisfies_air(scan: &MdocValueDigestsScan) {
        let trace = scan.witness.as_ref().unwrap();
        for row in 0..MDOC_VALUE_DIGESTS_SCAN_ROWS {
            let evaluated = test_eval(scan).evaluate(RowEval::for_row(trace, &scan.spec, row));
            let nonzero = evaluated.nonzero_constraints();
            assert!(
                nonzero.is_empty(),
                "honest scanner row {row} violates constraints: {nonzero:?}"
            );
        }
    }

    fn assert_mutated_row_rejected(
        scan: &MdocValueDigestsScan,
        trace: &MdocValueDigestsWitnessTrace,
        row: usize,
    ) {
        let evaluated = test_eval(scan).evaluate(RowEval::for_row(trace, &scan.spec, row));
        assert!(
            !evaluated.nonzero_constraints().is_empty(),
            "mutated scanner row {row} unexpectedly satisfies the AIR"
        );
    }

    fn hidden_duplicate_requested_namespace(
        scan: &MdocValueDigestsScan,
    ) -> (MdocValueDigestsWitnessTrace, usize) {
        let mut forged = scan.witness.as_ref().unwrap().clone();
        let duplicate_row = forged
            .rows
            .iter()
            .position(|row| {
                matches!(
                    &row.kind,
                    RowKind::Namespace {
                        requested: false,
                        ..
                    }
                )
            })
            .unwrap();
        assert_eq!(
            forged.columns[trace_col::NAMESPACE_LEN][duplicate_row],
            m31(REQUESTED_NAMESPACE.len())
        );
        for (index, byte) in REQUESTED_NAMESPACE.bytes().enumerate() {
            forged.columns[trace_col::BYTE + 2 + index][duplicate_row] = m31_u32(u32::from(byte));
        }

        let hidden_byte = REQUESTED_NAMESPACE.len();
        assert_eq!(hidden_byte % NAMESPACE_PACK_BYTES, NAMESPACE_PACK_BYTES - 1);
        forged.columns[trace_col::BYTE + 2 + hidden_byte][duplicate_row] = m31(1);
        for mismatch in 0..NAMESPACE_MISMATCHES {
            forged.columns[trace_col::NAMESPACE_MISMATCH_INV + mismatch][duplicate_row] = m31(0);
        }
        let hidden_pack = hidden_byte / NAMESPACE_PACK_BYTES;
        forged.columns[trace_col::NAMESPACE_MISMATCH_INV + 1 + hidden_pack][duplicate_row] = m31(1);
        (forged, duplicate_row)
    }

    fn forge_duplicate_digest_id(scan: &mut MdocValueDigestsScan, namespace_index: usize) -> usize {
        let trace = scan.witness.as_mut().unwrap();
        let raw_row = trace
            .rows
            .iter()
            .position(|row| {
                row.namespace_index == namespace_index
                    && matches!(&row.kind, RowKind::Digest { id: 3, .. })
            })
            .unwrap();
        assert_eq!(
            trace.columns[trace_col::DIGEST_ENCODING_LEN][raw_row],
            m31(1)
        );
        trace.columns[trace_col::BYTE][raw_row] = m31(2);
        trace.columns[trace_col::DIGEST_ID_LO][raw_row] = m31(2);
        write_bits(
            &mut trace.columns,
            trace_col::DIGEST_CANONICAL_SLACK_BITS,
            raw_row,
            21,
            DIGEST_CANONICAL_SLACK_BITS,
        );

        let sorted_row = (0..MDOC_VALUE_DIGESTS_SCAN_ROWS)
            .find(|&row| {
                trace.columns[trace_col::SORTED_ACTIVE][row] == m31(1)
                    && trace.columns[trace_col::SORTED_NAMESPACE][row] == m31(namespace_index)
                    && trace.columns[trace_col::SORTED_ID][row] == m31(3)
            })
            .unwrap();
        trace.columns[trace_col::SORTED_ID][sorted_row] = m31(2);
        sorted_row
    }

    #[test]
    fn honest_trace_satisfies_every_air_row() {
        let (scan, _, _) = fixture();
        assert_trace_satisfies_air(&scan);
    }

    #[test]
    fn air_rejects_unsupported_five_byte_digest_shape() {
        let (scan, _, _) = fixture();
        let mut forged = scan.witness.as_ref().unwrap().clone();
        let row = forged
            .rows
            .iter()
            .position(|row| {
                matches!(
                    row.kind,
                    RowKind::Digest {
                        id,
                        ..
                    } if id == u16::MAX as u32
                )
            })
            .unwrap();

        forged.columns[trace_col::DIGEST_ENCODING_LEN][row] = m31(5);
        assert_mutated_row_rejected(&scan, &forged, row);
    }

    #[test]
    fn air_rejects_cursor_namespace_digest_and_sorted_mutations() {
        let (scan, _, _) = fixture();
        let honest = scan.witness.as_ref().unwrap();

        let mut wrong_cursor = honest.clone();
        wrong_cursor.columns[trace_col::CURSOR][1] += m31(1);
        assert_mutated_row_rejected(&scan, &wrong_cursor, 0);

        let namespace_row = honest
            .rows
            .iter()
            .position(|row| {
                matches!(
                    &row.kind,
                    RowKind::Namespace {
                        requested: true,
                        ..
                    }
                )
            })
            .unwrap();
        let mut wrong_namespace = honest.clone();
        wrong_namespace.columns[trace_col::BYTE + 2][namespace_row] += m31(1);
        assert_mutated_row_rejected(&scan, &wrong_namespace, namespace_row);

        let digest_row = honest
            .rows
            .iter()
            .position(|row| matches!(row.kind, RowKind::Digest { .. }))
            .unwrap();
        let mut wrong_digest_id = honest.clone();
        wrong_digest_id.columns[trace_col::DIGEST_ID_LO][digest_row] += m31(1);
        assert_mutated_row_rejected(&scan, &wrong_digest_id, digest_row);

        let mut duplicate_sorted = honest.clone();
        duplicate_sorted.columns[trace_col::SORTED_NAMESPACE][1] =
            duplicate_sorted.columns[trace_col::SORTED_NAMESPACE][0];
        duplicate_sorted.columns[trace_col::SORTED_ID][1] =
            duplicate_sorted.columns[trace_col::SORTED_ID][0];
        assert_mutated_row_rejected(&scan, &duplicate_sorted, 1);
    }

    #[test]
    fn air_rejects_duplicate_requested_namespace_hidden_in_a_trailing_byte() {
        let (scan, _, _) = fixture();
        let (forged, duplicate_row) = hidden_duplicate_requested_namespace(&scan);
        let evaluated =
            test_eval(&scan).evaluate(RowEval::for_row(&forged, &scan.spec, duplicate_row));
        assert_eq!(
            evaluated.nonzero_constraints().len(),
            1,
            "the trailing-byte zeroing constraint must be the only rejection"
        );
    }

    const TEST_COUNTER_DOMAIN: u64 = 0x4d44_4f43_5644_4354;
    const TEST_ISSUER: usize = 0;
    const TEST_MSO_START: usize = 1;
    const TEST_ITEM_ID: usize = 2;
    const TEST_DIGEST: usize = 3;
    const TEST_COUNTER_SELECTORS: usize = 4;
    const TEST_COUNTER_VALUES: usize = 32;
    const TEST_COUNTER_COLS: usize = TEST_COUNTER_SELECTORS + TEST_COUNTER_VALUES;

    #[derive(Clone, Debug)]
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

    fn test_column(log_size: u32, values: Vec<M31>) -> Column {
        let mut ordered = vec![m31(0); 1usize << log_size];
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
            .map(|values| test_column(log_size, values))
            .collect()
    }

    #[derive(Clone)]
    struct TestCounterEval {
        log_size: u32,
        issuer: FieldBytesRelation,
        mso_start: MdocMsoStartRelation,
        item_id: MdocPrivateDigestIdRelation,
        digest: DigestBytesRelation,
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
                add_boolean(&mut eval, selector.clone(), &one);
            }
            add_boolean(&mut eval, selector_sum, &one);
            eval.add_to_relation(RelationEntry::new(
                &self.issuer,
                -E::EF::from(selectors[TEST_ISSUER].clone()),
                &values[..3],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.mso_start,
                -E::EF::from(selectors[TEST_MSO_START].clone()),
                &values[..1],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.item_id,
                -E::EF::from(selectors[TEST_ITEM_ID].clone()),
                &values[..8],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.digest,
                -E::EF::from(selectors[TEST_DIGEST].clone()),
                &values,
            ));
            eval.finalize_logup_in_pairs();
            eval
        }
    }

    fn external_relations(
        handles: &MdocValueDigestsScanHandles,
    ) -> (
        FieldBytesRelation,
        MdocMsoStartRelation,
        MdocPrivateDigestIdRelation,
        DigestBytesRelation,
    ) {
        (
            handles.issuer_message.get(),
            handles.mso_start.get(),
            handles.item.digest_id.get(),
            handles.item.digest.get(),
        )
    }

    fn test_counter_interaction(
        rows: &[TestCounterRow],
        log_size: u32,
        handles: &MdocValueDigestsScanHandles,
    ) -> (Vec<Column>, QM31) {
        let trace = test_counter_evals(rows, log_size);
        let packed_rows = 1usize << (log_size - LOG_N_LANES);
        let (issuer, mso_start, item_id, digest) = external_relations(handles);
        let values = |row: usize| -> [PackedM31; TEST_COUNTER_VALUES] {
            std::array::from_fn(|index| trace[TEST_COUNTER_SELECTORS + index].data[row])
        };
        let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
            Vec::with_capacity(TEST_COUNTER_SELECTORS);
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        -PackedQM31::from(trace[TEST_ISSUER].data[row]),
                        issuer.combine(&values[..3]),
                    )
                })
                .collect(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        -PackedQM31::from(trace[TEST_MSO_START].data[row]),
                        mso_start.combine(&values[..1]),
                    )
                })
                .collect(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        -PackedQM31::from(trace[TEST_ITEM_ID].data[row]),
                        item_id.combine(&values[..8]),
                    )
                })
                .collect(),
        );
        sites.push(
            (0..packed_rows)
                .map(|row| {
                    let values = values(row);
                    (
                        -PackedQM31::from(trace[TEST_DIGEST].data[row]),
                        digest.combine(&values),
                    )
                })
                .collect(),
        );
        assert_eq!(sites.len(), TEST_COUNTER_SELECTORS);

        let mut logup = LogupTraceGenerator::new(log_size);
        for pair in sites.chunks_exact(2) {
            logup.col_from_iter((0..packed_rows).map(|row| {
                let (left_num, left_den) = pair[0][row];
                let (right_num, right_den) = pair[1][row];
                (
                    left_num * right_den + right_num * left_den,
                    left_den * right_den,
                )
            }));
        }
        logup.finalize_last()
    }

    struct TestExternalCounter {
        rows: Vec<TestCounterRow>,
        log_size: u32,
        handles: MdocValueDigestsScanHandles,
        component: Option<FrameworkComponent<TestCounterEval>>,
    }

    impl TestExternalCounter {
        fn new(rows: Vec<TestCounterRow>, handles: MdocValueDigestsScanHandles) -> Self {
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

    impl Air for TestExternalCounter {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_u64(TEST_COUNTER_DOMAIN);
            channel.mix_u64(u64::from(self.log_size));
            channel.mix_u64(self.rows.len() as u64);
        }

        fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
            assert!(!self.handles.issuer_message.is_set());
            assert!(!self.handles.mso_start.is_set());
            self.handles
                .issuer_message
                .set(FieldBytesRelation::draw(channel));
            self.handles
                .mso_start
                .set(MdocMsoStartRelation::draw(channel));
            assert!(!self.handles.item.digest_id.is_set());
            assert!(!self.handles.item.digest.is_set());
            self.handles
                .item
                .digest_id
                .set(MdocPrivateDigestIdRelation::draw(channel));
            self.handles
                .item
                .digest
                .set(DigestBytesRelation::draw(channel));
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
            let (issuer, mso_start, item_id, digest) = external_relations(&self.handles);
            self.component = Some(FrameworkComponent::new(
                allocator,
                TestCounterEval {
                    log_size: self.log_size,
                    issuer,
                    mso_start,
                    item_id,
                    digest,
                },
                self.interaction().1,
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().unwrap()]
        }
    }

    impl AirProver for TestExternalCounter {
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

    fn honest_counter_rows(scan: &MdocValueDigestsScan) -> Vec<TestCounterRow> {
        let trace = scan.witness.as_ref().unwrap();
        let mut rows = Vec::new();
        for row in 0..MDOC_VALUE_DIGESTS_SCAN_ROWS {
            for site in 0..BYTE_SITES {
                if trace.columns[trace_col::BYTE_ACTIVE + site][row] == m31(1) {
                    rows.push(TestCounterRow::new(
                        TEST_ISSUER,
                        &[
                            m31_u32(HOSTED_MSG_FIELD_ID),
                            trace.columns[trace_col::MSO_START][row]
                                + trace.columns[trace_col::CURSOR][row]
                                + trace.columns[trace_col::BYTE_OFFSET + site][row],
                            trace.columns[trace_col::BYTE + site][row],
                        ],
                    ));
                }
            }
            if trace.columns[trace_col::HEAD][row] == m31(1) {
                rows.push(TestCounterRow::new(
                    TEST_MSO_START,
                    &[trace.columns[trace_col::MSO_START][row]],
                ));
            }
            if trace.columns[trace_col::SELECTED][row] == m31(1) {
                rows.push(TestCounterRow::new(
                    TEST_ITEM_ID,
                    &[
                        trace.columns[trace_col::DIGEST_ENCODING_LEN][row],
                        trace.columns[trace_col::BYTE][row],
                        trace.columns[trace_col::BYTE + 1][row],
                        trace.columns[trace_col::BYTE + 2][row],
                        m31(0),
                        m31(0),
                        trace.columns[trace_col::DIGEST_ID_LO][row],
                        m31(0),
                    ],
                ));
                let digest_values = (0..32)
                    .map(|index| trace.columns[trace_col::BYTE + DIGEST_BYTES_START + index][row])
                    .collect::<Vec<_>>();
                rows.push(TestCounterRow::new(TEST_DIGEST, &digest_values));
            }
        }
        rows
    }

    struct ComposedScannerProof {
        stark: stwo::core::proof::StarkProof<air_core::Hasher>,
        scan_claim: MdocValueDigestsInteractionClaim,
        counter_rows: Vec<TestCounterRow>,
        spec: MdocValueDigestsScanSpec,
    }

    fn prove_composed_scan(mut scan: MdocValueDigestsScan) -> ComposedScannerProof {
        let counter_rows = honest_counter_rows(&scan);
        let mut counter = TestExternalCounter::new(counter_rows.clone(), scan.handles.clone());
        let stark = air_core::prove(
            &mut [&mut counter, &mut scan],
            crate::mdoc::mdoc_ts13_pcs_config(),
        )
        .expect("honest valueDigests scanner composition proves");
        ComposedScannerProof {
            stark,
            scan_claim: scan.claim().clone(),
            counter_rows,
            spec: scan.spec.clone(),
        }
    }

    fn prove_composed_scanner() -> ComposedScannerProof {
        let (scan, _, _) = fixture();
        prove_composed_scan(scan)
    }

    fn verify_composed_scanner(
        fixture: &ComposedScannerProof,
        counter_rows: Vec<TestCounterRow>,
    ) -> Result<(), air_core::VerifyError> {
        let handles = handles();
        let mut counter = TestExternalCounter::new(counter_rows, handles.clone());
        let mut scan = MdocValueDigestsScan::verifier(
            fixture.spec.clone(),
            handles,
            fixture.scan_claim.clone(),
        )
        .unwrap();
        air_core::verify_with_expected_preprocessed_root(
            &mut [&mut counter, &mut scan],
            &fixture.stark,
            None,
        )
    }

    fn assert_forged_scan_does_not_prove(mut scan: MdocValueDigestsScan, message: &str) {
        let counter_rows = honest_counter_rows(&scan);
        let mut counter = TestExternalCounter::new(counter_rows, scan.handles.clone());
        assert!(
            air_core::prove(
                &mut [&mut counter, &mut scan],
                crate::mdoc::mdoc_ts13_pcs_config(),
            )
            .is_err(),
            "{message}"
        );
    }

    fn assert_counter_mutation_rejects(
        fixture: &ComposedScannerProof,
        name: &str,
        kind: usize,
        value_index: usize,
    ) {
        let mut rows = fixture.counter_rows.clone();
        rows.iter_mut().find(|row| row.kind == kind).unwrap().values[value_index] += m31(1);
        match verify_composed_scanner(fixture, rows)
            .expect_err("mutated scanner counterpart must not verify")
        {
            air_core::VerifyError::Stark(
                stwo::core::verifier::VerificationError::InvalidStructure(reason),
            ) => assert_eq!(reason, "LogUp claimed sums do not cancel", "{name}"),
            other => panic!("{name}: expected global LogUp rejection, got {other:?}"),
        }
    }

    #[test]
    fn composed_proof_verifies_and_rejects_every_external_relation_seam() {
        let fixture = prove_composed_scanner();
        verify_composed_scanner(&fixture, fixture.counter_rows.clone())
            .expect("honest valueDigests relation composition verifies");
        for (name, kind, value_index) in [
            ("issuer field", TEST_ISSUER, 0),
            ("issuer index", TEST_ISSUER, 1),
            ("issuer byte", TEST_ISSUER, 2),
            ("MSO start", TEST_MSO_START, 0),
            ("item encoding", TEST_ITEM_ID, 0),
            ("item digest ID", TEST_ITEM_ID, 6),
            ("SHA digest", TEST_DIGEST, 0),
        ] {
            assert_counter_mutation_rejects(&fixture, name, kind, value_index);
        }
    }

    #[test]
    fn composed_proof_rejects_decoy_or_missing_namespace_with_counterparts_moved() {
        let decoy_namespace = "org.example.extra";
        let decoy_digest = digest(0xa0);
        let requested_digest = digest(0x20);
        let mso = encode_value_digests(&[
            (decoy_namespace.as_bytes().to_vec(), vec![(7, decoy_digest)]),
            (
                REQUESTED_NAMESPACE.as_bytes().to_vec(),
                vec![(7, requested_digest)],
            ),
        ]);
        for public_namespace in [REQUESTED_NAMESPACE, "org.example.missing"] {
            let (mut scan, _) = scanner_for_mso(
                mso.clone(),
                decoy_namespace,
                MdocSelectedValueDigest {
                    digest_id: 7,
                    digest: decoy_digest,
                },
            )
            .unwrap();
            scan.spec.namespace = public_namespace.to_owned();
            assert_forged_scan_does_not_prove(
                scan,
                &format!(
                    "moving both private item/digest counterparts to a decoy namespace must not \
                     prove under public namespace {public_namespace}"
                ),
            );
        }
    }

    #[test]
    fn proof_matrix_rejects_ordered_and_unordered_duplicate_ids_in_every_namespace() {
        for requested_target in [false, true] {
            for ordered in [false, true] {
                let unique_entries = if ordered {
                    vec![(1, digest(0x10)), (2, digest(0x20)), (3, digest(0x30))]
                } else {
                    vec![(3, digest(0x30)), (1, digest(0x10)), (2, digest(0x20))]
                };
                let duplicate_entries = if ordered {
                    vec![(1, digest(0x10)), (2, digest(0x20)), (2, digest(0x30))]
                } else {
                    vec![(2, digest(0x30)), (1, digest(0x10)), (2, digest(0x20))]
                };
                let requested_digest = digest(0x90);
                let (duplicate_namespaces, unique_namespaces, selected_digest, namespace_index) =
                    if requested_target {
                        (
                            vec![
                                (b"org.example.extra".to_vec(), vec![(9, digest(0xa0))]),
                                (REQUESTED_NAMESPACE.as_bytes().to_vec(), duplicate_entries),
                            ],
                            vec![
                                (b"org.example.extra".to_vec(), vec![(9, digest(0xa0))]),
                                (REQUESTED_NAMESPACE.as_bytes().to_vec(), unique_entries),
                            ],
                            MdocSelectedValueDigest {
                                digest_id: 1,
                                digest: digest(0x10),
                            },
                            1,
                        )
                    } else {
                        (
                            vec![
                                (b"org.example.extra".to_vec(), duplicate_entries),
                                (
                                    REQUESTED_NAMESPACE.as_bytes().to_vec(),
                                    vec![(9, requested_digest)],
                                ),
                            ],
                            vec![
                                (b"org.example.extra".to_vec(), unique_entries),
                                (
                                    REQUESTED_NAMESPACE.as_bytes().to_vec(),
                                    vec![(9, requested_digest)],
                                ),
                            ],
                            MdocSelectedValueDigest {
                                digest_id: 9,
                                digest: requested_digest,
                            },
                            0,
                        )
                    };

                assert_eq!(
                    canonical_reason(scanner_error(scanner_for_mso(
                        encode_value_digests(&duplicate_namespaces),
                        REQUESTED_NAMESPACE,
                        selected_digest.clone(),
                    ))),
                    MsoValueDigestsCanonicalityReason::DuplicateDigestId,
                    "requested_target={requested_target}, ordered={ordered}"
                );

                let (mut scan, _) = scanner_for_mso(
                    encode_value_digests(&unique_namespaces),
                    REQUESTED_NAMESPACE,
                    selected_digest,
                )
                .unwrap();
                let sorted_row = forge_duplicate_digest_id(&mut scan, namespace_index);
                assert_mutated_row_rejected(&scan, scan.witness.as_ref().unwrap(), sorted_row);
                assert_forged_scan_does_not_prove(
                    scan,
                    &format!(
                        "duplicate ID proof must fail: requested_target={requested_target}, \
                         ordered={ordered}"
                    ),
                );
            }
        }
    }

    #[test]
    fn proof_matrix_rejects_nonminimal_or_indefinite_map_and_text_headers() {
        for (name, namespace_row, site, byte) in [
            ("outer map nonminimal", false, VALUE_DIGESTS_KEY.len(), 0xb8),
            ("outer map indefinite", false, VALUE_DIGESTS_KEY.len(), 0xbf),
            ("namespace key nonminimal", true, 0, 0x78),
            ("namespace key indefinite", true, 0, 0x7f),
            ("inner map nonminimal", true, 34, 0xb8),
            ("inner map indefinite", true, 34, 0xbf),
        ] {
            let (mut scan, _, _) = fixture();
            let trace = scan.witness.as_mut().unwrap();
            let row = if namespace_row {
                trace
                    .rows
                    .iter()
                    .position(|row| {
                        matches!(
                            &row.kind,
                            RowKind::Namespace {
                                requested: true,
                                ..
                            }
                        )
                    })
                    .unwrap()
            } else {
                0
            };
            trace.columns[trace_col::BYTE + site][row] = m31(byte);
            assert_forged_scan_does_not_prove(
                scan,
                &format!("{name} with its issuer counterpart moved must not prove"),
            );
        }
    }

    #[test]
    fn full_255_item_witness_proves_and_declared_256_rejects_before_schedule_allocation() {
        let selected_digest = digest(0x20);
        let mut namespaces = Vec::with_capacity(254);
        namespaces.push((
            REQUESTED_NAMESPACE.as_bytes().to_vec(),
            vec![(7, selected_digest)],
        ));
        namespaces.extend((0..253).map(|index| (format!("n{index:03}").into_bytes(), Vec::new())));
        let (scan, census) = scanner_for_mso(
            encode_value_digests(&namespaces),
            REQUESTED_NAMESPACE,
            MdocSelectedValueDigest {
                digest_id: 7,
                digest: selected_digest,
            },
        )
        .unwrap();
        assert_eq!(census.namespaces + census.digest_entries, 255);
        assert_eq!(census.active_rows, 256);
        assert_trace_satisfies_air(&scan);
        let fixture = prove_composed_scan(scan);
        verify_composed_scanner(&fixture, fixture.counter_rows.clone())
            .expect("the exact 255-item scanner witness must prove and verify");

        assert_eq!(
            scanner_error(scanner_for_mso(
                with_value_digests_tail(&[0xb9, 0x01, 0x00]),
                REQUESTED_NAMESPACE,
                MdocSelectedValueDigest {
                    digest_id: 7,
                    digest: selected_digest,
                },
            )),
            MdocValueDigestsScanError::ScanItemCapExceeded {
                items: 256,
                max: MDOC_MAX_VALUE_DIGEST_SCAN_ITEMS,
            }
        );
    }

    #[test]
    fn composed_proof_rejects_a_hidden_duplicate_requested_namespace() {
        let (mut scan, _, _) = fixture();
        let (forged, _) = hidden_duplicate_requested_namespace(&scan);
        scan.witness = Some(forged);
        assert_forged_scan_does_not_prove(
            scan,
            "a namespace duplicate hidden in an inactive trailing byte must not prove",
        );
    }

    #[test]
    fn fixed_geometry_and_inactive_randomization_are_stable() {
        let (mut scan, _, _) = fixture();
        assert_eq!(scan.layout().preprocessed, vec![9; PREPROCESSED_COLS]);
        assert_eq!(scan.layout().trace, vec![9; 305]);
        assert_eq!(MAIN_RELATION_SITES, 43);
        assert_eq!(scan.layout().interaction, vec![9; 48]);
        assert_eq!(
            <MdocValueDigestsScanEval as FrameworkEval>::max_constraint_log_degree_bound(
                &test_eval(&scan),
            ),
            11
        );
        assert_eq!(
            <MdocValueDigestsScan as AirProver>::max_constraint_log_degree_bound(&scan),
            11
        );
        assert!(<MdocValueDigestsScan as AirProver>::store_polynomial_coefficients(&scan));
        assert_eq!(scan.preprocessed_column_ids().len(), PREPROCESSED_COLS);
        assert_eq!(
            scan.preprocessed_column_fingerprints().len(),
            PREPROCESSED_COLS
        );

        let (first, _, _) = fixture();
        let (second, _, _) = fixture();
        let first = first.witness.as_ref().unwrap();
        let second = second.witness.as_ref().unwrap();
        let inactive = first.rows.len();
        for column in [
            trace_col::BYTE,
            trace_col::BYTE_OFFSET,
            trace_col::CURSOR_BITS,
        ] {
            assert_ne!(
                &first.columns[column][inactive..],
                &second.columns[column][inactive..],
                "inactive scanner column {column} must be freshly randomized"
            );
        }
    }
}
