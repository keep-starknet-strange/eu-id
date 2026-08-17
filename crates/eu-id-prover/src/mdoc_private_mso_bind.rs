//! Private MobileSecurityObject fact binding for the TS13 identity proof.
//!
//! ## Data flow
//!
//! `mdoc_private_message::MdocPrivateMessageProvider` provides the issuer
//! `Sig_structure`.
//! This component consumes positive issuer-message tuples.
//! Each tuple contains `(HOSTED_MSG_FIELD_ID, absolute_index, byte)`.
//! Private range-checked offsets select the tuples.
//! The component proves the required MSO facts.
//!
//! A separate component scans the namespace-scoped `valueDigests` map.
//! Both components share [`SharedMdocMsoStartRelation`].
//!
//! ## Relation polarity
//!
//! | relation | provider | sign | consumer | sign |
//! |---|---|---:|---|---:|
//! | issuer hosted message | private-message provider | `-` | this binder | `+` |
//! | full padded MSO SHA stream | SHA-256 AIR | `-` | this binder | `+` |
//! | private `mso_start` | this binder | `-` | valueDigests scanner | `+` |
//! | private `device_pk_start` | this binder | `-` | device-key binder | `+` |
//! | authenticated validity bytes | this binder | `-` | exact validity AIR | `+` |
//!
//! The SHA-stream sites follow the 32 issuer sites.
//! The `mso_start` site follows them.
//! The device-key-start site and two validity sites come next.
//! The claimed-sum blinder is always the final site.

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
use stwo_mldsa::statement::HOSTED_MSG_FIELD_ID;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};
use crate::mdoc_private_mso_validity::{
    MdocMsoValidityBytesRelation, MdocPrivateMsoValidityWitness,
    SharedMdocMsoValidityBytesRelation, MDOC_TDATE_BYTES,
};
use crate::randomness::{random_bit, random_m31};

pub(crate) const MDOC_PRIVATE_MSO_BIND_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_PRIVATE_MSO_BIND_ROWS: usize = 1usize << MDOC_PRIVATE_MSO_BIND_LOG_SIZE;
pub(crate) const MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS: usize = 256;
pub(crate) const MDOC_PRIVATE_MSO_MIN_BLIND_ROWS: usize = 256;
pub(crate) const MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES: usize = 1_987;
pub(crate) const MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES: usize = 23;

/// Matches the `finalize_logup_batched(LOGUP_BATCH)` call in `evaluate()`. Degree-recounted
/// safe at the declared +2 bound: the widest numerator here is degree 2
/// (`mirror_row * byte_active`), and a batch-4 fold multiplies each numerator by only the
/// other three degree-1 denominators, so the constraint tops out at max(1+4, 2+3) = D5.
const LOGUP_BATCH: usize = 4;
const BIND_VERSION: u64 = 5;
const BIND_DOMAIN: u64 = 0x4d44_4f43_4d53_4f42; // "MDOCMSOB"
const CHUNK_BYTES: usize = 32;
const DOC_TYPE_CHUNKS: usize = 1;
const OFFSET_BITS: usize = 13;
const M31_MODULUS: u32 = 2_147_483_647;

// Canonical CBOR prefix through the protected-header byte-string head for
// `["Signature1", h'a1013830', h'', <payload bstr>]`.
const ISSUER_SIGNATURE1_CONTEXT_PREFIX: &[u8] = b"\x84\x6aSignature1\x44";
const VERSION_1_0_RUN: &[u8] = b"\x67version\x631.0";
const DIGEST_ALGORITHM_RUN: &[u8] = b"\x6fdigestAlgorithm\x67SHA-256";
const DOC_TYPE_KEY: &[u8] = b"\x67docType";
const VALID_FROM_ANCHOR: &[u8] = b"\x69validFrom\xc0\x74";
const VALID_UNTIL_ANCHOR: &[u8] = b"\x6avalidUntil\xc0\x74";
const DEVICE_KEY_INFO_PREFIX: &[u8; 35] =
    b"\x6ddeviceKeyInfo\xa1\x69deviceKey\xa3\x01\x07\x03\x38\x30\x20\x59\x07\xa0";

relation!(MdocMsoStartRelation, 1);
relation!(MdocDevicePkStartRelation, 1);

/// Private `mso_start` handoff to the namespace-scoped scanner.
///
/// This binder constrains the MSO version to `1.0`.
/// This binder emits one negative tuple.
/// The scanner consumes one positive tuple.
pub(crate) type SharedMdocMsoStartRelation = SharedRelation<MdocMsoStartRelation>;
pub(crate) type SharedMdocDevicePkStartRelation = SharedRelation<MdocDevicePkStartRelation>;

type MdocPrivateMsoColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocPrivateMsoComponent = FrameworkComponent<MdocPrivateMsoEval>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoShaStreamSpec {
    pub(crate) field_id: u32,
    pub(crate) padded_len: usize,
}

/// Verifier-known shape and constants.
/// This type excludes private MSO bytes, offsets, and dates.
/// It also excludes private multiplicities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoBindSpec {
    pub(crate) issuer_message_len: usize,
    pub(crate) mso_len: usize,
    pub(crate) doc_type: String,
    pub(crate) sha_stream: MdocPrivateMsoShaStreamSpec,
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoUseCensus {
    /// Additional positive hosted-message consumers contributed by this
    /// binder, indexed by the issuer message position.
    pub(crate) issuer_position_uses: Vec<u32>,
    pub(crate) issuer_uses_total: usize,
    pub(crate) sha_stream_uses: usize,
    pub(crate) mso_start_uses: usize,
    pub(crate) device_pk_start_uses: usize,
    pub(crate) validity_uses: usize,
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
    EmptyDocType,
    DocTypeTooLong {
        length: usize,
        max: usize,
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
            Self::EmptyDocType => write!(f, "public docType is empty"),
            Self::DocTypeTooLong { length, max } => write!(
                f,
                "public docType has {length} bytes; the supported canonical one-chunk profile allows at most {max}"
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
    /// [`MdocMsoStartRelation`]. Do not compute it with a separate byte search.
    pub(crate) fn mso_start(&self, mso_len: usize) -> Result<usize, MdocPrivateMsoBindError> {
        let anchor_len = payload_anchor(mso_len).len();
        self.payload_anchor_offset.checked_add(anchor_len).ok_or(
            MdocPrivateMsoBindError::PayloadOffsetOverflow {
                offset: self.payload_anchor_offset,
                anchor_len,
            },
        )
    }

    /// Absolute issuer-message position of the first private FIPS `pkEncode` byte.
    /// This binder authenticates the fixed canonical COSE prefix.
    /// The device-key binder consumes this position.
    /// It uses [`MdocDevicePkStartRelation`].
    pub(crate) fn device_pk_start(
        &self,
        spec: &MdocPrivateMsoBindSpec,
    ) -> Result<usize, MdocPrivateMsoBindError> {
        checked_window_end(
            WindowKind::DeviceKeyInfo,
            self.device_key_info_offset,
            MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES,
            spec.mso_len,
        )?;
        self.mso_start(spec.mso_len)?
            .checked_add(self.device_key_info_offset)
            .and_then(|start| start.checked_add(DEVICE_KEY_INFO_PREFIX.len()))
            .ok_or(MdocPrivateMsoBindError::WindowOffsetOverflow {
                window: "device pkEncode",
                offset: self.device_key_info_offset,
                len: DEVICE_KEY_INFO_PREFIX.len(),
            })
    }

    /// The two authenticated RFC 3339 byte strings consumed by the exact
    /// validity component. This is direct indexed witness access: it does not
    /// search or independently parse the MSO again.
    pub(crate) fn validity_witness(
        &self,
        spec: &MdocPrivateMsoBindSpec,
    ) -> Result<MdocPrivateMsoValidityWitness, MdocPrivateMsoBindError> {
        let mso_start = self.mso_start(spec.mso_len)?;
        let bytes_at = |kind: WindowKind,
                        offset: usize,
                        anchor_len: usize|
         -> Result<[u8; MDOC_TDATE_BYTES], MdocPrivateMsoBindError> {
            checked_window_end(kind, offset, anchor_len + MDOC_TDATE_BYTES, spec.mso_len)?;
            let start = mso_start + offset + anchor_len;
            Ok(self.issuer_message[start..start + MDOC_TDATE_BYTES]
                .try_into()
                .expect("checked tdate window has exactly 20 bytes"))
        };
        Ok(MdocPrivateMsoValidityWitness {
            valid_from: bytes_at(
                WindowKind::ValidFrom,
                self.valid_from_offset,
                VALID_FROM_ANCHOR.len(),
            )?,
            valid_until: bytes_at(
                WindowKind::ValidUntil,
                self.valid_until_offset,
                VALID_UNTIL_ANCHOR.len(),
            )?,
        })
    }

    /// Derive every private offset from canonical bytes.
    ///
    /// The complete payload occurrence must be unique.
    /// Its form is `empty external_aad || bstr-head || mso_bytes`.
    /// Each supported fact anchor must also be unique.
    /// These rules define the canonical issuer boundary.
    ///
    pub(crate) fn from_canonical_issuer_message(
        spec: &MdocPrivateMsoBindSpec,
        issuer_message: Vec<u8>,
        mso_bytes: &[u8],
    ) -> Result<Self, MdocPrivateMsoBindError> {
        // Validate all public limits before constructing the search value.
        // Relation handles do not change this canonical witness helper.
        validate_spec(spec)?;
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

        let version_offset = unique_subslice(mso_bytes, VERSION_1_0_RUN, "MSO version")?;
        let digest_algorithm_offset =
            unique_subslice(mso_bytes, DIGEST_ALGORITHM_RUN, "MSO digestAlgorithm")?;
        let doc_type_offset = unique_subslice(
            mso_bytes,
            &canonical_doc_type_run(&spec.doc_type),
            "MSO docType",
        )?;
        let device_key_info_offset =
            unique_subslice(mso_bytes, DEVICE_KEY_INFO_PREFIX, "MSO deviceKeyInfo")?;
        checked_window_end(
            WindowKind::DeviceKeyInfo,
            device_key_info_offset,
            MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES,
            spec.mso_len,
        )?;
        let valid_from_offset = unique_subslice(mso_bytes, VALID_FROM_ANCHOR, "MSO validFrom")?;
        checked_window_end(
            WindowKind::ValidFrom,
            valid_from_offset,
            VALID_FROM_ANCHOR.len() + MDOC_TDATE_BYTES,
            spec.mso_len,
        )?;
        let valid_until_offset = unique_subslice(mso_bytes, VALID_UNTIL_ANCHOR, "MSO validUntil")?;
        checked_window_end(
            WindowKind::ValidUntil,
            valid_until_offset,
            VALID_UNTIL_ANCHOR.len() + MDOC_TDATE_BYTES,
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
    doc_type_chunk: Option<usize>,
    issuer_active: [bool; CHUNK_BYTES],
    valid_from_date_row: bool,
    valid_until_date_row: bool,
    device_pk_start_row: bool,
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
            doc_type_chunk: None,
            issuer_active: [false; CHUNK_BYTES],
            valid_from_date_row: false,
            valid_until_date_row: false,
            device_pk_start_row: false,
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
    byte_active_masks: ByteMaskAliases,
    issuer_active_masks: ByteMaskAliases,
    expected_active_masks: ByteMaskAliases,
}

impl PublicShape {
    fn preprocessed_cols(&self) -> usize {
        self.device_pk_start_row_column() + 1
    }

    fn byte_active_column(&self, byte_index: usize) -> usize {
        PP_BYTE_ACTIVE_START + self.byte_active_masks.aliases[byte_index]
    }

    fn issuer_active_start(&self) -> usize {
        PP_BYTE_ACTIVE_START + self.byte_active_masks.representatives.len()
    }

    fn issuer_active_column(&self, byte_index: usize) -> usize {
        self.issuer_active_start() + self.issuer_active_masks.aliases[byte_index]
    }

    fn expected_active_start(&self) -> usize {
        self.issuer_active_start() + self.issuer_active_masks.representatives.len()
    }

    fn expected_active_column(&self, byte_index: usize) -> usize {
        self.expected_active_start() + self.expected_active_masks.aliases[byte_index]
    }

    fn expected_start(&self) -> usize {
        self.expected_active_start() + self.expected_active_masks.representatives.len()
    }

    fn expected_column(&self, byte_index: usize) -> usize {
        self.expected_start() + byte_index
    }

    fn doc_type_chunk_start(&self) -> usize {
        self.expected_start() + CHUNK_BYTES
    }

    fn device_pk_start_row_column(&self) -> usize {
        self.doc_type_chunk_start() + DOC_TYPE_CHUNKS
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ByteMaskAliases {
    representatives: Vec<usize>,
    aliases: [usize; CHUNK_BYTES],
}

impl ByteMaskAliases {
    fn from_rows(rows: &[PublicRow], value: fn(&PublicRow, usize) -> bool) -> Self {
        let mut representatives = Vec::new();
        let mut aliases = [0; CHUNK_BYTES];
        for (byte_index, alias) in aliases.iter_mut().enumerate() {
            *alias = representatives
                .iter()
                .position(|&representative| {
                    rows.iter()
                        .all(|row| value(row, byte_index) == value(row, representative))
                })
                .unwrap_or_else(|| {
                    representatives.push(byte_index);
                    representatives.len() - 1
                });
        }
        Self {
            representatives,
            aliases,
        }
    }

    #[cfg(test)]
    fn representative(&self, byte_index: usize) -> usize {
        self.representatives[self.aliases[byte_index]]
    }
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
    let mut anchor = ISSUER_SIGNATURE1_CONTEXT_PREFIX.to_vec();
    anchor.extend_from_slice(crate::mdoc::MLDSA_PROTECTED_HEADER);
    anchor.push(0x40); // canonical empty external_aad bstr
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

fn push_doc_type_window(rows: &mut Vec<PublicRow>, bytes_len: usize) {
    for (chunk_index, chunk_relative) in (0..bytes_len).step_by(CHUNK_BYTES).enumerate() {
        let chunk_len = (bytes_len - chunk_relative).min(CHUNK_BYTES);
        let mut row = PublicRow::new(
            WindowKind::DocType,
            bytes_len,
            chunk_relative,
            chunk_len,
            chunk_index != 0,
        );
        row.doc_type_chunk = Some(chunk_index);
        row.issuer_active[..chunk_len].fill(true);
        rows.push(row);
    }
}

fn push_private_device_key_window(rows: &mut Vec<PublicRow>) {
    for (chunk_index, chunk) in DEVICE_KEY_INFO_PREFIX.chunks(CHUNK_BYTES).enumerate() {
        let chunk_relative = chunk_index * CHUNK_BYTES;
        let mut row = PublicRow::new(
            WindowKind::DeviceKeyInfo,
            MDOC_PRIVATE_MSO_DEVICE_KEY_INFO_BYTES,
            chunk_relative,
            chunk.len(),
            chunk_index != 0,
        );
        row.expected_active[..chunk.len()].fill(true);
        row.expected[..chunk.len()].copy_from_slice(chunk);
        row.issuer_active[..chunk.len()].fill(true);
        row.device_pk_start_row = chunk_index == 0;
        rows.push(row);
    }
}

fn push_tdate_window(rows: &mut Vec<PublicRow>, kind: WindowKind, anchor: &[u8], valid_from: bool) {
    let window_len = anchor.len() + MDOC_TDATE_BYTES;
    let mut anchor_row = PublicRow::new(kind, window_len, 0, anchor.len(), false);
    anchor_row.expected_active[..anchor.len()].fill(true);
    anchor_row.expected[..anchor.len()].copy_from_slice(anchor);
    anchor_row.issuer_active[..anchor.len()].fill(true);
    rows.push(anchor_row);

    let mut date_row = PublicRow::new(kind, window_len, anchor.len(), MDOC_TDATE_BYTES, true);
    date_row.issuer_active[..MDOC_TDATE_BYTES].fill(true);
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

fn validate_spec(spec: &MdocPrivateMsoBindSpec) -> Result<PublicShape, MdocPrivateMsoBindError> {
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
    if spec.doc_type.is_empty() {
        return Err(MdocPrivateMsoBindError::EmptyDocType);
    }
    if spec.doc_type.len() > MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES {
        return Err(MdocPrivateMsoBindError::DocTypeTooLong {
            length: spec.doc_type.len(),
            max: MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES,
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
    if spec.sha_stream.field_id >= M31_MODULUS {
        return Err(MdocPrivateMsoBindError::ShaFieldIdOutOfRange {
            field_id: spec.sha_stream.field_id,
        });
    }
    let expected = checked_sha_padded_len(spec.mso_len)
        .expect("bounded MSO length cannot overflow SHA padding");
    if spec.sha_stream.padded_len != expected {
        return Err(MdocPrivateMsoBindError::ShaPaddedLengthMismatch {
            expected,
            actual: spec.sha_stream.padded_len,
        });
    }

    let mut rows = Vec::with_capacity(MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS);
    let mut anchor_row =
        PublicRow::new(WindowKind::PayloadAnchor, 0, 0, payload_anchor.len(), false);
    anchor_row.expected_active[..payload_anchor.len()].fill(true);
    anchor_row.expected[..payload_anchor.len()].copy_from_slice(&payload_anchor);
    anchor_row.issuer_active[..payload_anchor.len()].fill(true);
    rows.push(anchor_row);

    push_constant_window(&mut rows, WindowKind::Version, VERSION_1_0_RUN);
    push_constant_window(&mut rows, WindowKind::DigestAlgorithm, DIGEST_ALGORITHM_RUN);
    push_doc_type_window(&mut rows, canonical_doc_type_run(&spec.doc_type).len());
    push_private_device_key_window(&mut rows);
    push_tdate_window(&mut rows, WindowKind::ValidFrom, VALID_FROM_ANCHOR, true);
    push_tdate_window(&mut rows, WindowKind::ValidUntil, VALID_UNTIL_ANCHOR, false);
    push_mirror_rows(&mut rows, spec.mso_len, spec.sha_stream.padded_len);
    if rows.len() > MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS {
        return Err(MdocPrivateMsoBindError::ScheduleTooLarge {
            active_rows: rows.len(),
            max: MDOC_PRIVATE_MSO_MAX_ACTIVE_ROWS,
        });
    }
    debug_assert!(MDOC_PRIVATE_MSO_BIND_ROWS - rows.len() >= MDOC_PRIVATE_MSO_MIN_BLIND_ROWS);
    let byte_active_masks = ByteMaskAliases::from_rows(&rows, |row, index| index < row.byte_len);
    let issuer_active_masks =
        ByteMaskAliases::from_rows(&rows, |row, index| row.issuer_active[index]);
    let expected_active_masks =
        ByteMaskAliases::from_rows(&rows, |row, index| row.expected_active[index]);
    Ok(PublicShape {
        payload_anchor,
        rows,
        byte_active_masks,
        issuer_active_masks,
        expected_active_masks,
    })
}

const PP_ACTIVE: usize = 0;
const PP_MSO_WINDOW: usize = 1;
const PP_WINDOW_START: usize = 2;
const PP_CONTINUATION: usize = 3;
const PP_WINDOW_LEN: usize = 4;
const PP_CHUNK_RELATIVE: usize = 5;
const PP_VALID_FROM_DATE_ROW: usize = 6;
const PP_VALID_UNTIL_DATE_ROW: usize = 7;
const PP_MIRROR_ROW: usize = 8;
const PP_ANCHOR_ROW: usize = 9;
const PP_SAME_PAYLOAD_PREV: usize = 10;
const PP_BYTE_ACTIVE_START: usize = 11;

const TRACE_BYTE_START: usize = 0;
const TRACE_PAYLOAD_OFFSET: usize = TRACE_BYTE_START + CHUNK_BYTES;
const TRACE_PAYLOAD_OFFSET_BITS: usize = TRACE_PAYLOAD_OFFSET + 1;
const TRACE_PAYLOAD_SLACK: usize = TRACE_PAYLOAD_OFFSET_BITS + OFFSET_BITS;
const TRACE_PAYLOAD_SLACK_BITS: usize = TRACE_PAYLOAD_SLACK + 1;
const TRACE_WINDOW_OFFSET: usize = TRACE_PAYLOAD_SLACK_BITS + OFFSET_BITS;
const TRACE_WINDOW_OFFSET_BITS: usize = TRACE_WINDOW_OFFSET + 1;
const TRACE_WINDOW_SLACK: usize = TRACE_WINDOW_OFFSET_BITS + OFFSET_BITS;
const TRACE_WINDOW_SLACK_BITS: usize = TRACE_WINDOW_SLACK + 1;
const TRACE_COLS: usize = TRACE_WINDOW_SLACK_BITS + OFFSET_BITS;

fn m31(value: usize) -> M31 {
    M31::from_u32_unchecked(value as u32)
}

fn m31_u32(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
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

fn preprocessed_column_ids(shape: &PublicShape) -> Vec<PreProcessedColumnId> {
    let mut ids = vec![
        col_id("active"),
        col_id("mso_window"),
        col_id("window_start"),
        col_id("continuation"),
        col_id("window_len"),
        col_id("chunk_relative"),
        col_id("valid_from_date_row"),
        col_id("valid_until_date_row"),
        col_id("mirror_row"),
        col_id("anchor_row"),
        col_id("same_payload_prev"),
    ];
    ids.extend(
        shape
            .byte_active_masks
            .representatives
            .iter()
            .map(|index| col_id(&format!("byte_active_{index}"))),
    );
    ids.extend(
        shape
            .issuer_active_masks
            .representatives
            .iter()
            .map(|index| col_id(&format!("issuer_active_{index}"))),
    );
    ids.extend(
        shape
            .expected_active_masks
            .representatives
            .iter()
            .map(|index| col_id(&format!("expected_active_{index}"))),
    );
    ids.extend((0..CHUNK_BYTES).map(|index| col_id(&format!("expected_{index}"))));
    ids.extend((0..DOC_TYPE_CHUNKS).map(|index| col_id(&format!("doc_type_chunk_{index}"))));
    ids.push(col_id("device_pk_start_row"));
    debug_assert_eq!(ids.len(), shape.preprocessed_cols());
    ids
}

fn preprocessed_columns(shape: &PublicShape) -> Vec<MdocPrivateMsoColumnEval> {
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); MDOC_PRIVATE_MSO_BIND_ROWS];
        shape.preprocessed_cols()
    ];
    for (row_index, row) in shape.rows.iter().enumerate() {
        columns[PP_ACTIVE][row_index] = m31_u32(1);
        columns[PP_MSO_WINDOW][row_index] = m31_u32(u32::from(row.mso_window()));
        columns[PP_WINDOW_START][row_index] =
            m31_u32(u32::from(row.mso_window() && !row.continuation));
        columns[PP_CONTINUATION][row_index] = m31_u32(u32::from(row.continuation));
        columns[PP_WINDOW_LEN][row_index] = m31(row.window_len);
        columns[PP_CHUNK_RELATIVE][row_index] = m31(row.chunk_relative);
        columns[PP_VALID_FROM_DATE_ROW][row_index] = m31_u32(u32::from(row.valid_from_date_row));
        columns[PP_VALID_UNTIL_DATE_ROW][row_index] = m31_u32(u32::from(row.valid_until_date_row));
        columns[PP_MIRROR_ROW][row_index] = m31_u32(u32::from(row.mirror_row));
        columns[PP_ANCHOR_ROW][row_index] =
            m31_u32(u32::from(row.kind == WindowKind::PayloadAnchor));
        columns[PP_SAME_PAYLOAD_PREV][row_index] = m31_u32(u32::from(row_index != 0));
        for byte_index in 0..CHUNK_BYTES {
            columns[shape.byte_active_column(byte_index)][row_index] =
                m31_u32(u32::from(byte_index < row.byte_len));
            columns[shape.issuer_active_column(byte_index)][row_index] =
                m31_u32(u32::from(row.issuer_active[byte_index]));
            columns[shape.expected_active_column(byte_index)][row_index] =
                m31_u32(u32::from(row.expected_active[byte_index]));
            columns[shape.expected_column(byte_index)][row_index] =
                m31_u32(u32::from(row.expected[byte_index]));
        }
        if let Some(chunk_index) = row.doc_type_chunk {
            columns[shape.doc_type_chunk_start() + chunk_index][row_index] = m31_u32(1);
        }
        columns[shape.device_pk_start_row_column()][row_index] =
            m31_u32(u32::from(row.device_pk_start_row));
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

fn randomize_globally_constrained_cells(columns: &mut [Vec<M31>], rng: &mut impl RngCore) {
    for row in 0..MDOC_PRIVATE_MSO_BIND_ROWS {
        for start in [
            TRACE_PAYLOAD_OFFSET_BITS,
            TRACE_PAYLOAD_SLACK_BITS,
            TRACE_WINDOW_OFFSET_BITS,
            TRACE_WINDOW_SLACK_BITS,
        ] {
            for column in &mut columns[start..start + OFFSET_BITS] {
                column[row] = random_bit(rng);
            }
        }
    }
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
    let padded = padded_mso(raw_mso, spec.sha_stream.padded_len);
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); MDOC_PRIVATE_MSO_BIND_ROWS]; TRACE_COLS];
    let mut rng = rand::thread_rng();
    for column in &mut columns {
        for value in column.iter_mut() {
            *value = random_m31(&mut rng);
        }
    }
    randomize_globally_constrained_cells(&mut columns, &mut rng);

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
        let source: &[u8] = if row.kind == WindowKind::PayloadAnchor {
            let start = witness.payload_anchor_offset + row.chunk_relative;
            &witness.issuer_message[start..start + row.byte_len]
        } else if row.kind == WindowKind::MsoMirror {
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
    }
    let active_rows = shape.rows.len();
    Ok((
        MdocPrivateMsoTrace { columns },
        MdocPrivateMsoUseCensus {
            issuer_position_uses,
            issuer_uses_total,
            sha_stream_uses: spec.sha_stream.padded_len,
            mso_start_uses: 1,
            device_pk_start_uses: 1,
            validity_uses: 2,
            active_rows,
            blind_rows: MDOC_PRIVATE_MSO_BIND_ROWS - active_rows,
        },
    ))
}

#[derive(Clone)]
struct MdocPrivateMsoEval {
    spec: MdocPrivateMsoBindSpec,
    payload_anchor_len: usize,
    byte_active_masks: ByteMaskAliases,
    issuer_active_masks: ByteMaskAliases,
    expected_active_masks: ByteMaskAliases,
    issuer_relation: FieldBytesRelation,
    sha_relation: FieldBytesRelation,
    mso_start_relation: MdocMsoStartRelation,
    device_pk_start_relation: MdocDevicePkStartRelation,
    validity_relation: MdocMsoValidityBytesRelation,
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
    sha_relation: &'a FieldBytesRelation,
    mso_start_relation: &'a MdocMsoStartRelation,
    device_pk_start_relation: &'a MdocDevicePkStartRelation,
    validity_relation: &'a MdocMsoValidityBytesRelation,
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
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(2 * CHUNK_BYTES + 5);

    // Fixed sites 0..32: hosted issuer-message consumers.
    for byte_index in 0..CHUNK_BYTES {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(
                        public[shape.issuer_active_column(byte_index)].data[vec_row],
                    );
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

    // Fixed sites 32..64: complete canonical padded MSO stream.
    for byte_index in 0..CHUNK_BYTES {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(
                        public[PP_MIRROR_ROW].data[vec_row]
                            * public[shape.byte_active_column(byte_index)].data[vec_row],
                    );
                    let denominator = inputs.sha_relation.combine(&[
                        PackedM31::broadcast(m31_u32(spec.sha_stream.field_id)),
                        public[PP_CHUNK_RELATIVE].data[vec_row]
                            + PackedM31::broadcast(m31(byte_index)),
                        private[TRACE_BYTE_START + byte_index].data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    // Scanner handoff: binder provider (-), scanner consumer (+).
    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let numerator = -PackedQM31::from(public[PP_ANCHOR_ROW].data[vec_row]);
                let denominator = inputs
                    .mso_start_relation
                    .combine(&[private[TRACE_PAYLOAD_OFFSET].data[vec_row]
                        + PackedM31::broadcast(m31(shape.payload_anchor.len()))]);
                (numerator, denominator)
            })
            .collect(),
    );

    // Private device-key handoff: binder provider (-), key-binder consumer (+).
    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let numerator =
                    -PackedQM31::from(public[shape.device_pk_start_row_column()].data[vec_row]);
                let start = private[TRACE_PAYLOAD_OFFSET].data[vec_row]
                    + PackedM31::broadcast(m31(shape.payload_anchor.len()))
                    + private[TRACE_WINDOW_OFFSET].data[vec_row]
                    + PackedM31::broadcast(m31(DEVICE_KEY_INFO_PREFIX.len()));
                (numerator, inputs.device_pk_start_relation.combine(&[start]))
            })
            .collect(),
    );

    // Exact-validity handoff. The binder emits one negative tuple
    // for each authenticated tdate and the validity component consumes both.
    for (kind, selector_column) in [
        (0u32, PP_VALID_FROM_DATE_ROW),
        (1u32, PP_VALID_UNTIL_DATE_ROW),
    ] {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let mut tuple = Vec::with_capacity(1 + MDOC_TDATE_BYTES);
                    tuple.push(PackedM31::broadcast(m31_u32(kind)));
                    tuple.extend(
                        (0..MDOC_TDATE_BYTES)
                            .map(|index| private[TRACE_BYTE_START + index].data[vec_row]),
                    );
                    (
                        -PackedQM31::from(public[selector_column].data[vec_row]),
                        inputs.validity_relation.combine(&tuple),
                    )
                })
                .collect(),
        );
    }

    // The claimed-sum blinder is always the final main-component site.
    let blinder_numerator = PackedQM31::broadcast(inputs.blinder_m);
    let blinder_denominator = blinder_denominator(inputs.blinder_relation, inputs.blinder_v);
    sites.push(vec![(blinder_numerator, blinder_denominator); n_vec_rows]);

    // Mirrors `finalize_logup_batched(LOGUP_BATCH)`'s recursive fraction fold exactly
    // (`num = num*d + n*den; den = den*d`, left-to-right over the chunk) so the prover's
    // trace matches what the AIR verifies.
    let mut logup = LogupTraceGenerator::new(MDOC_PRIVATE_MSO_BIND_LOG_SIZE);
    let mut site_index = 0usize;
    while site_index < sites.len() {
        let end = (site_index + LOGUP_BATCH).min(sites.len());
        let chunk = &sites[site_index..end];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let mut iter = chunk.iter().map(|site| site[vec_row]);
            let (mut numerator, mut denominator) = iter.next().unwrap();
            for (n, d) in iter {
                numerator = numerator * d + n * denominator;
                denominator *= d;
            }
            (numerator, denominator)
        }));
        site_index = end;
    }
    logup.finalize_last()
}

impl FrameworkEval for MdocPrivateMsoEval {
    fn log_size(&self) -> u32 {
        MDOC_PRIVATE_MSO_BIND_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Absolute issuer indices remain linear.
        // Non-MSO active rows set `window_offset` to zero.
        // Each row then adds the offset.
        // Paired LogUp denominators and selector numerators are cubic.
        MDOC_PRIVATE_MSO_BIND_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(col_id("active"));
        let mso_window = eval.get_preprocessed_column(col_id("mso_window"));
        let window_start = eval.get_preprocessed_column(col_id("window_start"));
        let continuation = eval.get_preprocessed_column(col_id("continuation"));
        let window_len = eval.get_preprocessed_column(col_id("window_len"));
        let chunk_relative = eval.get_preprocessed_column(col_id("chunk_relative"));
        let valid_from_date_row = eval.get_preprocessed_column(col_id("valid_from_date_row"));
        let valid_until_date_row = eval.get_preprocessed_column(col_id("valid_until_date_row"));
        let mirror_row = eval.get_preprocessed_column(col_id("mirror_row"));
        let anchor_row = eval.get_preprocessed_column(col_id("anchor_row"));
        let same_payload_prev = eval.get_preprocessed_column(col_id("same_payload_prev"));
        let byte_active_masks: Vec<E::F> = self
            .byte_active_masks
            .representatives
            .iter()
            .map(|index| eval.get_preprocessed_column(col_id(&format!("byte_active_{index}"))))
            .collect();
        let byte_active: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            byte_active_masks[self.byte_active_masks.aliases[index]].clone()
        });
        let issuer_active_masks: Vec<E::F> = self
            .issuer_active_masks
            .representatives
            .iter()
            .map(|index| eval.get_preprocessed_column(col_id(&format!("issuer_active_{index}"))))
            .collect();
        let issuer_active: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            issuer_active_masks[self.issuer_active_masks.aliases[index]].clone()
        });
        let expected_active_masks: Vec<E::F> = self
            .expected_active_masks
            .representatives
            .iter()
            .map(|index| eval.get_preprocessed_column(col_id(&format!("expected_active_{index}"))))
            .collect();
        let expected_active: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            expected_active_masks[self.expected_active_masks.aliases[index]].clone()
        });
        let expected: [E::F; CHUNK_BYTES] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("expected_{index}")))
        });
        let doc_type_chunks: [E::F; DOC_TYPE_CHUNKS] = std::array::from_fn(|index| {
            eval.get_preprocessed_column(col_id(&format!("doc_type_chunk_{index}")))
        });
        let device_pk_start_row = eval.get_preprocessed_column(col_id("device_pk_start_row"));

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

        let one = m31_const::<E>(1);
        for selector in [
            active.clone(),
            mso_window.clone(),
            window_start.clone(),
            continuation.clone(),
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
        for selector in &doc_type_chunks {
            add_boolean(&mut eval, selector.clone(), &one);
            eval.add_constraint(selector.clone() * (active.clone() - one.clone()));
        }
        add_boolean(&mut eval, device_pk_start_row.clone(), &one);
        eval.add_constraint(device_pk_start_row.clone() * (active.clone() - one.clone()));
        // All private decomposition bits are boolean on every row.
        // Inactive rows therefore receive fresh valid bits rather than zeros.
        for bit in payload_offset_bits
            .iter()
            .chain(payload_slack_bits.iter())
            .chain(window_offset_bits.iter())
            .chain(window_slack_bits.iter())
        {
            add_boolean(&mut eval, bit.clone(), &one);
        }

        // One payload anchor is common to every active row.
        // Continuation rows retain one logical-window offset.
        eval.add_constraint(
            same_payload_prev.clone() * (payload_offset.clone() - payload_offset_prev),
        );
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
        // Fixed relation-site order: 32 issuer, 32 SHA, one MSO start,
        // one device start, two validity tuples, and the blinder.
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
        for index in 0..CHUNK_BYTES {
            eval.add_to_relation(RelationEntry::new(
                &self.sha_relation,
                E::EF::from(mirror_row.clone() * byte_active[index].clone()),
                &[
                    m31_const::<E>(self.spec.sha_stream.field_id as usize),
                    chunk_relative.clone() + m31_const::<E>(index),
                    bytes[index].clone(),
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::new(
            &self.mso_start_relation,
            -E::EF::from(anchor_row),
            &[payload_offset.clone() + m31_const::<E>(self.payload_anchor_len)],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.device_pk_start_relation,
            -E::EF::from(device_pk_start_row),
            &[payload_offset.clone()
                + m31_const::<E>(self.payload_anchor_len)
                + window_offset
                + m31_const::<E>(DEVICE_KEY_INFO_PREFIX.len())],
        ));
        for (kind, selector) in [
            (0usize, valid_from_date_row),
            (1usize, valid_until_date_row),
        ] {
            let mut tuple = Vec::with_capacity(1 + MDOC_TDATE_BYTES);
            tuple.push(m31_const::<E>(kind));
            tuple.extend(bytes.iter().take(MDOC_TDATE_BYTES).cloned());
            eval.add_to_relation(RelationEntry::new(
                &self.validity_relation,
                -E::EF::from(selector),
                &tuple,
            ));
        }
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

pub(crate) struct MdocPrivateMsoBind {
    spec: MdocPrivateMsoBindSpec,
    shape: PublicShape,
    trace: Option<MdocPrivateMsoTrace>,
    issuer_handle: SharedFieldRelation,
    sha_handle: SharedFieldRelation,
    mso_start_handle: SharedMdocMsoStartRelation,
    device_pk_start_handle: SharedMdocDevicePkStartRelation,
    validity_handle: SharedMdocMsoValidityBytesRelation,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocPrivateMsoInteractionClaim>,
    component: Option<MdocPrivateMsoComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocPrivateMsoBind {
    pub(crate) fn prover(
        spec: MdocPrivateMsoBindSpec,
        witness: MdocPrivateMsoBindWitness,
        issuer_handle: SharedFieldRelation,
        sha_handle: SharedFieldRelation,
        mso_start_handle: SharedMdocMsoStartRelation,
        device_pk_start_handle: SharedMdocDevicePkStartRelation,
        validity_handle: SharedMdocMsoValidityBytesRelation,
    ) -> Result<(Self, MdocPrivateMsoUseCensus), MdocPrivateMsoBindError> {
        let shape = validate_spec(&spec)?;
        let (trace, census) = private_trace(&spec, &shape, &witness)?;
        Ok((
            Self {
                spec,
                shape,
                trace: Some(trace),
                issuer_handle,
                sha_handle,
                mso_start_handle,
                device_pk_start_handle,
                validity_handle,
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
        sha_handle: SharedFieldRelation,
        mso_start_handle: SharedMdocMsoStartRelation,
        device_pk_start_handle: SharedMdocDevicePkStartRelation,
        validity_handle: SharedMdocMsoValidityBytesRelation,
        interaction_claim: MdocPrivateMsoInteractionClaim,
    ) -> Result<Self, MdocPrivateMsoBindError> {
        let shape = validate_spec(&spec)?;
        Ok(Self {
            spec,
            shape,
            trace: None,
            issuer_handle,
            sha_handle,
            mso_start_handle,
            device_pk_start_handle,
            validity_handle,
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

    fn sha_relation(&self) -> FieldBytesRelation {
        self.sha_handle.get()
    }

    fn n_main_sites(&self) -> usize {
        2 * CHUNK_BYTES + 5
    }

    fn interaction_columns(&self) -> usize {
        // Main batched LogUp columns plus one blinder-counterpart column.
        (self.n_main_sites().div_ceil(LOGUP_BATCH) + 1) * SECURE_EXTENSION_DEGREE
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
        channel.mix_u64(self.shape.preprocessed_cols() as u64);
        channel.mix_u64(TRACE_COLS as u64);
        channel.mix_u64(self.interaction_columns() as u64);
        channel.mix_u64(self.spec.doc_type.len() as u64);
        for &byte in self.spec.doc_type.as_bytes() {
            channel.mix_u64(u64::from(byte));
        }
        // Bind the fixed private-start layout and key length.
        channel.mix_u64(1);
        channel.mix_u64(stwo_mldsa::profile::ML_DSA_65.pk_bytes() as u64);
        channel.mix_u64(u64::from(self.spec.sha_stream.field_id));
        channel.mix_u64(self.spec.sha_stream.padded_len as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        assert!(
            !self.mso_start_handle.is_set(),
            "private MSO binder needs a fresh mso_start relation handle"
        );
        let relation = MdocMsoStartRelation::draw(channel);
        self.mso_start_handle.set(relation);

        assert!(
            !self.device_pk_start_handle.is_set(),
            "private MSO binder needs a fresh device-pk-start relation handle"
        );
        let device_pk_start_relation = MdocDevicePkStartRelation::draw(channel);
        self.device_pk_start_handle.set(device_pk_start_relation);

        assert!(
            !self.validity_handle.is_set(),
            "private MSO binder needs a fresh validity-bytes relation handle"
        );
        let validity_relation = MdocMsoValidityBytesRelation::draw(channel);
        self.validity_handle.set(validity_relation);
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; self.shape.preprocessed_cols()],
            trace: vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; TRACE_COLS],
            interaction: vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; self.interaction_columns()],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids(&self.shape)
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
                byte_active_masks: self.shape.byte_active_masks.clone(),
                issuer_active_masks: self.shape.issuer_active_masks.clone(),
                expected_active_masks: self.shape.expected_active_masks.clone(),
                issuer_relation: self.issuer_relation(),
                sha_relation: self.sha_relation(),
                mso_start_relation: self.mso_start_handle.get(),
                device_pk_start_relation: self.device_pk_start_handle.get(),
                validity_relation: self.validity_handle.get(),
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
        self.write_selected_preprocessed(tb, &preprocessed_column_ids(&self.shape));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_private_mso_bind::MdocPrivateMsoBind",
            &preprocessed_column_ids(&self.shape),
            &preprocessed_columns(&self.shape),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = preprocessed_column_ids(&self.shape);
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
        let mso_start_relation = self.mso_start_handle.get();
        let device_pk_start_relation = self.device_pk_start_handle.get();
        let validity_relation = self.validity_handle.get();
        let (interaction, claimed_sum) = private_mso_interaction_trace(
            &self.spec,
            &self.shape,
            trace,
            MdocPrivateMsoInteractionInputs {
                issuer_relation: &issuer_relation,
                sha_relation: &sha_relation,
                mso_start_relation: &mso_start_relation,
                device_pk_start_relation: &device_pk_start_relation,
                validity_relation: &validity_relation,
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
    const TS13_DEMO_PREPROCESSED_COLS: usize = 67;
    const MAX_PROFILE_PREPROCESSED_COLS: usize = 65;

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

    fn test_spec() -> MdocPrivateMsoBindSpec {
        MdocPrivateMsoBindSpec {
            issuer_message_len: crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES,
            mso_len: crate::ts13::TS13_MAX_MSO_PAYLOAD_BYTES,
            doc_type: PID.to_string(),
            sha_stream: MdocPrivateMsoShaStreamSpec {
                field_id: 91,
                padded_len: 4_160,
            },
        }
    }

    fn write_at(target: &mut [u8], offset: usize, bytes: &[u8]) {
        target[offset..offset + bytes.len()].copy_from_slice(bytes);
    }

    fn fixture_device_key_info() -> Vec<u8> {
        let mut run = DEVICE_KEY_INFO_PREFIX.to_vec();
        run.extend((0..stwo_mldsa::profile::ML_DSA_65.pk_bytes()).map(|index| (index * 73) as u8));
        run
    }

    fn test_parts_for_spec(
        spec: MdocPrivateMsoBindSpec,
    ) -> (MdocPrivateMsoBindSpec, Vec<u8>, Vec<u8>) {
        let mut mso = vec![0x55; spec.mso_len];

        write_at(&mut mso, VERSION_OFFSET, VERSION_1_0_RUN);
        write_at(&mut mso, ALGORITHM_OFFSET, DIGEST_ALGORITHM_RUN);
        write_at(
            &mut mso,
            DOC_TYPE_OFFSET,
            &canonical_doc_type_run(&spec.doc_type),
        );
        write_at(&mut mso, DEVICE_KEY_OFFSET, &fixture_device_key_info());
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

    fn test_parts() -> (MdocPrivateMsoBindSpec, Vec<u8>, Vec<u8>) {
        test_parts_for_spec(test_spec())
    }

    fn test_witness(
        spec: &MdocPrivateMsoBindSpec,
        issuer_message: Vec<u8>,
        mso: &[u8],
    ) -> MdocPrivateMsoBindWitness {
        MdocPrivateMsoBindWitness::from_canonical_issuer_message(spec, issuer_message, mso).unwrap()
    }

    fn test_binder() -> (MdocPrivateMsoBind, MdocPrivateMsoUseCensus) {
        let (spec, issuer_message, mso) = test_parts();
        let witness = test_witness(&spec, issuer_message, &mso);
        MdocPrivateMsoBind::prover(
            spec,
            witness,
            SharedFieldRelation::new(),
            SharedFieldRelation::new(),
            SharedMdocMsoStartRelation::new(),
            SharedMdocDevicePkStartRelation::new(),
            SharedMdocMsoValidityBytesRelation::new(),
        )
        .unwrap()
    }

    fn test_binder_with_witness() -> (
        MdocPrivateMsoBind,
        MdocPrivateMsoUseCensus,
        MdocPrivateMsoBindWitness,
    ) {
        let (spec, issuer_message, mso) = test_parts();
        let witness = test_witness(&spec, issuer_message, &mso);
        let witness_copy = witness.clone();
        let (binder, census) = MdocPrivateMsoBind::prover(
            spec,
            witness,
            SharedFieldRelation::new(),
            SharedFieldRelation::new(),
            SharedMdocMsoStartRelation::new(),
            SharedMdocDevicePkStartRelation::new(),
            SharedMdocMsoValidityBytesRelation::new(),
        )
        .unwrap();
        (binder, census, witness_copy)
    }

    fn logical_value(column: &MdocPrivateMsoColumnEval, index: usize) -> M31 {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(index, MDOC_PRIVATE_MSO_BIND_LOG_SIZE),
            MDOC_PRIVATE_MSO_BIND_LOG_SIZE,
        );
        column.values.at(row)
    }

    fn assert_mask_aliases_match(
        name: &str,
        rows: &[PublicRow],
        aliases: &ByteMaskAliases,
        value: fn(&PublicRow, usize) -> bool,
    ) {
        for byte_index in 0..CHUNK_BYTES {
            let representative = aliases.representative(byte_index);
            assert!(
                rows.iter()
                    .all(|row| value(row, byte_index) == value(row, representative)),
                "{name} byte {byte_index} differs from representative {representative}"
            );
        }
        for (index, &representative) in aliases.representatives.iter().enumerate() {
            assert!(
                rows.iter().any(|row| value(row, representative)),
                "{name} representative {representative} is dead"
            );
            for &previous in &aliases.representatives[..index] {
                assert!(
                    rows.iter()
                        .any(|row| value(row, representative) != value(row, previous)),
                    "{name} representatives {previous} and {representative} are duplicates"
                );
            }
        }
    }

    #[derive(Clone, Copy)]
    struct TestCounterRow {
        issuer: u32,
        sha: u32,
        start: u32,
        device_start: u32,
        validity: u32,
        field_id: u32,
        index: u32,
        byte: u32,
        validity_bytes: [u8; MDOC_TDATE_BYTES],
    }

    impl TestCounterRow {
        fn issuer(index: usize, byte: u8) -> Self {
            Self {
                issuer: 1,
                sha: 0,
                start: 0,
                device_start: 0,
                validity: 0,
                field_id: HOSTED_MSG_FIELD_ID,
                index: index as u32,
                byte: u32::from(byte),
                validity_bytes: [0; MDOC_TDATE_BYTES],
            }
        }

        fn sha(field_id: u32, index: usize, byte: u8) -> Self {
            Self {
                issuer: 0,
                sha: 1,
                start: 0,
                device_start: 0,
                validity: 0,
                field_id,
                index: index as u32,
                byte: u32::from(byte),
                validity_bytes: [0; MDOC_TDATE_BYTES],
            }
        }

        fn start(index: usize, active: bool) -> Self {
            Self {
                issuer: 0,
                sha: 0,
                start: u32::from(active),
                device_start: 0,
                validity: 0,
                field_id: 0,
                index: index as u32,
                byte: 0,
                validity_bytes: [0; MDOC_TDATE_BYTES],
            }
        }

        fn device_start(index: usize) -> Self {
            Self {
                issuer: 0,
                sha: 0,
                start: 0,
                device_start: 1,
                validity: 0,
                field_id: 0,
                index: index as u32,
                byte: 0,
                validity_bytes: [0; MDOC_TDATE_BYTES],
            }
        }

        fn validity(kind: u32, bytes: [u8; MDOC_TDATE_BYTES]) -> Self {
            Self {
                issuer: 0,
                sha: 0,
                start: 0,
                device_start: 0,
                validity: 1,
                field_id: kind,
                index: 0,
                byte: 0,
                validity_bytes: bytes,
            }
        }
    }

    const TEST_COUNTER_COLS: usize = TEST_VALIDITY_BYTES + MDOC_TDATE_BYTES;
    const TEST_ISSUER: usize = 0;
    const TEST_SHA: usize = 1;
    const TEST_START: usize = 2;
    const TEST_DEVICE_START: usize = 3;
    const TEST_VALIDITY: usize = 4;
    const TEST_FIELD_ID: usize = 5;
    const TEST_INDEX: usize = 6;
    const TEST_BYTE: usize = 7;
    const TEST_VALIDITY_BYTES: usize = 8;

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
                row.device_start,
                row.validity,
                row.field_id,
                row.index,
                row.byte,
            ]
            .into_iter()
            .enumerate()
            {
                columns[column][index] = m31_u32(value);
            }
            for (byte_index, byte) in row.validity_bytes.iter().copied().enumerate() {
                columns[TEST_VALIDITY_BYTES + byte_index][index] = m31_u32(u32::from(byte));
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
        device_start: MdocDevicePkStartRelation,
        validity: MdocMsoValidityBytesRelation,
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
            let device_start = eval.next_trace_mask();
            let validity = eval.next_trace_mask();
            let field_id = eval.next_trace_mask();
            let index = eval.next_trace_mask();
            let byte = eval.next_trace_mask();
            let validity_bytes: [E::F; MDOC_TDATE_BYTES] =
                std::array::from_fn(|_| eval.next_trace_mask());
            let one = E::F::from(m31_u32(1));
            for selector in [&issuer, &sha, &start, &device_start, &validity] {
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
                &[field_id.clone(), index.clone(), byte.clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.start,
                E::EF::from(start),
                std::slice::from_ref(&index),
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.device_start,
                E::EF::from(device_start),
                &[index],
            ));
            let mut validity_tuple = Vec::with_capacity(1 + MDOC_TDATE_BYTES);
            validity_tuple.push(field_id);
            validity_tuple.extend(validity_bytes);
            eval.add_to_relation(RelationEntry::new(
                &self.validity,
                E::EF::from(validity),
                &validity_tuple,
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
        device_start_relation: &MdocDevicePkStartRelation,
        validity_relation: &MdocMsoValidityBytesRelation,
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
            let start_denominator: PackedQM31 =
                start_relation.combine(&[trace[TEST_INDEX].data[vec_row]]);
            let device_denominator: PackedQM31 =
                device_start_relation.combine(&[trace[TEST_INDEX].data[vec_row]]);
            let start_numerator = PackedQM31::from(trace[TEST_START].data[vec_row]);
            let device_numerator = PackedQM31::from(trace[TEST_DEVICE_START].data[vec_row]);
            (
                start_numerator * device_denominator + device_numerator * start_denominator,
                start_denominator * device_denominator,
            )
        }));
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let mut tuple = Vec::with_capacity(1 + MDOC_TDATE_BYTES);
            tuple.push(trace[TEST_FIELD_ID].data[vec_row]);
            tuple.extend(
                (0..MDOC_TDATE_BYTES).map(|index| trace[TEST_VALIDITY_BYTES + index].data[vec_row]),
            );
            (
                PackedQM31::from(trace[TEST_VALIDITY].data[vec_row]),
                validity_relation.combine(&tuple),
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
        device_start_handle: SharedMdocDevicePkStartRelation,
        validity_handle: SharedMdocMsoValidityBytesRelation,
        component: Option<FrameworkComponent<TestCounterEval>>,
    }

    impl TestRelationCounter {
        fn new(
            rows: Vec<TestCounterRow>,
            issuer_handle: SharedFieldRelation,
            sha_handle: SharedFieldRelation,
            start_handle: SharedMdocMsoStartRelation,
            device_start_handle: SharedMdocDevicePkStartRelation,
            validity_handle: SharedMdocMsoValidityBytesRelation,
        ) -> Self {
            Self {
                log_size: test_counter_log_size(rows.len()),
                rows,
                issuer_handle,
                sha_handle,
                start_handle,
                device_start_handle,
                validity_handle,
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
                &self.device_start_handle.get(),
                &self.validity_handle.get(),
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
                    sha: self.sha_handle.get(),
                    start: self.start_handle.get(),
                    device_start: self.device_start_handle.get(),
                    validity: self.validity_handle.get(),
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
                if matches!(index, TRACE_PAYLOAD_OFFSET | TRACE_WINDOW_OFFSET) {
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

        fn finalize_logup_batched(&mut self, _batch_size: usize) {}
    }

    fn test_eval(spec: &MdocPrivateMsoBindSpec, shape: &PublicShape) -> MdocPrivateMsoEval {
        MdocPrivateMsoEval {
            spec: spec.clone(),
            payload_anchor_len: shape.payload_anchor.len(),
            byte_active_masks: shape.byte_active_masks.clone(),
            issuer_active_masks: shape.issuer_active_masks.clone(),
            expected_active_masks: shape.expected_active_masks.clone(),
            issuer_relation: FieldBytesRelation::dummy(),
            sha_relation: FieldBytesRelation::dummy(),
            mso_start_relation: MdocMsoStartRelation::dummy(),
            device_pk_start_relation: MdocDevicePkStartRelation::dummy(),
            validity_relation: MdocMsoValidityBytesRelation::dummy(),
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
        let sha = &spec.sha_stream;
        let raw_mso = &issuer_message[mso_start..mso_start + spec.mso_len];
        let padded = padded_mso(raw_mso, sha.padded_len);
        let valid_from_start = mso_start + VALID_FROM_OFFSET + VALID_FROM_ANCHOR.len();
        let valid_until_start = mso_start + VALID_UNTIL_OFFSET + VALID_UNTIL_ANCHOR.len();
        let valid_from = issuer_message[valid_from_start..valid_from_start + MDOC_TDATE_BYTES]
            .try_into()
            .unwrap();
        let valid_until = issuer_message[valid_until_start..valid_until_start + MDOC_TDATE_BYTES]
            .try_into()
            .unwrap();
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
                TestCounterRow::start(mso_start, true),
                TestCounterRow::start(mso_start, false),
                TestCounterRow::device_start(
                    mso_start + DEVICE_KEY_OFFSET + DEVICE_KEY_INFO_PREFIX.len(),
                ),
                TestCounterRow::validity(0, valid_from),
                TestCounterRow::validity(1, valid_until),
            ])
            .collect()
    }

    fn prove_composed_mso(config: stwo::core::pcs::PcsConfig) -> TestComposedMsoProof {
        let (spec, issuer_message, mso) = test_parts();
        let witness = test_witness(&spec, issuer_message.clone(), &mso);
        let mso_start = witness.payload_anchor_offset + payload_anchor(spec.mso_len).len();
        let issuer_handle = SharedFieldRelation::new();
        let sha_handle = SharedFieldRelation::new();
        let start_handle = SharedMdocMsoStartRelation::new();
        let device_start_handle = SharedMdocDevicePkStartRelation::new();
        let validity_handle = SharedMdocMsoValidityBytesRelation::new();
        let (mut binder, census) = MdocPrivateMsoBind::prover(
            spec.clone(),
            witness,
            issuer_handle.clone(),
            sha_handle.clone(),
            start_handle.clone(),
            device_start_handle.clone(),
            validity_handle.clone(),
        )
        .unwrap();
        let counter_rows = honest_counter_rows(&spec, &issuer_message, mso_start, &census);
        let mut counter = TestRelationCounter::new(
            counter_rows.clone(),
            issuer_handle,
            sha_handle,
            start_handle,
            device_start_handle,
            validity_handle,
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
        let device_start_handle = SharedMdocDevicePkStartRelation::new();
        let validity_handle = SharedMdocMsoValidityBytesRelation::new();
        let mut counter = TestRelationCounter::new(
            counter_rows,
            issuer_handle.clone(),
            sha_handle.clone(),
            start_handle.clone(),
            device_start_handle.clone(),
            validity_handle.clone(),
        );
        let mut binder = MdocPrivateMsoBind::verifier(
            fixture.spec.clone(),
            issuer_handle,
            sha_handle,
            start_handle,
            device_start_handle,
            validity_handle,
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
        let fixture = prove_composed_mso(crate::mdoc::mdoc_ts13_pcs_config());
        verify_composed_mso(&fixture, fixture.counter_rows.clone())
            .expect("canonical private MSO relation composition must verify");

        assert_counter_mutation_rejects(&fixture, "shifted payload anchor", |rows| {
            rows.iter_mut()
                .find(|row| row.issuer == 1 && row.index == PAYLOAD_OFFSET as u32)
                .unwrap()
                .index += 1;
        });
        assert_counter_mutation_rejects(&fixture, "shifted mso_start", |rows| {
            rows.iter_mut().find(|row| row.start == 1).unwrap().index += 1;
        });
        assert_counter_mutation_rejects(&fixture, "shifted device key start", |rows| {
            rows.iter_mut()
                .find(|row| row.device_start == 1)
                .unwrap()
                .index += 1;
        });
        assert_counter_mutation_rejects(&fixture, "valid-from byte", |rows| {
            rows.iter_mut()
                .find(|row| row.validity == 1 && row.field_id == 0)
                .unwrap()
                .validity_bytes[0] ^= 1;
        });
        assert_counter_mutation_rejects(&fixture, "valid-until byte", |rows| {
            rows.iter_mut()
                .find(|row| row.validity == 1 && row.field_id == 1)
                .unwrap()
                .validity_bytes[19] ^= 1;
        });
        assert_counter_mutation_rejects(&fixture, "validity endpoint kind", |rows| {
            rows.iter_mut()
                .find(|row| row.validity == 1 && row.field_id == 0)
                .unwrap()
                .field_id = 1;
        });
        assert_counter_mutation_rejects(&fixture, "missing validity endpoint", |rows| {
            rows.iter_mut()
                .find(|row| row.validity == 1 && row.field_id == 0)
                .unwrap()
                .validity = 0;
        });
        assert_counter_mutation_rejects(&fixture, "swapped validity endpoints", |rows| {
            let from = rows
                .iter()
                .position(|row| row.validity == 1 && row.field_id == 0)
                .unwrap();
            let until = rows
                .iter()
                .position(|row| row.validity == 1 && row.field_id == 1)
                .unwrap();
            let from_bytes = rows[from].validity_bytes;
            rows[from].validity_bytes = rows[until].validity_bytes;
            rows[until].validity_bytes = from_bytes;
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
                fixture.spec.sha_stream.padded_len - 1,
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
    fn alternate_same_width_issuer_algorithm_is_rejected_by_the_production_air() {
        let (spec, issuer_message, mso) = test_parts();
        let mut witness = test_witness(&spec, issuer_message, &mso);
        let algorithm_argument = PAYLOAD_OFFSET
            + ISSUER_SIGNATURE1_CONTEXT_PREFIX.len()
            + crate::mdoc::MLDSA_PROTECTED_HEADER.len()
            - 1;
        witness.issuer_message[algorithm_argument] = 0x31;
        let alternate_issuer_message = witness.issuer_message.clone();
        let mso_start = witness.mso_start(spec.mso_len).unwrap();

        let issuer_handle = SharedFieldRelation::new();
        let sha_handle = SharedFieldRelation::new();
        let start_handle = SharedMdocMsoStartRelation::new();
        let device_start_handle = SharedMdocDevicePkStartRelation::new();
        let validity_handle = SharedMdocMsoValidityBytesRelation::new();
        let (mut binder, census) = MdocPrivateMsoBind::prover(
            spec.clone(),
            witness,
            issuer_handle.clone(),
            sha_handle.clone(),
            start_handle.clone(),
            device_start_handle.clone(),
            validity_handle.clone(),
        )
        .expect("test bypasses host extraction and reaches the circuit AIR");
        let counter_rows =
            honest_counter_rows(&spec, &alternate_issuer_message, mso_start, &census);
        let mut counter = TestRelationCounter::new(
            counter_rows,
            issuer_handle,
            sha_handle,
            start_handle,
            device_start_handle,
            validity_handle,
        );
        let error = air_core::prove(
            &mut [&mut counter, &mut binder],
            crate::mdoc::mdoc_ts13_pcs_config(),
        )
        .expect_err(
            "the canonical protected-header constraint must reject the alternate algorithm",
        );
        assert!(
            matches!(error, stwo::prover::ProvingError::ConstraintsNotSatisfied),
            "alternate algorithm failed with the wrong prover error: {error}"
        );
    }

    #[test]
    fn minimum_blowup_proves_the_linearized_mso_degree_bound() {
        let fixture = prove_composed_mso(stwo::core::pcs::PcsConfig::default());
        verify_composed_mso(&fixture, fixture.counter_rows.clone())
            .expect("coefficient-backed minimum-blowup MSO proof must verify");
    }

    #[test]
    fn canonical_constructor_derives_unique_offsets_and_rejects_ambiguity() {
        let (spec, mut issuer_message, mut mso) = test_parts();
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

        write_at(&mut mso, 3_000, VERSION_1_0_RUN);
        write_at(
            &mut issuer_message,
            PAYLOAD_OFFSET + payload_anchor(spec.mso_len).len(),
            &mso,
        );
        assert_eq!(
            MdocPrivateMsoBindWitness::from_canonical_issuer_message(&spec, issuer_message, &mso)
                .unwrap_err(),
            MdocPrivateMsoBindError::CanonicalAnchorAmbiguous {
                anchor: "MSO version"
            }
        );
    }

    #[test]
    fn ts13_demo_payload_anchor_is_the_complete_canonical_signature1_prefix() {
        let anchor = payload_anchor(crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES);
        assert_eq!(
            anchor,
            b"\x84\x6aSignature1\x44\xa1\x01\x38\x30\x40\x59\x09\xd1"
        );
        assert_eq!(
            anchor.len() + crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES,
            crate::mdoc::TS13_DEMO_ISSUER_MESSAGE_BYTES,
            "the fixed issuer Sig_structure is exactly prefix || private MSO"
        );
    }

    #[test]
    fn canonical_shape_census_and_witness_handoffs_are_exact() {
        let (binder, census, witness) = test_binder_with_witness();
        assert_eq!(TRACE_COLS, 88);
        assert_eq!(
            binder.shape.preprocessed_cols(),
            MAX_PROFILE_PREPROCESSED_COLS
        );
        assert_eq!(binder.active_rows(), 140);
        assert_eq!(census.active_rows, 140);
        assert_eq!(census.blind_rows, 372);
        assert_eq!(census.issuer_uses_total, 4_285);
        assert_eq!(census.sha_stream_uses, 4_160);
        assert_eq!(census.mso_start_uses, 1);
        assert_eq!(census.device_pk_start_uses, 1);
        assert_eq!(census.validity_uses, 2);
        assert_eq!(binder.n_main_sites(), 69);
        assert_eq!(binder.interaction_columns(), 19 * SECURE_EXTENSION_DEGREE);

        let expected_start = PAYLOAD_OFFSET
            + payload_anchor(binder.spec.mso_len).len()
            + DEVICE_KEY_OFFSET
            + DEVICE_KEY_INFO_PREFIX.len();
        assert_eq!(
            witness.device_pk_start(&binder.spec).unwrap(),
            expected_start
        );
        let validity = witness.validity_witness(&binder.spec).unwrap();
        assert_eq!(validity.valid_from, *b"2020-01-01T00:00:00Z");
        assert_eq!(validity.valid_until, *b"2030-12-31T23:59:59Z");
    }

    #[test]
    fn ts13_demo_mask_aliases_preserve_every_logical_selector() {
        let spec = MdocPrivateMsoBindSpec {
            issuer_message_len: crate::mdoc::TS13_DEMO_ISSUER_MESSAGE_BYTES,
            mso_len: crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES,
            doc_type: PID.to_string(),
            sha_stream: MdocPrivateMsoShaStreamSpec {
                field_id: 91,
                padded_len: checked_sha_padded_len(crate::mdoc::TS13_DEMO_MSO_PAYLOAD_BYTES)
                    .unwrap(),
            },
        };
        let shape = validate_spec(&spec).unwrap();
        assert_eq!(shape.byte_active_masks.representatives.len(), 7);
        assert_eq!(shape.issuer_active_masks.representatives.len(), 8);
        assert_eq!(shape.expected_active_masks.representatives.len(), 7);
        assert_eq!(shape.preprocessed_cols(), TS13_DEMO_PREPROCESSED_COLS);

        let ids = preprocessed_column_ids(&shape);
        assert_eq!(ids.len(), TS13_DEMO_PREPROCESSED_COLS);
        for (index, id) in ids.iter().enumerate() {
            assert!(
                ids[..index].iter().all(|previous| previous != id),
                "duplicate physical preprocessed id: {id:?}"
            );
        }

        let columns = preprocessed_columns(&shape);
        for row_index in 0..MDOC_PRIVATE_MSO_BIND_ROWS {
            let row = shape.rows.get(row_index);
            for byte_index in 0..CHUNK_BYTES {
                let byte_active = row.is_some_and(|row| byte_index < row.byte_len);
                let issuer_active = row.is_some_and(|row| row.issuer_active[byte_index]);
                let expected_active = row.is_some_and(|row| row.expected_active[byte_index]);
                assert_eq!(
                    logical_value(&columns[shape.byte_active_column(byte_index)], row_index),
                    m31_u32(u32::from(byte_active)),
                    "byte-active alias mismatch at row {row_index}, byte {byte_index}"
                );
                assert_eq!(
                    logical_value(&columns[shape.issuer_active_column(byte_index)], row_index),
                    m31_u32(u32::from(issuer_active)),
                    "issuer-active alias mismatch at row {row_index}, byte {byte_index}"
                );
                assert_eq!(
                    logical_value(
                        &columns[shape.expected_active_column(byte_index)],
                        row_index,
                    ),
                    m31_u32(u32::from(expected_active)),
                    "expected-active alias mismatch at row {row_index}, byte {byte_index}"
                );
            }
        }

        assert_mask_aliases_match(
            "byte-active",
            &shape.rows,
            &shape.byte_active_masks,
            |row, index| index < row.byte_len,
        );
        assert_mask_aliases_match(
            "issuer-active",
            &shape.rows,
            &shape.issuer_active_masks,
            |row, index| row.issuer_active[index],
        );
        assert_mask_aliases_match(
            "expected-active",
            &shape.rows,
            &shape.expected_active_masks,
            |row, index| row.expected_active[index],
        );
    }

    #[test]
    fn canonical_binder_publishes_owned_relation_handles() {
        let (spec, issuer_message, mso) = test_parts();
        let witness = test_witness(&spec, issuer_message, &mso);
        let sha = SharedFieldRelation::new();
        let mso_start = SharedMdocMsoStartRelation::new();
        let device_start = SharedMdocDevicePkStartRelation::new();
        let validity = SharedMdocMsoValidityBytesRelation::new();
        let (mut binder, _) = MdocPrivateMsoBind::prover(
            spec,
            witness,
            SharedFieldRelation::new(),
            sha.clone(),
            mso_start.clone(),
            device_start.clone(),
            validity.clone(),
        )
        .unwrap();
        let mut channel = Blake2sChannel::default();
        binder.draw_relations(&mut channel);
        assert!(!sha.is_set());
        assert!(mso_start.is_set());
        assert!(device_start.is_set());
        assert!(validity.is_set());
    }

    #[test]
    fn private_device_key_is_absent_from_tree_zero_and_public_mix() {
        let (spec, first_message, first_mso) = test_parts();
        let mut second_message = first_message.clone();
        let mut second_mso = first_mso.clone();
        let key_offset = DEVICE_KEY_OFFSET + DEVICE_KEY_INFO_PREFIX.len();
        for index in 0..stwo_mldsa::profile::ML_DSA_65.pk_bytes() {
            second_mso[key_offset + index] ^= 0x5a;
        }
        let mso_start = PAYLOAD_OFFSET + payload_anchor(spec.mso_len).len();
        second_message[mso_start..mso_start + spec.mso_len].copy_from_slice(&second_mso);

        let first_witness = test_witness(&spec, first_message, &first_mso);
        let second_witness = test_witness(&spec, second_message, &second_mso);
        let handles = || {
            (
                SharedFieldRelation::new(),
                SharedFieldRelation::new(),
                SharedMdocMsoStartRelation::new(),
                SharedMdocDevicePkStartRelation::new(),
                SharedMdocMsoValidityBytesRelation::new(),
            )
        };
        let (issuer, sha, mso_start, device_start, validity) = handles();
        let (mut first, _) = MdocPrivateMsoBind::prover(
            spec.clone(),
            first_witness,
            issuer,
            sha,
            mso_start,
            device_start,
            validity,
        )
        .unwrap();
        let (issuer, sha, mso_start, device_start, validity) = handles();
        let (mut second, _) = MdocPrivateMsoBind::prover(
            spec,
            second_witness,
            issuer,
            sha,
            mso_start,
            device_start,
            validity,
        )
        .unwrap();

        assert_eq!(
            first.preprocessed_column_fingerprints(),
            second.preprocessed_column_fingerprints()
        );
        let first_root = air_core::compute_preprocessed_root_uncached(
            &mut [&mut first],
            stwo::core::pcs::PcsConfig::default(),
        );
        let second_root = air_core::compute_preprocessed_root_uncached(
            &mut [&mut second],
            stwo::core::pcs::PcsConfig::default(),
        );
        assert_eq!(first_root, second_root);
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
    fn precise_public_shape_and_private_offset_errors_reject_before_trace_allocation() {
        let mut spec = test_spec();
        spec.issuer_message_len = crate::ts13::TS13_MAX_ISSUER_MLDSA_MESSAGE_BYTES + 1;
        assert!(matches!(
            validate_spec(&spec),
            Err(MdocPrivateMsoBindError::IssuerMessageTooLong { .. })
        ));

        let mut spec = test_spec();
        spec.sha_stream.padded_len -= 64;
        assert!(matches!(
            validate_spec(&spec),
            Err(MdocPrivateMsoBindError::ShaPaddedLengthMismatch { .. })
        ));

        let mut spec = test_spec();
        spec.doc_type = "x".repeat(MDOC_PRIVATE_MSO_MAX_DOC_TYPE_BYTES + 1);
        assert!(matches!(
            validate_spec(&spec),
            Err(MdocPrivateMsoBindError::DocTypeTooLong { .. })
        ));

        let (spec, issuer_message, mso) = test_parts();
        let mut witness = test_witness(&spec, issuer_message, &mso);
        witness.version_offset = spec.mso_len - 1;
        let shape = validate_spec(&spec).unwrap();
        assert!(matches!(
            private_trace(&spec, &shape, &witness),
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
        let (binder, _) = test_binder();
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
    fn canonical_anchors_offsets_prefix_and_padding_mutations_reject() {
        let (binder, _) = test_binder();
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

        let mut protected_algorithm = honest.clone();
        let protected_algorithm_byte =
            ISSUER_SIGNATURE1_CONTEXT_PREFIX.len() + crate::mdoc::MLDSA_PROTECTED_HEADER.len() - 1;
        protected_algorithm.columns[TRACE_BYTE_START + protected_algorithm_byte][0] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &protected_algorithm, 0);

        let mut payload_bits = honest.clone();
        payload_bits.columns[TRACE_PAYLOAD_OFFSET_BITS][0] =
            m31_u32(1) - payload_bits.columns[TRACE_PAYLOAD_OFFSET_BITS][0];
        assert_row_rejects(&binder.spec, &binder.shape, &payload_bits, 0);

        let mut shifted_window = honest.clone();
        shifted_window.columns[TRACE_WINDOW_OFFSET][2] += m31_u32(1);
        assert_row_rejects(&binder.spec, &binder.shape, &shifted_window, 2);

        let mut version = honest.clone();
        version.columns[TRACE_BYTE_START + VERSION_1_0_RUN.len() - 3][1] = m31_u32(b'9' as u32);
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

        let padding_marker_row = 138;
        let mut padding = honest.clone();
        padding.columns[TRACE_BYTE_START][padding_marker_row] = m31_u32(0);
        assert_row_rejects(&binder.spec, &binder.shape, &padding, padding_marker_row);
    }

    #[test]
    fn relation_claim_changes_for_raw_byte_and_fully_shifted_payload_mutations() {
        let (binder, _) = test_binder();
        let mut channel = Blake2sChannel::default();
        let issuer = FieldBytesRelation::draw(&mut channel);
        let sha = FieldBytesRelation::draw(&mut channel);
        let start = MdocMsoStartRelation::draw(&mut channel);
        let device_start = MdocDevicePkStartRelation::draw(&mut channel);
        let validity = MdocMsoValidityBytesRelation::draw(&mut channel);
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
                    sha_relation: &sha,
                    mso_start_relation: &start,
                    device_pk_start_relation: &device_start,
                    validity_relation: &validity,
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
        let (spec, issuer_message, mso) = test_parts();
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
            SharedFieldRelation::new(),
            SharedMdocMsoStartRelation::new(),
            SharedMdocDevicePkStartRelation::new(),
            SharedMdocMsoValidityBytesRelation::new(),
        )
        .unwrap();
        let (mut second, _) = MdocPrivateMsoBind::prover(
            spec,
            second_witness,
            SharedFieldRelation::new(),
            SharedFieldRelation::new(),
            SharedMdocMsoStartRelation::new(),
            SharedMdocDevicePkStartRelation::new(),
            SharedMdocMsoValidityBytesRelation::new(),
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
        let (first_spec, first_message, first_mso) = test_parts();
        let mut second_spec = first_spec.clone();
        second_spec.doc_type = "a".repeat(first_spec.doc_type.len());
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
            SharedFieldRelation::new(),
            SharedMdocMsoStartRelation::new(),
            SharedMdocDevicePkStartRelation::new(),
            SharedMdocMsoValidityBytesRelation::new(),
        )
        .unwrap();
        let (mut second, _) = MdocPrivateMsoBind::prover(
            second_spec,
            second_witness,
            SharedFieldRelation::new(),
            SharedFieldRelation::new(),
            SharedMdocMsoStartRelation::new(),
            SharedMdocDevicePkStartRelation::new(),
            SharedMdocMsoValidityBytesRelation::new(),
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
    fn inactive_decomposition_bits_are_fresh_and_boolean() {
        let (first, _) = test_binder();
        let (second, _) = test_binder();
        let inactive = first.active_rows();
        let first = first.trace.as_ref().unwrap();
        let second = second.trace.as_ref().unwrap();
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
            ] {
                assert!(first.columns[start..start + OFFSET_BITS]
                    .iter()
                    .all(|column| matches!(column[row].0, 0 | 1)));
            }
        }
    }

    #[test]
    fn layout_claim_shape_site_order_and_component_order_are_fixed() {
        let spec = test_spec();
        let issuer_handle = SharedFieldRelation::new();
        let sha_handle = SharedFieldRelation::new();
        let start_handle = SharedMdocMsoStartRelation::new();
        let device_start_handle = SharedMdocDevicePkStartRelation::new();
        let validity_handle = SharedMdocMsoValidityBytesRelation::new();
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
            sha_handle,
            start_handle.clone(),
            device_start_handle.clone(),
            validity_handle.clone(),
            decoded,
        )
        .unwrap();
        assert_eq!(verifier.n_main_sites(), 69);
        assert_eq!(
            verifier.layout().preprocessed,
            vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; MAX_PROFILE_PREPROCESSED_COLS]
        );
        assert_eq!(
            verifier.layout().trace,
            vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; TRACE_COLS]
        );
        assert_eq!(
            verifier.layout().interaction,
            vec![MDOC_PRIVATE_MSO_BIND_LOG_SIZE; 19 * SECURE_EXTENSION_DEGREE]
        );
        assert_eq!(verifier.claimed_sums(), vec![qm31(1), qm31(4)]);

        verifier.draw_relations(&mut channel);
        assert!(start_handle.is_set());
        assert!(device_start_handle.is_set());
        assert!(validity_handle.is_set());
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
