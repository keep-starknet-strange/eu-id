//! Sound byte-stream parsing for mdoc CBOR.
//!
//! This component does not interpret semantic field values.
//! It consumes each byte from a SHA-padded or raw nested stream.
//! It proves that one definite-length CBOR root occupies the raw prefix.
//! It yields one [`ParsedCborByteRelation`] tuple for each raw CBOR byte.
//! A semantic component must consume each tuple.
//! Constrained parent and ordinal data identifies tokens without public offsets.

use std::fmt;

use air_core::claim_mask::{
    add_claim_mask_fraction, ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS,
};
use air_core::relations::{FieldBytesRelation, SharedFieldRelation, SharedRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use rayon::prelude::*;
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

/// The product accepts CBOR values nested to a fixed depth of eight levels.
pub(crate) const MDOC_CBOR_MAX_DEPTH: usize = 8;
const MDOC_CBOR_MIN_LOG_SIZE: u32 = 9;
const MDOC_CBOR_MAX_LOG_SIZE: u32 = 17;
pub(crate) const MDOC_CBOR_BLIND_ROWS: usize = 256;
pub(crate) const MDOC_CBOR_MAX_ACTIVE_BYTES: usize =
    (1usize << MDOC_CBOR_MAX_LOG_SIZE) - MDOC_CBOR_BLIND_ROWS;
const SHA_BLOCK_BYTES: usize = 64;
const SHA_LENGTH_BYTES: usize = 8;
const MDOC_CBOR_MESSAGE_BOUND_BITS: usize = 15;

const _: () = assert!(MDOC_CBOR_MAX_ACTIVE_BYTES == 130_816);

/// Tuple layout for [`ParsedCborByteRelation`].
pub(crate) mod parsed_cbor_tuple {
    pub(crate) const BYTE_INDEX: usize = 1;
    pub(crate) const BYTE: usize = 2;
    pub(crate) const HEADER: usize = 3;
    pub(crate) const MAJOR: usize = 4;
    pub(crate) const ARG_LO16: usize = 5;
    pub(crate) const ARG_16_31: usize = 6;
    pub(crate) const ARG_32_47: usize = 7;
    pub(crate) const ARG_HI16: usize = 8;
    pub(crate) const CONTENT_LEN: usize = 9;
    pub(crate) const ARITY: usize = 15;
}

relation!(ParsedCborByteRelation, 15);
const _: () = assert!(parsed_cbor_tuple::ARITY == 15);

/// One parser-instance output channel. The parser draws and sets this relation.
/// A semantic component reads the same handle and consumes every parsed row.
/// Callers must allocate a distinct handle per parser instance.
pub(crate) type SharedParsedCborByteRelation = SharedRelation<ParsedCborByteRelation>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocCborInputMode {
    /// Consume the complete SHA compression input, including marker, zeros and
    /// the final eight-byte big-endian bit length.
    ShaPadded,
    /// Consume raw CBOR bytes only. The unique root must end at the final active
    /// byte. This is used for recursively parsing selected tag-24 bstr content.
    Raw,
}

impl MdocCborInputMode {
    fn transcript_tag(self) -> u64 {
        match self {
            Self::ShaPadded => 0,
            Self::Raw => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocCborPhase {
    Cbor,
    Marker,
    ZeroPadding,
    LengthByte(u8),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocCborStreamError {
    EmptyInput,
    TraceTooLarge { bytes: usize },
    MessageTooLong { bytes: usize, max: usize },
    InvalidShaPadding(&'static str),
    TruncatedToken { index: usize, needed: usize },
    InvalidAdditionalInfo { index: usize, additional: u8 },
    UnsupportedContainerLength { index: usize, additional: u8 },
    NonMinimalArgument { index: usize, argument: u64 },
    InvalidSimpleValue { index: usize, additional: u8 },
    NestingTooDeep { index: usize },
    MissingContainer { index: usize },
    TrailingCbor { root_end: usize, input_len: usize },
    IncompleteRoot,
}

impl fmt::Display for MdocCborStreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => write!(f, "CBOR stream is empty"),
            Self::TraceTooLarge { bytes } => {
                write!(
                    f,
                    "CBOR stream of {bytes} bytes exceeds the parser trace bound"
                )
            }
            Self::MessageTooLong { bytes, max } => {
                write!(
                    f,
                    "CBOR message of {bytes} bytes exceeds the fixed bound {max}"
                )
            }
            Self::InvalidShaPadding(reason) => write!(f, "invalid SHA-256 padding: {reason}"),
            Self::TruncatedToken { index, needed } => {
                write!(f, "CBOR token at byte {index} needs {needed} more bytes")
            }
            Self::InvalidAdditionalInfo { index, additional } => write!(
                f,
                "CBOR token at byte {index} has invalid additional-info {additional}"
            ),
            Self::UnsupportedContainerLength { index, additional } => write!(
                f,
                "CBOR string/container at byte {index} uses unsupported {additional}-width length"
            ),
            Self::NonMinimalArgument { index, argument } => write!(
                f,
                "CBOR token at byte {index} non-minimally encodes argument {argument}"
            ),
            Self::InvalidSimpleValue { index, additional } => write!(
                f,
                "CBOR simple token at byte {index} has unsupported additional-info {additional}"
            ),
            Self::NestingTooDeep { index } => {
                write!(
                    f,
                    "CBOR nesting exceeds {} at byte {index}",
                    MDOC_CBOR_MAX_DEPTH
                )
            }
            Self::MissingContainer { index } => {
                write!(
                    f,
                    "CBOR byte {index} starts after the unique root completed"
                )
            }
            Self::TrailingCbor {
                root_end,
                input_len,
            } => write!(
                f,
                "CBOR root ends at byte {root_end}, before raw input length {input_len}"
            ),
            Self::IncompleteRoot => write!(f, "CBOR root is incomplete"),
        }
    }
}

impl std::error::Error for MdocCborStreamError {}

#[derive(Clone, Debug)]
struct DecodedHeader {
    major: u8,
    additional: u8,
    argument: u64,
    argument_width: usize,
    content_len: usize,
    span_after_header: usize,
    child_count: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct MdocCborWitnessRow {
    pub(crate) byte_index: u32,
    pub(crate) byte: u8,
    pub(crate) phase: MdocCborPhase,
    pub(crate) header: bool,
    pub(crate) major: u8,
    pub(crate) argument: u64,
    pub(crate) content_len: u32,
    pub(crate) depth: u8,
    pub(crate) parent_header_index: u32,
    pub(crate) child_ordinal: u32,
    pub(crate) map_key: bool,
    pub(crate) map_value: bool,
    pub(crate) root_end: bool,
    message_len: u32,
    remaining: u32,
    span_after_header: u32,
    child_count: u32,
    counters: [u32; MDOC_CBOR_MAX_DEPTH],
    selected: [bool; MDOC_CBOR_MAX_DEPTH],
    map_kinds: [bool; MDOC_CBOR_MAX_DEPTH],
    map_key_states: [bool; MDOC_CBOR_MAX_DEPTH],
    parent_indices: [u32; MDOC_CBOR_MAX_DEPTH],
    child_ordinals: [u32; MDOC_CBOR_MAX_DEPTH],
    ext_flags: [bool; 4],
}

impl MdocCborWitnessRow {
    pub(crate) fn argument_limbs(&self) -> [u16; 4] {
        [
            self.argument as u16,
            (self.argument >> 16) as u16,
            (self.argument >> 32) as u16,
            (self.argument >> 48) as u16,
        ]
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MdocCborWitness {
    #[cfg(test)]
    pub(crate) mode: MdocCborInputMode,
    pub(crate) message_len: usize,
    pub(crate) rows: Vec<MdocCborWitnessRow>,
    pub(crate) log_size: u32,
}

impl MdocCborWitness {
    pub(crate) fn new(bytes: &[u8], mode: MdocCborInputMode) -> Result<Self, MdocCborStreamError> {
        let message_len = match mode {
            MdocCborInputMode::ShaPadded => validate_sha_padding(bytes)?,
            MdocCborInputMode::Raw => {
                if bytes.is_empty() {
                    return Err(MdocCborStreamError::EmptyInput);
                }
                bytes.len()
            }
        };
        let log_size = parser_log_size(bytes.len())?;
        let mut rows = parse_cbor_prefix(bytes, message_len)?;

        if mode == MdocCborInputMode::ShaPadded {
            for (index, &byte) in bytes.iter().enumerate().skip(message_len) {
                let phase = if index == message_len {
                    MdocCborPhase::Marker
                } else if index < bytes.len() - SHA_LENGTH_BYTES {
                    MdocCborPhase::ZeroPadding
                } else {
                    MdocCborPhase::LengthByte((index - (bytes.len() - SHA_LENGTH_BYTES)) as u8)
                };
                rows.push(padding_row(index, byte, message_len, phase));
            }
        }
        debug_assert_eq!(rows.len(), bytes.len());

        Ok(Self {
            #[cfg(test)]
            mode,
            message_len,
            rows,
            log_size,
        })
    }

    fn with_shape(
        bytes: &[u8],
        mode: MdocCborInputMode,
        fixed_log_size: Option<u32>,
        max_message_len: Option<u32>,
    ) -> Result<Self, MdocCborStreamError> {
        let mut witness = Self::new(bytes, mode)?;
        if let Some(max) = max_message_len {
            let max = usize::try_from(max).expect("u32 message bound fits usize");
            if witness.message_len > max {
                return Err(MdocCborStreamError::MessageTooLong {
                    bytes: witness.message_len,
                    max,
                });
            }
        }
        if let Some(log_size) = fixed_log_size {
            if !(MDOC_CBOR_MIN_LOG_SIZE..=MDOC_CBOR_MAX_LOG_SIZE).contains(&log_size)
                || witness.log_size > log_size
            {
                return Err(MdocCborStreamError::TraceTooLarge { bytes: bytes.len() });
            }
            witness.log_size = log_size;
        }
        Ok(witness)
    }
}

fn parser_log_size(active_rows: usize) -> Result<u32, MdocCborStreamError> {
    let needed = active_rows
        .checked_add(MDOC_CBOR_BLIND_ROWS)
        .ok_or(MdocCborStreamError::TraceTooLarge { bytes: active_rows })?;
    let log_size = needed
        .next_power_of_two()
        .trailing_zeros()
        .max(MDOC_CBOR_MIN_LOG_SIZE);
    if log_size > MDOC_CBOR_MAX_LOG_SIZE {
        return Err(MdocCborStreamError::TraceTooLarge { bytes: active_rows });
    }
    Ok(log_size)
}

fn validate_sha_padding(bytes: &[u8]) -> Result<usize, MdocCborStreamError> {
    if bytes.is_empty() {
        return Err(MdocCborStreamError::EmptyInput);
    }
    if !bytes.len().is_multiple_of(SHA_BLOCK_BYTES) {
        return Err(MdocCborStreamError::InvalidShaPadding(
            "compression input is not block-aligned",
        ));
    }
    let length_start =
        bytes
            .len()
            .checked_sub(SHA_LENGTH_BYTES)
            .ok_or(MdocCborStreamError::InvalidShaPadding(
                "missing eight-byte length",
            ))?;
    let bit_len = u64::from_be_bytes(
        bytes[length_start..]
            .try_into()
            .expect("length suffix has eight bytes"),
    );
    if bit_len % 8 != 0 {
        return Err(MdocCborStreamError::InvalidShaPadding(
            "bit length is not byte-aligned",
        ));
    }
    let message_len = usize::try_from(bit_len / 8).map_err(|_| {
        MdocCborStreamError::InvalidShaPadding("bit length does not fit the host index")
    })?;
    if message_len >= length_start {
        return Err(MdocCborStreamError::InvalidShaPadding(
            "marker does not precede the length suffix",
        ));
    }
    if bytes[message_len] != 0x80 {
        return Err(MdocCborStreamError::InvalidShaPadding(
            "missing 0x80 marker",
        ));
    }
    if bytes[message_len + 1..length_start]
        .iter()
        .any(|byte| *byte != 0)
    {
        return Err(MdocCborStreamError::InvalidShaPadding(
            "nonzero byte between marker and length",
        ));
    }
    let expected_len = (message_len + 9).div_ceil(SHA_BLOCK_BYTES) * SHA_BLOCK_BYTES;
    if expected_len != bytes.len() {
        return Err(MdocCborStreamError::InvalidShaPadding(
            "padding contains an extra or missing block",
        ));
    }
    Ok(message_len)
}

fn decode_header(
    bytes: &[u8],
    message_len: usize,
    index: usize,
) -> Result<DecodedHeader, MdocCborStreamError> {
    let byte = bytes[index];
    let major = byte >> 5;
    let additional = byte & 0x1f;
    let argument_width = match additional {
        0..=23 => 0,
        24 => 1,
        25 => 2,
        26 => 4,
        27 => 8,
        _ => return Err(MdocCborStreamError::InvalidAdditionalInfo { index, additional }),
    };
    if matches!(major, 2..=5) && argument_width > 2 {
        return Err(MdocCborStreamError::UnsupportedContainerLength { index, additional });
    }
    if index + argument_width >= message_len {
        return Err(MdocCborStreamError::TruncatedToken {
            index,
            needed: argument_width,
        });
    }
    let argument = if argument_width == 0 {
        u64::from(additional)
    } else {
        bytes[index + 1..=index + argument_width]
            .iter()
            .fold(0u64, |value, byte| (value << 8) | u64::from(*byte))
    };
    let minimum = match argument_width {
        0 => 0,
        1 => 24,
        2 => 1 << 8,
        4 => 1 << 16,
        8 => 1 << 32,
        _ => unreachable!(),
    };
    if argument_width != 0 && argument < minimum {
        return Err(MdocCborStreamError::NonMinimalArgument { index, argument });
    }
    if major == 7 && !(20..=23).contains(&additional) {
        return Err(MdocCborStreamError::InvalidSimpleValue { index, additional });
    }
    let content_len = if matches!(major, 2 | 3) {
        usize::try_from(argument).expect("16-bit string length fits usize")
    } else {
        0
    };
    let span_after_header =
        argument_width
            .checked_add(content_len)
            .ok_or(MdocCborStreamError::TruncatedToken {
                index,
                needed: usize::MAX,
            })?;
    if index
        .checked_add(span_after_header)
        .is_none_or(|end| end >= message_len)
    {
        return Err(MdocCborStreamError::TruncatedToken {
            index,
            needed: span_after_header,
        });
    }
    let child_count = match major {
        4 => argument as u32,
        5 => (argument as u32) * 2,
        6 => 1,
        _ => 0,
    };
    Ok(DecodedHeader {
        major,
        additional,
        argument,
        argument_width,
        content_len,
        span_after_header,
        child_count,
    })
}

fn parse_cbor_prefix(
    bytes: &[u8],
    message_len: usize,
) -> Result<Vec<MdocCborWitnessRow>, MdocCborStreamError> {
    if message_len == 0 {
        return Err(MdocCborStreamError::EmptyInput);
    }
    let mut rows = Vec::with_capacity(bytes.len());
    let mut remaining = 0u32;
    let mut counters = [0u32; MDOC_CBOR_MAX_DEPTH];
    counters[0] = 1;
    let mut map_kinds = [false; MDOC_CBOR_MAX_DEPTH];
    let mut map_key_states = [false; MDOC_CBOR_MAX_DEPTH];
    let mut parent_indices = [0u32; MDOC_CBOR_MAX_DEPTH];
    let mut child_ordinals = [0u32; MDOC_CBOR_MAX_DEPTH];

    for index in 0..message_len {
        let counters_before = counters;
        let map_kinds_before = map_kinds;
        let map_key_states_before = map_key_states;
        let parent_indices_before = parent_indices;
        let child_ordinals_before = child_ordinals;
        let remaining_before = remaining;
        let mut selected = [false; MDOC_CBOR_MAX_DEPTH];
        let mut header = false;
        let mut major = 0u8;
        let mut argument = 0u64;
        let mut content_len = 0u32;
        let mut depth = 0u8;
        let mut parent_header_index = 0u32;
        let mut child_ordinal = 0u32;
        let mut map_key = false;
        let mut map_value = false;
        let mut span_after_header = 0u32;
        let mut child_count = 0u32;
        let mut ext_flags = [false; 4];

        if remaining == 0 {
            header = true;
            let selected_depth = counters
                .iter()
                .rposition(|counter| *counter != 0)
                .ok_or(MdocCborStreamError::MissingContainer { index })?;
            selected[selected_depth] = true;
            depth = selected_depth as u8;
            parent_header_index = parent_indices[selected_depth];
            child_ordinal = child_ordinals[selected_depth];
            map_key = map_kinds[selected_depth] && map_key_states[selected_depth];
            map_value = map_kinds[selected_depth] && !map_key_states[selected_depth];

            let decoded = decode_header(bytes, message_len, index)?;
            major = decoded.major;
            argument = decoded.argument;
            content_len = decoded.content_len as u32;
            span_after_header = decoded.span_after_header as u32;
            child_count = decoded.child_count;
            if decoded.argument_width != 0 {
                ext_flags[(decoded.additional - 24) as usize] = true;
            }

            counters[selected_depth] -= 1;
            child_ordinals[selected_depth] += 1;
            if map_kinds[selected_depth] {
                map_key_states[selected_depth] = !map_key_states[selected_depth];
            }
            if decoded.child_count != 0 {
                let child_depth = selected_depth + 1;
                if child_depth >= MDOC_CBOR_MAX_DEPTH {
                    return Err(MdocCborStreamError::NestingTooDeep { index });
                }
                counters[child_depth] = decoded.child_count;
                map_kinds[child_depth] = decoded.major == 5;
                map_key_states[child_depth] = decoded.major == 5;
                parent_indices[child_depth] = index as u32;
                child_ordinals[child_depth] = 0;
            }
            remaining = decoded.span_after_header as u32;
        } else {
            remaining -= 1;
        }

        let root_end = counters.iter().all(|counter| *counter == 0) && remaining == 0;
        rows.push(MdocCborWitnessRow {
            byte_index: index as u32,
            byte: bytes[index],
            phase: MdocCborPhase::Cbor,
            header,
            major,
            argument,
            content_len,
            depth,
            parent_header_index,
            child_ordinal,
            map_key,
            map_value,
            root_end,
            message_len: message_len as u32,
            remaining: remaining_before,
            span_after_header,
            child_count,
            counters: counters_before,
            selected,
            map_kinds: map_kinds_before,
            map_key_states: map_key_states_before,
            parent_indices: parent_indices_before,
            child_ordinals: child_ordinals_before,
            ext_flags,
        });
        if root_end && index + 1 != message_len {
            return Err(MdocCborStreamError::TrailingCbor {
                root_end: index,
                input_len: message_len,
            });
        }
    }
    let complete = rows.last().is_some_and(|row| row.root_end);
    if !complete {
        return Err(MdocCborStreamError::IncompleteRoot);
    }
    Ok(rows)
}

fn padding_row(
    index: usize,
    byte: u8,
    message_len: usize,
    phase: MdocCborPhase,
) -> MdocCborWitnessRow {
    MdocCborWitnessRow {
        byte_index: index as u32,
        byte,
        phase,
        header: false,
        major: 0,
        argument: 0,
        content_len: 0,
        depth: 0,
        parent_header_index: 0,
        child_ordinal: 0,
        map_key: false,
        map_value: false,
        root_end: false,
        message_len: message_len as u32,
        remaining: 0,
        span_after_header: 0,
        child_count: 0,
        counters: [0; MDOC_CBOR_MAX_DEPTH],
        selected: [false; MDOC_CBOR_MAX_DEPTH],
        map_kinds: [false; MDOC_CBOR_MAX_DEPTH],
        map_key_states: [false; MDOC_CBOR_MAX_DEPTH],
        parent_indices: [0; MDOC_CBOR_MAX_DEPTH],
        child_ordinals: [0; MDOC_CBOR_MAX_DEPTH],
        ext_flags: [false; 4],
    }
}

const MDOC_CBOR_PREPROCESSED_COLS: usize = 3;
// Four prefix columns per extended additional-info flag factor the five-bit
// header equality into degree-three/four constraints.  The final flag column
// remains the witness-provided conjunction result.
const MDOC_CBOR_EXT_MATCH_PREFIX_COLS: usize = 4 * 4;
const MDOC_CBOR_TRACE_COLS: usize = 117 + MDOC_CBOR_EXT_MATCH_PREFIX_COLS;

type MdocCborColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocCborComponent = FrameworkComponent<MdocCborStreamEval>;

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn m31_inverse(value: u32) -> M31 {
    if value == 0 {
        m31(0)
    } else {
        M31::from(value).inverse()
    }
}

fn bits(value: u32, count: usize) -> impl Iterator<Item = M31> {
    (0..count).map(move |bit| m31((value >> bit) & 1))
}

fn minimal_high_sum(row: &MdocCborWitnessRow) -> u32 {
    let encoded = row.argument.to_be_bytes();
    if row.ext_flags[1] {
        // ai=25: the first byte must be nonzero.
        u32::from(encoded[6])
    } else if row.ext_flags[2] {
        // ai=26: the first two bytes may not both be zero.
        u32::from(encoded[4]) + u32::from(encoded[5])
    } else if row.ext_flags[3] {
        // ai=27: the first four bytes may not all be zero.
        encoded[..4].iter().map(|byte| u32::from(*byte)).sum()
    } else {
        0
    }
}

fn row_values(row: &MdocCborWitnessRow) -> Vec<M31> {
    let mut values = Vec::with_capacity(MDOC_CBOR_TRACE_COLS);
    values.push(m31(1)); // active
    values.push(m31(u32::from(row.byte)));
    values.extend(bits(u32::from(row.byte), 8));

    values.push(m31(u32::from(row.phase == MdocCborPhase::Cbor)));
    values.push(m31(u32::from(row.phase == MdocCborPhase::Marker)));
    values.push(m31(u32::from(row.phase == MdocCborPhase::ZeroPadding)));
    values.extend((0..8).map(|index| {
        m31(u32::from(
            row.phase == MdocCborPhase::LengthByte(index as u8),
        ))
    }));

    values.push(m31(u32::from(row.header)));
    values.push(m31(u32::from(row.root_end)));
    values.push(m31(u32::from(row.major)));
    values.extend((0..8).map(|major| m31(u32::from(row.header && row.major == major))));
    values.extend(row.argument_limbs().map(|limb| m31(u32::from(limb))));
    values.push(m31(row.content_len));
    values.push(m31(u32::from(row.depth)));
    values.push(m31(row.parent_header_index));
    values.push(m31(row.child_ordinal));
    values.push(m31(u32::from(row.map_key)));
    values.push(m31(u32::from(row.map_value)));
    values.push(m31(row.remaining));
    values.push(m31_inverse(row.remaining));
    values.push(m31(row.span_after_header));
    values.push(m31(row.child_count));
    values.push(m31(u32::from(row.child_count != 0)));
    values.push(m31_inverse(row.child_count));
    let selected_counter = row
        .selected
        .iter()
        .zip(row.counters)
        .find_map(|(selected, counter)| selected.then_some(counter))
        .unwrap_or(0);
    values.push(m31_inverse(selected_counter));
    values.push(m31(row.message_len));
    values.push(m31_inverse(minimal_high_sum(row)));

    let short_slack = if row.ext_flags[0] {
        (row.argument - 24) as u32
    } else {
        0
    };
    values.extend(bits(short_slack, 8));
    values.extend(row.ext_flags.map(|flag| m31(u32::from(flag))));
    for expected in 24..28 {
        let mut prefix = true;
        for bit in 0..4 {
            prefix &= ((row.byte >> bit) & 1) == ((expected >> bit) & 1);
            values.push(m31(u32::from(prefix)));
        }
    }

    let pad_slack = if row.phase == MdocCborPhase::LengthByte(0) {
        row.byte_index - row.message_len - 1
    } else {
        0
    };
    values.extend(bits(pad_slack, 6));
    values.extend(row.counters.map(m31));
    values.extend(row.selected.map(|flag| m31(u32::from(flag))));
    values.extend(row.map_kinds.map(|flag| m31(u32::from(flag))));
    values.extend(row.map_key_states.map(|flag| m31(u32::from(flag))));
    values.extend(row.parent_indices.map(m31));
    values.extend(row.child_ordinals.map(m31));
    debug_assert_eq!(values.len(), MDOC_CBOR_TRACE_COLS);
    values
}

fn inactive_row_values() -> Vec<M31> {
    let mut values = (0..MDOC_CBOR_TRACE_COLS)
        .map(|_| random_m31_cell())
        .collect::<Vec<_>>();
    // These columns encode the variable-length schedule itself. Cross-row
    // phase constraints force the inactive suffix to zero. Every private
    // byte/metadata/state column remains independently blinded.
    values[trace_col::ACTIVE] = m31(0);
    for value in &mut values[trace_col::CBOR..=22] {
        *value = m31(0);
    }
    values
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

fn column_eval(log_size: u32, values: Vec<M31>) -> MdocCborColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, values)),
    )
}

fn mdoc_cbor_base_columns_with_bound(
    witness: &MdocCborWitness,
    max_message_len: Option<u32>,
) -> Vec<Vec<M31>> {
    let n_rows = 1usize << witness.log_size;
    let bound_columns = usize::from(max_message_len.is_some()) * MDOC_CBOR_MESSAGE_BOUND_BITS;
    // Each row's cell values are an independent pure function of the witness row,
    // so compute them row-major in parallel, then transpose to column-major.
    // The transpose is pure data movement; the emitted columns are identical to a
    // serial row loop, so the committed trace is unchanged.
    let row_major: Vec<Vec<M31>> = (0..n_rows)
        .into_par_iter()
        .map(|row_index| {
            witness
                .rows
                .get(row_index)
                .map(row_values)
                .unwrap_or_else(inactive_row_values)
        })
        .collect();
    let mut columns: Vec<Vec<M31>> = Vec::with_capacity(MDOC_CBOR_TRACE_COLS + bound_columns);
    columns.par_extend(
        (0..MDOC_CBOR_TRACE_COLS)
            .into_par_iter()
            .map(|column_index| {
                let mut column = Vec::with_capacity(n_rows);
                for values in &row_major {
                    column.push(values[column_index]);
                }
                column
            }),
    );
    if let Some(max) = max_message_len {
        assert!(max <= 1 << MDOC_CBOR_MESSAGE_BOUND_BITS);
        let message_len =
            u32::try_from(witness.message_len).expect("validated CBOR message length fits u32");
        let slack = max
            .checked_sub(message_len)
            .expect("fixed CBOR message bound was validated");
        let root_end = witness.message_len - 1;
        for bit in 0..MDOC_CBOR_MESSAGE_BOUND_BITS {
            let mut column = vec![m31(0); n_rows];
            column.fill_with(random_m31_cell);
            column[root_end] = m31((slack >> bit) & 1);
            columns.push(column);
        }
    }
    columns
}

#[cfg(test)]
fn mdoc_cbor_base_columns(witness: &MdocCborWitness) -> Vec<Vec<M31>> {
    mdoc_cbor_base_columns_with_bound(witness, None)
}

fn mdoc_cbor_base_trace_with_bound(
    witness: &MdocCborWitness,
    max_message_len: Option<u32>,
) -> Vec<MdocCborColumnEval> {
    mdoc_cbor_base_columns_with_bound(witness, max_message_len)
        .into_iter()
        .map(|values| column_eval(witness.log_size, values))
        .collect()
}

#[cfg(test)]
fn mdoc_cbor_base_trace(witness: &MdocCborWitness) -> Vec<MdocCborColumnEval> {
    mdoc_cbor_base_trace_with_bound(witness, None)
}

fn preprocessed_id(log_size: u32, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/cbor_stream/log{log_size}/{name}"),
    }
}

fn preprocessed_ids(log_size: u32) -> Vec<PreProcessedColumnId> {
    vec![
        preprocessed_id(log_size, "row_index"),
        preprocessed_id(log_size, "first"),
        preprocessed_id(log_size, "last"),
    ]
}

fn mdoc_cbor_preprocessed_values(log_size: u32) -> Vec<Vec<M31>> {
    let n_rows = 1usize << log_size;
    let row_index = (0..n_rows).map(|index| m31(index as u32)).collect();
    let mut first = vec![m31(0); n_rows];
    first[0] = m31(1);
    let mut last = vec![m31(0); n_rows];
    last[n_rows - 1] = m31(1);
    vec![row_index, first, last]
}

fn mdoc_cbor_preprocessed_columns(log_size: u32) -> Vec<MdocCborColumnEval> {
    mdoc_cbor_preprocessed_values(log_size)
        .into_iter()
        .map(|values| column_eval(log_size, values))
        .collect()
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(m31(value))
}

fn boolean_constraint<E: EvalAtRow>(eval: &mut E, gate: E::F, value: E::F) {
    eval.add_constraint(gate * value.clone() * (value - m31_const::<E>(1)));
}

fn eq_bit<E: EvalAtRow>(bit: E::F, expected: bool) -> E::F {
    if expected {
        bit
    } else {
        m31_const::<E>(1) - bit
    }
}

#[derive(Clone)]
struct MdocCborStreamEval {
    log_size: u32,
    mode: MdocCborInputMode,
    stream_id: u32,
    input_field_id: u32,
    input_relation: FieldBytesRelation,
    raw_input: Option<(u32, FieldBytesRelation)>,
    max_message_len: Option<u32>,
    parsed_relation: Option<ParsedCborByteRelation>,
    claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for MdocCborStreamEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // The extended additional-info equality is factored through four
        // committed bit-prefix columns per flag.  All resulting constraints
        // have degree at most five, so the fixed two-bit PCS blowup suffices.
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let row_index = eval.get_preprocessed_column(preprocessed_id(self.log_size, "row_index"));
        let first = eval.get_preprocessed_column(preprocessed_id(self.log_size, "first"));
        let last = eval.get_preprocessed_column(preprocessed_id(self.log_size, "last"));
        let one = m31_const::<E>(1);
        let zero = m31_const::<E>(0);

        let active = eval.next_trace_mask();
        let byte_mask = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1, 2, 3, 4, 5, 6, 7, 8]);
        let byte = byte_mask[0].clone();
        let byte_bits: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());

        let [cbor, cbor_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [marker, marker_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let [zero_pad, zero_pad_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let length_phases: [[E::F; 2]; 8] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));

        let header = eval.next_trace_mask();
        let root_end = eval.next_trace_mask();
        let major = eval.next_trace_mask();
        let major_flags: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());
        let argument: [E::F; 4] = std::array::from_fn(|_| eval.next_trace_mask());
        let content_len = eval.next_trace_mask();
        let depth = eval.next_trace_mask();
        let parent_header_index = eval.next_trace_mask();
        let child_ordinal = eval.next_trace_mask();
        let map_key = eval.next_trace_mask();
        let map_value = eval.next_trace_mask();
        let [remaining, remaining_next] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let remaining_inv = eval.next_trace_mask();
        let span_after_header = eval.next_trace_mask();
        let child_count = eval.next_trace_mask();
        let has_children = eval.next_trace_mask();
        let children_inv = eval.next_trace_mask();
        let selected_counter_inv = eval.next_trace_mask();
        let [message_len, message_len_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]);
        let minimal_inv = eval.next_trace_mask();
        let short_slack_bits: [E::F; 8] = std::array::from_fn(|_| eval.next_trace_mask());
        let ext_flags: [E::F; 4] = std::array::from_fn(|_| eval.next_trace_mask());
        let ext_match: [[E::F; 4]; 4] =
            std::array::from_fn(|_| std::array::from_fn(|_| eval.next_trace_mask()));
        let pad_slack_bits: [E::F; 6] = std::array::from_fn(|_| eval.next_trace_mask());
        let counters: [[E::F; 2]; MDOC_CBOR_MAX_DEPTH] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let selected: [E::F; MDOC_CBOR_MAX_DEPTH] = std::array::from_fn(|_| eval.next_trace_mask());
        let map_kinds: [[E::F; 2]; MDOC_CBOR_MAX_DEPTH] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let map_key_states: [[E::F; 2]; MDOC_CBOR_MAX_DEPTH] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let parent_indices: [[E::F; 2]; MDOC_CBOR_MAX_DEPTH] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let child_ordinals: [[E::F; 2]; MDOC_CBOR_MAX_DEPTH] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1]));
        let message_bound_slack: Option<[E::F; MDOC_CBOR_MESSAGE_BOUND_BITS]> = self
            .max_message_len
            .map(|_| std::array::from_fn(|_| eval.next_trace_mask()));

        // Active rows are exactly one phase. The all-zero suffix cannot reactivate.
        boolean_constraint(&mut eval, one.clone(), active.clone());
        boolean_constraint(&mut eval, one.clone(), cbor.clone());
        boolean_constraint(&mut eval, one.clone(), marker.clone());
        boolean_constraint(&mut eval, one.clone(), zero_pad.clone());
        for phase in &length_phases {
            boolean_constraint(&mut eval, one.clone(), phase[0].clone());
        }
        let phase_sum = cbor.clone()
            + marker.clone()
            + zero_pad.clone()
            + length_phases
                .iter()
                .fold(zero.clone(), |sum, phase| sum + phase[0].clone());
        eval.add_constraint(active.clone() - phase_sum);
        eval.add_constraint(first.clone() * (cbor.clone() - one.clone()));
        eval.add_constraint(last.clone() * active.clone());

        boolean_constraint(&mut eval, one.clone(), root_end.clone());
        eval.add_constraint(root_end.clone() * (one.clone() - cbor.clone()));
        let not_last = one.clone() - last;
        match self.mode {
            MdocCborInputMode::ShaPadded => {
                eval.add_constraint(
                    not_last.clone() * (cbor_next.clone() - cbor.clone() + root_end.clone()),
                );
                eval.add_constraint(not_last.clone() * (marker_next.clone() - root_end.clone()));
                eval.add_constraint(
                    not_last.clone()
                        * (marker.clone() + zero_pad.clone()
                            - zero_pad_next.clone()
                            - length_phases[0][1].clone()),
                );
                for index in 0..7 {
                    eval.add_constraint(
                        not_last.clone()
                            * (length_phases[index + 1][1].clone()
                                - length_phases[index][0].clone()),
                    );
                }
            }
            MdocCborInputMode::Raw => {
                eval.add_constraint(
                    not_last.clone() * (cbor_next.clone() - cbor.clone() + root_end.clone()),
                );
                eval.add_constraint(marker.clone());
                eval.add_constraint(zero_pad.clone());
                for phase in &length_phases {
                    eval.add_constraint(phase[0].clone());
                }
            }
        }

        // Every consumed byte is an actual byte.
        for bit in &byte_bits {
            boolean_constraint(&mut eval, active.clone(), bit.clone());
        }
        let recomposed_byte = byte_bits
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (bit, value)| {
                sum + m31_const::<E>(1u32 << bit) * value.clone()
            });
        eval.add_constraint(active.clone() * (byte.clone() - recomposed_byte));

        // SHA padding is exact and minimal.
        eval.add_constraint(marker.clone() * (byte.clone() - m31_const::<E>(0x80)));
        eval.add_constraint(zero_pad.clone() * byte.clone());
        for phase in length_phases.iter().take(5) {
            eval.add_constraint(phase[0].clone() * byte.clone());
        }
        let len0 = length_phases[0][0].clone();
        eval.add_constraint(
            len0.clone()
                * (m31_const::<E>(65536) * byte_mask[5].clone()
                    + m31_const::<E>(256) * byte_mask[6].clone()
                    + byte_mask[7].clone()
                    - m31_const::<E>(8) * message_len.clone()),
        );
        let pad_slack = pad_slack_bits
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (bit, value)| {
                sum + m31_const::<E>(1u32 << bit) * value.clone()
            });
        for bit in &pad_slack_bits {
            boolean_constraint(&mut eval, len0.clone(), bit.clone());
        }
        eval.add_constraint(
            len0.clone() * (row_index.clone() - message_len.clone() - one.clone() - pad_slack),
        );
        eval.add_constraint(
            active.clone()
                * (cbor_next.clone()
                    + marker_next.clone()
                    + zero_pad_next.clone()
                    + length_phases
                        .iter()
                        .fold(zero.clone(), |sum, phase| sum + phase[1].clone()))
                * (message_len_next.clone() - message_len.clone()),
        );
        eval.add_constraint(
            root_end.clone() * (message_len.clone() - row_index.clone() - one.clone()),
        );
        if let (Some(max), Some(slack_bits)) = (self.max_message_len, message_bound_slack) {
            let slack = slack_bits
                .iter()
                .enumerate()
                .fold(zero.clone(), |sum, (bit, value)| {
                    sum + m31_const::<E>(1u32 << bit) * value.clone()
                });
            for bit in slack_bits {
                boolean_constraint(&mut eval, root_end.clone(), bit);
            }
            eval.add_constraint(
                root_end.clone() * (message_len.clone() + slack - m31_const::<E>(max)),
            );
        }

        // This row is a header if and only if the token-byte countdown is zero.
        boolean_constraint(&mut eval, cbor.clone(), header.clone());
        eval.add_constraint(header.clone() * (one.clone() - cbor.clone()));
        eval.add_constraint(cbor.clone() * remaining.clone() * header.clone());
        eval.add_constraint(
            cbor.clone()
                * (remaining.clone() * remaining_inv.clone() - one.clone() + header.clone()),
        );

        // Decode major type and additional-info width from the header byte.
        for (major_value, flag) in major_flags.iter().enumerate() {
            boolean_constraint(&mut eval, cbor.clone(), flag.clone());
            let eq = eq_bit::<E>(byte_bits[5].clone(), major_value & 1 != 0)
                * eq_bit::<E>(byte_bits[6].clone(), major_value & 2 != 0)
                * eq_bit::<E>(byte_bits[7].clone(), major_value & 4 != 0);
            eval.add_constraint(cbor.clone() * (flag.clone() - header.clone() * eq));
        }
        let decoded_major = major_flags
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (value, flag)| {
                sum + m31_const::<E>(value as u32) * flag.clone()
            });
        eval.add_constraint(cbor.clone() * (major.clone() - decoded_major));

        let ai = byte_bits
            .iter()
            .take(5)
            .enumerate()
            .fold(zero.clone(), |sum, (bit, value)| {
                sum + m31_const::<E>(1u32 << bit) * value.clone()
            });
        for (offset, (flag, prefixes)) in ext_flags.iter().zip(ext_match).enumerate() {
            boolean_constraint(&mut eval, cbor.clone(), flag.clone());
            let value = 24 + offset;
            for prefix in &prefixes {
                boolean_constraint(&mut eval, cbor.clone(), prefix.clone());
            }
            eval.add_constraint(
                cbor.clone()
                    * (prefixes[0].clone() - eq_bit::<E>(byte_bits[0].clone(), value & 1 != 0)),
            );
            for bit in 1..4 {
                eval.add_constraint(
                    cbor.clone()
                        * (prefixes[bit].clone()
                            - prefixes[bit - 1].clone()
                                * eq_bit::<E>(byte_bits[bit].clone(), value & (1 << bit) != 0)),
                );
            }
            eval.add_constraint(
                cbor.clone()
                    * (flag.clone()
                        - header.clone()
                            * prefixes[3].clone()
                            * eq_bit::<E>(byte_bits[4].clone(), value & (1 << 4) != 0)),
            );
        }
        let ext_sum = ext_flags
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, flag| sum + flag);
        let inline = header.clone() - ext_sum.clone();
        eval.add_constraint(
            header.clone() * byte_bits[4].clone() * byte_bits[3].clone() * byte_bits[2].clone(),
        );

        let b = &byte_mask;
        let arg_expected = [
            inline.clone() * ai.clone()
                + ext_flags[0].clone() * b[1].clone()
                + ext_flags[1].clone() * (m31_const::<E>(256) * b[1].clone() + b[2].clone())
                + ext_flags[2].clone() * (m31_const::<E>(256) * b[3].clone() + b[4].clone())
                + ext_flags[3].clone() * (m31_const::<E>(256) * b[7].clone() + b[8].clone()),
            ext_flags[2].clone() * (m31_const::<E>(256) * b[1].clone() + b[2].clone())
                + ext_flags[3].clone() * (m31_const::<E>(256) * b[5].clone() + b[6].clone()),
            ext_flags[3].clone() * (m31_const::<E>(256) * b[3].clone() + b[4].clone()),
            ext_flags[3].clone() * (m31_const::<E>(256) * b[1].clone() + b[2].clone()),
        ];
        for (actual, expected) in argument.iter().zip(arg_expected) {
            eval.add_constraint(cbor.clone() * (actual.clone() - expected));
        }

        // ai=24 must encode >=24. Wider encodings must have a nonzero high
        // byte region, which is equivalent to their canonical lower bound.
        let short_slack = short_slack_bits
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (bit, value)| {
                sum + m31_const::<E>(1u32 << bit) * value.clone()
            });
        for bit in &short_slack_bits {
            boolean_constraint(&mut eval, cbor.clone() * ext_flags[0].clone(), bit.clone());
        }
        eval.add_constraint(
            cbor.clone()
                * ext_flags[0].clone()
                * (argument[0].clone() - m31_const::<E>(24) - short_slack),
        );
        let wide = ext_flags[1].clone() + ext_flags[2].clone() + ext_flags[3].clone();
        let high_sum = ext_flags[1].clone() * b[1].clone()
            + ext_flags[2].clone() * (b[1].clone() + b[2].clone())
            + ext_flags[3].clone() * (b[1].clone() + b[2].clone() + b[3].clone() + b[4].clone());
        eval.add_constraint(cbor.clone() * (high_sum * minimal_inv - wide));

        let string = major_flags[2].clone() + major_flags[3].clone();
        let array = major_flags[4].clone();
        let map = major_flags[5].clone();
        let tag = major_flags[6].clone();
        let simple = major_flags[7].clone();
        eval.add_constraint(
            cbor.clone()
                * (string.clone() + array.clone() + map.clone())
                * (ext_flags[2].clone() + ext_flags[3].clone()),
        );
        eval.add_constraint(cbor.clone() * simple.clone() * (byte_bits[4].clone() - one.clone()));
        eval.add_constraint(cbor.clone() * simple.clone() * byte_bits[3].clone());
        eval.add_constraint(cbor.clone() * simple.clone() * (byte_bits[2].clone() - one.clone()));

        eval.add_constraint(
            cbor.clone() * (content_len.clone() - string.clone() * argument[0].clone()),
        );
        let argument_width = ext_flags[0].clone()
            + m31_const::<E>(2) * ext_flags[1].clone()
            + m31_const::<E>(4) * ext_flags[2].clone()
            + m31_const::<E>(8) * ext_flags[3].clone();
        eval.add_constraint(
            cbor.clone() * (span_after_header.clone() - argument_width - content_len.clone()),
        );
        eval.add_constraint(
            cbor.clone()
                * (child_count.clone()
                    - array.clone() * argument[0].clone()
                    - m31_const::<E>(2) * map.clone() * argument[0].clone()
                    - tag),
        );
        boolean_constraint(&mut eval, cbor.clone(), has_children.clone());
        eval.add_constraint(
            cbor.clone() * (child_count.clone() * children_inv.clone() - has_children.clone()),
        );
        eval.add_constraint(
            cbor.clone() * child_count.clone() * (one.clone() - has_children.clone()),
        );

        let expected_remaining_next = header.clone() * span_after_header.clone()
            + (cbor.clone() - header.clone()) * (remaining.clone() - one.clone());
        let continue_cbor = cbor.clone() * cbor_next.clone();
        eval.add_constraint(
            continue_cbor.clone() * (remaining_next.clone() - expected_remaining_next.clone()),
        );
        eval.add_constraint(root_end.clone() * expected_remaining_next);
        eval.add_constraint(active.clone() * (one.clone() - cbor.clone()) * remaining.clone());

        // Bounded stack selection and exact count transitions.
        let selected_sum = selected
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, value| sum + value);
        eval.add_constraint(cbor.clone() * (selected_sum.clone() - header.clone()));
        let mut selected_counter = zero.clone();
        for level in 0..MDOC_CBOR_MAX_DEPTH {
            boolean_constraint(&mut eval, cbor.clone(), selected[level].clone());
            selected_counter += selected[level].clone() * counters[level][0].clone();
            for higher in level + 1..MDOC_CBOR_MAX_DEPTH {
                eval.add_constraint(
                    cbor.clone() * selected[level].clone() * counters[higher][0].clone(),
                );
            }
        }
        eval.add_constraint(
            cbor.clone() * (selected_counter * selected_counter_inv - header.clone()),
        );
        eval.add_constraint(first.clone() * (remaining.clone()));
        eval.add_constraint(first.clone() * (counters[0][0].clone() - one.clone()));
        for level in 1..MDOC_CBOR_MAX_DEPTH {
            eval.add_constraint(first.clone() * counters[level][0].clone());
        }
        for level in 0..MDOC_CBOR_MAX_DEPTH {
            eval.add_constraint(first.clone() * map_kinds[level][0].clone());
            eval.add_constraint(first.clone() * map_key_states[level][0].clone());
            eval.add_constraint(first.clone() * parent_indices[level][0].clone());
            eval.add_constraint(first.clone() * child_ordinals[level][0].clone());
        }
        eval.add_constraint(first.clone() * depth.clone());
        eval.add_constraint(first.clone() * parent_header_index.clone());
        eval.add_constraint(first.clone() * child_ordinal.clone());
        eval.add_constraint(first.clone() * map_key.clone());
        eval.add_constraint(first.clone() * map_value.clone());

        let push: [E::F; MDOC_CBOR_MAX_DEPTH] = std::array::from_fn(|level| {
            if level == 0 {
                zero.clone()
            } else {
                selected[level - 1].clone() * has_children.clone()
            }
        });
        eval.add_constraint(
            cbor.clone() * selected[MDOC_CBOR_MAX_DEPTH - 1].clone() * has_children.clone(),
        );
        for level in 0..MDOC_CBOR_MAX_DEPTH {
            let decrement = selected[level].clone();
            let pushed_count = if level == 0 {
                zero.clone()
            } else {
                selected[level - 1].clone() * child_count.clone()
            };
            let expected_counter_next = counters[level][0].clone() - decrement + pushed_count;
            eval.add_constraint(
                continue_cbor.clone()
                    * (counters[level][1].clone() - expected_counter_next.clone()),
            );
            eval.add_constraint(root_end.clone() * expected_counter_next);

            boolean_constraint(&mut eval, cbor.clone(), map_kinds[level][0].clone());
            boolean_constraint(&mut eval, cbor.clone(), map_key_states[level][0].clone());
            let pushed_map = push[level].clone() * map.clone();
            eval.add_constraint(
                continue_cbor.clone()
                    * (map_kinds[level][1].clone()
                        - map_kinds[level][0].clone()
                        - push[level].clone() * (map.clone() - map_kinds[level][0].clone())),
            );
            eval.add_constraint(
                continue_cbor.clone()
                    * (map_key_states[level][1].clone()
                        - map_key_states[level][0].clone()
                        - selected[level].clone()
                            * map_kinds[level][0].clone()
                            * (one.clone() - m31_const::<E>(2) * map_key_states[level][0].clone())
                        - push[level].clone() * (map.clone() - map_key_states[level][0].clone())),
            );
            let _ = pushed_map;
            eval.add_constraint(
                continue_cbor.clone()
                    * (parent_indices[level][1].clone()
                        - parent_indices[level][0].clone()
                        - push[level].clone()
                            * (row_index.clone() - parent_indices[level][0].clone())),
            );
            eval.add_constraint(
                continue_cbor.clone()
                    * (child_ordinals[level][1].clone()
                        - child_ordinals[level][0].clone()
                        - selected[level].clone()
                        + push[level].clone() * child_ordinals[level][0].clone()),
            );
        }

        let expected_depth = selected
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (level, value)| {
                sum + m31_const::<E>(level as u32) * value.clone()
            });
        let expected_parent = selected
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (level, value)| {
                sum + value.clone() * parent_indices[level][0].clone()
            });
        let expected_ordinal = selected
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (level, value)| {
                sum + value.clone() * child_ordinals[level][0].clone()
            });
        let expected_map_key =
            selected
                .iter()
                .enumerate()
                .fold(zero.clone(), |sum, (level, value)| {
                    sum + value.clone()
                        * map_kinds[level][0].clone()
                        * map_key_states[level][0].clone()
                });
        let expected_map_value =
            selected
                .iter()
                .enumerate()
                .fold(zero.clone(), |sum, (level, value)| {
                    sum + value.clone()
                        * map_kinds[level][0].clone()
                        * (one.clone() - map_key_states[level][0].clone())
                });
        eval.add_constraint(cbor.clone() * (depth.clone() - expected_depth));
        eval.add_constraint(cbor.clone() * (parent_header_index.clone() - expected_parent));
        eval.add_constraint(cbor.clone() * (child_ordinal.clone() - expected_ordinal));
        eval.add_constraint(cbor.clone() * (map_key.clone() - expected_map_key));
        eval.add_constraint(cbor.clone() * (map_value.clone() - expected_map_value));
        boolean_constraint(&mut eval, cbor.clone(), map_key.clone());
        boolean_constraint(&mut eval, cbor.clone(), map_value.clone());

        for level in 0..MDOC_CBOR_MAX_DEPTH {
            eval.add_constraint(
                active.clone() * (one.clone() - cbor.clone()) * counters[level][0].clone(),
            );
        }

        // Consume every input byte. The row-index key plus the active-prefix
        // constraints make omissions, duplicates and reorderings impossible.
        eval.add_to_relation(RelationEntry::new(
            &self.input_relation,
            E::EF::from(active.clone()),
            &[
                m31_const::<E>(self.input_field_id),
                row_index.clone(),
                byte.clone(),
            ],
        ));

        if let Some((field_id, relation)) = &self.raw_input {
            eval.add_to_relation(RelationEntry::new(
                relation,
                E::EF::from(cbor.clone()),
                &[m31_const::<E>(*field_id), row_index.clone(), byte.clone()],
            ));
        }

        if let Some(relation) = &self.parsed_relation {
            let tuple = [
                m31_const::<E>(self.stream_id),
                row_index,
                byte,
                header,
                major,
                argument[0].clone(),
                argument[1].clone(),
                argument[2].clone(),
                argument[3].clone(),
                content_len,
                depth,
                parent_header_index,
                child_ordinal,
                map_key,
                map_value,
            ];
            eval.add_to_relation(RelationEntry::new(relation, -E::EF::from(cbor), &tuple));
        }
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

mod trace_col {
    pub(super) const ACTIVE: usize = 0;
    pub(super) const BYTE: usize = 1;
    pub(super) const CBOR: usize = 10;
    pub(super) const HEADER: usize = 21;
    pub(super) const MAJOR: usize = 23;
    pub(super) const ARGUMENT: usize = 32;
    pub(super) const CONTENT_LEN: usize = 36;
    pub(super) const DEPTH: usize = 37;
    pub(super) const PARENT: usize = 38;
    pub(super) const ORDINAL: usize = 39;
    pub(super) const MAP_KEY: usize = 40;
    pub(super) const MAP_VALUE: usize = 41;
    #[cfg(test)]
    pub(super) const SHORT_SLACK: usize = 51;
    #[cfg(test)]
    pub(super) const EXT_MATCH: usize = 63;
    #[cfg(test)]
    pub(super) const PAD_SLACK: usize = 79;
    #[cfg(test)]
    pub(super) const COUNTERS: usize = 85;
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocCborStreamInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

pub(crate) struct MdocCborStream {
    mode: MdocCborInputMode,
    stream_id: u32,
    input_field_id: u32,
    log_size: u32,
    witness: Option<MdocCborWitness>,
    prover_bytes: Option<Vec<u8>>,
    input_handle: SharedFieldRelation,
    raw_input: Option<(u32, SharedFieldRelation)>,
    max_message_len: Option<u32>,
    parsed_handle: Option<SharedParsedCborByteRelation>,
    claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocCborStreamInteractionClaim>,
    component: Option<MdocCborComponent>,
}

impl MdocCborStream {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_with_log_size(
        bytes: Vec<u8>,
        mode: MdocCborInputMode,
        stream_id: u32,
        input_field_id: u32,
        input: SharedFieldRelation,
        parsed: Option<SharedParsedCborByteRelation>,
        log_size: u32,
        max_message_len: Option<u32>,
    ) -> Result<Self, MdocCborStreamError> {
        Self::new_shaped(
            bytes,
            mode,
            stream_id,
            input_field_id,
            input,
            None,
            parsed,
            Some(log_size),
            max_message_len,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_exact_sha(
        bytes: Vec<u8>,
        stream_id: u32,
        sha_field_id: u32,
        sha_input: SharedFieldRelation,
        raw_field_id: u32,
        raw_input: SharedFieldRelation,
        parsed: Option<SharedParsedCborByteRelation>,
        log_size: u32,
        max_message_len: u32,
    ) -> Result<Self, MdocCborStreamError> {
        Self::new_shaped(
            bytes,
            MdocCborInputMode::ShaPadded,
            stream_id,
            sha_field_id,
            sha_input,
            Some((raw_field_id, raw_input)),
            parsed,
            Some(log_size),
            Some(max_message_len),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_shaped(
        bytes: Vec<u8>,
        mode: MdocCborInputMode,
        stream_id: u32,
        input_field_id: u32,
        input: SharedFieldRelation,
        raw_input: Option<(u32, SharedFieldRelation)>,
        parsed: Option<SharedParsedCborByteRelation>,
        fixed_log_size: Option<u32>,
        max_message_len: Option<u32>,
    ) -> Result<Self, MdocCborStreamError> {
        if max_message_len.is_some_and(|max| max > 1 << MDOC_CBOR_MESSAGE_BOUND_BITS) {
            return Err(MdocCborStreamError::TraceTooLarge {
                bytes: usize::try_from(max_message_len.unwrap()).unwrap_or(usize::MAX),
            });
        }
        let witness = MdocCborWitness::with_shape(&bytes, mode, fixed_log_size, max_message_len)?;
        Ok(Self {
            mode,
            stream_id,
            input_field_id,
            log_size: witness.log_size,
            witness: Some(witness),
            prover_bytes: Some(bytes),
            input_handle: input,
            raw_input,
            max_message_len,
            parsed_handle: parsed,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verifier(
        mode: MdocCborInputMode,
        stream_id: u32,
        input_field_id: u32,
        log_size: u32,
        input: SharedFieldRelation,
        parsed: Option<SharedParsedCborByteRelation>,
        max_message_len: Option<u32>,
        interaction_claim: MdocCborStreamInteractionClaim,
    ) -> Result<Self, MdocCborStreamError> {
        if !(MDOC_CBOR_MIN_LOG_SIZE..=MDOC_CBOR_MAX_LOG_SIZE).contains(&log_size)
            || max_message_len.is_some_and(|max| max > 1 << MDOC_CBOR_MESSAGE_BOUND_BITS)
        {
            return Err(MdocCborStreamError::TraceTooLarge {
                bytes: 1usize << log_size.min(usize::BITS - 1),
            });
        }
        Ok(Self {
            mode,
            stream_id,
            input_field_id,
            log_size,
            witness: None,
            prover_bytes: None,
            input_handle: input,
            raw_input: None,
            max_message_len,
            parsed_handle: parsed,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verifier_exact_sha(
        stream_id: u32,
        sha_field_id: u32,
        sha_input: SharedFieldRelation,
        raw_field_id: u32,
        raw_input: SharedFieldRelation,
        parsed: Option<SharedParsedCborByteRelation>,
        log_size: u32,
        max_message_len: u32,
        interaction_claim: MdocCborStreamInteractionClaim,
    ) -> Result<Self, MdocCborStreamError> {
        if !(MDOC_CBOR_MIN_LOG_SIZE..=MDOC_CBOR_MAX_LOG_SIZE).contains(&log_size)
            || max_message_len > 1 << MDOC_CBOR_MESSAGE_BOUND_BITS
        {
            return Err(MdocCborStreamError::TraceTooLarge {
                bytes: 1usize << log_size.min(usize::BITS - 1),
            });
        }
        Ok(Self {
            mode: MdocCborInputMode::ShaPadded,
            stream_id,
            input_field_id: sha_field_id,
            log_size,
            witness: None,
            prover_bytes: None,
            input_handle: sha_input,
            raw_input: Some((raw_field_id, raw_input)),
            max_message_len: Some(max_message_len),
            parsed_handle: parsed,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
        })
    }

    pub(crate) fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![self.log_size]
    }

    pub(crate) fn with_claim_mask(
        mut self,
        trace: ClaimMaskTrace,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        assert_eq!(
            trace.log_size(),
            self.log_size,
            "mdoc CBOR claim-mask log size mismatch"
        );
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
            .map(|shared| shared.require().expect("claim-mask anchor drawn first"))
    }

    pub(crate) fn log_size(&self) -> u32 {
        self.log_size
    }

    pub(crate) fn interaction_claim(&self) -> &MdocCborStreamInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc CBOR stream interaction claim is set")
    }

    fn input_relation(&self) -> FieldBytesRelation {
        self.input_handle.get()
    }

    fn raw_input_relation(&self) -> Option<(u32, FieldBytesRelation)> {
        self.raw_input
            .as_ref()
            .map(|(field_id, handle)| (*field_id, handle.get()))
    }

    fn parsed_relation(&self) -> Option<ParsedCborByteRelation> {
        self.parsed_handle.as_ref().map(SharedRelation::get)
    }

    fn n_main_lookups(&self) -> usize {
        // Full input consume, optional parsed-byte yield, optional private
        // claimed-sum mask.
        1 + usize::from(self.raw_input.is_some())
            + usize::from(self.parsed_handle.is_some())
            + usize::from(self.claim_mask_challenge.is_some())
    }
}

fn mdoc_cbor_interaction_trace_with_raw(
    witness: &MdocCborWitness,
    stream_id: u32,
    input_field_id: u32,
    input_relation: &FieldBytesRelation,
    raw_input: Option<&(u32, FieldBytesRelation)>,
    parsed_relation: Option<&ParsedCborByteRelation>,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<MdocCborColumnEval>, QM31) {
    let base = mdoc_cbor_base_trace_with_bound(witness, None);
    let preprocessed = mdoc_cbor_preprocessed_columns(witness.log_size);
    let n_vec_rows = 1usize << (witness.log_size - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(2 + usize::from(parsed_relation.is_some()));

    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let numerator = PackedQM31::from(base[trace_col::ACTIVE].data[vec_row]);
                let denominator = input_relation.combine(&[
                    PackedM31::broadcast(m31(input_field_id)),
                    preprocessed[0].data[vec_row],
                    base[trace_col::BYTE].data[vec_row],
                ]);
                (numerator, denominator)
            })
            .collect(),
    );

    if let Some((field_id, relation)) = raw_input {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(base[trace_col::CBOR].data[vec_row]);
                    let denominator = relation.combine(&[
                        PackedM31::broadcast(m31(*field_id)),
                        preprocessed[0].data[vec_row],
                        base[trace_col::BYTE].data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    if let Some(relation) = parsed_relation {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = -PackedQM31::from(base[trace_col::CBOR].data[vec_row]);
                    let denominator = relation.combine(&[
                        PackedM31::broadcast(m31(stream_id)),
                        preprocessed[0].data[vec_row],
                        base[trace_col::BYTE].data[vec_row],
                        base[trace_col::HEADER].data[vec_row],
                        base[trace_col::MAJOR].data[vec_row],
                        base[trace_col::ARGUMENT].data[vec_row],
                        base[trace_col::ARGUMENT + 1].data[vec_row],
                        base[trace_col::ARGUMENT + 2].data[vec_row],
                        base[trace_col::ARGUMENT + 3].data[vec_row],
                        base[trace_col::CONTENT_LEN].data[vec_row],
                        base[trace_col::DEPTH].data[vec_row],
                        base[trace_col::PARENT].data[vec_row],
                        base[trace_col::ORDINAL].data[vec_row],
                        base[trace_col::MAP_KEY].data[vec_row],
                        base[trace_col::MAP_VALUE].data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    if let Some((mask, beta)) = claim_mask {
        assert_eq!(mask.packed_rows(), n_vec_rows);
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| mask.packed_fraction_at(vec_row, beta))
                .collect(),
        );
    }

    let mut logup = LogupTraceGenerator::new(witness.log_size);
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

#[cfg(test)]
fn mdoc_cbor_interaction_trace(
    witness: &MdocCborWitness,
    stream_id: u32,
    input_relation: &FieldBytesRelation,
    parsed_relation: Option<&ParsedCborByteRelation>,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<MdocCborColumnEval>, QM31) {
    mdoc_cbor_interaction_trace_with_raw(
        witness,
        stream_id,
        stream_id,
        input_relation,
        None,
        parsed_relation,
        claim_mask,
    )
}

impl Air for MdocCborStream {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x4d44_4f43_4342_4f52);
        channel.mix_u64(self.mode.transcript_tag());
        channel.mix_u64(u64::from(self.stream_id));
        channel.mix_u64(u64::from(self.input_field_id));
        channel.mix_u64(u64::from(self.log_size));
        channel.mix_u64(
            self.raw_input
                .as_ref()
                .map_or(u64::MAX, |(field_id, _)| u64::from(*field_id)),
        );
        channel.mix_u64(self.max_message_len.map_or(u64::MAX, u64::from));
        channel.mix_u64(u64::from(self.parsed_handle.is_some()));
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        if let Some(handle) = &self.parsed_handle {
            assert!(
                !handle.is_set(),
                "each mdoc CBOR parser instance needs a distinct parsed relation handle"
            );
            handle.set(ParsedCborByteRelation::draw(channel));
        }
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.log_size; MDOC_CBOR_PREPROCESSED_COLS],
            trace: vec![
                self.log_size;
                MDOC_CBOR_TRACE_COLS
                    + usize::from(self.max_message_len.is_some())
                        * MDOC_CBOR_MESSAGE_BOUND_BITS
                    + usize::from(self.claim_mask_challenge.is_some())
                        * CLAIM_MASK_TRACE_COLUMNS
            ],
            interaction: vec![
                self.log_size;
                self.n_main_lookups().div_ceil(2) * SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_ids(self.log_size)
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(mdoc_cbor_preprocessed_columns(self.log_size))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.component = Some(MdocCborComponent::new(
            allocator,
            MdocCborStreamEval {
                log_size: self.log_size,
                mode: self.mode,
                stream_id: self.stream_id,
                input_field_id: self.input_field_id,
                input_relation: self.input_relation(),
                raw_input: self.raw_input_relation(),
                max_message_len: self.max_message_len,
                parsed_relation: self.parsed_relation(),
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc CBOR component is built")]
    }
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

impl AirProver for MdocCborStream {
    fn max_log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 3
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &preprocessed_ids(self.log_size));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_cbor_stream::MdocCborStream",
            &preprocessed_ids(self.log_size),
            &mdoc_cbor_preprocessed_columns(self.log_size),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = preprocessed_ids(self.log_size);
        let all_columns = mdoc_cbor_preprocessed_columns(self.log_size);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected mdoc CBOR preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let witness = self.witness.take().expect("mdoc CBOR prover has a witness");
        tb.extend_evals(mdoc_cbor_base_trace_with_bound(
            &witness,
            self.max_message_len,
        ));
        if let Some(mask) = &self.claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let witness = MdocCborWitness::with_shape(
            self.prover_bytes
                .as_deref()
                .expect("mdoc CBOR prover retains its source bytes"),
            self.mode,
            Some(self.log_size),
            self.max_message_len,
        )
        .expect("mdoc CBOR witness rebuild succeeds");
        let claim_mask = self.claim_mask_trace.as_ref().zip(self.claim_mask_beta());
        let raw_input = self.raw_input_relation();
        let (trace, claimed_sum) = mdoc_cbor_interaction_trace_with_raw(
            &witness,
            self.stream_id,
            self.input_field_id,
            &self.input_relation(),
            raw_input.as_ref(),
            self.parsed_relation().as_ref(),
            claim_mask,
        );
        tb.extend_evals(trace);
        self.interaction_claim = Some(MdocCborStreamInteractionClaim { claimed_sum });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc CBOR component is built")]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use air_core::claim_mask::ClaimMaskRing;
    use stwo::core::fields::qm31::SECURE_EXTENSION_DEGREE;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{assert_constraints_on_trace, Multiplicity};

    const TEST_STREAM_ID: u32 = 77;

    fn sha_pad(message: &[u8]) -> Vec<u8> {
        let mut padded = message.to_vec();
        padded.push(0x80);
        while (padded.len() + SHA_LENGTH_BYTES) % SHA_BLOCK_BYTES != 0 {
            padded.push(0);
        }
        padded.extend_from_slice(&((message.len() as u64) * 8).to_be_bytes());
        padded
    }

    struct RecordingEval<'a> {
        preprocessed: &'a [Vec<M31>],
        base: &'a [Vec<M31>],
        preprocessed_column: usize,
        base_column: usize,
        row: usize,
        constraints: Vec<QM31>,
        fractions: Vec<(QM31, QM31)>,
    }

    impl EvalAtRow for RecordingEval<'_> {
        type F = M31;
        type EF = QM31;

        fn get_preprocessed_column(&mut self, _column: PreProcessedColumnId) -> Self::F {
            let value = self.preprocessed[self.preprocessed_column][self.row];
            self.preprocessed_column += 1;
            value
        }

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            offsets: [isize; N],
        ) -> [Self::F; N] {
            assert_eq!(interaction, ORIGINAL_TRACE_IDX);
            let column = self.base_column;
            self.base_column += 1;
            let n_rows = self.base[column].len() as isize;
            offsets.map(|offset| {
                let row = (self.row as isize + offset).rem_euclid(n_rows) as usize;
                self.base[column][row]
            })
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.constraints.push(Self::EF::from(constraint));
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            Self::EF::from_m31_array(values)
        }

        fn write_logup_frac_typed(
            &mut self,
            numerator: Multiplicity<Self::F, Self::EF>,
            denominator: Self::EF,
        ) {
            self.fractions.push((numerator.to_ef(), denominator));
        }

        fn finalize_logup_in_pairs(&mut self) {}
    }

    fn evaluate_columns<'a>(
        witness: &MdocCborWitness,
        base: &'a [Vec<M31>],
    ) -> Vec<RecordingEval<'a>> {
        evaluate_columns_with_bound(witness, base, None)
    }

    fn evaluate_columns_with_bound<'a>(
        witness: &MdocCborWitness,
        base: &'a [Vec<M31>],
        max_message_len: Option<u32>,
    ) -> Vec<RecordingEval<'a>> {
        let preprocessed = Box::leak(Box::new(mdoc_cbor_preprocessed_values(witness.log_size)));
        let eval = MdocCborStreamEval {
            log_size: witness.log_size,
            mode: witness.mode,
            stream_id: TEST_STREAM_ID,
            input_field_id: TEST_STREAM_ID,
            input_relation: FieldBytesRelation::dummy(),
            raw_input: max_message_len.map(|_| (TEST_STREAM_ID + 1, FieldBytesRelation::dummy())),
            max_message_len,
            parsed_relation: Some(ParsedCborByteRelation::dummy()),
            claim_mask_beta: None,
        };
        (0..1usize << witness.log_size)
            .map(|row| {
                let recorder = RecordingEval {
                    preprocessed,
                    base,
                    preprocessed_column: 0,
                    base_column: 0,
                    row,
                    constraints: Vec::new(),
                    fractions: Vec::new(),
                };
                let recorder = eval.evaluate(recorder);
                assert_eq!(
                    recorder.preprocessed_column, MDOC_CBOR_PREPROCESSED_COLS,
                    "all preprocessed columns must be read"
                );
                assert_eq!(
                    recorder.base_column,
                    MDOC_CBOR_TRACE_COLS
                        + usize::from(max_message_len.is_some()) * MDOC_CBOR_MESSAGE_BOUND_BITS,
                    "all base columns must be read"
                );
                recorder
            })
            .collect()
    }

    fn constraints_hold(witness: &MdocCborWitness, base: &[Vec<M31>]) -> bool {
        constraints_hold_with_bound(witness, base, None)
    }

    fn constraints_hold_with_bound(
        witness: &MdocCborWitness,
        base: &[Vec<M31>],
        max_message_len: Option<u32>,
    ) -> bool {
        let zero = QM31::from_u32_unchecked(0, 0, 0, 0);
        for (row_index, row) in evaluate_columns_with_bound(witness, base, max_message_len)
            .iter()
            .enumerate()
        {
            if let Some((constraint_index, value)) = row
                .constraints
                .iter()
                .enumerate()
                .find(|(_, constraint)| **constraint != zero)
            {
                eprintln!(
                    "nonzero mdoc CBOR constraint row={row_index} constraint={constraint_index} value={value:?}"
                );
                return false;
            }
        }
        true
    }

    fn set_byte(base: &mut [Vec<M31>], row: usize, byte: u8) {
        base[trace_col::BYTE][row] = m31(u32::from(byte));
        for bit in 0..8 {
            base[2 + bit][row] = m31(u32::from((byte >> bit) & 1));
        }
        for expected in 24..28 {
            let mut prefix = true;
            for bit in 0..4 {
                prefix &= ((byte >> bit) & 1) == ((expected >> bit) & 1);
                base[trace_col::EXT_MATCH + usize::from(expected - 24) * 4 + bit][row] =
                    m31(u32::from(prefix));
            }
        }
    }

    fn nested_nationality_cbor() -> Vec<u8> {
        let mut bytes = vec![0xa1, 0x6b];
        bytes.extend_from_slice(b"nationality");
        bytes.extend_from_slice(&[0x82, 0x62, b'D', b'E', 0x62, b'F', b'R']);
        bytes
    }

    #[test]
    fn raw_parser_emits_stable_parent_and_child_metadata() {
        let bytes = nested_nationality_cbor();
        let witness = MdocCborWitness::new(&bytes, MdocCborInputMode::Raw).unwrap();
        assert_eq!(witness.message_len, bytes.len());
        assert_eq!(witness.rows[0].depth, 0);
        assert_eq!(witness.rows[0].parent_header_index, 0);
        assert_eq!(witness.rows[0].child_ordinal, 0);

        let key = &witness.rows[1];
        assert!(key.header);
        assert_eq!(key.parent_header_index, 0);
        assert_eq!(key.child_ordinal, 0);
        assert!(key.map_key);
        assert!(!key.map_value);

        let array = &witness.rows[13];
        assert!(array.header);
        assert_eq!(array.major, 4);
        assert_eq!(array.parent_header_index, 0);
        assert_eq!(array.child_ordinal, 1);
        assert!(array.map_value);

        let first_code = &witness.rows[14];
        let second_code = &witness.rows[17];
        assert_eq!(
            (
                first_code.parent_header_index,
                first_code.child_ordinal,
                first_code.depth
            ),
            (13, 0, 2)
        );
        assert_eq!(
            (
                second_code.parent_header_index,
                second_code.child_ordinal,
                second_code.depth
            ),
            (13, 1, 2)
        );
        assert!(witness.rows.last().unwrap().root_end);
    }

    #[test]
    fn supports_minimal_16_bit_byte_string_length() {
        let mut bytes = vec![0x59, 0x01, 0x00];
        bytes.extend((0..256).map(|value| value as u8));
        let witness = MdocCborWitness::new(&bytes, MdocCborInputMode::Raw).unwrap();
        assert_eq!(witness.rows[0].argument, 256);
        assert_eq!(witness.rows[0].content_len, 256);
        assert_eq!(witness.rows[0].argument_limbs(), [256, 0, 0, 0]);
        assert!(witness.rows[258].root_end);
    }

    #[test]
    fn reference_parser_rejects_nonminimal_and_indefinite_tokens() {
        assert!(matches!(
            MdocCborWitness::new(&[0x18, 0x17], MdocCborInputMode::Raw),
            Err(MdocCborStreamError::NonMinimalArgument { .. })
        ));
        assert!(matches!(
            MdocCborWitness::new(&[0x9f, 0xff], MdocCborInputMode::Raw),
            Err(MdocCborStreamError::InvalidAdditionalInfo { .. })
        ));
        assert!(matches!(
            MdocCborWitness::new(&[0x79, 0x00, 0x18], MdocCborInputMode::Raw),
            Err(MdocCborStreamError::NonMinimalArgument { .. })
        ));

        let mut too_deep = vec![0xc0; MDOC_CBOR_MAX_DEPTH];
        too_deep.push(0);
        assert!(matches!(
            MdocCborWitness::new(&too_deep, MdocCborInputMode::Raw),
            Err(MdocCborStreamError::NestingTooDeep { .. })
        ));
    }

    #[test]
    fn sha_reference_rejects_extra_padding_block() {
        let mut padded = sha_pad(&nested_nationality_cbor());
        let length = padded.split_off(padded.len() - SHA_LENGTH_BYTES);
        padded.extend([0; SHA_BLOCK_BYTES]);
        padded.extend(length);
        assert!(matches!(
            MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded),
            Err(MdocCborStreamError::InvalidShaPadding(
                "padding contains an extra or missing block"
            ))
        ));
    }

    #[test]
    fn sha_padded_honest_trace_satisfies_every_polynomial_constraint() {
        let padded = sha_pad(&nested_nationality_cbor());
        let witness = MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded).unwrap();
        let base = mdoc_cbor_base_columns(&witness);
        assert!(constraints_hold(&witness, &base));
    }

    #[test]
    fn exact_sha_private_lengths_share_one_fixed_shape() {
        const FIXED_LOG_SIZE: u32 = MDOC_CBOR_MIN_LOG_SIZE;
        const MAX_MESSAGE_LEN: u32 = 64;
        let short = MdocCborWitness::with_shape(
            &sha_pad(&[0]),
            MdocCborInputMode::ShaPadded,
            Some(FIXED_LOG_SIZE),
            Some(MAX_MESSAGE_LEN),
        )
        .unwrap();
        let long = MdocCborWitness::with_shape(
            &sha_pad(&nested_nationality_cbor()),
            MdocCborInputMode::ShaPadded,
            Some(FIXED_LOG_SIZE),
            Some(MAX_MESSAGE_LEN),
        )
        .unwrap();

        assert_ne!(short.message_len, long.message_len);
        assert_eq!(short.log_size, long.log_size);
        assert_eq!(
            mdoc_cbor_base_columns_with_bound(&short, Some(MAX_MESSAGE_LEN)).len(),
            mdoc_cbor_base_columns_with_bound(&long, Some(MAX_MESSAGE_LEN)).len(),
        );
    }

    #[test]
    fn exact_sha_private_length_bound_is_constrained() {
        const MAX_MESSAGE_LEN: u32 = 64;
        let padded = sha_pad(&nested_nationality_cbor());
        let witness = MdocCborWitness::with_shape(
            &padded,
            MdocCborInputMode::ShaPadded,
            Some(MDOC_CBOR_MIN_LOG_SIZE),
            Some(MAX_MESSAGE_LEN),
        )
        .unwrap();
        let mut base = mdoc_cbor_base_columns_with_bound(&witness, Some(MAX_MESSAGE_LEN));
        assert!(constraints_hold_with_bound(
            &witness,
            &base,
            Some(MAX_MESSAGE_LEN)
        ));

        let root_end = witness.message_len - 1;
        base[MDOC_CBOR_TRACE_COLS][root_end] += m31(1);
        assert!(
            !constraints_hold_with_bound(&witness, &base, Some(MAX_MESSAGE_LEN)),
            "a changed private bound-slack bit must violate the root-end equality"
        );
    }

    #[test]
    fn exact_sha_rejects_message_past_private_bound() {
        let padded = sha_pad(&[0x43, 1, 2, 3]);
        assert!(matches!(
            MdocCborWitness::with_shape(
                &padded,
                MdocCborInputMode::ShaPadded,
                Some(MDOC_CBOR_MIN_LOG_SIZE),
                Some(3),
            ),
            Err(MdocCborStreamError::MessageTooLong { bytes: 4, max: 3 })
        ));
    }

    #[test]
    fn proof_side_sha_bounds_reject_exact_boundary_plus_one() {
        fn canonical_byte_string(total_len: usize) -> Vec<u8> {
            let payload_len = total_len - 3;
            let mut bytes = vec![0x59, (payload_len >> 8) as u8, payload_len as u8];
            bytes.resize(total_len, 0);
            bytes
        }

        for limit in [1_024usize, 6_144, 6_164] {
            let accepted = stwo_sha256::native::pad_message(&canonical_byte_string(limit));
            let witness = MdocCborWitness::with_shape(
                &accepted,
                MdocCborInputMode::ShaPadded,
                None,
                Some(u32::try_from(limit).unwrap()),
            )
            .unwrap();
            assert_eq!(witness.message_len, limit);

            let rejected = stwo_sha256::native::pad_message(&canonical_byte_string(limit + 1));
            assert!(matches!(
                MdocCborWitness::with_shape(
                    &rejected,
                    MdocCborInputMode::ShaPadded,
                    None,
                    Some(u32::try_from(limit).unwrap()),
                ),
                Err(MdocCborStreamError::MessageTooLong { bytes, max })
                    if bytes == limit + 1 && max == limit
            ));
        }
    }

    #[test]
    fn sha_padded_circle_trace_and_logup_satisfy_component() {
        let padded = sha_pad(&nested_nationality_cbor());
        let witness = MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded).unwrap();
        let input = FieldBytesRelation::dummy();
        let parsed = ParsedCborByteRelation::dummy();
        let (interaction, claimed_sum) =
            mdoc_cbor_interaction_trace(&witness, TEST_STREAM_ID, &input, Some(&parsed), None);
        let trees = TreeVec::new(vec![
            mdoc_cbor_preprocessed_columns(witness.log_size)
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
            mdoc_cbor_base_trace(&witness)
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
            interaction
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
        ]);
        let trace = trees.as_cols_ref();
        let component = MdocCborStreamEval {
            log_size: witness.log_size,
            mode: witness.mode,
            stream_id: TEST_STREAM_ID,
            input_field_id: TEST_STREAM_ID,
            input_relation: input,
            raw_input: None,
            max_message_len: None,
            parsed_relation: Some(parsed),
            claim_mask_beta: None,
        };
        assert_constraints_on_trace(
            &trace,
            witness.log_size,
            |eval| {
                let _ = component.evaluate(eval);
            },
            claimed_sum,
        );
    }

    #[test]
    fn claim_mask_changes_cbor_claim_by_beta_times_target_sum() {
        let witness =
            MdocCborWitness::new(&nested_nationality_cbor(), MdocCborInputMode::Raw).unwrap();
        let input = FieldBytesRelation::dummy();
        let parsed = ParsedCborByteRelation::dummy();
        let (_, unmasked_claim) =
            mdoc_cbor_interaction_trace(&witness, TEST_STREAM_ID, &input, Some(&parsed), None);

        let mut ring = ClaimMaskRing::new(&[witness.log_size, witness.log_size]).unwrap();
        let mask = ring.take(witness.log_size).unwrap();
        let beta = QM31::from_m31_array([m31(3), m31(5), m31(7), m31(11)]);
        let (_, masked_claim) = mdoc_cbor_interaction_trace(
            &witness,
            TEST_STREAM_ID,
            &input,
            Some(&parsed),
            Some((&mask, beta)),
        );

        assert_eq!(masked_claim - unmasked_claim, beta * mask.target_sum());
    }

    #[test]
    fn raw_honest_trace_satisfies_every_polynomial_constraint() {
        let witness =
            MdocCborWitness::new(&nested_nationality_cbor(), MdocCborInputMode::Raw).unwrap();
        let base = mdoc_cbor_base_columns(&witness);
        assert!(constraints_hold(&witness, &base));
    }

    #[test]
    fn constraints_reject_active_gap_and_stack_tampering() {
        let padded = sha_pad(&nested_nationality_cbor());
        let witness = MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded).unwrap();

        let mut active_gap = mdoc_cbor_base_columns(&witness);
        active_gap[trace_col::ACTIVE][5] = m31(0);
        assert!(!constraints_hold(&witness, &active_gap));

        let mut stack = mdoc_cbor_base_columns(&witness);
        // Counter 0 starts after the fixed 69-column prefix.
        stack[trace_col::COUNTERS][1] += m31(1);
        assert!(!constraints_hold(&witness, &stack));

        let mut parent = mdoc_cbor_base_columns(&witness);
        parent[trace_col::PARENT][14] += m31(1);
        assert!(!constraints_hold(&witness, &parent));
    }

    #[test]
    fn constraints_reject_nonminimal_additional_argument() {
        let witness = MdocCborWitness::new(&[0x18, 0x18], MdocCborInputMode::Raw).unwrap();
        let mut forged = mdoc_cbor_base_columns(&witness);
        set_byte(&mut forged, 1, 23);
        forged[trace_col::ARGUMENT][0] = m31(23);
        for column in forged.iter_mut().skip(trace_col::SHORT_SLACK).take(8) {
            column[0] = m31(0);
        }
        assert!(!constraints_hold(&witness, &forged));
    }

    #[test]
    fn constraints_reject_marker_length_and_extra_padding_tampering() {
        let padded = sha_pad(&nested_nationality_cbor());
        let witness = MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded).unwrap();

        let mut marker = mdoc_cbor_base_columns(&witness);
        set_byte(&mut marker, witness.message_len, 0x81);
        assert!(!constraints_hold(&witness, &marker));

        let mut nonzero_padding = mdoc_cbor_base_columns(&witness);
        set_byte(&mut nonzero_padding, witness.message_len + 1, 1);
        assert!(!constraints_hold(&witness, &nonzero_padding));

        let mut length = mdoc_cbor_base_columns(&witness);
        let last = padded.len() - 1;
        set_byte(&mut length, last, padded[last].wrapping_add(8));
        assert!(!constraints_hold(&witness, &length));

        let mut extra_block = mdoc_cbor_base_columns(&witness);
        // Forge the len0 distance-to-marker witness. The six constrained bits
        // are the AIR's `0..=63` minimal-padding bound.
        let len0 = padded.len() - SHA_LENGTH_BYTES;
        for bit in 0..6 {
            extra_block[trace_col::PAD_SLACK + bit][len0] = m31(0);
        }
        assert!(!constraints_hold(&witness, &extra_block));
    }

    #[test]
    fn input_relation_detects_a_valid_cbor_payload_substitution() {
        let original = [0x42, 0xaa, 0xbb];
        let witness = MdocCborWitness::new(&original, MdocCborInputMode::Raw).unwrap();
        let mut base = mdoc_cbor_base_columns(&witness);
        set_byte(&mut base, 1, 0xcc);
        // String contents are intentionally semantic-free, so this remains a
        // valid CBOR trace. The full-stream relation must bind it to SHA.
        assert!(constraints_hold(&witness, &base));

        let rows = evaluate_columns(&witness, &base);
        let actual = rows[1].fractions[0].1;
        let expected = FieldBytesRelation::dummy().combine(&[
            m31(TEST_STREAM_ID),
            m31(1),
            m31(u32::from(original[1])),
        ]);
        assert_ne!(actual, expected);
    }

    #[test]
    fn parsed_relation_yields_every_cbor_byte_and_no_padding() {
        let raw = [0x82, 0x01, 0x02];
        let padded = sha_pad(&raw);
        let witness = MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded).unwrap();
        let base = mdoc_cbor_base_columns(&witness);
        let rows = evaluate_columns(&witness, &base);
        let zero = QM31::from_u32_unchecked(0, 0, 0, 0);
        for (index, row) in rows.iter().enumerate() {
            // Fraction 0 is input. Fraction 1 is parsed output.
            let parsed_num = row.fractions[1].0;
            if index < raw.len() {
                assert_ne!(parsed_num, zero);
            } else {
                assert_eq!(parsed_num, zero);
            }
        }
    }

    #[test]
    fn same_witness_materializations_randomize_every_sensitive_inactive_column() {
        let padded = sha_pad(&nested_nationality_cbor());
        let witness = MdocCborWitness::new(&padded, MdocCborInputMode::ShaPadded).unwrap();
        let first = mdoc_cbor_base_columns(&witness);
        let second = mdoc_cbor_base_columns(&witness);
        let inactive = witness.rows.len()..1usize << witness.log_size;
        assert!(inactive.len() >= MDOC_CBOR_BLIND_ROWS);

        // The real witness is deterministic.
        for column in 0..MDOC_CBOR_TRACE_COLS {
            assert_eq!(
                &first[column][..witness.rows.len()],
                &second[column][..witness.rows.len()]
            );
        }

        // Bytes and every relation-visible semantic metadata column receive
        // independent free evaluations in the blind suffix.
        for column in [
            trace_col::BYTE,
            trace_col::MAJOR,
            trace_col::ARGUMENT,
            trace_col::ARGUMENT + 1,
            trace_col::ARGUMENT + 2,
            trace_col::ARGUMENT + 3,
            trace_col::CONTENT_LEN,
            trace_col::DEPTH,
            trace_col::PARENT,
            trace_col::ORDINAL,
            trace_col::MAP_KEY,
            trace_col::MAP_VALUE,
        ] {
            assert_ne!(
                &first[column][inactive.clone()],
                &second[column][inactive.clone()],
                "inactive sensitive column {column} was not freshly blinded"
            );
        }
        assert!(constraints_hold(&witness, &first));
        assert!(constraints_hold(&witness, &second));

        // Random inactive values never open through either byte relation.
        let rows = evaluate_columns(&witness, &first);
        let zero = QM31::from_u32_unchecked(0, 0, 0, 0);
        for row in rows.iter().skip(witness.rows.len()) {
            assert_eq!(row.fractions[0].0, zero, "input lookup opened blind row");
            assert_eq!(row.fractions[1].0, zero, "parsed lookup opened blind row");
        }
    }
}
