//! Sound byte-stream parsing for mdoc CBOR.
//!
//! This component does not interpret semantics.
//! It consumes each byte of a SHA-padded or raw nested stream.
//! The bytes come from [`FieldBytesRelation`].
//! The component proves that one definite-length CBOR root occupies the prefix.
//! It emits one [`ParsedCborByteRelation`] tuple for each raw CBOR byte.
//! A semantic component must consume each emitted tuple.
//! Constrained parent and ordinal metadata identify genuine tokens.
//! The verifier does not supply byte offsets.

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

use crate::randomness::random_m31;

/// Use eight counters to support the nested maps in the TS13 mdoc profile.
pub(crate) const MDOC_CBOR_MAX_DEPTH: usize = 8;
const MDOC_CBOR_MIN_LOG_SIZE: u32 = 9;
const MDOC_CBOR_MAX_LOG_SIZE: u32 = 17;
const MDOC_CBOR_BLIND_ROWS: usize = 256;
const SHA_BLOCK_BYTES: usize = 64;
const SHA_LENGTH_BYTES: usize = 8;

relation!(ParsedCborByteRelation, 15);

/// One parser-instance output channel.
/// The parser draws and sets this relation.
/// A semantic component consumes each parsed row through the same handle.
/// Callers must allocate a distinct handle per parser instance.
pub(crate) type SharedParsedCborByteRelation = SharedRelation<ParsedCborByteRelation>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MdocCborInputMode {
    /// Consume the complete SHA compression input.
    /// This input includes the marker, zeros, and final big-endian bit length.
    ShaPadded,
    /// Consume raw CBOR bytes only.
    /// The unique root must end at the final active byte.
    /// Use this mode to parse selected tag-24 byte-string content.
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

        Ok(Self { rows, log_size })
    }
}

pub(crate) fn parser_log_size(active_rows: usize) -> Result<u32, MdocCborStreamError> {
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
const MDOC_CBOR_TRACE_COLS: usize = 117;

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

fn inactive_row_values(rng: &mut impl RngCore) -> Vec<M31> {
    let mut values = (0..MDOC_CBOR_TRACE_COLS)
        .map(|_| random_m31(rng))
        .collect::<Vec<_>>();
    // These columns encode the variable-length schedule.
    // Cross-row constraints set the inactive suffix to zero.
    // Other private byte, metadata, and state cells use independent random
    // filler values. STWO does not hide committed cells.
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

fn mdoc_cbor_base_columns(witness: &MdocCborWitness) -> Vec<Vec<M31>> {
    let n_rows = 1usize << witness.log_size;
    let mut columns = vec![vec![m31(0); n_rows]; MDOC_CBOR_TRACE_COLS];
    let mut rng = rand::thread_rng();
    for row_index in 0..n_rows {
        let values = witness
            .rows
            .get(row_index)
            .map(row_values)
            .unwrap_or_else(|| inactive_row_values(&mut rng));
        for (column, value) in columns.iter_mut().zip(values) {
            column[row_index] = value;
        }
    }
    columns
}

fn mdoc_cbor_base_trace(witness: &MdocCborWitness) -> Vec<MdocCborColumnEval> {
    mdoc_cbor_base_columns(witness)
        .into_iter()
        .map(|values| column_eval(witness.log_size, values))
        .collect()
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

#[derive(Clone)]
struct MdocCborStreamEval {
    log_size: u32,
    mode: MdocCborInputMode,
    stream_id: u32,
    input_relation: FieldBytesRelation,
    parsed_relation: ParsedCborByteRelation,
}

impl FrameworkEval for MdocCborStreamEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
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

        // Active rows form one contiguous prefix.
        // The zero suffix cannot become active.
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
        let not_last = one.clone() - last.clone();
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

        // Header iff the token-byte countdown is zero.
        boolean_constraint(&mut eval, cbor.clone(), header.clone());
        eval.add_constraint(header.clone() * (one.clone() - cbor.clone()));
        eval.add_constraint(cbor.clone() * remaining.clone() * header.clone());
        eval.add_constraint(
            cbor.clone()
                * (remaining.clone() * remaining_inv.clone() - one.clone() + header.clone()),
        );

        // Decode major type and additional-info width from the header byte.
        for flag in &major_flags {
            boolean_constraint(&mut eval, cbor.clone(), flag.clone());
        }
        let major_flag_sum = major_flags
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, flag| sum + flag);
        let decoded_major = major_flags
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (value, flag)| {
                sum + m31_const::<E>(value as u32) * flag.clone()
            });
        let major_from_bits = byte_bits[5].clone()
            + m31_const::<E>(2) * byte_bits[6].clone()
            + m31_const::<E>(4) * byte_bits[7].clone();
        eval.add_constraint(cbor.clone() * (major_flag_sum - header.clone()));
        eval.add_constraint(
            cbor.clone() * (decoded_major.clone() - header.clone() * major_from_bits),
        );
        eval.add_constraint(cbor.clone() * (major.clone() - decoded_major));

        let ai = byte_bits
            .iter()
            .take(5)
            .enumerate()
            .fold(zero.clone(), |sum, (bit, value)| {
                sum + m31_const::<E>(1u32 << bit) * value.clone()
            });
        for flag in &ext_flags {
            boolean_constraint(&mut eval, cbor.clone(), flag.clone());
        }
        let ext_sum = ext_flags
            .iter()
            .cloned()
            .fold(zero.clone(), |sum, flag| sum + flag);
        let decoded_ext_offset = ext_flags
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (offset, flag)| {
                sum + m31_const::<E>(offset as u32) * flag.clone()
            });
        let ext_offset_from_bits = byte_bits[0].clone() + m31_const::<E>(2) * byte_bits[1].clone();
        eval.add_constraint(
            cbor.clone()
                * (ext_sum.clone() - header.clone() * byte_bits[4].clone() * byte_bits[3].clone()),
        );
        eval.add_constraint(
            cbor.clone() * (decoded_ext_offset - ext_sum.clone() * ext_offset_from_bits),
        );
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

        // Canonical CBOR requires an argument of at least 24 for ai=24.
        // Wider arguments require a nonzero high byte.
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
        // The schedule makes `cbor_next` imply `cbor` away from the cyclic last row.
        // At the last row, `cbor_next` wraps to the first row's pinned value of one.
        let continue_cbor = cbor_next.clone() - last;
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
        for (level, (selected_value, counter)) in selected.iter().zip(counters.iter()).enumerate() {
            boolean_constraint(&mut eval, cbor.clone(), selected_value.clone());
            selected_counter += selected_value.clone() * counter[0].clone();
            for higher_counter in counters.iter().skip(level + 1) {
                eval.add_constraint(
                    cbor.clone() * selected_value.clone() * higher_counter[0].clone(),
                );
            }
        }
        eval.add_constraint(
            cbor.clone() * (selected_counter * selected_counter_inv - header.clone()),
        );
        eval.add_constraint(first.clone() * (remaining.clone()));
        eval.add_constraint(first.clone() * (counters[0][0].clone() - one.clone()));
        for counter in counters.iter().skip(1) {
            eval.add_constraint(first.clone() * counter[0].clone());
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

        for counter in &counters {
            eval.add_constraint(active.clone() * (one.clone() - cbor.clone()) * counter[0].clone());
        }

        // Consume each input byte.
        // The row index and active-prefix constraints prevent omissions.
        // They also prevent duplicates and changes to the byte order.
        eval.add_to_relation(RelationEntry::new(
            &self.input_relation,
            E::EF::from(active.clone()),
            &[
                m31_const::<E>(self.stream_id),
                row_index.clone(),
                byte.clone(),
            ],
        ));

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
        eval.add_to_relation(RelationEntry::new(
            &self.parsed_relation,
            -E::EF::from(cbor),
            &tuple,
        ));
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
    #[cfg(test)]
    pub(super) const MAJOR_FLAGS: usize = 24;
    pub(super) const ARGUMENT: usize = 32;
    pub(super) const CONTENT_LEN: usize = 36;
    pub(super) const DEPTH: usize = 37;
    pub(super) const PARENT: usize = 38;
    pub(super) const ORDINAL: usize = 39;
    pub(super) const MAP_KEY: usize = 40;
    pub(super) const MAP_VALUE: usize = 41;
    #[cfg(test)]
    pub(super) const EXT_FLAGS: usize = 59;
    #[cfg(test)]
    pub(super) const COUNTERS: usize = 69;
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocCborStreamInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

pub(crate) struct MdocCborStream {
    mode: MdocCborInputMode,
    stream_id: u32,
    log_size: u32,
    witness: Option<MdocCborWitness>,
    input_handle: SharedFieldRelation,
    parsed_handle: SharedParsedCborByteRelation,
    interaction_claim: Option<MdocCborStreamInteractionClaim>,
    component: Option<MdocCborComponent>,
}

impl MdocCborStream {
    pub(crate) fn new(
        bytes: Vec<u8>,
        mode: MdocCborInputMode,
        stream_id: u32,
        input: SharedFieldRelation,
        parsed: SharedParsedCborByteRelation,
    ) -> Result<Self, MdocCborStreamError> {
        let witness = MdocCborWitness::new(&bytes, mode)?;
        Ok(Self {
            mode,
            stream_id,
            log_size: witness.log_size,
            witness: Some(witness),
            input_handle: input,
            parsed_handle: parsed,
            interaction_claim: None,
            component: None,
        })
    }

    pub(crate) fn verifier(
        mode: MdocCborInputMode,
        stream_id: u32,
        log_size: u32,
        input: SharedFieldRelation,
        parsed: SharedParsedCborByteRelation,
        interaction_claim: MdocCborStreamInteractionClaim,
    ) -> Result<Self, MdocCborStreamError> {
        if !(MDOC_CBOR_MIN_LOG_SIZE..=MDOC_CBOR_MAX_LOG_SIZE).contains(&log_size) {
            return Err(MdocCborStreamError::TraceTooLarge {
                bytes: 1usize << log_size.min(usize::BITS - 1),
            });
        }
        Ok(Self {
            mode,
            stream_id,
            log_size,
            witness: None,
            input_handle: input,
            parsed_handle: parsed,
            interaction_claim: Some(interaction_claim),
            component: None,
        })
    }

    pub(crate) fn interaction_claim(&self) -> &MdocCborStreamInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc CBOR stream interaction claim is set")
    }

    fn input_relation(&self) -> FieldBytesRelation {
        self.input_handle.get()
    }

    fn parsed_relation(&self) -> ParsedCborByteRelation {
        self.parsed_handle.get()
    }
}

fn mdoc_cbor_interaction_trace(
    witness: &MdocCborWitness,
    stream_id: u32,
    input_relation: &FieldBytesRelation,
    parsed_relation: &ParsedCborByteRelation,
) -> (Vec<MdocCborColumnEval>, QM31) {
    let base = mdoc_cbor_base_trace(witness);
    let preprocessed = mdoc_cbor_preprocessed_columns(witness.log_size);
    let n_vec_rows = 1usize << (witness.log_size - LOG_N_LANES);

    let mut logup = LogupTraceGenerator::new(witness.log_size);
    logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
        let input_numerator = PackedQM31::from(base[trace_col::ACTIVE].data[vec_row]);
        let input_denominator: PackedQM31 = input_relation.combine(&[
            PackedM31::broadcast(m31(stream_id)),
            preprocessed[0].data[vec_row],
            base[trace_col::BYTE].data[vec_row],
        ]);
        let parsed_numerator = -PackedQM31::from(base[trace_col::CBOR].data[vec_row]);
        let parsed_denominator: PackedQM31 = parsed_relation.combine(&[
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
        (
            input_numerator * parsed_denominator + parsed_numerator * input_denominator,
            input_denominator * parsed_denominator,
        )
    }));
    logup.finalize_last()
}

impl Air for MdocCborStream {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x4d44_4f43_4342_4f52);
        channel.mix_u64(self.mode.transcript_tag());
        channel.mix_u64(u64::from(self.stream_id));
        channel.mix_u64(u64::from(self.log_size));
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        assert!(
            !self.parsed_handle.is_set(),
            "each mdoc CBOR parser instance needs a distinct parsed relation handle"
        );
        self.parsed_handle
            .set(ParsedCborByteRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![self.log_size; MDOC_CBOR_PREPROCESSED_COLS],
            trace: vec![self.log_size; MDOC_CBOR_TRACE_COLS],
            interaction: vec![self.log_size; SECURE_EXTENSION_DEGREE],
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
                input_relation: self.input_relation(),
                parsed_relation: self.parsed_relation(),
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

impl AirProver for MdocCborStream {
    fn max_log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 2
    }

    fn store_polynomial_coefficients(&self) -> bool {
        true
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
        let witness = self
            .witness
            .as_ref()
            .expect("mdoc CBOR prover has a witness");
        tb.extend_evals(mdoc_cbor_base_trace(witness));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let witness = self
            .witness
            .as_ref()
            .expect("mdoc CBOR prover has a witness");
        let (trace, claimed_sum) = mdoc_cbor_interaction_trace(
            witness,
            self.stream_id,
            &self.input_relation(),
            &self.parsed_relation(),
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

    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::assert_constraints_on_trace;

    fn weighted_mask(mask: u16, width: usize) -> u32 {
        (0..width)
            .filter(|offset| mask & (1 << offset) != 0)
            .map(|offset| offset as u32)
            .sum()
    }

    #[test]
    fn major_flag_moments_match_equality_decode_for_every_header_byte() {
        for byte in 0u16..=u8::MAX.into() {
            for header in [false, true] {
                let equality_mask = if header { 1 << (byte >> 5) } else { 0 };
                for mask in 0u16..1 << 8 {
                    let moments_accept = mask.count_ones() == u32::from(header)
                        && weighted_mask(mask, 8) == u32::from(header) * u32::from(byte >> 5);
                    assert_eq!(
                        moments_accept,
                        mask == equality_mask,
                        "byte={byte:#04x}, header={header}, mask={mask:#05x}"
                    );
                }
            }
        }
    }

    #[test]
    fn extended_flag_moments_match_equality_decode_for_every_header_byte() {
        for byte in 0u16..=u8::MAX.into() {
            let additional = byte & 0x1f;
            let bit_2 = (additional >> 2) & 1;
            let bit_3 = (additional >> 3) & 1;
            let bit_4 = (additional >> 4) & 1;
            for header in [false, true] {
                let equality_mask = if header && (24..=27).contains(&additional) {
                    1 << (additional - 24)
                } else {
                    0
                };
                let legal = !(header && bit_4 * bit_3 * bit_2 != 0);
                let extended = u32::from(header) * u32::from(bit_4 * bit_3);
                for mask in 0u16..1 << 4 {
                    let moments_accept = legal
                        && mask.count_ones() == extended
                        && weighted_mask(mask, 4) == extended * u32::from(additional & 0x03);
                    assert_eq!(
                        moments_accept,
                        legal && mask == equality_mask,
                        "byte={byte:#04x}, header={header}, mask={mask:#04x}"
                    );
                }
            }
        }
    }

    fn extended_byte_string_witness() -> MdocCborWitness {
        let mut bytes = vec![0x58, 24];
        bytes.extend(0u8..24);
        MdocCborWitness::new(&bytes, MdocCborInputMode::Raw)
            .expect("the fixture is one canonical 24-byte CBOR byte string")
    }

    fn sha_padded_single_item_witness() -> MdocCborWitness {
        let mut bytes = vec![0x01, 0x80];
        bytes.resize(SHA_BLOCK_BYTES - SHA_LENGTH_BYTES, 0);
        bytes.extend_from_slice(&8u64.to_be_bytes());
        MdocCborWitness::new(&bytes, MdocCborInputMode::ShaPadded)
            .expect("the fixture is one canonical CBOR integer with SHA-256 padding")
    }

    fn two_item_array_witness() -> MdocCborWitness {
        MdocCborWitness::new(&[0x82, 0x00, 0x01], MdocCborInputMode::Raw)
            .expect("the fixture is one canonical CBOR array with two items")
    }

    fn assert_witness_constraints(
        witness: &MdocCborWitness,
        mode: MdocCborInputMode,
        base_columns: Vec<Vec<M31>>,
    ) {
        let input_relation = FieldBytesRelation::dummy();
        let parsed_relation = ParsedCborByteRelation::dummy();
        let (interaction, claimed_sum) =
            mdoc_cbor_interaction_trace(witness, 0, &input_relation, &parsed_relation);
        let base = base_columns
            .into_iter()
            .map(|values| column_eval(witness.log_size, values))
            .collect();
        let trace = TreeVec::new(vec![
            mdoc_cbor_preprocessed_columns(witness.log_size),
            base,
            interaction,
        ]);
        let trace = trace.as_ref().map_cols(|column| column.to_cpu().values);
        let trace = trace.as_cols_ref();
        let eval = MdocCborStreamEval {
            log_size: witness.log_size,
            mode,
            stream_id: 0,
            input_relation,
            parsed_relation,
        };
        assert_constraints_on_trace(
            &trace,
            eval.log_size(),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn weighted_flag_tamper_rejects(changes: &[(usize, M31)]) -> bool {
        let witness = extended_byte_string_witness();
        let mut base = mdoc_cbor_base_columns(&witness);
        for &(column, value) in changes {
            base[column][0] = value;
        }
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_witness_constraints(&witness, MdocCborInputMode::Raw, base);
        }))
        .is_err()
    }

    #[test]
    fn linear_continue_gate_matches_product_on_every_schedule_edge() {
        let witnesses = [
            extended_byte_string_witness(),
            sha_padded_single_item_witness(),
            two_item_array_witness(),
        ];
        let mut saw_cbor_to_cbor = false;
        let mut saw_cbor_to_item = false;
        let mut saw_cbor_to_non_cbor = false;
        let mut saw_inactive_padding = false;
        let mut saw_cyclic_last_to_first = false;

        for witness in &witnesses {
            let base = mdoc_cbor_base_columns(witness);
            let n_rows = 1usize << witness.log_size;
            for row in 0..n_rows {
                let next = (row + 1) % n_rows;
                let cbor = base[trace_col::CBOR][row];
                let cbor_next = base[trace_col::CBOR][next];
                let last = m31(u32::from(row + 1 == n_rows));
                assert_eq!(
                    cbor * cbor_next,
                    cbor_next - last,
                    "schedule gate differs at row {row}"
                );

                saw_cbor_to_cbor |= cbor == m31(1) && cbor_next == m31(1);
                saw_cbor_to_item |= row + 1 < witness.rows.len()
                    && witness.rows[row].phase == MdocCborPhase::Cbor
                    && witness.rows[row + 1].header;
                saw_cbor_to_non_cbor |= cbor == m31(1) && cbor_next == m31(0);
                saw_inactive_padding |= row + 1 < n_rows
                    && base[trace_col::ACTIVE][row] == m31(0)
                    && cbor == m31(0)
                    && cbor_next == m31(0);
                saw_cyclic_last_to_first |=
                    row + 1 == n_rows && cbor == m31(0) && cbor_next == m31(1);
            }
        }

        assert!(saw_cbor_to_cbor);
        assert!(saw_cbor_to_item);
        assert!(saw_cbor_to_non_cbor);
        assert!(saw_inactive_padding);
        assert!(saw_cyclic_last_to_first);
    }

    #[test]
    fn major_flag_weight_tamper_is_rejected() {
        assert!(weighted_flag_tamper_rejects(&[
            (trace_col::MAJOR_FLAGS + 2, m31(0)),
            (trace_col::MAJOR_FLAGS + 3, m31(1)),
        ]));
    }

    #[test]
    fn extended_flag_weight_tamper_is_rejected() {
        assert!(weighted_flag_tamper_rejects(&[
            (trace_col::EXT_FLAGS, m31(0)),
            (trace_col::EXT_FLAGS + 1, m31(1)),
        ]));
    }

    #[test]
    fn non_cbor_stack_transition_tamper_is_rejected() {
        let witness = sha_padded_single_item_witness();
        let mut base = mdoc_cbor_base_columns(&witness);
        let marker_row = 1;
        assert_eq!(base[trace_col::CBOR][marker_row], m31(0));
        base[trace_col::COUNTERS][marker_row] = m31(1);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_witness_constraints(&witness, MdocCborInputMode::ShaPadded, base);
        }))
        .is_err());
    }
}
