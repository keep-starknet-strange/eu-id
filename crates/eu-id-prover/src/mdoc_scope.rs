//! Semantic issuer-scope proof for ISO 18013-5 mdoc credentials.
//!
//! This component is deliberately byte-stream based.  Each input stream is
//! first proved by [`crate::mdoc_cbor_stream::MdocCborStream`], and this AIR
//! consumes every resulting [`ParsedCborByteRelation`] tuple.  A public DFA
//! recognizes the complete byte language for:
//!
//! * the issuer COSE `Sig_structure`;
//! * the optional tag-24 MSO wrapper and the normalized MSO;
//! * every requested `IssuerSignedItemBytes` wrapper and inner item map.
//!
//! Variable byte strings are handled by a relation-linked `(state, remaining,
//! position)` chain.  The chain is keyed by `(stream_slot, byte_index)`, so
//! prover-selected host offsets cannot stand in for semantic navigation.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::io::Cursor;

use air_core::claim_mask::{
    add_claim_mask_fraction, ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS,
};
use air_core::relations::{
    field_id, DigestBytesRelation, FieldBytesRelation, SharedDigestRelation, SharedFieldRelation,
};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use ciborium::value::Value;
use predicates::nat::types::MAX_PRESENTED_NATIONALITIES;
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
    RelationEntry, TraceLocationAllocator,
};

use crate::mdoc_cbor_stream::{
    parsed_cbor_tuple, MdocCborInputMode, MdocCborStreamError, MdocCborWitness, MdocCborWitnessRow,
    ParsedCborByteRelation, SharedParsedCborByteRelation,
};

pub(crate) const MDOC_SCOPE_MAX_ITEMS: usize = 4;
pub(crate) const MDOC_SCOPE_MIN_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_SCOPE_MAX_LOG_SIZE: u32 = 20;
pub(crate) const MDOC_SCOPE_BLIND_ROWS: usize = 256;
pub(crate) const MDOC_SCOPE_MAX_DIGEST_ID: u32 = u16::MAX as u32;
const MDOC_SCOPE_NATIONALITY_SLACK_BITS: usize = 8;
const MDOC_SCOPE_UNORDERED_MAP_DEPTH: usize = 3;
const _: () = assert!(MAX_PRESENTED_NATIONALITIES == 1usize << MDOC_SCOPE_NATIONALITY_SLACK_BITS);

pub(crate) const ISSUER_SIG_STRUCTURE_STREAM_ID: u32 = 0x4d53_0000;
pub(crate) const ISSUER_PAYLOAD_STREAM_ID: u32 = 0x4d53_0001;
pub(crate) const NORMALIZED_MSO_STREAM_ID: u32 = 0x4d53_0002;
pub(crate) const ITEM_STREAM_ID_BASE: u32 = 0x4d49_0000;
/// Existing TS13 `mso_payload_exposure` field tag.  This output is the exact
/// issuerAuth payload, before optional tag-24 normalization.
pub(crate) const MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID: u32 = 40;

pub(crate) const fn item_outer_stream_id(index: usize) -> u32 {
    ITEM_STREAM_ID_BASE + (index as u32) * 2
}

pub(crate) const fn item_inner_stream_id(index: usize) -> u32 {
    item_outer_stream_id(index) + 1
}

/// A public, value-free profile selector.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MdocScopeProfile {
    V1,
    V2,
}

impl MdocScopeProfile {
    fn version_bytes(self) -> &'static [u8] {
        match self {
            Self::V1 => b"1.0",
            Self::V2 => b"2.0",
        }
    }

    fn transcript_tag(self) -> u64 {
        match self {
            Self::V1 => 1,
            Self::V2 => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MdocScopeBirthDateEncoding {
    Packed,
    Text,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MdocScopeNationalityEncoding {
    Numeric,
    Alpha2,
}

/// The verifier-selected semantics for one requested issuer-signed item.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MdocScopeMode {
    /// The complete definite-length, minimally encoded CBOR `elementValue`.
    ValueEquality(Vec<u8>),
    AgeOver(MdocScopeBirthDateEncoding),
    /// Every signed scalar/array element is emitted at indices `2*i,2*i+1`.
    Alpha2Set(MdocScopeNationalityEncoding),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocScopeItem {
    pub(crate) element_identifier: Vec<u8>,
    pub(crate) mode: MdocScopeMode,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocScopeStatement {
    pub(crate) request_binding: [u8; 32],
    pub(crate) profile: MdocScopeProfile,
    pub(crate) doc_type: Vec<u8>,
    pub(crate) namespace: Vec<u8>,
    pub(crate) items: Vec<MdocScopeItem>,
}

impl MdocScopeStatement {
    fn validate(&self) -> Result<(), MdocScopeError> {
        if !(1..=MDOC_SCOPE_MAX_ITEMS).contains(&self.items.len()) {
            return Err(MdocScopeError::InvalidItemCount(self.items.len()));
        }
        if self.doc_type.is_empty() || self.namespace.is_empty() {
            return Err(MdocScopeError::EmptyPublicIdentifier);
        }
        if std::str::from_utf8(&self.doc_type).is_err()
            || std::str::from_utf8(&self.namespace).is_err()
        {
            return Err(MdocScopeError::WrongShape("public identifier UTF-8"));
        }
        if self.doc_type.len() > MDOC_SCOPE_MAX_PUBLIC_IDENTIFIER_BYTES
            || self.namespace.len() > MDOC_SCOPE_MAX_PUBLIC_IDENTIFIER_BYTES
        {
            return Err(MdocScopeError::TraceTooLarge(
                self.doc_type.len().max(self.namespace.len()),
            ));
        }
        let mut identifiers = BTreeSet::new();
        let mut age = false;
        let mut nationality = false;
        for item in &self.items {
            if item.element_identifier.is_empty()
                || !identifiers.insert(item.element_identifier.clone())
            {
                return Err(MdocScopeError::DuplicateOrEmptyElementIdentifier);
            }
            if std::str::from_utf8(&item.element_identifier).is_err() {
                return Err(MdocScopeError::WrongShape("element identifier UTF-8"));
            }
            if item.element_identifier.len() > MDOC_SCOPE_MAX_PUBLIC_IDENTIFIER_BYTES {
                return Err(MdocScopeError::TraceTooLarge(item.element_identifier.len()));
            }
            match &item.mode {
                MdocScopeMode::ValueEquality(value) => {
                    if value.len() > MDOC_SCOPE_MAX_VALUE_EQUALITY_BYTES {
                        return Err(MdocScopeError::TraceTooLarge(value.len()));
                    }
                    MdocCborWitness::new(value, MdocCborInputMode::Raw)
                        .map_err(MdocScopeError::Cbor)?;
                    decode_exact(value, "value equality")?;
                }
                MdocScopeMode::AgeOver(_) => {
                    if std::mem::replace(&mut age, true) {
                        return Err(MdocScopeError::DuplicateMode("AgeOver"));
                    }
                    let coherent = matches!(
                        (self.profile, &item.mode),
                        (
                            MdocScopeProfile::V1,
                            MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Packed)
                        ) | (
                            MdocScopeProfile::V2,
                            MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Text)
                        )
                    );
                    if !coherent {
                        return Err(MdocScopeError::WrongShape("profile/birth_date encoding"));
                    }
                }
                MdocScopeMode::Alpha2Set(_) => {
                    if std::mem::replace(&mut nationality, true) {
                        return Err(MdocScopeError::DuplicateMode("Alpha2Set"));
                    }
                    let coherent = matches!(
                        (self.profile, &item.mode),
                        (
                            MdocScopeProfile::V1,
                            MdocScopeMode::Alpha2Set(MdocScopeNationalityEncoding::Numeric)
                        ) | (
                            MdocScopeProfile::V2,
                            MdocScopeMode::Alpha2Set(MdocScopeNationalityEncoding::Alpha2)
                        )
                    );
                    if !coherent {
                        return Err(MdocScopeError::WrongShape("profile/nationality encoding"));
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocScopeError {
    InvalidItemCount(usize),
    EmptyPublicIdentifier,
    DuplicateOrEmptyElementIdentifier,
    DuplicateMode(&'static str),
    HandleCount {
        kind: &'static str,
        expected: usize,
        actual: usize,
    },
    Decode(&'static str),
    WrongShape(&'static str),
    Cbor(MdocCborStreamError),
    NoDfaPath {
        stream_id: u32,
        byte_index: usize,
    },
    AmbiguousDfaPath {
        stream_id: u32,
        paths: usize,
    },
    TraceTooLarge(usize),
}

impl fmt::Display for MdocScopeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidItemCount(count) => write!(f, "invalid mdoc scope item count {count}"),
            Self::EmptyPublicIdentifier => write!(f, "docType and namespace must be non-empty"),
            Self::DuplicateOrEmptyElementIdentifier => {
                write!(f, "element identifiers must be non-empty and unique")
            }
            Self::DuplicateMode(mode) => write!(f, "duplicate mdoc scope mode {mode}"),
            Self::HandleCount {
                kind,
                expected,
                actual,
            } => write!(f, "{kind} handle count {actual}, expected {expected}"),
            Self::Decode(name) => write!(f, "cannot decode {name}"),
            Self::WrongShape(name) => write!(f, "wrong semantic shape for {name}"),
            Self::Cbor(error) => write!(f, "{error}"),
            Self::NoDfaPath {
                stream_id,
                byte_index,
            } => write!(
                f,
                "semantic DFA has no path for stream {stream_id:#x} at byte {byte_index}"
            ),
            Self::AmbiguousDfaPath { stream_id, paths } => write!(
                f,
                "semantic DFA has {paths} accepting paths for stream {stream_id:#x}"
            ),
            Self::TraceTooLarge(rows) => {
                write!(f, "mdoc semantic scope needs too many rows ({rows})")
            }
        }
    }
}

impl std::error::Error for MdocScopeError {}

relation!(MdocScopeDfaRelation, 6);
relation!(MdocScopeStateRelation, 20);
relation!(MdocScopeDigestIdRelation, 2);
relation!(MdocScopeDigestByteRelation, 3);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u32)]
enum ScopeAction {
    Exact = 0,
    Any = 1,
    Argument = 2,
    BeginBstr0 = 3,
    BeginBstr1 = 4,
    BeginBstr2 = 5,
    RawStay = 6,
    RawExit = 7,
    IgnoreStay = 8,
    IgnoreExit = 9,
    DirectMapStart = 10,
    CopyStay = 11,
    CopyExit = 12,
    FieldByte = 13,
    BeginArray0 = 14,
    BeginArray1 = 15,
    BeginArray2 = 16,
    NatAlphaFirst = 17,
    NatAlphaStay = 18,
    NatAlphaExit = 19,
    NatNumericFirst = 20,
    NatNumericStay = 21,
    NatNumericExit = 22,
    ItemDigestId0 = 23,
    ItemDigestId1 = 24,
    ItemDigestId2 = 25,
    BeginDigestMap0 = 26,
    BeginDigestMap1 = 27,
    BeginDigestMap2 = 28,
    SelectedDigestId0 = 29,
    SelectedDigestId1 = 30,
    SelectedDigestId2 = 31,
    UnknownDigestId0 = 32,
    UnknownDigestId1 = 33,
    UnknownDigestId2 = 34,
    SelectedDigestByte = 35,
    SelectedDigestStay = 36,
    SelectedDigestExit = 37,
    UnknownDigestByte = 38,
    UnknownDigestStay = 39,
    UnknownDigestExit = 40,
    /// Emit a byte that is also fixed by `p1 = index*256 + byte`.
    FieldExact = 41,
    /// Match one private ASCII decimal digit.
    AsciiDigit = 42,
    /// Match and emit one private ASCII decimal digit (`p0=field`, `p1=index`).
    FieldDigit = 43,
    BeginMap0 = 44,
    BeginMap1 = 45,
    BeginMap2 = 46,
    MapKeyStay0 = 47,
    MapKeyStay1 = 48,
    MapKeyStay2 = 49,
    MapKeyExit0 = 50,
    MapKeyExit1 = 51,
    MapKeyExit2 = 52,
}

const ALL_SCOPE_ACTIONS: [ScopeAction; 53] = [
    ScopeAction::Exact,
    ScopeAction::Any,
    ScopeAction::Argument,
    ScopeAction::BeginBstr0,
    ScopeAction::BeginBstr1,
    ScopeAction::BeginBstr2,
    ScopeAction::RawStay,
    ScopeAction::RawExit,
    ScopeAction::IgnoreStay,
    ScopeAction::IgnoreExit,
    ScopeAction::DirectMapStart,
    ScopeAction::CopyStay,
    ScopeAction::CopyExit,
    ScopeAction::FieldByte,
    ScopeAction::BeginArray0,
    ScopeAction::BeginArray1,
    ScopeAction::BeginArray2,
    ScopeAction::NatAlphaFirst,
    ScopeAction::NatAlphaStay,
    ScopeAction::NatAlphaExit,
    ScopeAction::NatNumericFirst,
    ScopeAction::NatNumericStay,
    ScopeAction::NatNumericExit,
    ScopeAction::ItemDigestId0,
    ScopeAction::ItemDigestId1,
    ScopeAction::ItemDigestId2,
    ScopeAction::BeginDigestMap0,
    ScopeAction::BeginDigestMap1,
    ScopeAction::BeginDigestMap2,
    ScopeAction::SelectedDigestId0,
    ScopeAction::SelectedDigestId1,
    ScopeAction::SelectedDigestId2,
    ScopeAction::UnknownDigestId0,
    ScopeAction::UnknownDigestId1,
    ScopeAction::UnknownDigestId2,
    ScopeAction::SelectedDigestByte,
    ScopeAction::SelectedDigestStay,
    ScopeAction::SelectedDigestExit,
    ScopeAction::UnknownDigestByte,
    ScopeAction::UnknownDigestStay,
    ScopeAction::UnknownDigestExit,
    ScopeAction::FieldExact,
    ScopeAction::AsciiDigit,
    ScopeAction::FieldDigit,
    ScopeAction::BeginMap0,
    ScopeAction::BeginMap1,
    ScopeAction::BeginMap2,
    ScopeAction::MapKeyStay0,
    ScopeAction::MapKeyStay1,
    ScopeAction::MapKeyStay2,
    ScopeAction::MapKeyExit0,
    ScopeAction::MapKeyExit1,
    ScopeAction::MapKeyExit2,
];
const SCOPE_ACTION_COUNT: usize = ALL_SCOPE_ACTIONS.len();

impl ScopeAction {
    fn index(self) -> usize {
        self as usize
    }

    fn is_selected_digest_id(self) -> bool {
        matches!(
            self,
            Self::SelectedDigestId0 | Self::SelectedDigestId1 | Self::SelectedDigestId2
        )
    }

    fn emits_raw(self) -> bool {
        matches!(
            self,
            Self::RawStay | Self::RawExit | Self::DirectMapStart | Self::CopyStay | Self::CopyExit
        )
    }

    fn emits_digest_byte(self) -> bool {
        matches!(
            self,
            Self::SelectedDigestByte | Self::SelectedDigestStay | Self::SelectedDigestExit
        )
    }

    fn unordered_map_level(self) -> Option<usize> {
        match self {
            Self::BeginMap0 | Self::MapKeyStay0 | Self::MapKeyExit0 => Some(0),
            Self::BeginMap1 | Self::MapKeyStay1 | Self::MapKeyExit1 => Some(1),
            Self::BeginMap2 | Self::MapKeyStay2 | Self::MapKeyExit2 => Some(2),
            _ => None,
        }
    }

    fn stays_in_unordered_map(self) -> bool {
        matches!(
            self,
            Self::MapKeyStay0 | Self::MapKeyStay1 | Self::MapKeyStay2
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DfaEdge {
    from: u32,
    to: u32,
    action: ScopeAction,
    p0: u32,
    p1: u32,
}

impl DfaEdge {
    fn tuple(self, slot: usize) -> [u32; 6] {
        [
            slot as u32,
            self.from,
            self.to,
            self.action as u32,
            self.p0,
            self.p1,
        ]
    }
}

#[derive(Clone, Debug)]
struct DfaProgram {
    start: u32,
    end: u32,
    edges: Vec<DfaEdge>,
}

#[derive(Clone, Debug)]
enum Grammar {
    Exact(Vec<u8>),
    Action(ScopeAction, u32, u32),
    Sequence(Vec<Grammar>),
    Choice(Vec<Grammar>),
    UnorderedMap {
        level: usize,
        fields: Vec<(Vec<u8>, Grammar)>,
    },
    VariableBstr {
        minimum_len: u32,
        output_raw_slot: Option<usize>,
    },
    Nationality(MdocScopeNationalityEncoding),
    DynamicItemDigestId(usize),
    DynamicDigestMap(usize),
    DirectOrWrappedMso {
        output_raw_slot: usize,
    },
}

#[derive(Default)]
struct ProgramBuilder {
    next_state: u32,
    edges: Vec<DfaEdge>,
    outgoing: HashMap<u32, Vec<DfaEdge>>,
}

impl ProgramBuilder {
    fn new() -> Self {
        // State zero is the unique accepting state.
        Self {
            next_state: 1,
            edges: Vec::new(),
            outgoing: HashMap::new(),
        }
    }

    fn state(&mut self) -> u32 {
        let state = self.next_state;
        self.next_state += 1;
        state
    }

    fn edge(&mut self, from: u32, to: u32, action: ScopeAction, p0: u32, p1: u32) {
        let edge = DfaEdge {
            from,
            to,
            action,
            p0,
            p1,
        };
        self.edges.push(edge);
        self.outgoing.entry(from).or_default().push(edge);
    }

    fn outgoing_edges(&self, state: u32) -> Vec<DfaEdge> {
        self.outgoing.get(&state).cloned().unwrap_or_default()
    }

    fn action(&mut self, action: ScopeAction, p0: u32, p1: u32, continuation: u32) -> u32 {
        let start = self.state();
        self.edge(start, continuation, action, p0, p1);
        start
    }

    fn merge_starts(&mut self, starts: &[u32]) -> u32 {
        assert!(!starts.is_empty());
        if starts.len() == 1 {
            return starts[0];
        }
        let merged = self.state();
        for &start in starts {
            for mut copied in self.outgoing_edges(start) {
                copied.from = merged;
                if copied.to == start {
                    copied.to = merged;
                }
                self.edge(copied.from, copied.to, copied.action, copied.p0, copied.p1);
            }
        }
        merged
    }

    fn compile(&mut self, grammar: &Grammar, continuation: u32) -> u32 {
        match grammar {
            Grammar::Exact(bytes) => bytes.iter().rev().fold(continuation, |next, &byte| {
                self.action(ScopeAction::Exact, u32::from(byte), 0, next)
            }),
            Grammar::Action(action, p0, p1) => self.action(*action, *p0, *p1, continuation),
            Grammar::Sequence(parts) => parts
                .iter()
                .rev()
                .fold(continuation, |next, part| self.compile(part, next)),
            Grammar::Choice(alternatives) => {
                let starts: Vec<_> = alternatives
                    .iter()
                    .map(|alternative| self.compile(alternative, continuation))
                    .collect();
                self.merge_starts(&starts)
            }
            Grammar::UnorderedMap { level, fields } => {
                self.compile_unordered_map(*level, fields, continuation)
            }
            Grammar::VariableBstr {
                minimum_len,
                output_raw_slot,
            } => self.compile_variable_bstr(*minimum_len, *output_raw_slot, continuation),
            Grammar::Nationality(encoding) => self.compile_nationality(*encoding, continuation),
            Grammar::DynamicItemDigestId(item) => {
                self.compile_dynamic_uint(true, *item, continuation)
            }
            Grammar::DynamicDigestMap(items) => self.compile_digest_map(*items, continuation),
            Grammar::DirectOrWrappedMso { output_raw_slot } => {
                self.compile_direct_or_wrapped(*output_raw_slot, continuation)
            }
        }
    }

    fn compile_unordered_map(
        &mut self,
        level: usize,
        fields: &[(Vec<u8>, Grammar)],
        continuation: u32,
    ) -> u32 {
        assert!(level < MDOC_SCOPE_UNORDERED_MAP_DEPTH);
        assert!(!fields.is_empty() && fields.len() < 24);
        let begin_action = [
            ScopeAction::BeginMap0,
            ScopeAction::BeginMap1,
            ScopeAction::BeginMap2,
        ][level];
        let stay_action = [
            ScopeAction::MapKeyStay0,
            ScopeAction::MapKeyStay1,
            ScopeAction::MapKeyStay2,
        ][level];
        let exit_action = [
            ScopeAction::MapKeyExit0,
            ScopeAction::MapKeyExit1,
            ScopeAction::MapKeyExit2,
        ][level];

        let entry = self.state();
        for (index, (key, value)) in fields.iter().enumerate() {
            let (&first_key_byte, key_suffix) =
                key.split_first().expect("unordered-map key is non-empty");
            let suffix =
                Grammar::Sequence(vec![Grammar::Exact(key_suffix.to_vec()), value.clone()]);
            let stay = self.compile(&suffix, entry);
            let exit = self.compile(&suffix, continuation);
            let bit = 1u32 << index;
            self.edge(entry, stay, stay_action, u32::from(first_key_byte), bit);
            self.edge(entry, exit, exit_action, u32::from(first_key_byte), bit);
        }

        let start = self.state();
        self.edge(
            start,
            entry,
            begin_action,
            fields.len() as u32,
            (1u32 << fields.len()) - 1,
        );
        start
    }

    fn compile_variable_bstr(
        &mut self,
        minimum_len: u32,
        output_raw_slot: Option<usize>,
        continuation: u32,
    ) -> u32 {
        let content = self.state();
        let (stay, exit, target) = if let Some(slot) = output_raw_slot {
            (ScopeAction::RawStay, ScopeAction::RawExit, slot as u32)
        } else {
            (ScopeAction::IgnoreStay, ScopeAction::IgnoreExit, 0)
        };
        self.edge(content, content, stay, target, 0);
        self.edge(content, continuation, exit, target, 0);

        let arg1 = self.action(ScopeAction::Argument, 0, 0, content);
        let arg2_second = self.action(ScopeAction::Argument, 0, 0, content);
        let arg2_first = self.action(ScopeAction::Argument, 0, 0, arg2_second);
        let start = self.state();
        self.edge(start, content, ScopeAction::BeginBstr0, minimum_len, 0);
        self.edge(start, arg1, ScopeAction::BeginBstr1, minimum_len, 0);
        self.edge(start, arg2_first, ScopeAction::BeginBstr2, minimum_len, 0);
        start
    }

    fn compile_dynamic_uint(&mut self, item_provider: bool, item: usize, continuation: u32) -> u32 {
        let actions = if item_provider {
            [
                ScopeAction::ItemDigestId0,
                ScopeAction::ItemDigestId1,
                ScopeAction::ItemDigestId2,
            ]
        } else {
            [
                ScopeAction::SelectedDigestId0,
                ScopeAction::SelectedDigestId1,
                ScopeAction::SelectedDigestId2,
            ]
        };
        let arg1 = self.action(ScopeAction::Argument, 0, 0, continuation);
        let arg2_second = self.action(ScopeAction::Argument, 0, 0, continuation);
        let arg2_first = self.action(ScopeAction::Argument, 0, 0, arg2_second);
        let start = self.state();
        self.edge(start, continuation, actions[0], item as u32, 0);
        self.edge(start, arg1, actions[1], item as u32, 0);
        self.edge(start, arg2_first, actions[2], item as u32, 0);
        start
    }

    fn compile_unknown_uint(&mut self, continuation: u32) -> u32 {
        let arg1 = self.action(ScopeAction::Argument, 0, 0, continuation);
        let arg2_second = self.action(ScopeAction::Argument, 0, 0, continuation);
        let arg2_first = self.action(ScopeAction::Argument, 0, 0, arg2_second);
        let start = self.state();
        self.edge(start, continuation, ScopeAction::UnknownDigestId0, 0, 0);
        self.edge(start, arg1, ScopeAction::UnknownDigestId1, 0, 0);
        self.edge(start, arg2_first, ScopeAction::UnknownDigestId2, 0, 0);
        start
    }

    fn compile_digest_map(&mut self, items: usize, continuation: u32) -> u32 {
        let entry = self.state();
        for item in 0..items {
            let last = self.state();
            self.edge(
                last,
                entry,
                ScopeAction::SelectedDigestStay,
                item as u32,
                31,
            );
            self.edge(
                last,
                continuation,
                ScopeAction::SelectedDigestExit,
                item as u32,
                31,
            );
            let mut value = last;
            for index in (0..31).rev() {
                value = self.action(ScopeAction::SelectedDigestByte, item as u32, index, value);
            }
            value = self.compile(&Grammar::Exact(vec![0x58, 0x20]), value);
            let key = self.compile_dynamic_uint(false, item, value);
            for mut edge in self.outgoing_edges(key) {
                edge.from = entry;
                self.edge(edge.from, edge.to, edge.action, edge.p0, edge.p1);
            }
        }

        let unknown_last = self.state();
        self.edge(unknown_last, entry, ScopeAction::UnknownDigestStay, 0, 31);
        self.edge(
            unknown_last,
            continuation,
            ScopeAction::UnknownDigestExit,
            0,
            31,
        );
        let mut unknown_value = unknown_last;
        for index in (0..31).rev() {
            unknown_value = self.action(ScopeAction::UnknownDigestByte, 0, index, unknown_value);
        }
        unknown_value = self.compile(&Grammar::Exact(vec![0x58, 0x20]), unknown_value);
        let unknown_key = self.compile_unknown_uint(unknown_value);
        for mut edge in self.outgoing_edges(unknown_key) {
            edge.from = entry;
            self.edge(edge.from, edge.to, edge.action, edge.p0, edge.p1);
        }

        let arg1 = self.action(ScopeAction::Argument, 0, 0, entry);
        let arg2_second = self.action(ScopeAction::Argument, 0, 0, entry);
        let arg2_first = self.action(ScopeAction::Argument, 0, 0, arg2_second);
        let start = self.state();
        self.edge(start, entry, ScopeAction::BeginDigestMap0, items as u32, 0);
        self.edge(start, arg1, ScopeAction::BeginDigestMap1, items as u32, 0);
        self.edge(
            start,
            arg2_first,
            ScopeAction::BeginDigestMap2,
            items as u32,
            0,
        );
        start
    }

    fn compile_nationality(
        &mut self,
        encoding: MdocScopeNationalityEncoding,
        continuation: u32,
    ) -> u32 {
        let (header, first, stay, exit) = match encoding {
            MdocScopeNationalityEncoding::Alpha2 => (
                0x62,
                ScopeAction::NatAlphaFirst,
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
            ),
            MdocScopeNationalityEncoding::Numeric => (
                0x42,
                ScopeAction::NatNumericFirst,
                ScopeAction::NatNumericStay,
                ScopeAction::NatNumericExit,
            ),
        };

        let scalar = Grammar::Sequence(vec![
            Grammar::Exact(vec![header]),
            Grammar::Action(ScopeAction::FieldByte, field_id::NATIONALITY, 0),
            Grammar::Action(ScopeAction::FieldByte, field_id::NATIONALITY, 1),
        ]);
        let scalar_start = self.compile(&scalar, continuation);

        let element = self.state();
        let second = self.state();
        self.edge(element, second, ScopeAction::Exact, u32::from(header), 0);
        let first_state = self.state();
        self.edge(second, first_state, first, field_id::NATIONALITY, 0);
        self.edge(first_state, element, stay, field_id::NATIONALITY, 0);
        self.edge(first_state, continuation, exit, field_id::NATIONALITY, 0);

        let arg1 = self.action(ScopeAction::Argument, 0, 0, element);
        let arg2_second = self.action(ScopeAction::Argument, 0, 0, element);
        let arg2_first = self.action(ScopeAction::Argument, 0, 0, arg2_second);
        let array_start = self.state();
        self.edge(array_start, element, ScopeAction::BeginArray0, 1, 0);
        self.edge(array_start, arg1, ScopeAction::BeginArray1, 1, 0);
        self.edge(array_start, arg2_first, ScopeAction::BeginArray2, 1, 0);

        self.merge_starts(&[scalar_start, array_start])
    }

    fn compile_direct_or_wrapped(&mut self, output_raw_slot: usize, continuation: u32) -> u32 {
        let copy = self.state();
        self.edge(copy, copy, ScopeAction::CopyStay, output_raw_slot as u32, 0);
        self.edge(
            copy,
            continuation,
            ScopeAction::CopyExit,
            output_raw_slot as u32,
            0,
        );
        let direct = self.action(ScopeAction::DirectMapStart, output_raw_slot as u32, 0, copy);
        let wrapped = Grammar::Sequence(vec![
            Grammar::Exact(cbor_head(6, 24)),
            Grammar::VariableBstr {
                minimum_len: 1,
                output_raw_slot: Some(output_raw_slot),
            },
        ]);
        let wrapped = self.compile(&wrapped, continuation);
        self.merge_starts(&[direct, wrapped])
    }

    fn finish(mut self, start: u32) -> DfaProgram {
        self.edges.sort_unstable();
        self.edges.dedup();
        DfaProgram {
            start,
            end: 0,
            edges: self.edges,
        }
    }
}

fn compile_program(grammar: Grammar) -> DfaProgram {
    let mut builder = ProgramBuilder::new();
    let start = builder.compile(&grammar, 0);
    builder.finish(start)
}

fn cbor_head(major: u8, argument: u64) -> Vec<u8> {
    let mut bytes = Vec::new();
    match argument {
        0..=23 => bytes.push((major << 5) | argument as u8),
        24..=0xff => {
            bytes.push((major << 5) | 24);
            bytes.push(argument as u8);
        }
        0x100..=0xffff => {
            bytes.push((major << 5) | 25);
            bytes.extend_from_slice(&(argument as u16).to_be_bytes());
        }
        0x1_0000..=0xffff_ffff => {
            bytes.push((major << 5) | 26);
            bytes.extend_from_slice(&(argument as u32).to_be_bytes());
        }
        _ => {
            bytes.push((major << 5) | 27);
            bytes.extend_from_slice(&argument.to_be_bytes());
        }
    }
    bytes
}

fn cbor_text(bytes: &[u8]) -> Vec<u8> {
    let mut encoded = cbor_head(3, bytes.len() as u64);
    encoded.extend_from_slice(bytes);
    encoded
}

fn exact_text(bytes: &[u8]) -> Grammar {
    Grammar::Exact(cbor_text(bytes))
}

fn exact_uint(value: u64) -> Grammar {
    Grammar::Exact(cbor_head(0, value))
}

fn exact_negative(argument: u64) -> Grammar {
    Grammar::Exact(cbor_head(1, argument))
}

fn fixed_private_bytes(field: u32, len: usize) -> Grammar {
    Grammar::Sequence(
        (0..len)
            .map(|index| Grammar::Action(ScopeAction::FieldByte, field, index as u32))
            .collect(),
    )
}

fn fixed_bstr_field(field: u32, len: usize) -> Grammar {
    Grammar::Sequence(vec![
        Grammar::Exact(cbor_head(2, len as u64)),
        fixed_private_bytes(field, len),
    ])
}

fn tdate_byte(field: Option<u32>, index: usize, byte: u8) -> Grammar {
    match field.filter(|_| index < 10) {
        Some(field) => Grammar::Action(
            ScopeAction::FieldExact,
            field,
            (index as u32) * 256 + u32::from(byte),
        ),
        None => Grammar::Exact(vec![byte]),
    }
}

fn tdate_digit(field: Option<u32>, index: usize) -> Grammar {
    match field {
        Some(field) => Grammar::Action(ScopeAction::FieldDigit, field, index as u32),
        None => Grammar::Action(ScopeAction::AsciiDigit, 0, 0),
    }
}

fn tdate_byte_set(
    field: Option<u32>,
    index: usize,
    bytes: impl IntoIterator<Item = u8>,
) -> Grammar {
    Grammar::Choice(
        bytes
            .into_iter()
            .map(|byte| tdate_byte(field, index, byte))
            .collect(),
    )
}

fn tdate_day_1_to_28(field: Option<u32>, index: usize) -> Grammar {
    Grammar::Choice(vec![
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'0'),
            tdate_byte_set(field, index + 1, b'1'..=b'9'),
        ]),
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'1'),
            tdate_digit(field, index + 1),
        ]),
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'2'),
            tdate_byte_set(field, index + 1, b'0'..=b'8'),
        ]),
    ])
}

fn tdate_day_1_to_30(field: Option<u32>, index: usize) -> Grammar {
    Grammar::Choice(vec![
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'0'),
            tdate_byte_set(field, index + 1, b'1'..=b'9'),
        ]),
        Grammar::Sequence(vec![
            tdate_byte_set(field, index, [b'1', b'2']),
            tdate_digit(field, index + 1),
        ]),
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'3'),
            tdate_byte(field, index + 1, b'0'),
        ]),
    ])
}

fn tdate_day_1_to_31(field: Option<u32>, index: usize) -> Grammar {
    Grammar::Choice(vec![
        tdate_day_1_to_30(field, index),
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'3'),
            tdate_byte(field, index + 1, b'1'),
        ]),
    ])
}

fn tdate_two_byte_values(field: Option<u32>, index: usize, values: &[[u8; 2]]) -> Grammar {
    Grammar::Choice(
        values
            .iter()
            .map(|value| {
                Grammar::Sequence(vec![
                    tdate_byte(field, index, value[0]),
                    tdate_byte(field, index + 1, value[1]),
                ])
            })
            .collect(),
    )
}

fn tdate_divisible_by_four_pair(field: Option<u32>, index: usize, allow_zero: bool) -> Grammar {
    let mut alternatives = vec![
        Grammar::Sequence(vec![
            tdate_byte_set(field, index, [b'1', b'3', b'5', b'7', b'9']),
            tdate_byte_set(field, index + 1, [b'2', b'6']),
        ]),
        Grammar::Sequence(vec![
            tdate_byte_set(field, index, [b'2', b'4', b'6', b'8']),
            tdate_byte_set(field, index + 1, [b'0', b'4', b'8']),
        ]),
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'0'),
            tdate_byte_set(field, index + 1, [b'4', b'8']),
        ]),
    ];
    if allow_zero {
        alternatives.push(Grammar::Sequence(vec![
            tdate_byte(field, index, b'0'),
            tdate_byte(field, index + 1, b'0'),
        ]));
    }
    Grammar::Choice(alternatives)
}

fn tdate_any_year(field: Option<u32>) -> Grammar {
    Grammar::Sequence((0..4).map(|index| tdate_digit(field, index)).collect())
}

fn tdate_leap_year(field: Option<u32>) -> Grammar {
    Grammar::Choice(vec![
        Grammar::Sequence(vec![
            tdate_digit(field, 0),
            tdate_digit(field, 1),
            tdate_divisible_by_four_pair(field, 2, false),
        ]),
        Grammar::Sequence(vec![
            tdate_divisible_by_four_pair(field, 0, true),
            tdate_byte(field, 2, b'0'),
            tdate_byte(field, 3, b'0'),
        ]),
    ])
}

fn tdate_month_and_day_except_february_29(field: Option<u32>) -> Grammar {
    Grammar::Choice(vec![
        Grammar::Sequence(vec![
            tdate_two_byte_values(
                field,
                5,
                &[*b"01", *b"03", *b"05", *b"07", *b"08", *b"10", *b"12"],
            ),
            tdate_byte(field, 7, b'-'),
            tdate_day_1_to_31(field, 8),
        ]),
        Grammar::Sequence(vec![
            tdate_two_byte_values(field, 5, &[*b"04", *b"06", *b"09", *b"11"]),
            tdate_byte(field, 7, b'-'),
            tdate_day_1_to_30(field, 8),
        ]),
        Grammar::Sequence(vec![
            tdate_byte(field, 5, b'0'),
            tdate_byte(field, 6, b'2'),
            tdate_byte(field, 7, b'-'),
            tdate_day_1_to_28(field, 8),
        ]),
    ])
}

fn tdate_hour(field: Option<u32>, index: usize) -> Grammar {
    Grammar::Choice(vec![
        Grammar::Sequence(vec![
            tdate_byte_set(field, index, [b'0', b'1']),
            tdate_digit(field, index + 1),
        ]),
        Grammar::Sequence(vec![
            tdate_byte(field, index, b'2'),
            tdate_byte_set(field, index + 1, b'0'..=b'3'),
        ]),
    ])
}

fn tdate_minute_or_second(field: Option<u32>, index: usize) -> Grammar {
    Grammar::Sequence(vec![
        tdate_byte_set(field, index, b'0'..=b'5'),
        tdate_digit(field, index + 1),
    ])
}

fn private_tdate(field: Option<u32>) -> Grammar {
    Grammar::Sequence(vec![
        Grammar::Exact(cbor_head(6, 0)),
        Grammar::Exact(cbor_head(3, 20)),
        Grammar::Choice(vec![
            Grammar::Sequence(vec![
                tdate_any_year(field),
                tdate_byte(field, 4, b'-'),
                tdate_month_and_day_except_february_29(field),
            ]),
            Grammar::Sequence(vec![
                tdate_leap_year(field),
                tdate_byte(field, 4, b'-'),
                tdate_byte(field, 5, b'0'),
                tdate_byte(field, 6, b'2'),
                tdate_byte(field, 7, b'-'),
                tdate_byte(field, 8, b'2'),
                tdate_byte(field, 9, b'9'),
            ]),
        ]),
        Grammar::Exact(vec![b'T']),
        tdate_hour(None, 11),
        Grammar::Exact(vec![b':']),
        tdate_minute_or_second(None, 14),
        Grammar::Exact(vec![b':']),
        tdate_minute_or_second(None, 17),
        Grammar::Exact(vec![b'Z']),
    ])
}

fn value_grammar(item: &MdocScopeItem) -> Grammar {
    match &item.mode {
        MdocScopeMode::ValueEquality(value) => Grammar::Exact(value.clone()),
        MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Packed) => {
            fixed_bstr_field(field_id::DOB, 4)
        }
        MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Text) => {
            let date = Grammar::Sequence(vec![
                Grammar::Exact(cbor_head(3, 10)),
                fixed_private_bytes(field_id::DOB, 10),
            ]);
            Grammar::Choice(vec![
                date.clone(),
                Grammar::Sequence(vec![Grammar::Exact(cbor_head(6, 1004)), date]),
            ])
        }
        MdocScopeMode::Alpha2Set(encoding) => Grammar::Nationality(*encoding),
    }
}

fn item_inner_grammar(
    profile: MdocScopeProfile,
    item_index: usize,
    item: &MdocScopeItem,
) -> Grammar {
    let fields = vec![
        (
            cbor_text(b"random"),
            Grammar::VariableBstr {
                minimum_len: 16,
                output_raw_slot: None,
            },
        ),
        (
            cbor_text(b"digestID"),
            Grammar::DynamicItemDigestId(item_index),
        ),
        (cbor_text(b"elementValue"), value_grammar(item)),
        (
            cbor_text(b"elementIdentifier"),
            exact_text(&item.element_identifier),
        ),
    ];
    match profile {
        MdocScopeProfile::V1 => Grammar::UnorderedMap { level: 0, fields },
        MdocScopeProfile::V2 => {
            let mut parts = vec![Grammar::Exact(cbor_head(5, fields.len() as u64))];
            for (key, value) in fields {
                parts.push(Grammar::Exact(key));
                parts.push(value);
            }
            Grammar::Sequence(parts)
        }
    }
}

fn cose_key_grammar() -> Grammar {
    let required = vec![
        (cbor_head(0, 1), exact_uint(2)),
        (cbor_head(1, 0), exact_uint(1)),
        (
            cbor_head(1, 1),
            fixed_bstr_field(field_id::MDOC_DEVICE_KEY_X, 32),
        ),
        (
            cbor_head(1, 2),
            fixed_bstr_field(field_id::MDOC_DEVICE_KEY_Y, 32),
        ),
    ];
    let mut with_alg = required.clone();
    with_alg.push((cbor_head(0, 3), exact_negative(6)));
    Grammar::Choice(vec![
        Grammar::UnorderedMap {
            level: 2,
            fields: required,
        },
        Grammar::UnorderedMap {
            level: 2,
            fields: with_alg,
        },
    ])
}

fn validity_grammar() -> Grammar {
    let required = vec![
        (cbor_text(b"signed"), private_tdate(None)),
        (
            cbor_text(b"validFrom"),
            private_tdate(Some(field_id::MDOC_VALID_FROM)),
        ),
        (
            cbor_text(b"validUntil"),
            private_tdate(Some(field_id::MDOC_VALID_UNTIL)),
        ),
    ];
    let mut with_expected_update = required.clone();
    with_expected_update.push((cbor_text(b"expectedUpdate"), private_tdate(None)));
    Grammar::Choice(vec![
        Grammar::UnorderedMap {
            level: 1,
            fields: required,
        },
        Grammar::UnorderedMap {
            level: 1,
            fields: with_expected_update,
        },
    ])
}

fn mso_grammar(statement: &MdocScopeStatement) -> Grammar {
    let value_digests = Grammar::Sequence(vec![
        Grammar::Exact(cbor_head(5, 1)),
        exact_text(&statement.namespace),
        Grammar::DynamicDigestMap(statement.items.len()),
    ]);
    let device_key_info = Grammar::UnorderedMap {
        level: 1,
        fields: vec![(cbor_text(b"deviceKey"), cose_key_grammar())],
    };
    Grammar::UnorderedMap {
        level: 0,
        fields: vec![
            (
                cbor_text(b"version"),
                exact_text(statement.profile.version_bytes()),
            ),
            (cbor_text(b"docType"), exact_text(&statement.doc_type)),
            (cbor_text(b"digestAlgorithm"), exact_text(b"SHA-256")),
            (cbor_text(b"valueDigests"), value_digests),
            (cbor_text(b"deviceKeyInfo"), device_key_info),
            (cbor_text(b"validityInfo"), validity_grammar()),
        ],
    }
}

fn sig_structure_grammar() -> Grammar {
    Grammar::Sequence(vec![
        Grammar::Exact(cbor_head(4, 4)),
        exact_text(b"Signature1"),
        Grammar::Exact(vec![0x43, 0xa1, 0x01, 0x26]),
        Grammar::Exact(vec![0x40]),
        Grammar::VariableBstr {
            minimum_len: 1,
            output_raw_slot: Some(0),
        },
    ])
}

fn item_outer_grammar(raw_output_slot: usize) -> Grammar {
    Grammar::Sequence(vec![
        Grammar::Exact(cbor_head(6, 24)),
        Grammar::VariableBstr {
            minimum_len: 1,
            output_raw_slot: Some(raw_output_slot),
        },
    ])
}

#[derive(Clone, Copy, Debug)]
struct StreamSpec {
    stream_id: u32,
    role_tag: u32,
    mode: MdocCborInputMode,
    raw_output_target: Option<u32>,
}

fn stream_specs(items: usize) -> Vec<StreamSpec> {
    let mut specs = vec![
        StreamSpec {
            stream_id: ISSUER_SIG_STRUCTURE_STREAM_ID,
            role_tag: 0,
            mode: MdocCborInputMode::ShaPadded,
            raw_output_target: Some(ISSUER_PAYLOAD_STREAM_ID),
        },
        StreamSpec {
            stream_id: ISSUER_PAYLOAD_STREAM_ID,
            role_tag: 1,
            mode: MdocCborInputMode::Raw,
            raw_output_target: Some(NORMALIZED_MSO_STREAM_ID),
        },
        StreamSpec {
            stream_id: NORMALIZED_MSO_STREAM_ID,
            role_tag: 2,
            mode: MdocCborInputMode::Raw,
            raw_output_target: None,
        },
    ];
    for index in 0..items {
        specs.push(StreamSpec {
            stream_id: item_outer_stream_id(index),
            role_tag: 3 + (index as u32) * 2,
            mode: MdocCborInputMode::ShaPadded,
            raw_output_target: Some(item_inner_stream_id(index)),
        });
        specs.push(StreamSpec {
            stream_id: item_inner_stream_id(index),
            role_tag: 4 + (index as u32) * 2,
            mode: MdocCborInputMode::Raw,
            raw_output_target: None,
        });
    }
    specs
}

fn programs(statement: &MdocScopeStatement) -> Vec<DfaProgram> {
    let mut result = vec![
        compile_program(sig_structure_grammar()),
        compile_program(Grammar::DirectOrWrappedMso { output_raw_slot: 1 }),
        compile_program(mso_grammar(statement)),
    ];
    for (index, item) in statement.items.iter().enumerate() {
        result.push(compile_program(item_outer_grammar(2 + index)));
        result.push(compile_program(item_inner_grammar(
            statement.profile,
            index,
            item,
        )));
    }
    result
}

const MDOC_SCOPE_MAX_PUBLIC_IDENTIFIER_BYTES: usize = 256;
const MDOC_SCOPE_MAX_VALUE_EQUALITY_BYTES: usize = 256;
const MDOC_SCOPE_MAX_STREAM_BYTES: usize = 130_000;
const MDOC_SCOPE_MAX_TOTAL_STREAM_BYTES: usize = 520_000;
const MDOC_SCOPE_MAX_DFA_CONFIGURATIONS: usize = 4096;

/// Shared handles needed by the complete recursive parser/scope composition.
///
/// Recommended module order:
///
/// 1. issuer/item SHA modules, then the SHA-padded outer parsers;
/// 2. `MdocScope` (draws each raw-stream relation and `semantic_fields`);
/// 3. payload/MSO/item-inner raw parsers;
/// 4. age/nationality/validity/device-key consumers.
///
/// `air_core` draws every module before writing interactions, so the scope may
/// consume parsed handles drawn by the later raw parsers.  Relation signs are:
/// parser parsed-byte providers `-1`, scope parsed consumers `+1`; scope raw
/// and semantic providers `-1`, raw-parser/predicate consumers `+1`; item SHA
/// digest providers `-1`, scope digest consumers `+1`.
#[derive(Clone)]
pub(crate) struct MdocScopeHandles {
    pub(crate) parsed_streams: Vec<SharedParsedCborByteRelation>,
    pub(crate) raw_streams: Vec<SharedFieldRelation>,
    pub(crate) semantic_fields: SharedFieldRelation,
    pub(crate) payload_hash_fields: SharedFieldRelation,
    pub(crate) item_digests: Vec<SharedDigestRelation>,
}

impl MdocScopeHandles {
    pub(crate) fn fresh(statement: &MdocScopeStatement) -> Result<Self, MdocScopeError> {
        statement.validate()?;
        let stream_count = 3 + statement.items.len() * 2;
        Ok(Self {
            parsed_streams: (0..stream_count)
                .map(|_| SharedParsedCborByteRelation::new())
                .collect(),
            raw_streams: (0..(2 + statement.items.len()))
                .map(|_| SharedFieldRelation::new())
                .collect(),
            semantic_fields: SharedFieldRelation::new(),
            payload_hash_fields: SharedFieldRelation::new(),
            item_digests: (0..statement.items.len())
                .map(|_| SharedDigestRelation::new())
                .collect(),
        })
    }

    pub(crate) fn stream_specs(
        &self,
        statement: &MdocScopeStatement,
    ) -> Result<Vec<MdocScopeParserSpec>, MdocScopeError> {
        validate_handle_counts(statement, self)?;
        let specs = stream_specs(statement.items.len());
        Ok(specs
            .into_iter()
            .enumerate()
            .map(|(slot, spec)| {
                let input = match slot {
                    0 => MdocScopeParserInput::ShaIssuer,
                    slot if slot >= 3 && (slot - 3).is_multiple_of(2) => {
                        MdocScopeParserInput::ShaItem((slot - 3) / 2)
                    }
                    1 => MdocScopeParserInput::Raw(self.raw_streams[0].clone()),
                    2 => MdocScopeParserInput::Raw(self.raw_streams[1].clone()),
                    _ => {
                        let item = (slot - 4) / 2;
                        MdocScopeParserInput::Raw(self.raw_streams[2 + item].clone())
                    }
                };
                MdocScopeParserSpec {
                    stream_id: spec.stream_id,
                    mode: spec.mode,
                    parsed: self.parsed_streams[slot].clone(),
                    input,
                }
            })
            .collect())
    }
}

#[derive(Clone)]
pub(crate) enum MdocScopeParserInput {
    /// The orchestrator supplies the issuer SHA field-exposure handle.
    ShaIssuer,
    /// The orchestrator supplies item `i`'s SHA field-exposure handle.
    ShaItem(usize),
    /// The scope itself provides this reindexed raw stream.
    Raw(SharedFieldRelation),
}

#[derive(Clone)]
pub(crate) struct MdocScopeParserSpec {
    pub(crate) stream_id: u32,
    pub(crate) mode: MdocCborInputMode,
    pub(crate) parsed: SharedParsedCborByteRelation,
    pub(crate) input: MdocScopeParserInput,
}

fn validate_handle_counts(
    statement: &MdocScopeStatement,
    handles: &MdocScopeHandles,
) -> Result<(), MdocScopeError> {
    let expected_streams = 3 + statement.items.len() * 2;
    if handles.parsed_streams.len() != expected_streams {
        return Err(MdocScopeError::HandleCount {
            kind: "parsed stream",
            expected: expected_streams,
            actual: handles.parsed_streams.len(),
        });
    }
    let expected_raw = 2 + statement.items.len();
    if handles.raw_streams.len() != expected_raw {
        return Err(MdocScopeError::HandleCount {
            kind: "raw stream",
            expected: expected_raw,
            actual: handles.raw_streams.len(),
        });
    }
    if handles.item_digests.len() != statement.items.len() {
        return Err(MdocScopeError::HandleCount {
            kind: "item digest",
            expected: statement.items.len(),
            actual: handles.item_digests.len(),
        });
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct MachineContext {
    remaining: u32,
    position: u32,
    previous_id: u32,
    have_previous: bool,
    seen: [bool; MDOC_SCOPE_MAX_ITEMS],
    map_remaining: [u32; MDOC_SCOPE_UNORDERED_MAP_DEPTH],
    map_accumulator: [u32; MDOC_SCOPE_UNORDERED_MAP_DEPTH],
    map_full: [u32; MDOC_SCOPE_UNORDERED_MAP_DEPTH],
}

impl MachineContext {
    const ZERO: Self = Self {
        remaining: 0,
        position: 0,
        previous_id: 0,
        have_previous: false,
        seen: [false; MDOC_SCOPE_MAX_ITEMS],
        map_remaining: [0; MDOC_SCOPE_UNORDERED_MAP_DEPTH],
        map_accumulator: [0; MDOC_SCOPE_UNORDERED_MAP_DEPTH],
        map_full: [0; MDOC_SCOPE_UNORDERED_MAP_DEPTH],
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct MachineKey {
    state: u32,
    context: MachineContext,
}

#[derive(Clone, Copy, Debug)]
struct AppliedEdge {
    edge: DfaEdge,
    before: MachineContext,
    after: MachineContext,
    slack: u16,
    inverse: M31,
}

fn width_matches(action: ScopeAction, byte: u8, base: u8) -> bool {
    match action {
        ScopeAction::BeginBstr0
        | ScopeAction::BeginArray0
        | ScopeAction::BeginDigestMap0
        | ScopeAction::ItemDigestId0
        | ScopeAction::SelectedDigestId0
        | ScopeAction::UnknownDigestId0 => byte >= base && byte < base + 24,
        ScopeAction::BeginBstr1
        | ScopeAction::BeginArray1
        | ScopeAction::BeginDigestMap1
        | ScopeAction::ItemDigestId1
        | ScopeAction::SelectedDigestId1
        | ScopeAction::UnknownDigestId1 => byte == base + 24,
        ScopeAction::BeginBstr2
        | ScopeAction::BeginArray2
        | ScopeAction::BeginDigestMap2
        | ScopeAction::ItemDigestId2
        | ScopeAction::SelectedDigestId2
        | ScopeAction::UnknownDigestId2 => byte == base + 25,
        _ => false,
    }
}

fn apply_edge_native(
    edge: DfaEdge,
    before: MachineContext,
    row: &MdocCborWitnessRow,
    is_last: bool,
    item_count: usize,
    expected_item_digest_ids: Option<&[u32]>,
) -> Option<AppliedEdge> {
    let action = edge.action;
    let mut after = before;
    let mut slack = 0u16;
    let mut inverse = M31::from_u32_unchecked(0);

    let matches = match action {
        ScopeAction::Exact => u32::from(row.byte) == edge.p0,
        ScopeAction::Any => !row.header,
        ScopeAction::Argument => !row.header,
        ScopeAction::BeginBstr0 | ScopeAction::BeginBstr1 | ScopeAction::BeginBstr2 => {
            let minimum = edge.p0;
            let ok = row.header
                && row.major == 2
                && width_matches(action, row.byte, 0x40)
                && row.content_len >= minimum;
            if ok {
                slack = (row.content_len - minimum) as u16;
                after.remaining = row.content_len;
                after.position = 0;
            }
            ok
        }
        ScopeAction::RawStay | ScopeAction::IgnoreStay => {
            let ok = !row.header && before.remaining > 1;
            if ok {
                after.remaining -= 1;
                after.position += 1;
                inverse = M31::from_u32_unchecked(after.remaining).inverse();
            }
            ok
        }
        ScopeAction::RawExit | ScopeAction::IgnoreExit => {
            let ok = !row.header && before.remaining == 1;
            if ok {
                after.remaining = 0;
                after.position += 1;
            }
            ok
        }
        ScopeAction::DirectMapStart => {
            let ok = row.header
                && row.major == 5
                && row.depth == 0
                && row.parent_header_index == 0
                && row.child_ordinal == 0;
            if ok {
                after.position = 1;
            }
            ok
        }
        ScopeAction::CopyStay => {
            let ok = !is_last;
            if ok {
                after.position += 1;
            }
            ok
        }
        ScopeAction::CopyExit => {
            let ok = is_last;
            if ok {
                after.position += 1;
            }
            ok
        }
        ScopeAction::FieldByte => !row.header,
        ScopeAction::FieldExact => !row.header && u32::from(row.byte) == edge.p1 % 256,
        ScopeAction::AsciiDigit | ScopeAction::FieldDigit => {
            let ok = !row.header && row.byte.is_ascii_digit();
            if ok {
                slack = u16::from(row.byte - b'0');
            }
            ok
        }
        ScopeAction::BeginMap0 | ScopeAction::BeginMap1 | ScopeAction::BeginMap2 => {
            let level = action
                .unordered_map_level()
                .expect("begin-map action has a level");
            let count = edge.p0;
            let ok = row.header
                && row.major == 5
                && row.argument == u64::from(count)
                && count < 24
                && u32::from(row.byte) == 0xa0 + count
                && edge.p1 == (1u32 << count) - 1
                && before.map_remaining[level] == 0;
            if ok {
                after.map_remaining[level] = count;
                after.map_accumulator[level] = 0;
                after.map_full[level] = edge.p1;
            }
            ok
        }
        ScopeAction::MapKeyStay0
        | ScopeAction::MapKeyStay1
        | ScopeAction::MapKeyStay2
        | ScopeAction::MapKeyExit0
        | ScopeAction::MapKeyExit1
        | ScopeAction::MapKeyExit2 => {
            let level = action
                .unordered_map_level()
                .expect("map-key action has a level");
            let stay = action.stays_in_unordered_map();
            let remaining = before.map_remaining[level];
            let ok = row.header
                && u32::from(row.byte) == edge.p0
                && edge.p1.is_power_of_two()
                && if stay {
                    remaining > 1
                } else {
                    remaining == 1
                        && before.map_accumulator[level] + edge.p1 == before.map_full[level]
                };
            if ok {
                after.map_remaining[level] -= 1;
                after.map_accumulator[level] += edge.p1;
                if stay {
                    inverse = M31::from_u32_unchecked(after.map_remaining[level]).inverse();
                }
            }
            ok
        }
        ScopeAction::BeginArray0 | ScopeAction::BeginArray1 | ScopeAction::BeginArray2 => {
            let minimum = edge.p0;
            let argument = u32::try_from(row.argument).ok()?;
            let ok = row.header
                && row.major == 4
                && width_matches(action, row.byte, 0x80)
                && argument >= minimum
                && argument <= MAX_PRESENTED_NATIONALITIES as u32;
            if ok {
                slack = (argument - minimum) as u16;
                after.remaining = argument;
                after.position = 0;
            }
            ok
        }
        ScopeAction::NatAlphaFirst | ScopeAction::NatNumericFirst => {
            !row.header && before.remaining != 0
        }
        ScopeAction::NatAlphaStay
        | ScopeAction::NatNumericStay
        | ScopeAction::NatAlphaExit
        | ScopeAction::NatNumericExit => {
            let stay = matches!(
                action,
                ScopeAction::NatAlphaStay | ScopeAction::NatNumericStay
            );
            let ok = !row.header
                && if stay {
                    before.remaining > 1
                } else {
                    before.remaining == 1
                };
            if ok {
                after.remaining -= 1;
                after.position += 1;
                if stay {
                    inverse = M31::from_u32_unchecked(after.remaining).inverse();
                }
            }
            ok
        }
        ScopeAction::ItemDigestId0 | ScopeAction::ItemDigestId1 | ScopeAction::ItemDigestId2 => {
            row.header
                && row.major == 0
                && row.argument <= u64::from(MDOC_SCOPE_MAX_DIGEST_ID)
                && width_matches(action, row.byte, 0)
                && (edge.p0 as usize) < item_count
        }
        ScopeAction::BeginDigestMap0
        | ScopeAction::BeginDigestMap1
        | ScopeAction::BeginDigestMap2 => {
            let minimum = edge.p0;
            let argument = u32::try_from(row.argument).ok()?;
            let ok = row.header
                && row.major == 5
                && width_matches(action, row.byte, 0xa0)
                && argument >= minimum
                && argument <= u32::from(u16::MAX);
            if ok {
                slack = (argument - minimum) as u16;
                after.remaining = argument;
                after.position = 0;
                after.previous_id = 0;
                after.have_previous = false;
                after.seen = [false; MDOC_SCOPE_MAX_ITEMS];
            }
            ok
        }
        ScopeAction::SelectedDigestId0
        | ScopeAction::SelectedDigestId1
        | ScopeAction::SelectedDigestId2
        | ScopeAction::UnknownDigestId0
        | ScopeAction::UnknownDigestId1
        | ScopeAction::UnknownDigestId2 => {
            let id = u32::try_from(row.argument).ok()?;
            let selected = action.is_selected_digest_id();
            let item = edge.p0 as usize;
            let order_ok = !before.have_previous || id > before.previous_id;
            let selected_ok = !selected || (item < item_count && !before.seen[item]);
            let expected_id_ok = expected_item_digest_ids.is_none_or(|expected| {
                if selected {
                    item < expected.len() && expected[item] == id
                } else {
                    !expected.contains(&id)
                }
            });
            let ok = row.header
                && row.major == 0
                && id <= MDOC_SCOPE_MAX_DIGEST_ID
                && width_matches(action, row.byte, 0)
                && order_ok
                && selected_ok
                && expected_id_ok;
            if ok {
                if before.have_previous {
                    slack = (id - before.previous_id - 1) as u16;
                }
                after.previous_id = id;
                after.have_previous = true;
                if selected {
                    after.seen[item] = true;
                }
            }
            ok
        }
        ScopeAction::SelectedDigestByte | ScopeAction::UnknownDigestByte => !row.header,
        ScopeAction::SelectedDigestStay | ScopeAction::UnknownDigestStay => {
            let ok = !row.header && before.remaining > 1;
            if ok {
                after.remaining -= 1;
                inverse = M31::from_u32_unchecked(after.remaining).inverse();
            }
            ok
        }
        ScopeAction::SelectedDigestExit | ScopeAction::UnknownDigestExit => {
            let ok = !row.header
                && before.remaining == 1
                && before.seen[..item_count].iter().all(|seen| *seen);
            if ok {
                after.remaining = 0;
            }
            ok
        }
    };
    matches.then_some(AppliedEdge {
        edge,
        before,
        after,
        slack,
        inverse,
    })
}

fn execute_program(
    stream_id: u32,
    program: &DfaProgram,
    rows: &[MdocCborWitnessRow],
    item_count: usize,
    expected_item_digest_ids: Option<&[u32]>,
) -> Result<Vec<AppliedEdge>, MdocScopeError> {
    let mut outgoing: HashMap<u32, Vec<DfaEdge>> = HashMap::new();
    for &edge in &program.edges {
        outgoing.entry(edge.from).or_default().push(edge);
    }
    let initial = MachineKey {
        state: program.start,
        context: MachineContext::ZERO,
    };
    let mut frontier = HashMap::from([(initial, ())]);
    let mut layers: Vec<HashMap<MachineKey, (MachineKey, AppliedEdge)>> =
        Vec::with_capacity(rows.len());

    for (index, row) in rows.iter().enumerate() {
        let mut next = HashMap::new();
        for key in frontier.keys().copied() {
            for &edge in outgoing.get(&key.state).into_iter().flatten() {
                if let Some(applied) = apply_edge_native(
                    edge,
                    key.context,
                    row,
                    index + 1 == rows.len(),
                    item_count,
                    expected_item_digest_ids,
                ) {
                    let next_key = MachineKey {
                        state: edge.to,
                        context: applied.after,
                    };
                    next.entry(next_key).or_insert((key, applied));
                }
            }
        }
        if next.is_empty() {
            return Err(MdocScopeError::NoDfaPath {
                stream_id,
                byte_index: index,
            });
        }
        if next.len() > MDOC_SCOPE_MAX_DFA_CONFIGURATIONS {
            return Err(MdocScopeError::AmbiguousDfaPath {
                stream_id,
                paths: next.len(),
            });
        }
        frontier = next.keys().copied().map(|key| (key, ())).collect();
        layers.push(next);
    }

    let accepting: Vec<_> = frontier
        .keys()
        .copied()
        .filter(|key| {
            key.state == program.end
                && key.context.remaining == 0
                && key
                    .context
                    .map_remaining
                    .iter()
                    .all(|remaining| *remaining == 0)
        })
        .collect();
    if accepting.len() != 1 {
        return Err(MdocScopeError::AmbiguousDfaPath {
            stream_id,
            paths: accepting.len(),
        });
    }
    let mut key = accepting[0];
    let mut path = Vec::with_capacity(rows.len());
    for layer in layers.iter().rev() {
        let (previous, edge) = layer
            .get(&key)
            .copied()
            .expect("accepting DFA state has a predecessor");
        path.push(edge);
        key = previous;
    }
    path.reverse();
    Ok(path)
}

fn decode_exact(bytes: &[u8], name: &'static str) -> Result<Value, MdocScopeError> {
    let mut cursor = Cursor::new(bytes);
    let value: Value =
        ciborium::de::from_reader(&mut cursor).map_err(|_| MdocScopeError::Decode(name))?;
    if cursor.position() as usize != bytes.len() {
        return Err(MdocScopeError::WrongShape(name));
    }
    Ok(value)
}

fn bytes_value<'a>(value: &'a Value, name: &'static str) -> Result<&'a [u8], MdocScopeError> {
    match value {
        Value::Bytes(bytes) => Ok(bytes),
        _ => Err(MdocScopeError::WrongShape(name)),
    }
}

fn extract_nested_streams(
    issuer_sig_structure: &[u8],
    item_outer_streams: &[Vec<u8>],
) -> Result<Vec<Vec<u8>>, MdocScopeError> {
    let issuer = decode_exact(issuer_sig_structure, "issuer Sig_structure")?;
    let issuer = match issuer {
        Value::Array(values) if values.len() == 4 => values,
        _ => return Err(MdocScopeError::WrongShape("issuer Sig_structure")),
    };
    let payload = bytes_value(&issuer[3], "issuer payload")?.to_vec();
    let decoded_payload = decode_exact(&payload, "issuer payload")?;
    let normalized_mso = match decoded_payload {
        Value::Map(_) => payload.clone(),
        Value::Tag(24, inner) => bytes_value(&inner, "MobileSecurityObjectBytes")?.to_vec(),
        _ => return Err(MdocScopeError::WrongShape("issuer payload")),
    };

    let mut streams = vec![issuer_sig_structure.to_vec(), payload, normalized_mso];
    for outer in item_outer_streams {
        let value = decode_exact(outer, "IssuerSignedItemBytes")?;
        let inner = match value {
            Value::Tag(24, inner) => bytes_value(&inner, "IssuerSignedItem")?.to_vec(),
            _ => return Err(MdocScopeError::WrongShape("IssuerSignedItemBytes")),
        };
        streams.push(outer.clone());
        streams.push(inner);
    }
    Ok(streams)
}

#[derive(Clone, Debug)]
struct ScopeActiveRow {
    stream_slot: usize,
    parsed: [u32; parsed_cbor_tuple::ARITY],
    first: bool,
    last: bool,
    applied: AppliedEdge,
}

#[derive(Clone, Debug)]
struct MdocScopeWitness {
    active_rows: Vec<ScopeActiveRow>,
    table_multiplicities: Vec<u32>,
    item_digest_bytes: Vec<[u8; 32]>,
    raw_stream_bytes: Vec<Vec<u8>>,
    nationality_count: Option<u16>,
}

impl MdocScopeWitness {
    fn new(
        statement: &MdocScopeStatement,
        issuer_sig_structure: &[u8],
        item_outer_streams: &[Vec<u8>],
        programs: &[DfaProgram],
        table_edges: &[(usize, DfaEdge)],
    ) -> Result<Self, MdocScopeError> {
        if issuer_sig_structure.len() > MDOC_SCOPE_MAX_STREAM_BYTES
            || item_outer_streams
                .iter()
                .any(|stream| stream.len() > MDOC_SCOPE_MAX_STREAM_BYTES)
        {
            return Err(MdocScopeError::TraceTooLarge(
                MDOC_SCOPE_MAX_STREAM_BYTES + 1,
            ));
        }
        let streams = extract_nested_streams(issuer_sig_structure, item_outer_streams)?;
        if streams
            .iter()
            .any(|stream| stream.len() > MDOC_SCOPE_MAX_STREAM_BYTES)
            || streams.iter().map(Vec::len).sum::<usize>() > MDOC_SCOPE_MAX_TOTAL_STREAM_BYTES
        {
            return Err(MdocScopeError::TraceTooLarge(
                streams.iter().map(Vec::len).sum(),
            ));
        }
        if streams.len() != programs.len() {
            return Err(MdocScopeError::HandleCount {
                kind: "witness stream",
                expected: programs.len(),
                actual: streams.len(),
            });
        }

        let specs = stream_specs(statement.items.len());
        let parsed_streams = streams
            .iter()
            .map(|bytes| {
                MdocCborWitness::new(bytes, MdocCborInputMode::Raw).map_err(MdocScopeError::Cbor)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut expected_item_digest_ids = Vec::with_capacity(statement.items.len());
        for item in 0..statement.items.len() {
            let slot = 4 + item * 2;
            let path = execute_program(
                specs[slot].stream_id,
                &programs[slot],
                &parsed_streams[slot].rows,
                statement.items.len(),
                None,
            )?;
            let digest_id = parsed_streams[slot]
                .rows
                .iter()
                .zip(path)
                .find_map(|(row, applied)| {
                    matches!(
                        applied.edge.action,
                        ScopeAction::ItemDigestId0
                            | ScopeAction::ItemDigestId1
                            | ScopeAction::ItemDigestId2
                    )
                    .then(|| u32::try_from(row.argument).ok())
                    .flatten()
                })
                .ok_or(MdocScopeError::WrongShape("IssuerSignedItem digestID"))?;
            expected_item_digest_ids.push(digest_id);
        }

        let mut active_rows = Vec::new();
        let mut use_counts: BTreeMap<(usize, DfaEdge), u32> = BTreeMap::new();
        let mut item_digest_bytes = vec![[0u8; 32]; statement.items.len()];
        let mut nationality_max_index = None::<u32>;
        for (slot, ((parsed, program), spec)) in parsed_streams
            .iter()
            .zip(programs)
            .zip(specs.iter())
            .enumerate()
        {
            let path = execute_program(
                spec.stream_id,
                program,
                &parsed.rows,
                statement.items.len(),
                Some(&expected_item_digest_ids),
            )?;
            for (index, (row, applied)) in parsed.rows.iter().zip(path).enumerate() {
                *use_counts.entry((slot, applied.edge)).or_default() += 1;
                if applied.edge.action.emits_digest_byte() {
                    let item = applied.edge.p0 as usize;
                    let byte_index = applied.edge.p1 as usize;
                    item_digest_bytes[item][byte_index] = row.byte;
                }
                let nationality_index = match applied.edge.action {
                    ScopeAction::FieldByte if applied.edge.p0 == field_id::NATIONALITY => {
                        Some(applied.edge.p1)
                    }
                    ScopeAction::NatAlphaFirst | ScopeAction::NatNumericFirst => {
                        Some(applied.before.position * 2)
                    }
                    ScopeAction::NatAlphaStay
                    | ScopeAction::NatAlphaExit
                    | ScopeAction::NatNumericStay
                    | ScopeAction::NatNumericExit => Some(applied.before.position * 2 + 1),
                    _ => None,
                };
                if let Some(index) = nationality_index {
                    nationality_max_index =
                        Some(nationality_max_index.map_or(index, |old| old.max(index)));
                }
                let limbs = row.argument_limbs();
                active_rows.push(ScopeActiveRow {
                    stream_slot: slot,
                    parsed: [
                        spec.stream_id,
                        row.byte_index,
                        u32::from(row.byte),
                        u32::from(row.header),
                        u32::from(row.major),
                        u32::from(limbs[0]),
                        u32::from(limbs[1]),
                        u32::from(limbs[2]),
                        u32::from(limbs[3]),
                        row.content_len,
                        u32::from(row.depth),
                        row.parent_header_index,
                        row.child_ordinal,
                        u32::from(row.map_key),
                        u32::from(row.map_value),
                    ],
                    first: index == 0,
                    last: index + 1 == parsed.rows.len(),
                    applied,
                });
            }
        }
        let table_multiplicities = table_edges
            .iter()
            .map(|edge| use_counts.get(edge).copied().unwrap_or(0))
            .collect();
        Ok(Self {
            active_rows,
            table_multiplicities,
            item_digest_bytes,
            raw_stream_bytes: streams,
            nationality_count: nationality_max_index
                .map(|index| u16::try_from(index / 2 + 1).expect("parser count fits u16")),
        })
    }
}

type MdocScopeColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocScopeComponent = FrameworkComponent<MdocScopeEval>;

const SCOPE_PREPROCESSED_FIXED_COLS: usize = 7;
const SCOPE_SLACK_BITS: usize = 16;
const SCOPE_DIGEST_BYTES: usize = 32;

#[derive(Clone, Debug)]
struct ScopeTraceColumns {
    active: usize,
    first: usize,
    last: usize,
    stream_selectors: std::ops::Range<usize>,
    byte_index: usize,
    byte: usize,
    parsed_meta: std::ops::Range<usize>,
    state_before: usize,
    state_after: usize,
    remaining_before: usize,
    remaining_after: usize,
    position_before: usize,
    position_after: usize,
    previous_id_before: usize,
    previous_id_after: usize,
    have_previous_before: usize,
    have_previous_after: usize,
    seen_before: std::ops::Range<usize>,
    seen_after: std::ops::Range<usize>,
    map_remaining_before: std::ops::Range<usize>,
    map_remaining_after: std::ops::Range<usize>,
    map_accumulator_before: std::ops::Range<usize>,
    map_accumulator_after: std::ops::Range<usize>,
    map_full_before: std::ops::Range<usize>,
    map_full_after: std::ops::Range<usize>,
    action_flags: std::ops::Range<usize>,
    p0: usize,
    p1: usize,
    slack_bits: std::ops::Range<usize>,
    inverse: usize,
    raw_selectors: std::ops::Range<usize>,
    field_id: usize,
    field_index: usize,
    digest_values: std::ops::Range<usize>,
    total: usize,
}

impl ScopeTraceColumns {
    fn new(streams: usize, raw_outputs: usize) -> Self {
        fn take(next: &mut usize) -> usize {
            let column = *next;
            *next += 1;
            column
        }
        let mut next = 0usize;
        let active = take(&mut next);
        let first = take(&mut next);
        let last = take(&mut next);
        let stream_selectors = next..next + streams;
        next += streams;
        let byte_index = take(&mut next);
        let byte = take(&mut next);
        let parsed_meta = next..next + (parsed_cbor_tuple::ARITY - 3);
        next += parsed_cbor_tuple::ARITY - 3;
        let state_before = take(&mut next);
        let state_after = take(&mut next);
        let remaining_before = take(&mut next);
        let remaining_after = take(&mut next);
        let position_before = take(&mut next);
        let position_after = take(&mut next);
        let previous_id_before = take(&mut next);
        let previous_id_after = take(&mut next);
        let have_previous_before = take(&mut next);
        let have_previous_after = take(&mut next);
        let seen_before = next..next + MDOC_SCOPE_MAX_ITEMS;
        next += MDOC_SCOPE_MAX_ITEMS;
        let seen_after = next..next + MDOC_SCOPE_MAX_ITEMS;
        next += MDOC_SCOPE_MAX_ITEMS;
        let map_remaining_before = next..next + MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        next += MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        let map_remaining_after = next..next + MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        next += MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        let map_accumulator_before = next..next + MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        next += MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        let map_accumulator_after = next..next + MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        next += MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        let map_full_before = next..next + MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        next += MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        let map_full_after = next..next + MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        next += MDOC_SCOPE_UNORDERED_MAP_DEPTH;
        let action_flags = next..next + SCOPE_ACTION_COUNT;
        next += SCOPE_ACTION_COUNT;
        let p0 = take(&mut next);
        let p1 = take(&mut next);
        let slack_bits = next..next + SCOPE_SLACK_BITS;
        next += SCOPE_SLACK_BITS;
        let inverse = take(&mut next);
        let raw_selectors = next..next + raw_outputs;
        next += raw_outputs;
        let field_id = take(&mut next);
        let field_index = take(&mut next);
        let digest_values = next..next + SCOPE_DIGEST_BYTES;
        next += SCOPE_DIGEST_BYTES;
        Self {
            active,
            first,
            last,
            stream_selectors,
            byte_index,
            byte,
            parsed_meta,
            state_before,
            state_after,
            remaining_before,
            remaining_after,
            position_before,
            position_after,
            previous_id_before,
            previous_id_after,
            have_previous_before,
            have_previous_after,
            seen_before,
            seen_after,
            map_remaining_before,
            map_remaining_after,
            map_accumulator_before,
            map_accumulator_after,
            map_full_before,
            map_full_after,
            action_flags,
            p0,
            p1,
            slack_bits,
            inverse,
            raw_selectors,
            field_id,
            field_index,
            digest_values,
            total: next,
        }
    }
}

fn scope_log_size(needed_rows: usize) -> Result<u32, MdocScopeError> {
    let rows = needed_rows
        .checked_add(MDOC_SCOPE_BLIND_ROWS)
        .ok_or(MdocScopeError::TraceTooLarge(needed_rows))?;
    let log_size = rows
        .next_power_of_two()
        .trailing_zeros()
        .max(MDOC_SCOPE_MIN_LOG_SIZE);
    if log_size > MDOC_SCOPE_MAX_LOG_SIZE {
        return Err(MdocScopeError::TraceTooLarge(needed_rows));
    }
    Ok(log_size)
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn random_m31() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
        if value < 2_147_483_647 {
            return m31(value);
        }
    }
}

fn coset_to_circle(log_size: u32, values: Vec<M31>) -> Vec<M31> {
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

fn scope_column(log_size: u32, values: Vec<M31>) -> MdocScopeColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_to_circle(log_size, values)),
    )
}

fn scope_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/scope/{name}"),
    }
}

fn scope_table_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    vec![
        scope_col_id("dfa_active"),
        scope_col_id("dfa_stream"),
        scope_col_id("dfa_from"),
        scope_col_id("dfa_to"),
        scope_col_id("dfa_action"),
        scope_col_id("dfa_p0"),
        scope_col_id("dfa_p1"),
    ]
}

fn scope_preprocessed_ids(item_count: usize) -> Vec<PreProcessedColumnId> {
    let mut ids = scope_table_preprocessed_ids();
    ids.extend((0..item_count).map(|item| scope_col_id(&format!("digest_item_{item}"))));
    ids
}

/// DFA edge-table preprocessed columns, hosted by the table component at its
/// own (edge-count driven) log size.
fn scope_table_preprocessed_columns(
    table_log_size: u32,
    table_edges: &[(usize, DfaEdge)],
) -> Vec<MdocScopeColumnEval> {
    let domain = 1usize << table_log_size;
    let mut columns = vec![vec![m31(0); domain]; SCOPE_PREPROCESSED_FIXED_COLS];
    for (row, (slot, edge)) in table_edges.iter().copied().enumerate() {
        columns[0][row] = m31(1);
        let tuple = edge.tuple(slot);
        for (index, value) in tuple.into_iter().enumerate() {
            columns[1 + index][row] = m31(value);
        }
    }
    columns
        .into_iter()
        .map(|values| scope_column(table_log_size, values))
        .collect()
}

/// Walk-side preprocessed columns (per-item digest aggregation flags) at the
/// walk component's log size.
fn scope_walk_preprocessed_columns(log_size: u32, item_count: usize) -> Vec<MdocScopeColumnEval> {
    let domain = 1usize << log_size;
    let mut columns = vec![vec![m31(0); domain]; item_count];
    for (item, column) in columns.iter_mut().enumerate() {
        column[item] = m31(1);
    }
    columns
        .into_iter()
        .map(|values| scope_column(log_size, values))
        .collect()
}

/// All scope preprocessed columns in [`scope_preprocessed_ids`] order: the DFA
/// edge table at the table log size, then the walk's digest-item flags.
fn scope_preprocessed_columns(
    log_size: u32,
    table_log_size: u32,
    table_edges: &[(usize, DfaEdge)],
    item_count: usize,
) -> Vec<MdocScopeColumnEval> {
    let mut columns = scope_table_preprocessed_columns(table_log_size, table_edges);
    columns.extend(scope_walk_preprocessed_columns(log_size, item_count));
    columns
}

/// Committed multiplicity column for the DFA edge table. Rows past the edge
/// list stay freshly blinded; the preprocessed `dfa_active` flag gates them out
/// of the LogUp yield.
fn scope_table_trace(table_log_size: u32, multiplicities: &[u32]) -> MdocScopeColumnEval {
    let domain = 1usize << table_log_size;
    let mut values: Vec<M31> = (0..domain).map(|_| random_m31()).collect();
    for (row, &multiplicity) in multiplicities.iter().enumerate() {
        values[row] = m31(multiplicity);
    }
    scope_column(table_log_size, values)
}

/// Table-side LogUp: yield `multiplicity` uses of every active edge tuple,
/// plus the private claimed-sum mask. Pairs into a single secure column.
fn scope_table_interaction_trace(
    table_log_size: u32,
    multiplicity: &MdocScopeColumnEval,
    table_preprocessed: &[MdocScopeColumnEval],
    dfa_relation: &MdocScopeDfaRelation,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<MdocScopeColumnEval>, QM31) {
    let n_vec_rows = 1usize << (table_log_size - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(table_log_size);
    match claim_mask {
        Some((mask, beta)) => {
            assert_eq!(mask.log_size(), table_log_size);
            logup.col_from_iter((0..n_vec_rows).map(|row| {
                let denominator: PackedQM31 = dfa_relation.combine(&[
                    table_preprocessed[1].data[row],
                    table_preprocessed[2].data[row],
                    table_preprocessed[3].data[row],
                    table_preprocessed[4].data[row],
                    table_preprocessed[5].data[row],
                    table_preprocessed[6].data[row],
                ]);
                let numerator =
                    -PackedQM31::from(table_preprocessed[0].data[row] * multiplicity.data[row]);
                let (mask_numerator, mask_denominator) = mask.packed_fraction_at(row, beta);
                (
                    numerator * mask_denominator + mask_numerator * denominator,
                    denominator * mask_denominator,
                )
            }));
        }
        None => {
            logup.col_from_iter((0..n_vec_rows).map(|row| {
                let denominator: PackedQM31 = dfa_relation.combine(&[
                    table_preprocessed[1].data[row],
                    table_preprocessed[2].data[row],
                    table_preprocessed[3].data[row],
                    table_preprocessed[4].data[row],
                    table_preprocessed[5].data[row],
                    table_preprocessed[6].data[row],
                ]);
                let numerator =
                    -PackedQM31::from(table_preprocessed[0].data[row] * multiplicity.data[row]);
                (numerator, denominator)
            }));
        }
    }
    logup.finalize_last()
}

fn set_bits(columns: &mut [Vec<M31>], range: std::ops::Range<usize>, row: usize, value: u16) {
    for (bit, column) in range.enumerate() {
        columns[column][row] = m31(u32::from((value >> bit) & 1));
    }
}

fn scope_base_trace(
    log_size: u32,
    columns: &ScopeTraceColumns,
    witness: &MdocScopeWitness,
    stream_count: usize,
    raw_count: usize,
) -> Vec<MdocScopeColumnEval> {
    let domain = 1usize << log_size;
    let mut values = (0..columns.total)
        .map(|_| (0..domain).map(|_| random_m31()).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let mut zero_columns = vec![columns.active, columns.first, columns.last];
    zero_columns.extend(columns.stream_selectors.clone());
    zero_columns.extend(columns.action_flags.clone());
    zero_columns.extend(columns.raw_selectors.clone());
    for column in zero_columns {
        values[column].fill(m31(0));
    }

    for (row_index, row) in witness.active_rows.iter().enumerate() {
        let applied = row.applied;
        values[columns.active][row_index] = m31(1);
        values[columns.first][row_index] = m31(u32::from(row.first));
        values[columns.last][row_index] = m31(u32::from(row.last));
        values[columns.stream_selectors.start + row.stream_slot][row_index] = m31(1);
        values[columns.byte_index][row_index] = m31(row.parsed[parsed_cbor_tuple::BYTE_INDEX]);
        values[columns.byte][row_index] = m31(row.parsed[parsed_cbor_tuple::BYTE]);
        for (offset, tuple_index) in (3..parsed_cbor_tuple::ARITY).enumerate() {
            values[columns.parsed_meta.start + offset][row_index] = m31(row.parsed[tuple_index]);
        }
        values[columns.state_before][row_index] = m31(applied.edge.from);
        values[columns.state_after][row_index] = m31(applied.edge.to);
        values[columns.remaining_before][row_index] = m31(applied.before.remaining);
        values[columns.remaining_after][row_index] = m31(applied.after.remaining);
        values[columns.position_before][row_index] = m31(applied.before.position);
        values[columns.position_after][row_index] = m31(applied.after.position);
        values[columns.previous_id_before][row_index] = m31(applied.before.previous_id);
        values[columns.previous_id_after][row_index] = m31(applied.after.previous_id);
        values[columns.have_previous_before][row_index] =
            m31(u32::from(applied.before.have_previous));
        values[columns.have_previous_after][row_index] =
            m31(u32::from(applied.after.have_previous));
        for item in 0..MDOC_SCOPE_MAX_ITEMS {
            values[columns.seen_before.start + item][row_index] =
                m31(u32::from(applied.before.seen[item]));
            values[columns.seen_after.start + item][row_index] =
                m31(u32::from(applied.after.seen[item]));
        }
        for level in 0..MDOC_SCOPE_UNORDERED_MAP_DEPTH {
            values[columns.map_remaining_before.start + level][row_index] =
                m31(applied.before.map_remaining[level]);
            values[columns.map_remaining_after.start + level][row_index] =
                m31(applied.after.map_remaining[level]);
            values[columns.map_accumulator_before.start + level][row_index] =
                m31(applied.before.map_accumulator[level]);
            values[columns.map_accumulator_after.start + level][row_index] =
                m31(applied.after.map_accumulator[level]);
            values[columns.map_full_before.start + level][row_index] =
                m31(applied.before.map_full[level]);
            values[columns.map_full_after.start + level][row_index] =
                m31(applied.after.map_full[level]);
        }
        values[columns.action_flags.start + applied.edge.action.index()][row_index] = m31(1);
        values[columns.p0][row_index] = m31(applied.edge.p0);
        values[columns.p1][row_index] = m31(applied.edge.p1);
        set_bits(
            &mut values,
            columns.slack_bits.clone(),
            row_index,
            applied.slack,
        );
        values[columns.inverse][row_index] = applied.inverse;

        if applied.edge.action.emits_raw() {
            values[columns.raw_selectors.start + applied.edge.p0 as usize][row_index] = m31(1);
        }
        let (field, index) = match applied.edge.action {
            ScopeAction::FieldByte => (applied.edge.p0, applied.edge.p1),
            ScopeAction::FieldExact => (applied.edge.p0, applied.edge.p1 / 256),
            ScopeAction::FieldDigit => (applied.edge.p0, applied.edge.p1),
            ScopeAction::NatAlphaFirst | ScopeAction::NatNumericFirst => (
                field_id::NATIONALITY,
                applied.before.position.saturating_mul(2),
            ),
            ScopeAction::NatAlphaStay
            | ScopeAction::NatAlphaExit
            | ScopeAction::NatNumericStay
            | ScopeAction::NatNumericExit => (
                field_id::NATIONALITY,
                applied.before.position.saturating_mul(2) + 1,
            ),
            _ => (0, 0),
        };
        values[columns.field_id][row_index] = m31(field);
        values[columns.field_index][row_index] = m31(index);
    }

    for (item, digest) in witness.item_digest_bytes.iter().enumerate() {
        for (byte, value) in digest.iter().copied().enumerate() {
            values[columns.digest_values.start + byte][item] = m31(u32::from(value));
        }
    }

    debug_assert_eq!(columns.stream_selectors.len(), stream_count);
    debug_assert_eq!(columns.raw_selectors.len(), raw_count);
    values
        .into_iter()
        .map(|column| scope_column(log_size, column))
        .collect()
}

#[derive(Clone)]
struct MdocScopeEval {
    log_size: u32,
    stream_ids: Vec<u32>,
    program_starts: Vec<u32>,
    program_ends: Vec<u32>,
    raw_target_stream_ids: Vec<u32>,
    parsed_relations: Vec<ParsedCborByteRelation>,
    raw_relations: Vec<FieldBytesRelation>,
    semantic_relation: FieldBytesRelation,
    payload_hash_relation: Option<FieldBytesRelation>,
    item_digest_relations: Vec<DigestBytesRelation>,
    dfa_relation: MdocScopeDfaRelation,
    state_relation: MdocScopeStateRelation,
    digest_id_relation: MdocScopeDigestIdRelation,
    digest_byte_relation: MdocScopeDigestByteRelation,
    claim_mask_beta: Option<QM31>,
}

fn f_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(m31(value))
}

fn action_sum<E: EvalAtRow>(
    trace: &[E::F],
    columns: &ScopeTraceColumns,
    actions: &[ScopeAction],
) -> E::F {
    actions.iter().fold(f_const::<E>(0), |sum, action| {
        sum + trace[columns.action_flags.start + action.index()].clone()
    })
}

fn item_selector<E: EvalAtRow>(value: E::F, item: usize, item_count: usize) -> E::F {
    let mut selector = f_const::<E>(1);
    for other in 0..item_count {
        if other == item {
            continue;
        }
        let denominator = m31(item as u32) - m31(other as u32);
        selector = selector
            * (value.clone() - f_const::<E>(other as u32))
            * E::F::from(denominator.inverse());
    }
    selector
}

impl FrameworkEval for MdocScopeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // The item selector is degree <= 3, multiplied by one action flag.
        self.log_size + 4
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let item_count = self.item_digest_relations.len();
        let stream_count = self.parsed_relations.len();
        let raw_count = self.raw_relations.len();
        let columns = ScopeTraceColumns::new(stream_count, raw_count);

        let aggregate: Vec<E::F> = (0..item_count)
            .map(|item| eval.get_preprocessed_column(scope_col_id(&format!("digest_item_{item}"))))
            .collect();
        let trace: Vec<E::F> = (0..columns.total).map(|_| eval.next_trace_mask()).collect();

        let zero = f_const::<E>(0);
        let one = f_const::<E>(1);
        let active = trace[columns.active].clone();
        let first = trace[columns.first].clone();
        let last = trace[columns.last].clone();
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(first.clone() * (first.clone() - one.clone()));
        eval.add_constraint(last.clone() * (last.clone() - one.clone()));
        eval.add_constraint(first.clone() * (one.clone() - active.clone()));
        eval.add_constraint(last.clone() * (one.clone() - active.clone()));

        let stream_selectors = trace[columns.stream_selectors.clone()].to_vec();
        let stream_sum = stream_selectors
            .iter()
            .cloned()
            .fold(zero.clone(), |a, b| a + b);
        eval.add_constraint(stream_sum - active.clone());
        for selector in &stream_selectors {
            eval.add_constraint(selector.clone() * (selector.clone() - one.clone()));
        }
        let stream_slot = stream_selectors
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (slot, selector)| {
                sum + selector.clone() * f_const::<E>(slot as u32)
            });

        let action_flags = trace[columns.action_flags.clone()].to_vec();
        let action_sum_all = action_flags
            .iter()
            .cloned()
            .fold(zero.clone(), |a, b| a + b);
        eval.add_constraint(action_sum_all - active.clone());
        for flag in &action_flags {
            eval.add_constraint(flag.clone() * (flag.clone() - one.clone()));
        }
        let action_code = action_flags
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (index, flag)| {
                sum + flag.clone() * f_const::<E>(index as u32)
            });
        let action = |which: ScopeAction| trace[columns.action_flags.start + which.index()].clone();

        let raw_selectors = trace[columns.raw_selectors.clone()].to_vec();
        for selector in &raw_selectors {
            eval.add_constraint(selector.clone() * (selector.clone() - one.clone()));
        }
        let emit_raw = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::RawStay,
                ScopeAction::RawExit,
                ScopeAction::DirectMapStart,
                ScopeAction::CopyStay,
                ScopeAction::CopyExit,
            ],
        );
        let raw_sum = raw_selectors
            .iter()
            .cloned()
            .fold(zero.clone(), |a, b| a + b);
        eval.add_constraint(raw_sum - emit_raw.clone());
        let raw_slot = raw_selectors
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (slot, selector)| {
                sum + selector.clone() * f_const::<E>(slot as u32)
            });
        eval.add_constraint(emit_raw.clone() * trace[columns.p0].clone() - raw_slot);

        let have_before = trace[columns.have_previous_before].clone();
        let have_after = trace[columns.have_previous_after].clone();
        eval.add_constraint(
            active.clone() * have_before.clone() * (have_before.clone() - one.clone()),
        );
        eval.add_constraint(
            active.clone() * have_after.clone() * (have_after.clone() - one.clone()),
        );
        let seen_before = trace[columns.seen_before.clone()].to_vec();
        let seen_after = trace[columns.seen_after.clone()].to_vec();
        let map_remaining_before = trace[columns.map_remaining_before.clone()].to_vec();
        let map_remaining_after = trace[columns.map_remaining_after.clone()].to_vec();
        let map_accumulator_before = trace[columns.map_accumulator_before.clone()].to_vec();
        let map_accumulator_after = trace[columns.map_accumulator_after.clone()].to_vec();
        let map_full_before = trace[columns.map_full_before.clone()].to_vec();
        let map_full_after = trace[columns.map_full_after.clone()].to_vec();
        for bit in seen_before.iter().chain(&seen_after) {
            eval.add_constraint(active.clone() * bit.clone() * (bit.clone() - one.clone()));
        }

        let starts =
            stream_selectors
                .iter()
                .enumerate()
                .fold(zero.clone(), |sum, (slot, selector)| {
                    sum + selector.clone() * f_const::<E>(self.program_starts[slot])
                });
        let ends = stream_selectors
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (slot, selector)| {
                sum + selector.clone() * f_const::<E>(self.program_ends[slot])
            });
        eval.add_constraint(first.clone() * (trace[columns.state_before].clone() - starts));
        eval.add_constraint(first.clone() * trace[columns.byte_index].clone());
        for column in [
            columns.remaining_before,
            columns.position_before,
            columns.previous_id_before,
            columns.have_previous_before,
        ] {
            eval.add_constraint(first.clone() * trace[column].clone());
        }
        for bit in &seen_before {
            eval.add_constraint(first.clone() * bit.clone());
        }
        for value in map_remaining_before
            .iter()
            .chain(&map_accumulator_before)
            .chain(&map_full_before)
        {
            eval.add_constraint(first.clone() * value.clone());
        }
        eval.add_constraint(last.clone() * (trace[columns.state_after].clone() - ends));
        eval.add_constraint(last.clone() * trace[columns.remaining_after].clone());
        for remaining in &map_remaining_after {
            eval.add_constraint(last.clone() * remaining.clone());
        }

        let begin_bstr = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::BeginBstr0,
                ScopeAction::BeginBstr1,
                ScopeAction::BeginBstr2,
            ],
        );
        let begin_array = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::BeginArray0,
                ScopeAction::BeginArray1,
                ScopeAction::BeginArray2,
            ],
        );
        let begin_digest_map = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::BeginDigestMap0,
                ScopeAction::BeginDigestMap1,
                ScopeAction::BeginDigestMap2,
            ],
        );
        let begin_any = begin_bstr.clone() + begin_array.clone() + begin_digest_map.clone();
        let decrement = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::RawStay,
                ScopeAction::RawExit,
                ScopeAction::IgnoreStay,
                ScopeAction::IgnoreExit,
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
                ScopeAction::NatNumericStay,
                ScopeAction::NatNumericExit,
                ScopeAction::SelectedDigestStay,
                ScopeAction::SelectedDigestExit,
                ScopeAction::UnknownDigestStay,
                ScopeAction::UnknownDigestExit,
            ],
        );
        let increment_position = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::RawStay,
                ScopeAction::RawExit,
                ScopeAction::IgnoreStay,
                ScopeAction::IgnoreExit,
                ScopeAction::DirectMapStart,
                ScopeAction::CopyStay,
                ScopeAction::CopyExit,
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
                ScopeAction::NatNumericStay,
                ScopeAction::NatNumericExit,
            ],
        );
        let content_len =
            trace[columns.parsed_meta.start + parsed_cbor_tuple::CONTENT_LEN - 3].clone();
        let arg_lo = trace[columns.parsed_meta.start + parsed_cbor_tuple::ARG_LO16 - 3].clone();
        let remaining_before = trace[columns.remaining_before].clone();
        let expected_remaining = remaining_before.clone()
            + begin_bstr.clone() * (content_len.clone() - remaining_before.clone())
            + (begin_array.clone() + begin_digest_map.clone())
                * (arg_lo.clone() - remaining_before.clone())
            - decrement.clone();
        eval.add_constraint(
            active.clone() * (trace[columns.remaining_after].clone() - expected_remaining),
        );
        let position_before = trace[columns.position_before].clone();
        let expected_position = position_before.clone() + increment_position
            - begin_any.clone() * position_before.clone();
        eval.add_constraint(
            active.clone() * (trace[columns.position_after].clone() - expected_position),
        );

        let selected_id = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::SelectedDigestId0,
                ScopeAction::SelectedDigestId1,
                ScopeAction::SelectedDigestId2,
            ],
        );
        let unknown_id = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::UnknownDigestId0,
                ScopeAction::UnknownDigestId1,
                ScopeAction::UnknownDigestId2,
            ],
        );
        let ordered_id = selected_id.clone() + unknown_id;
        let previous_before = trace[columns.previous_id_before].clone();
        let expected_previous = previous_before.clone()
            - begin_digest_map.clone() * previous_before.clone()
            + ordered_id.clone() * (arg_lo.clone() - previous_before.clone());
        eval.add_constraint(
            active.clone() * (trace[columns.previous_id_after].clone() - expected_previous),
        );
        let expected_have = have_before.clone() - begin_digest_map.clone() * have_before.clone()
            + ordered_id.clone() * (one.clone() - have_before.clone());
        eval.add_constraint(
            active.clone() * (trace[columns.have_previous_after].clone() - expected_have),
        );

        for item in 0..MDOC_SCOPE_MAX_ITEMS {
            let selected_for_item = if item < item_count {
                selected_id.clone()
                    * item_selector::<E>(trace[columns.p0].clone(), item, item_count)
            } else {
                zero.clone()
            };
            let expected_seen = seen_before[item].clone()
                - begin_digest_map.clone() * seen_before[item].clone()
                + selected_for_item.clone() * (one.clone() - seen_before[item].clone());
            eval.add_constraint(active.clone() * (seen_after[item].clone() - expected_seen));
            eval.add_constraint(selected_for_item * seen_before[item].clone());
        }

        let map_begin_actions = [
            ScopeAction::BeginMap0,
            ScopeAction::BeginMap1,
            ScopeAction::BeginMap2,
        ];
        let map_stay_actions = [
            ScopeAction::MapKeyStay0,
            ScopeAction::MapKeyStay1,
            ScopeAction::MapKeyStay2,
        ];
        let map_exit_actions = [
            ScopeAction::MapKeyExit0,
            ScopeAction::MapKeyExit1,
            ScopeAction::MapKeyExit2,
        ];
        for level in 0..MDOC_SCOPE_UNORDERED_MAP_DEPTH {
            let begin = action(map_begin_actions[level]);
            let stay = action(map_stay_actions[level]);
            let exit = action(map_exit_actions[level]);
            let key = stay.clone() + exit.clone();

            let expected_remaining = map_remaining_before[level].clone()
                + begin.clone() * (trace[columns.p0].clone() - map_remaining_before[level].clone())
                - key.clone();
            eval.add_constraint(
                active.clone() * (map_remaining_after[level].clone() - expected_remaining),
            );

            let expected_accumulator = map_accumulator_before[level].clone()
                - begin.clone() * map_accumulator_before[level].clone()
                + key.clone() * trace[columns.p1].clone();
            eval.add_constraint(
                active.clone() * (map_accumulator_after[level].clone() - expected_accumulator),
            );

            let expected_full = map_full_before[level].clone()
                + begin.clone() * (trace[columns.p1].clone() - map_full_before[level].clone());
            eval.add_constraint(active.clone() * (map_full_after[level].clone() - expected_full));

            eval.add_constraint(begin * map_remaining_before[level].clone());
            eval.add_constraint(
                stay * (map_remaining_after[level].clone() * trace[columns.inverse].clone()
                    - one.clone()),
            );
            eval.add_constraint(exit.clone() * (map_remaining_before[level].clone() - one.clone()));
            eval.add_constraint(
                exit * (map_accumulator_after[level].clone() - map_full_after[level].clone()),
            );
        }

        let slack = trace[columns.slack_bits.clone()]
            .iter()
            .enumerate()
            .fold(zero.clone(), |sum, (bit, value)| {
                sum + value.clone() * f_const::<E>(1u32 << bit)
            });
        let decimal_digit = action(ScopeAction::AsciiDigit) + action(ScopeAction::FieldDigit);
        let slack_gate = begin_any.clone() + ordered_id.clone() + decimal_digit.clone();
        for bit in &trace[columns.slack_bits.clone()] {
            eval.add_constraint(slack_gate.clone() * bit.clone() * (bit.clone() - one.clone()));
        }
        for bit in trace[columns.slack_bits.clone()].iter().skip(4) {
            eval.add_constraint(decimal_digit.clone() * bit.clone());
        }
        let digit_bits = &trace[columns.slack_bits.clone()];
        eval.add_constraint(decimal_digit.clone() * digit_bits[3].clone() * digit_bits[2].clone());
        eval.add_constraint(decimal_digit.clone() * digit_bits[3].clone() * digit_bits[1].clone());
        // Nationality arrays have minimum length one, so an eight-bit slack
        // is exactly the public 1..=256 entry bound.  Keep this invariant in
        // the scope AIR itself instead of relying on downstream relation
        // imbalance to reject oversized arrays.
        for bit in trace[columns.slack_bits.clone()]
            .iter()
            .skip(MDOC_SCOPE_NATIONALITY_SLACK_BITS)
        {
            eval.add_constraint(begin_array.clone() * bit.clone());
        }
        eval.add_constraint(
            begin_bstr.clone() * (content_len.clone() - trace[columns.p0].clone() - slack.clone()),
        );
        eval.add_constraint(
            (begin_array.clone() + begin_digest_map.clone())
                * (arg_lo.clone() - trace[columns.p0].clone() - slack.clone()),
        );
        eval.add_constraint(
            ordered_id.clone()
                * have_before.clone()
                * (arg_lo.clone() - previous_before.clone() - one.clone() - slack.clone()),
        );

        let stay = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::RawStay,
                ScopeAction::IgnoreStay,
                ScopeAction::NatAlphaStay,
                ScopeAction::NatNumericStay,
                ScopeAction::SelectedDigestStay,
                ScopeAction::UnknownDigestStay,
            ],
        );
        let exit = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::RawExit,
                ScopeAction::IgnoreExit,
                ScopeAction::NatAlphaExit,
                ScopeAction::NatNumericExit,
                ScopeAction::SelectedDigestExit,
                ScopeAction::UnknownDigestExit,
            ],
        );
        eval.add_constraint(
            stay.clone()
                * (trace[columns.remaining_after].clone() * trace[columns.inverse].clone()
                    - one.clone()),
        );
        eval.add_constraint(exit.clone() * (remaining_before.clone() - one.clone()));

        let header = trace[columns.parsed_meta.start + parsed_cbor_tuple::HEADER - 3].clone();
        let major = trace[columns.parsed_meta.start + parsed_cbor_tuple::MAJOR - 3].clone();
        let depth = trace[columns.parsed_meta.start + parsed_cbor_tuple::DEPTH - 3].clone();
        let parent =
            trace[columns.parsed_meta.start + parsed_cbor_tuple::PARENT_HEADER_INDEX - 3].clone();
        let ordinal =
            trace[columns.parsed_meta.start + parsed_cbor_tuple::CHILD_ORDINAL - 3].clone();
        let byte = trace[columns.byte].clone();
        eval.add_constraint(decimal_digit * (byte.clone() - f_const::<E>(u32::from(b'0')) - slack));
        let exact = action(ScopeAction::Exact);
        eval.add_constraint(exact * (byte.clone() - trace[columns.p0].clone()));
        let begin_unordered_map = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::BeginMap0,
                ScopeAction::BeginMap1,
                ScopeAction::BeginMap2,
            ],
        );
        eval.add_constraint(begin_unordered_map.clone() * (header.clone() - one.clone()));
        eval.add_constraint(begin_unordered_map.clone() * (major.clone() - f_const::<E>(5)));
        eval.add_constraint(
            begin_unordered_map.clone()
                * (byte.clone() - f_const::<E>(0xa0) - trace[columns.p0].clone()),
        );
        eval.add_constraint(begin_unordered_map * (arg_lo.clone() - trace[columns.p0].clone()));
        let unordered_map_key = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::MapKeyStay0,
                ScopeAction::MapKeyStay1,
                ScopeAction::MapKeyStay2,
                ScopeAction::MapKeyExit0,
                ScopeAction::MapKeyExit1,
                ScopeAction::MapKeyExit2,
            ],
        );
        eval.add_constraint(unordered_map_key.clone() * (header.clone() - one.clone()));
        eval.add_constraint(unordered_map_key * (byte.clone() - trace[columns.p0].clone()));
        let non_header_actions = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::Any,
                ScopeAction::Argument,
                ScopeAction::RawStay,
                ScopeAction::RawExit,
                ScopeAction::IgnoreStay,
                ScopeAction::IgnoreExit,
                ScopeAction::FieldByte,
                ScopeAction::FieldExact,
                ScopeAction::AsciiDigit,
                ScopeAction::FieldDigit,
                ScopeAction::NatAlphaFirst,
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
                ScopeAction::NatNumericFirst,
                ScopeAction::NatNumericStay,
                ScopeAction::NatNumericExit,
                ScopeAction::SelectedDigestByte,
                ScopeAction::SelectedDigestStay,
                ScopeAction::SelectedDigestExit,
                ScopeAction::UnknownDigestByte,
                ScopeAction::UnknownDigestStay,
                ScopeAction::UnknownDigestExit,
            ],
        );
        eval.add_constraint(non_header_actions * header.clone());

        for (which, expected_byte) in [
            (ScopeAction::BeginBstr0, None),
            (ScopeAction::BeginBstr1, Some(0x58)),
            (ScopeAction::BeginBstr2, Some(0x59)),
        ] {
            let gate = action(which);
            eval.add_constraint(gate.clone() * (header.clone() - one.clone()));
            eval.add_constraint(gate.clone() * (major.clone() - f_const::<E>(2)));
            match expected_byte {
                Some(expected) => {
                    eval.add_constraint(gate * (byte.clone() - f_const::<E>(expected)));
                }
                None => {
                    eval.add_constraint(
                        gate * (byte.clone() - f_const::<E>(0x40) - content_len.clone()),
                    );
                }
            }
        }
        for (which, expected_byte, expected_major) in [
            (ScopeAction::BeginArray0, None, 4),
            (ScopeAction::BeginArray1, Some(0x98), 4),
            (ScopeAction::BeginArray2, Some(0x99), 4),
            (ScopeAction::BeginDigestMap0, None, 5),
            (ScopeAction::BeginDigestMap1, Some(0xb8), 5),
            (ScopeAction::BeginDigestMap2, Some(0xb9), 5),
        ] {
            let gate = action(which);
            eval.add_constraint(gate.clone() * (header.clone() - one.clone()));
            eval.add_constraint(gate.clone() * (major.clone() - f_const::<E>(expected_major)));
            match expected_byte {
                Some(expected) => {
                    eval.add_constraint(gate * (byte.clone() - f_const::<E>(expected)));
                }
                None => {
                    eval.add_constraint(
                        gate * (byte.clone() - f_const::<E>(expected_major << 5) - arg_lo.clone()),
                    );
                }
            }
        }

        let id0 = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::ItemDigestId0,
                ScopeAction::SelectedDigestId0,
                ScopeAction::UnknownDigestId0,
            ],
        );
        let id1 = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::ItemDigestId1,
                ScopeAction::SelectedDigestId1,
                ScopeAction::UnknownDigestId1,
            ],
        );
        let id2 = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::ItemDigestId2,
                ScopeAction::SelectedDigestId2,
                ScopeAction::UnknownDigestId2,
            ],
        );
        let id_all = id0.clone() + id1.clone() + id2.clone();
        eval.add_constraint(id_all.clone() * (header.clone() - one.clone()));
        eval.add_constraint(id_all.clone() * major.clone());
        for tuple_index in [
            parsed_cbor_tuple::ARG_16_31,
            parsed_cbor_tuple::ARG_32_47,
            parsed_cbor_tuple::ARG_HI16,
        ] {
            eval.add_constraint(
                id_all.clone() * trace[columns.parsed_meta.start + tuple_index - 3].clone(),
            );
        }
        eval.add_constraint(id0 * (byte.clone() - arg_lo.clone()));
        eval.add_constraint(id1 * (byte.clone() - f_const::<E>(0x18)));
        eval.add_constraint(id2 * (byte.clone() - f_const::<E>(0x19)));

        let direct = action(ScopeAction::DirectMapStart);
        eval.add_constraint(direct.clone() * (header.clone() - one.clone()));
        eval.add_constraint(direct.clone() * (major.clone() - f_const::<E>(5)));
        eval.add_constraint(direct.clone() * depth);
        eval.add_constraint(direct.clone() * parent);
        eval.add_constraint(direct * ordinal);
        eval.add_constraint(action(ScopeAction::CopyStay) * last.clone());
        eval.add_constraint(action(ScopeAction::CopyExit) * (last.clone() - one.clone()));

        let emit_field = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::FieldByte,
                ScopeAction::FieldExact,
                ScopeAction::FieldDigit,
                ScopeAction::NatAlphaFirst,
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
                ScopeAction::NatNumericFirst,
                ScopeAction::NatNumericStay,
                ScopeAction::NatNumericExit,
            ],
        );
        let fixed_field = action(ScopeAction::FieldByte);
        let exact_field = action(ScopeAction::FieldExact);
        let digit_field = action(ScopeAction::FieldDigit);
        let nat_first = action(ScopeAction::NatAlphaFirst) + action(ScopeAction::NatNumericFirst);
        let nat_second = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
                ScopeAction::NatNumericStay,
                ScopeAction::NatNumericExit,
            ],
        );
        let expected_field = (fixed_field.clone() + exact_field.clone() + digit_field.clone())
            * trace[columns.p0].clone()
            + (nat_first.clone() + nat_second.clone()) * f_const::<E>(field_id::NATIONALITY);
        let expected_index = fixed_field * trace[columns.p1].clone()
            + exact_field.clone() * trace[columns.field_index].clone()
            + digit_field * trace[columns.p1].clone()
            + nat_first * (trace[columns.position_before].clone() * f_const::<E>(2))
            + nat_second * (trace[columns.position_before].clone() * f_const::<E>(2) + one.clone());
        eval.add_constraint(
            emit_field.clone() * (trace[columns.field_id].clone() - expected_field),
        );
        eval.add_constraint(
            emit_field.clone() * (trace[columns.field_index].clone() - expected_index),
        );
        eval.add_constraint(
            exact_field
                * (trace[columns.p1].clone()
                    - trace[columns.field_index].clone() * f_const::<E>(256)
                    - trace[columns.byte].clone()),
        );

        let digest_exit =
            action(ScopeAction::SelectedDigestExit) + action(ScopeAction::UnknownDigestExit);
        for bit in seen_before.iter().take(item_count) {
            eval.add_constraint(digest_exit.clone() * (bit.clone() - one.clone()));
        }

        for (slot, relation) in self.parsed_relations.iter().enumerate() {
            let mut tuple = Vec::with_capacity(parsed_cbor_tuple::ARITY);
            tuple.push(f_const::<E>(self.stream_ids[slot]));
            tuple.push(trace[columns.byte_index].clone());
            tuple.push(byte.clone());
            tuple.extend(trace[columns.parsed_meta.clone()].iter().cloned());
            eval.add_to_relation(RelationEntry::new(
                relation,
                E::EF::from(stream_selectors[slot].clone()),
                &tuple,
            ));
        }
        for (slot, relation) in self.raw_relations.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                relation,
                -E::EF::from(raw_selectors[slot].clone()),
                &[
                    f_const::<E>(self.raw_target_stream_ids[slot]),
                    trace[columns.position_before].clone(),
                    byte.clone(),
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::new(
            &self.semantic_relation,
            -E::EF::from(emit_field),
            &[
                trace[columns.field_id].clone(),
                trace[columns.field_index].clone(),
                byte.clone(),
            ],
        ));
        if let Some(payload_hash_relation) = &self.payload_hash_relation {
            eval.add_to_relation(RelationEntry::new(
                payload_hash_relation,
                -E::EF::from(raw_selectors[0].clone()),
                &[
                    f_const::<E>(MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID),
                    trace[columns.position_before].clone(),
                    trace[columns.byte].clone(),
                ],
            ));
        }

        let item_id_provider = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::ItemDigestId0,
                ScopeAction::ItemDigestId1,
                ScopeAction::ItemDigestId2,
            ],
        );
        eval.add_to_relation(RelationEntry::new(
            &self.digest_id_relation,
            E::EF::from(selected_id - item_id_provider),
            &[trace[columns.p0].clone(), arg_lo.clone()],
        ));
        let emit_digest_byte = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::SelectedDigestByte,
                ScopeAction::SelectedDigestStay,
                ScopeAction::SelectedDigestExit,
            ],
        );
        eval.add_to_relation(RelationEntry::new(
            &self.digest_byte_relation,
            -E::EF::from(emit_digest_byte),
            &[trace[columns.p0].clone(), trace[columns.p1].clone(), byte],
        ));

        for (item, digest_relation) in self.item_digest_relations.iter().enumerate() {
            let values = trace[columns.digest_values.clone()].to_vec();
            for (byte_index, value) in values.iter().enumerate() {
                eval.add_to_relation(RelationEntry::new(
                    &self.digest_byte_relation,
                    E::EF::from(aggregate[item].clone()),
                    &[
                        f_const::<E>(item as u32),
                        f_const::<E>(byte_index as u32),
                        value.clone(),
                    ],
                ));
            }
            eval.add_to_relation(RelationEntry::new(
                digest_relation,
                E::EF::from(aggregate[item].clone()),
                &values,
            ));
        }

        eval.add_to_relation(RelationEntry::new(
            &self.dfa_relation,
            E::EF::from(active.clone()),
            &[
                stream_slot.clone(),
                trace[columns.state_before].clone(),
                trace[columns.state_after].clone(),
                action_code,
                trace[columns.p0].clone(),
                trace[columns.p1].clone(),
            ],
        ));
        let mut current_state_tuple = vec![
            stream_slot.clone(),
            trace[columns.byte_index].clone(),
            trace[columns.state_before].clone(),
            trace[columns.remaining_before].clone(),
            trace[columns.position_before].clone(),
            trace[columns.previous_id_before].clone(),
            trace[columns.have_previous_before].clone(),
            seen_before[0].clone(),
            seen_before[1].clone(),
            seen_before[2].clone(),
            seen_before[3].clone(),
        ];
        current_state_tuple.extend(map_remaining_before.iter().cloned());
        current_state_tuple.extend(map_accumulator_before.iter().cloned());
        current_state_tuple.extend(map_full_before.iter().cloned());
        let mut next_state_tuple = vec![
            stream_slot,
            trace[columns.byte_index].clone() + one.clone(),
            trace[columns.state_after].clone(),
            trace[columns.remaining_after].clone(),
            trace[columns.position_after].clone(),
            trace[columns.previous_id_after].clone(),
            trace[columns.have_previous_after].clone(),
            seen_after[0].clone(),
            seen_after[1].clone(),
            seen_after[2].clone(),
            seen_after[3].clone(),
        ];
        next_state_tuple.extend(map_remaining_after.iter().cloned());
        next_state_tuple.extend(map_accumulator_after.iter().cloned());
        next_state_tuple.extend(map_full_after.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.state_relation,
            E::EF::from(active.clone() - first),
            &current_state_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.state_relation,
            -E::EF::from(active - last),
            &next_state_tuple,
        ));

        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// DFA edge-table component: hosts the preprocessed edge tuples and the
/// committed per-edge multiplicity at the table's natural height, yielding
/// `-active * multiplicity` uses of every edge into the shared
/// [`MdocScopeDfaRelation`]. The walk component consumes from the same
/// relation instance, so the two cancel in the global LogUp balance.
struct MdocScopeDfaTableEval {
    log_size: u32,
    dfa_relation: MdocScopeDfaRelation,
    claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for MdocScopeDfaTableEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Only the LogUp cumulative-sum constraints, with a degree-2 numerator
        // (preprocessed `dfa_active` times the committed multiplicity).
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let table_active = eval.get_preprocessed_column(scope_col_id("dfa_active"));
        let table_tuple = [
            eval.get_preprocessed_column(scope_col_id("dfa_stream")),
            eval.get_preprocessed_column(scope_col_id("dfa_from")),
            eval.get_preprocessed_column(scope_col_id("dfa_to")),
            eval.get_preprocessed_column(scope_col_id("dfa_action")),
            eval.get_preprocessed_column(scope_col_id("dfa_p0")),
            eval.get_preprocessed_column(scope_col_id("dfa_p1")),
        ];
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.dfa_relation,
            -E::EF::from(table_active * multiplicity),
            &table_tuple,
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn packed_action_sum(
    base: &[MdocScopeColumnEval],
    columns: &ScopeTraceColumns,
    row: usize,
    actions: &[ScopeAction],
) -> PackedM31 {
    actions
        .iter()
        .fold(PackedM31::broadcast(m31(0)), |sum, action| {
            sum + base[columns.action_flags.start + action.index()].data[row]
        })
}

#[allow(clippy::too_many_arguments)]
fn scope_interaction_trace(
    log_size: u32,
    columns: &ScopeTraceColumns,
    base: &[MdocScopeColumnEval],
    walk_preprocessed: &[MdocScopeColumnEval],
    stream_ids: &[u32],
    raw_target_stream_ids: &[u32],
    parsed_relations: &[ParsedCborByteRelation],
    raw_relations: &[FieldBytesRelation],
    semantic_relation: &FieldBytesRelation,
    payload_hash_relation: Option<&FieldBytesRelation>,
    item_digest_relations: &[DigestBytesRelation],
    dfa_relation: &MdocScopeDfaRelation,
    state_relation: &MdocScopeStateRelation,
    digest_id_relation: &MdocScopeDigestIdRelation,
    digest_byte_relation: &MdocScopeDigestByteRelation,
    claim_mask_trace: Option<&ClaimMaskTrace>,
    claim_mask_beta: Option<QM31>,
) -> (Vec<MdocScopeColumnEval>, QM31) {
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::new();
    let broadcast = |value: u32| PackedM31::broadcast(m31(value));

    for (slot, relation) in parsed_relations.iter().enumerate() {
        sites.push(
            (0..n_vec_rows)
                .map(|row| {
                    let numerator =
                        PackedQM31::from(base[columns.stream_selectors.start + slot].data[row]);
                    let mut tuple = Vec::with_capacity(parsed_cbor_tuple::ARITY);
                    tuple.push(broadcast(stream_ids[slot]));
                    tuple.push(base[columns.byte_index].data[row]);
                    tuple.push(base[columns.byte].data[row]);
                    tuple.extend(
                        base[columns.parsed_meta.clone()]
                            .iter()
                            .map(|column| column.data[row]),
                    );
                    (numerator, relation.combine(&tuple))
                })
                .collect(),
        );
    }
    for (slot, relation) in raw_relations.iter().enumerate() {
        sites.push(
            (0..n_vec_rows)
                .map(|row| {
                    let numerator =
                        -PackedQM31::from(base[columns.raw_selectors.start + slot].data[row]);
                    let denominator = relation.combine(&[
                        broadcast(raw_target_stream_ids[slot]),
                        base[columns.position_before].data[row],
                        base[columns.byte].data[row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let emit = packed_action_sum(
                    base,
                    columns,
                    row,
                    &[
                        ScopeAction::FieldByte,
                        ScopeAction::FieldExact,
                        ScopeAction::FieldDigit,
                        ScopeAction::NatAlphaFirst,
                        ScopeAction::NatAlphaStay,
                        ScopeAction::NatAlphaExit,
                        ScopeAction::NatNumericFirst,
                        ScopeAction::NatNumericStay,
                        ScopeAction::NatNumericExit,
                    ],
                );
                let denominator = semantic_relation.combine(&[
                    base[columns.field_id].data[row],
                    base[columns.field_index].data[row],
                    base[columns.byte].data[row],
                ]);
                (-PackedQM31::from(emit), denominator)
            })
            .collect(),
    );
    if let Some(payload_hash_relation) = payload_hash_relation {
        sites.push(
            (0..n_vec_rows)
                .map(|row| {
                    let numerator = -PackedQM31::from(base[columns.raw_selectors.start].data[row]);
                    let denominator = payload_hash_relation.combine(&[
                        broadcast(MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID),
                        base[columns.position_before].data[row],
                        base[columns.byte].data[row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }

    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let selected = packed_action_sum(
                    base,
                    columns,
                    row,
                    &[
                        ScopeAction::SelectedDigestId0,
                        ScopeAction::SelectedDigestId1,
                        ScopeAction::SelectedDigestId2,
                    ],
                );
                let provider = packed_action_sum(
                    base,
                    columns,
                    row,
                    &[
                        ScopeAction::ItemDigestId0,
                        ScopeAction::ItemDigestId1,
                        ScopeAction::ItemDigestId2,
                    ],
                );
                let denominator = digest_id_relation.combine(&[
                    base[columns.p0].data[row],
                    base[columns.parsed_meta.start + parsed_cbor_tuple::ARG_LO16 - 3].data[row],
                ]);
                (PackedQM31::from(selected - provider), denominator)
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let emit = packed_action_sum(
                    base,
                    columns,
                    row,
                    &[
                        ScopeAction::SelectedDigestByte,
                        ScopeAction::SelectedDigestStay,
                        ScopeAction::SelectedDigestExit,
                    ],
                );
                let denominator = digest_byte_relation.combine(&[
                    base[columns.p0].data[row],
                    base[columns.p1].data[row],
                    base[columns.byte].data[row],
                ]);
                (-PackedQM31::from(emit), denominator)
            })
            .collect(),
    );

    for (item, digest_relation) in item_digest_relations.iter().enumerate() {
        let aggregate = &walk_preprocessed[item];
        for byte in 0..SCOPE_DIGEST_BYTES {
            sites.push(
                (0..n_vec_rows)
                    .map(|row| {
                        let numerator = PackedQM31::from(aggregate.data[row]);
                        let denominator = digest_byte_relation.combine(&[
                            broadcast(item as u32),
                            broadcast(byte as u32),
                            base[columns.digest_values.start + byte].data[row],
                        ]);
                        (numerator, denominator)
                    })
                    .collect(),
            );
        }
        sites.push(
            (0..n_vec_rows)
                .map(|row| {
                    let numerator = PackedQM31::from(aggregate.data[row]);
                    let values: Vec<_> = base[columns.digest_values.clone()]
                        .iter()
                        .map(|column| column.data[row])
                        .collect();
                    (numerator, digest_relation.combine(&values))
                })
                .collect(),
        );
    }

    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let stream_slot =
                    (0..stream_ids.len()).fold(PackedM31::broadcast(m31(0)), |sum, slot| {
                        sum + base[columns.stream_selectors.start + slot].data[row]
                            * broadcast(slot as u32)
                    });
                let action_code =
                    (0..SCOPE_ACTION_COUNT).fold(PackedM31::broadcast(m31(0)), |sum, action| {
                        sum + base[columns.action_flags.start + action].data[row]
                            * broadcast(action as u32)
                    });
                let denominator = dfa_relation.combine(&[
                    stream_slot,
                    base[columns.state_before].data[row],
                    base[columns.state_after].data[row],
                    action_code,
                    base[columns.p0].data[row],
                    base[columns.p1].data[row],
                ]);
                (
                    PackedQM31::from(base[columns.active].data[row]),
                    denominator,
                )
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let stream_slot =
                    (0..stream_ids.len()).fold(PackedM31::broadcast(m31(0)), |sum, slot| {
                        sum + base[columns.stream_selectors.start + slot].data[row]
                            * broadcast(slot as u32)
                    });
                let mut tuple = vec![
                    stream_slot,
                    base[columns.byte_index].data[row],
                    base[columns.state_before].data[row],
                    base[columns.remaining_before].data[row],
                    base[columns.position_before].data[row],
                    base[columns.previous_id_before].data[row],
                    base[columns.have_previous_before].data[row],
                    base[columns.seen_before.start].data[row],
                    base[columns.seen_before.start + 1].data[row],
                    base[columns.seen_before.start + 2].data[row],
                    base[columns.seen_before.start + 3].data[row],
                ];
                tuple.extend(
                    base[columns.map_remaining_before.clone()]
                        .iter()
                        .map(|column| column.data[row]),
                );
                tuple.extend(
                    base[columns.map_accumulator_before.clone()]
                        .iter()
                        .map(|column| column.data[row]),
                );
                tuple.extend(
                    base[columns.map_full_before.clone()]
                        .iter()
                        .map(|column| column.data[row]),
                );
                let denominator = state_relation.combine(&tuple);
                let numerator = PackedQM31::from(
                    base[columns.active].data[row] - base[columns.first].data[row],
                );
                (numerator, denominator)
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let stream_slot =
                    (0..stream_ids.len()).fold(PackedM31::broadcast(m31(0)), |sum, slot| {
                        sum + base[columns.stream_selectors.start + slot].data[row]
                            * broadcast(slot as u32)
                    });
                let mut tuple = vec![
                    stream_slot,
                    base[columns.byte_index].data[row] + PackedM31::broadcast(m31(1)),
                    base[columns.state_after].data[row],
                    base[columns.remaining_after].data[row],
                    base[columns.position_after].data[row],
                    base[columns.previous_id_after].data[row],
                    base[columns.have_previous_after].data[row],
                    base[columns.seen_after.start].data[row],
                    base[columns.seen_after.start + 1].data[row],
                    base[columns.seen_after.start + 2].data[row],
                    base[columns.seen_after.start + 3].data[row],
                ];
                tuple.extend(
                    base[columns.map_remaining_after.clone()]
                        .iter()
                        .map(|column| column.data[row]),
                );
                tuple.extend(
                    base[columns.map_accumulator_after.clone()]
                        .iter()
                        .map(|column| column.data[row]),
                );
                tuple.extend(
                    base[columns.map_full_after.clone()]
                        .iter()
                        .map(|column| column.data[row]),
                );
                let denominator = state_relation.combine(&tuple);
                let numerator = -PackedQM31::from(
                    base[columns.active].data[row] - base[columns.last].data[row],
                );
                (numerator, denominator)
            })
            .collect(),
    );

    match (claim_mask_trace, claim_mask_beta) {
        (Some(mask), Some(beta)) => {
            assert_eq!(mask.log_size(), log_size);
            sites.push(
                (0..n_vec_rows)
                    .map(|row| mask.packed_fraction_at(row, beta))
                    .collect(),
            );
        }
        (None, None) => {}
        _ => panic!("mdoc scope claim-mask trace and challenge must be configured together"),
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    let mut site = 0usize;
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

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct MdocScopeProofMetadata {
    pub(crate) log_size: u32,
    /// `None` when no Alpha2Set item is requested; otherwise the exact signed
    /// scalar/array entry count.  The downstream nationality component consumes
    /// exactly `2*count` indexed field tuples, so tampering this value leaves
    /// the shared semantic-field relation unbalanced.
    pub(crate) nationality_count: Option<u16>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocScopeInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) table_claimed_sum: QM31,
}

pub(crate) struct MdocScope {
    statement: MdocScopeStatement,
    metadata: MdocScopeProofMetadata,
    /// Derived from the statement's DFA programs on both sides; never
    /// prover-supplied.
    table_log_size: u32,
    programs: Vec<DfaProgram>,
    table_edges: Vec<(usize, DfaEdge)>,
    handles: MdocScopeHandles,
    payload_hash_binding: bool,
    witness: Option<MdocScopeWitness>,
    trace_cache: Option<Vec<MdocScopeColumnEval>>,
    table_trace_cache: Option<MdocScopeColumnEval>,
    dfa_relation: Option<MdocScopeDfaRelation>,
    state_relation: Option<MdocScopeStateRelation>,
    digest_id_relation: Option<MdocScopeDigestIdRelation>,
    digest_byte_relation: Option<MdocScopeDigestByteRelation>,
    claim_mask_trace: Option<ClaimMaskTrace>,
    table_claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocScopeInteractionClaim>,
    component: Option<MdocScopeComponent>,
    table_component: Option<FrameworkComponent<MdocScopeDfaTableEval>>,
}

impl MdocScope {
    pub(crate) fn new(
        statement: MdocScopeStatement,
        issuer_sig_structure: Vec<u8>,
        item_outer_streams: Vec<Vec<u8>>,
        handles: MdocScopeHandles,
    ) -> Result<Self, MdocScopeError> {
        statement.validate()?;
        validate_handle_counts(&statement, &handles)?;
        if item_outer_streams.len() != statement.items.len() {
            return Err(MdocScopeError::HandleCount {
                kind: "item witness",
                expected: statement.items.len(),
                actual: item_outer_streams.len(),
            });
        }
        let programs = programs(&statement);
        let table_edges = programs
            .iter()
            .enumerate()
            .flat_map(|(slot, program)| program.edges.iter().copied().map(move |edge| (slot, edge)))
            .collect::<Vec<_>>();
        let witness = MdocScopeWitness::new(
            &statement,
            &issuer_sig_structure,
            &item_outer_streams,
            &programs,
            &table_edges,
        )?;
        // The walk runs at its natural (byte-count driven) height; the DFA
        // edge table lives in its own component at its own height.
        let log_size = scope_log_size(witness.active_rows.len())?;
        let table_log_size = scope_log_size(table_edges.len())?;
        let metadata = MdocScopeProofMetadata {
            log_size,
            nationality_count: witness.nationality_count,
        };
        validate_nationality_metadata(&statement, &metadata)?;
        Ok(Self {
            statement,
            metadata,
            table_log_size,
            programs,
            table_edges,
            handles,
            payload_hash_binding: false,
            witness: Some(witness),
            trace_cache: None,
            table_trace_cache: None,
            dfa_relation: None,
            state_relation: None,
            digest_id_relation: None,
            digest_byte_relation: None,
            claim_mask_trace: None,
            table_claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
            table_component: None,
        })
    }

    pub(crate) fn verifier(
        statement: MdocScopeStatement,
        metadata: MdocScopeProofMetadata,
        handles: MdocScopeHandles,
        interaction_claim: MdocScopeInteractionClaim,
    ) -> Result<Self, MdocScopeError> {
        statement.validate()?;
        validate_handle_counts(&statement, &handles)?;
        validate_nationality_metadata(&statement, &metadata)?;
        if !(MDOC_SCOPE_MIN_LOG_SIZE..=MDOC_SCOPE_MAX_LOG_SIZE).contains(&metadata.log_size) {
            return Err(MdocScopeError::TraceTooLarge(
                1usize << metadata.log_size.min(20),
            ));
        }
        let programs = programs(&statement);
        let table_edges = programs
            .iter()
            .enumerate()
            .flat_map(|(slot, program)| program.edges.iter().copied().map(move |edge| (slot, edge)))
            .collect::<Vec<_>>();
        // Verifier-derived: sized from the statement's DFA programs alone.
        let table_log_size = scope_log_size(table_edges.len())?;
        Ok(Self {
            statement,
            metadata,
            table_log_size,
            programs,
            table_edges,
            handles,
            payload_hash_binding: false,
            witness: None,
            trace_cache: None,
            table_trace_cache: None,
            dfa_relation: None,
            state_relation: None,
            digest_id_relation: None,
            digest_byte_relation: None,
            claim_mask_trace: None,
            table_claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            table_component: None,
        })
    }

    pub(crate) fn metadata(&self) -> &MdocScopeProofMetadata {
        &self.metadata
    }

    pub(crate) fn interaction_claim(&self) -> &MdocScopeInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc scope interaction claim is set")
    }

    /// Exact parser witnesses in the same order returned by
    /// [`MdocScopeHandles::stream_specs`]:
    ///
    /// issuer `Sig_structure`, issuer payload wrapper, normalized MSO, then
    /// each item's outer tag-24 wrapper and inner `IssuerSignedItem` map.
    ///
    /// This is prover-only witness data.  Verifiers intentionally cannot
    /// recover private credential bytes from proof metadata.
    pub(crate) fn parser_stream_bytes(&self) -> &[Vec<u8>] {
        &self
            .witness
            .as_ref()
            .expect("scope prover has witness")
            .raw_stream_bytes
    }

    fn columns(&self) -> ScopeTraceColumns {
        ScopeTraceColumns::new(
            self.handles.parsed_streams.len(),
            self.handles.raw_streams.len(),
        )
    }

    fn raw_target_stream_ids(&self) -> Vec<u32> {
        stream_specs(self.statement.items.len())
            .into_iter()
            .filter_map(|spec| spec.raw_output_target)
            .collect()
    }

    fn parsed_relations(&self) -> Vec<ParsedCborByteRelation> {
        self.handles
            .parsed_streams
            .iter()
            .map(SharedParsedCborByteRelation::get)
            .collect()
    }

    fn raw_relations(&self) -> Vec<FieldBytesRelation> {
        self.handles
            .raw_streams
            .iter()
            .map(SharedFieldRelation::get)
            .collect()
    }

    fn item_digest_relations(&self) -> Vec<DigestBytesRelation> {
        self.handles
            .item_digests
            .iter()
            .map(SharedDigestRelation::get)
            .collect()
    }

    pub(crate) fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![self.metadata.log_size, self.table_log_size]
    }

    pub(crate) fn with_claim_masks(
        mut self,
        traces: Vec<ClaimMaskTrace>,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        let [walk, table]: [ClaimMaskTrace; 2] = traces
            .try_into()
            .unwrap_or_else(|_| panic!("mdoc scope expects exactly two claim masks"));
        assert_eq!(walk.log_size(), self.metadata.log_size);
        assert_eq!(table.log_size(), self.table_log_size);
        self.claim_mask_trace = Some(walk);
        self.table_claim_mask_trace = Some(table);
        self.claim_mask_challenge = Some(challenge);
        self
    }

    pub(crate) fn with_claim_mask_verifier(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    pub(crate) fn with_payload_hash_binding(mut self) -> Self {
        self.payload_hash_binding = true;
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn first"))
    }

    /// Walk-component LogUp sites; the DFA table's yield lives in its own
    /// component (see [`Self::n_table_interaction_sites`]).
    fn n_interaction_sites(&self) -> usize {
        self.handles.parsed_streams.len()
            + self.handles.raw_streams.len()
            + 3 // semantic, digest-id, digest-byte
            + usize::from(self.payload_hash_binding)
            + self.statement.items.len() * (SCOPE_DIGEST_BYTES + 1)
            + 3 // DFA consume and state consume/provider
            + usize::from(self.claim_mask_challenge.is_some())
    }

    fn n_table_interaction_sites(&self) -> usize {
        1 + usize::from(self.claim_mask_challenge.is_some())
    }
}

fn validate_nationality_metadata(
    statement: &MdocScopeStatement,
    metadata: &MdocScopeProofMetadata,
) -> Result<(), MdocScopeError> {
    let has_nationality = statement
        .items
        .iter()
        .any(|item| matches!(item.mode, MdocScopeMode::Alpha2Set(_)));
    match (has_nationality, metadata.nationality_count) {
        (true, Some(count)) if count != 0 && usize::from(count) <= MAX_PRESENTED_NATIONALITIES => {
            Ok(())
        }
        (false, None) => Ok(()),
        _ => Err(MdocScopeError::WrongShape("nationality proof metadata")),
    }
}

impl Air for MdocScope {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x4d44_4f43_5343_4f50);
        channel.mix_u64(self.statement.profile.transcript_tag());
        channel.mix_u64(u64::from(self.payload_hash_binding));
        channel.mix_u64(u64::from(self.metadata.log_size));
        channel.mix_u64(u64::from(self.table_log_size));
        channel.mix_u64(self.metadata.nationality_count.map_or(u64::MAX, u64::from));
        for chunk in self.statement.request_binding.chunks_exact(8) {
            channel.mix_u64(u64::from_be_bytes(
                chunk.try_into().expect("request-binding chunk is 8 bytes"),
            ));
        }
        channel.mix_u64(self.statement.doc_type.len() as u64);
        for &byte in &self.statement.doc_type {
            channel.mix_u64(u64::from(byte));
        }
        channel.mix_u64(self.statement.namespace.len() as u64);
        for &byte in &self.statement.namespace {
            channel.mix_u64(u64::from(byte));
        }
        channel.mix_u64(self.statement.items.len() as u64);
        for item in &self.statement.items {
            channel.mix_u64(item.element_identifier.len() as u64);
            for &byte in &item.element_identifier {
                channel.mix_u64(u64::from(byte));
            }
            match &item.mode {
                MdocScopeMode::ValueEquality(value) => {
                    channel.mix_u64(0);
                    channel.mix_u64(value.len() as u64);
                    for &byte in value {
                        channel.mix_u64(u64::from(byte));
                    }
                }
                MdocScopeMode::AgeOver(encoding) => {
                    channel.mix_u64(1);
                    channel.mix_u64(match encoding {
                        MdocScopeBirthDateEncoding::Packed => 0,
                        MdocScopeBirthDateEncoding::Text => 1,
                    });
                }
                MdocScopeMode::Alpha2Set(encoding) => {
                    channel.mix_u64(2);
                    channel.mix_u64(match encoding {
                        MdocScopeNationalityEncoding::Numeric => 0,
                        MdocScopeNationalityEncoding::Alpha2 => 1,
                    });
                }
            }
        }
        for spec in stream_specs(self.statement.items.len()) {
            channel.mix_u64(u64::from(spec.stream_id));
            channel.mix_u64(u64::from(spec.role_tag));
        }
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        for handle in &self.handles.raw_streams {
            assert!(!handle.is_set(), "mdoc scope raw relation already drawn");
            handle.set(FieldBytesRelation::draw(channel));
        }
        assert!(
            !self.handles.semantic_fields.is_set(),
            "mdoc scope semantic relation already drawn"
        );
        self.handles
            .semantic_fields
            .set(FieldBytesRelation::draw(channel));
        if self.payload_hash_binding {
            assert!(
                !self.handles.payload_hash_fields.is_set(),
                "mdoc scope payload-hash relation already drawn"
            );
            self.handles
                .payload_hash_fields
                .set(FieldBytesRelation::draw(channel));
        }
        self.dfa_relation = Some(MdocScopeDfaRelation::draw(channel));
        self.state_relation = Some(MdocScopeStateRelation::draw(channel));
        self.digest_id_relation = Some(MdocScopeDigestIdRelation::draw(channel));
        self.digest_byte_relation = Some(MdocScopeDigestByteRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        let columns = self.columns();
        let mask_columns =
            usize::from(self.claim_mask_challenge.is_some()) * CLAIM_MASK_TRACE_COLUMNS;
        let mut preprocessed = vec![self.table_log_size; SCOPE_PREPROCESSED_FIXED_COLS];
        preprocessed.extend(vec![self.metadata.log_size; self.statement.items.len()]);
        let mut trace = vec![self.metadata.log_size; columns.total + mask_columns];
        trace.extend(vec![self.table_log_size; 1 + mask_columns]);
        let mut interaction = vec![
            self.metadata.log_size;
            self.n_interaction_sites().div_ceil(2) * SECURE_EXTENSION_DEGREE
        ];
        interaction.extend(vec![
            self.table_log_size;
            self.n_table_interaction_sites().div_ceil(2)
                * SECURE_EXTENSION_DEGREE
        ]);
        TreeLayout {
            preprocessed,
            trace,
            interaction,
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.table_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        scope_preprocessed_ids(self.statement.items.len())
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(scope_preprocessed_columns(
            self.metadata.log_size,
            self.table_log_size,
            &self.table_edges,
            self.statement.items.len(),
        ))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.component = Some(MdocScopeComponent::new(
            allocator,
            MdocScopeEval {
                log_size: self.metadata.log_size,
                stream_ids: stream_specs(self.statement.items.len())
                    .into_iter()
                    .map(|spec| spec.stream_id)
                    .collect(),
                program_starts: self.programs.iter().map(|program| program.start).collect(),
                program_ends: self.programs.iter().map(|program| program.end).collect(),
                raw_target_stream_ids: self.raw_target_stream_ids(),
                parsed_relations: self.parsed_relations(),
                raw_relations: self.raw_relations(),
                semantic_relation: self.handles.semantic_fields.get(),
                payload_hash_relation: self
                    .payload_hash_binding
                    .then(|| self.handles.payload_hash_fields.get()),
                item_digest_relations: self.item_digest_relations(),
                dfa_relation: self
                    .dfa_relation
                    .clone()
                    .expect("mdoc scope DFA relation drawn"),
                state_relation: self
                    .state_relation
                    .clone()
                    .expect("mdoc scope state relation drawn"),
                digest_id_relation: self
                    .digest_id_relation
                    .clone()
                    .expect("mdoc scope digest-id relation drawn"),
                digest_byte_relation: self
                    .digest_byte_relation
                    .clone()
                    .expect("mdoc scope digest-byte relation drawn"),
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.claimed_sum,
        ));
        self.table_component = Some(FrameworkComponent::new(
            allocator,
            MdocScopeDfaTableEval {
                log_size: self.table_log_size,
                dfa_relation: self
                    .dfa_relation
                    .clone()
                    .expect("mdoc scope DFA relation drawn"),
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.table_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc scope component is built"),
            self.table_component
                .as_ref()
                .expect("mdoc scope DFA table component is built"),
        ]
    }
}

impl AirProver for MdocScope {
    fn max_log_size(&self) -> u32 {
        self.metadata.log_size.max(self.table_log_size)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        (self.metadata.log_size + 4).max(self.table_log_size + 1)
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &scope_preprocessed_ids(self.statement.items.len()));
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_scope::MdocScope",
            &scope_preprocessed_ids(self.statement.items.len()),
            &scope_preprocessed_columns(
                self.metadata.log_size,
                self.table_log_size,
                &self.table_edges,
                self.statement.items.len(),
            ),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = scope_preprocessed_ids(self.statement.items.len());
        let all_columns = scope_preprocessed_columns(
            self.metadata.log_size,
            self.table_log_size,
            &self.table_edges,
            self.statement.items.len(),
        );
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected mdoc scope preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let witness = self
            .witness
            .as_ref()
            .expect("mdoc scope prover has a witness");
        let trace = scope_base_trace(
            self.metadata.log_size,
            &self.columns(),
            witness,
            self.handles.parsed_streams.len(),
            self.handles.raw_streams.len(),
        );
        let table_trace = scope_table_trace(self.table_log_size, &witness.table_multiplicities);
        self.trace_cache = Some(trace.clone());
        tb.extend_evals(trace);
        if let Some(mask) = &self.claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
        self.table_trace_cache = Some(table_trace.clone());
        tb.extend_evals(vec![table_trace]);
        if let Some(mask) = &self.table_claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let columns = self.columns();
        let base = self
            .trace_cache
            .as_ref()
            .expect("mdoc scope trace cached before interaction");
        let walk_preprocessed =
            scope_walk_preprocessed_columns(self.metadata.log_size, self.statement.items.len());
        let parsed_relations = self.parsed_relations();
        let raw_relations = self.raw_relations();
        let item_digest_relations = self.item_digest_relations();
        let dfa_relation = self.dfa_relation.as_ref().expect("DFA relation drawn");
        let state_relation = self.state_relation.as_ref().expect("state relation drawn");
        let digest_id_relation = self
            .digest_id_relation
            .as_ref()
            .expect("digest-id relation drawn");
        let digest_byte_relation = self
            .digest_byte_relation
            .as_ref()
            .expect("digest-byte relation drawn");
        let payload_hash_relation = self
            .payload_hash_binding
            .then(|| self.handles.payload_hash_fields.get());
        let (interaction, claimed_sum) = scope_interaction_trace(
            self.metadata.log_size,
            &columns,
            base,
            &walk_preprocessed,
            &stream_specs(self.statement.items.len())
                .into_iter()
                .map(|spec| spec.stream_id)
                .collect::<Vec<_>>(),
            &self.raw_target_stream_ids(),
            &parsed_relations,
            &raw_relations,
            &self.handles.semantic_fields.get(),
            payload_hash_relation.as_ref(),
            &item_digest_relations,
            dfa_relation,
            state_relation,
            digest_id_relation,
            digest_byte_relation,
            self.claim_mask_trace.as_ref(),
            self.claim_mask_beta(),
        );
        tb.extend_evals(interaction);
        let table_multiplicity = self
            .table_trace_cache
            .as_ref()
            .expect("mdoc scope table trace cached before interaction");
        let table_preprocessed =
            scope_table_preprocessed_columns(self.table_log_size, &self.table_edges);
        let table_claim_mask = self
            .table_claim_mask_trace
            .as_ref()
            .zip(self.claim_mask_beta());
        let (table_interaction, table_claimed_sum) = scope_table_interaction_trace(
            self.table_log_size,
            table_multiplicity,
            &table_preprocessed,
            dfa_relation,
            table_claim_mask,
        );
        tb.extend_evals(table_interaction);
        self.interaction_claim = Some(MdocScopeInteractionClaim {
            claimed_sum,
            table_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc scope component is built"),
            self.table_component
                .as_ref()
                .expect("mdoc scope DFA table component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use air_core::claim_mask::ClaimMaskRing;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::assert_constraints_on_trace;

    const VALID_SIGNED: &str = "2026-01-01T00:00:00Z";
    const VALID_FROM: &str = "2026-01-02T03:04:05Z";
    const VALID_UNTIL: &str = "2030-12-31T23:59:59Z";

    fn encoded_bstr(bytes: &[u8]) -> Vec<u8> {
        let mut encoded = cbor_head(2, bytes.len() as u64);
        encoded.extend_from_slice(bytes);
        encoded
    }

    fn encoded_array(values: &[Vec<u8>]) -> Vec<u8> {
        let mut encoded = cbor_head(4, values.len() as u64);
        for value in values {
            encoded.extend_from_slice(value);
        }
        encoded
    }

    fn encoded_map(entries: &[(Vec<u8>, Vec<u8>)]) -> Vec<u8> {
        let mut encoded = cbor_head(5, entries.len() as u64);
        for (key, value) in entries {
            encoded.extend_from_slice(key);
            encoded.extend_from_slice(value);
        }
        encoded
    }

    fn encoded_tag(tag: u64, value: &[u8]) -> Vec<u8> {
        let mut encoded = cbor_head(6, tag);
        encoded.extend_from_slice(value);
        encoded
    }

    fn encoded_tdate(value: &str) -> Vec<u8> {
        encoded_tag(0, &cbor_text(value.as_bytes()))
    }

    fn device_key_info() -> Vec<u8> {
        let device_key = encoded_map(&[
            (cbor_head(0, 1), cbor_head(0, 2)),
            (cbor_head(1, 0), cbor_head(0, 1)),
            (cbor_head(1, 1), encoded_bstr(&[0x11; 32])),
            (cbor_head(1, 2), encoded_bstr(&[0x22; 32])),
        ]);
        encoded_map(&[(cbor_text(b"deviceKey"), device_key)])
    }

    fn validity_info(signed: &str, valid_from: &str, valid_until: &str) -> Vec<u8> {
        encoded_map(&[
            (cbor_text(b"signed"), encoded_tdate(signed)),
            (cbor_text(b"validFrom"), encoded_tdate(valid_from)),
            (cbor_text(b"validUntil"), encoded_tdate(valid_until)),
        ])
    }

    fn validity_info_with_expected_update(
        signed: &str,
        valid_from: &str,
        valid_until: &str,
        expected_update: Vec<u8>,
    ) -> Vec<u8> {
        encoded_map(&[
            (cbor_text(b"signed"), encoded_tdate(signed)),
            (cbor_text(b"validFrom"), encoded_tdate(valid_from)),
            (cbor_text(b"validUntil"), encoded_tdate(valid_until)),
            (cbor_text(b"expectedUpdate"), expected_update),
        ])
    }

    fn value_digests(namespace: &[u8], digest_ids: &[u64]) -> Vec<u8> {
        let digests = digest_ids
            .iter()
            .map(|id| {
                (
                    cbor_head(0, *id),
                    encoded_bstr(&[u8::try_from(id & 0xff).unwrap(); 32]),
                )
            })
            .collect::<Vec<_>>();
        encoded_map(&[(cbor_text(namespace), encoded_map(&digests))])
    }

    fn mso_entries(
        statement: &MdocScopeStatement,
        digest_ids: &[u64],
        signed: &str,
        valid_from: &str,
        valid_until: &str,
    ) -> Vec<(Vec<u8>, Vec<u8>)> {
        vec![
            (
                cbor_text(b"version"),
                cbor_text(statement.profile.version_bytes()),
            ),
            (cbor_text(b"docType"), cbor_text(&statement.doc_type)),
            (cbor_text(b"digestAlgorithm"), cbor_text(b"SHA-256")),
            (
                cbor_text(b"valueDigests"),
                value_digests(&statement.namespace, digest_ids),
            ),
            (cbor_text(b"deviceKeyInfo"), device_key_info()),
            (
                cbor_text(b"validityInfo"),
                validity_info(signed, valid_from, valid_until),
            ),
        ]
    }

    fn item_entries(
        random_len: usize,
        digest_id: u64,
        element_identifier: &[u8],
        element_value: Vec<u8>,
    ) -> Vec<(Vec<u8>, Vec<u8>)> {
        vec![
            (cbor_text(b"random"), encoded_bstr(&vec![0x5a; random_len])),
            (cbor_text(b"digestID"), cbor_head(0, digest_id)),
            (cbor_text(b"elementValue"), element_value),
            (
                cbor_text(b"elementIdentifier"),
                cbor_text(element_identifier),
            ),
        ]
    }

    fn item_outer(inner: &[u8]) -> Vec<u8> {
        encoded_tag(24, &encoded_bstr(inner))
    }

    fn sig_structure(
        context: &[u8],
        protected: &[u8],
        external_aad: &[u8],
        payload: &[u8],
    ) -> Vec<u8> {
        encoded_array(&[
            cbor_text(context),
            encoded_bstr(protected),
            encoded_bstr(external_aad),
            encoded_bstr(payload),
        ])
    }

    fn v2_statement(nationality: bool) -> MdocScopeStatement {
        let mut items = vec![MdocScopeItem {
            element_identifier: b"birth_date".to_vec(),
            mode: MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Text),
        }];
        if nationality {
            items.push(MdocScopeItem {
                element_identifier: b"nationality".to_vec(),
                mode: MdocScopeMode::Alpha2Set(MdocScopeNationalityEncoding::Alpha2),
            });
        }
        MdocScopeStatement {
            request_binding: [0x42; 32],
            profile: MdocScopeProfile::V2,
            doc_type: b"org.iso.18013.5.1.mDL".to_vec(),
            namespace: b"org.iso.18013.5.1".to_vec(),
            items,
        }
    }

    fn v1_statement() -> MdocScopeStatement {
        MdocScopeStatement {
            request_binding: [0x24; 32],
            profile: MdocScopeProfile::V1,
            doc_type: b"org.iso.18013.5.1.mDL".to_vec(),
            namespace: b"org.iso.18013.5.1".to_vec(),
            items: vec![
                MdocScopeItem {
                    element_identifier: b"birth_date".to_vec(),
                    mode: MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Packed),
                },
                MdocScopeItem {
                    element_identifier: b"nationality".to_vec(),
                    mode: MdocScopeMode::Alpha2Set(MdocScopeNationalityEncoding::Numeric),
                },
            ],
        }
    }

    fn v2_item_inners(nationalities: &[&[u8; 2]]) -> Vec<Vec<u8>> {
        let birth_date = encoded_map(&item_entries(
            16,
            7,
            b"birth_date",
            cbor_text(b"1990-01-02"),
        ));
        let nationality_value = if nationalities.len() == 1 {
            cbor_text(nationalities[0])
        } else {
            encoded_array(
                &nationalities
                    .iter()
                    .map(|code| cbor_text(code.as_slice()))
                    .collect::<Vec<_>>(),
            )
        };
        let nationality = encoded_map(&item_entries(16, 9, b"nationality", nationality_value));
        vec![birth_date, nationality]
    }

    fn construct(
        statement: MdocScopeStatement,
        mso: Vec<u8>,
        item_inners: Vec<Vec<u8>>,
        wrapped_mso: bool,
    ) -> Result<MdocScope, MdocScopeError> {
        let payload = if wrapped_mso {
            encoded_tag(24, &encoded_bstr(&mso))
        } else {
            mso
        };
        let issuer = sig_structure(b"Signature1", &[0xa1, 0x01, 0x26], &[], &payload);
        let items = item_inners.iter().map(|inner| item_outer(inner)).collect();
        let handles = MdocScopeHandles::fresh(&statement)?;
        MdocScope::new(statement, issuer, items, handles)
    }

    fn construct_v2(
        nationalities: &[&[u8; 2]],
        wrapped_mso: bool,
    ) -> Result<MdocScope, MdocScopeError> {
        let statement = v2_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        construct(statement, mso, v2_item_inners(nationalities), wrapped_mso)
    }

    fn nationality_emissions(scope: &MdocScope) -> Vec<(u32, u8)> {
        scope
            .witness
            .as_ref()
            .expect("prover witness")
            .active_rows
            .iter()
            .filter_map(|row| {
                let index = match row.applied.edge.action {
                    ScopeAction::FieldByte if row.applied.edge.p0 == field_id::NATIONALITY => {
                        row.applied.edge.p1
                    }
                    ScopeAction::NatAlphaFirst | ScopeAction::NatNumericFirst => {
                        row.applied.before.position * 2
                    }
                    ScopeAction::NatAlphaStay
                    | ScopeAction::NatAlphaExit
                    | ScopeAction::NatNumericStay
                    | ScopeAction::NatNumericExit => row.applied.before.position * 2 + 1,
                    _ => return None,
                };
                Some((
                    index,
                    u8::try_from(row.parsed[parsed_cbor_tuple::BYTE]).unwrap(),
                ))
            })
            .collect()
    }

    #[test]
    fn action_table_is_explicit_dense_and_complete() {
        assert_eq!(SCOPE_ACTION_COUNT, ALL_SCOPE_ACTIONS.len());
        for (index, action) in ALL_SCOPE_ACTIONS.into_iter().enumerate() {
            assert_eq!(action.index(), index);
        }
    }

    #[test]
    fn accepts_direct_and_tag24_wrapped_mso_and_exposes_parser_order() {
        let direct = construct_v2(&[b"FR", b"DE"], false).unwrap();
        let wrapped = construct_v2(&[b"FR", b"DE"], true).unwrap();

        assert_eq!(direct.metadata().nationality_count, Some(2));
        assert_eq!(wrapped.metadata().nationality_count, Some(2));
        assert_eq!(direct.parser_stream_bytes().len(), 7);
        assert_eq!(wrapped.parser_stream_bytes().len(), 7);
        assert_eq!(
            direct.parser_stream_bytes()[1],
            direct.parser_stream_bytes()[2]
        );
        assert_ne!(
            wrapped.parser_stream_bytes()[1],
            wrapped.parser_stream_bytes()[2]
        );
        assert!(matches!(
            decode_exact(&wrapped.parser_stream_bytes()[1], "payload").unwrap(),
            Value::Tag(24, _)
        ));
        assert!(matches!(
            decode_exact(&wrapped.parser_stream_bytes()[2], "MSO").unwrap(),
            Value::Map(_)
        ));
    }

    #[test]
    fn accepts_v1_packed_date_numeric_nationality_and_unordered_item_map() {
        let statement = v1_statement();
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let mut birth_entries = item_entries(
            16,
            7,
            b"birth_date",
            encoded_bstr(&[0x07, 0xe6, 0x01, 0x02]),
        );
        birth_entries.swap(0, 3);
        let mut nationality_entries =
            item_entries(16, 9, b"nationality", encoded_bstr(&[0x01, 0x14]));
        nationality_entries.rotate_left(1);

        let scope = construct(
            statement,
            mso,
            vec![
                encoded_map(&birth_entries),
                encoded_map(&nationality_entries),
            ],
            false,
        )
        .unwrap();

        assert_eq!(scope.metadata().nationality_count, Some(1));
        assert_eq!(nationality_emissions(&scope), vec![(0, 0x01), (1, 0x14)]);
    }

    #[test]
    fn accepts_reordered_top_validity_and_cose_maps() {
        let statement = v2_statement(true);
        let mut cose_entries = vec![
            (cbor_head(0, 1), cbor_head(0, 2)),
            (cbor_head(1, 0), cbor_head(0, 1)),
            (cbor_head(1, 1), encoded_bstr(&[0x11; 32])),
            (cbor_head(1, 2), encoded_bstr(&[0x22; 32])),
        ];
        cose_entries.reverse();
        let reordered_device_key_info =
            encoded_map(&[(cbor_text(b"deviceKey"), encoded_map(&cose_entries))]);

        let mut validity_entries = vec![
            (cbor_text(b"signed"), encoded_tdate(VALID_SIGNED)),
            (cbor_text(b"validFrom"), encoded_tdate(VALID_FROM)),
            (cbor_text(b"validUntil"), encoded_tdate(VALID_UNTIL)),
        ];
        validity_entries.reverse();

        let mut entries = mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        entries[4].1 = reordered_device_key_info;
        entries[5].1 = encoded_map(&validity_entries);
        entries.reverse();

        construct(
            statement,
            encoded_map(&entries),
            v2_item_inners(&[b"FR"]),
            false,
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong_cose_sig_structure_context_protected_or_external_aad() {
        let statement = v2_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let payload = mso;
        let inners = v2_item_inners(&[b"FR"]);
        for issuer in [
            sig_structure(b"Signature", &[0xa1, 0x01, 0x26], &[], &payload),
            sig_structure(b"Signature1", &[0xa1, 0x01, 0x27], &[], &payload),
            sig_structure(b"Signature1", &[0xa1, 0x01, 0x26], &[0], &payload),
        ] {
            let handles = MdocScopeHandles::fresh(&statement).unwrap();
            let error = MdocScope::new(
                statement.clone(),
                issuer,
                inners.iter().map(|inner| item_outer(inner)).collect(),
                handles,
            )
            .err()
            .expect("wrong Sig_structure must fail");
            assert!(matches!(error, MdocScopeError::NoDfaPath { .. }));
        }
    }

    #[test]
    fn rejects_duplicate_wrong_or_missing_mso_fields() {
        let statement = v2_statement(true);
        let inners = v2_item_inners(&[b"FR"]);

        let mut duplicate = mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        duplicate[1] = duplicate[0].clone();

        let mut wrong_algorithm =
            mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        wrong_algorithm[2].1 = cbor_text(b"SHA-384");

        let mut wrong_doc_type =
            mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        wrong_doc_type[1].1 = cbor_text(b"org.example.other");

        let mut wrong_namespace =
            mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        wrong_namespace[3].1 = value_digests(b"org.example.other", &[7, 9]);

        let mut missing = mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        missing.pop();

        let mut duplicate_validity =
            mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        duplicate_validity[5].1 = encoded_map(&[
            (cbor_text(b"signed"), encoded_tdate(VALID_SIGNED)),
            (cbor_text(b"validFrom"), encoded_tdate(VALID_FROM)),
            (cbor_text(b"validFrom"), encoded_tdate(VALID_UNTIL)),
        ]);

        let mut duplicate_cose =
            mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        let malformed_key = encoded_map(&[
            (cbor_head(0, 1), cbor_head(0, 2)),
            (cbor_head(1, 0), cbor_head(0, 1)),
            (cbor_head(1, 1), encoded_bstr(&[0x11; 32])),
            (cbor_head(1, 1), encoded_bstr(&[0x22; 32])),
        ]);
        duplicate_cose[4].1 = encoded_map(&[(cbor_text(b"deviceKey"), malformed_key)]);

        for entries in [
            duplicate,
            wrong_algorithm,
            wrong_doc_type,
            wrong_namespace,
            missing,
            duplicate_validity,
            duplicate_cose,
        ] {
            assert!(construct(
                statement.clone(),
                encoded_map(&entries),
                inners.clone(),
                false,
            )
            .is_err());
        }
    }

    #[test]
    fn rejects_duplicate_unsorted_missing_or_oversized_digest_ids() {
        let statement = v2_statement(true);
        let inners = v2_item_inners(&[b"FR"]);
        for ids in [
            vec![7, 7],
            vec![9, 7],
            vec![7],
            vec![7, u64::from(u16::MAX) + 1],
        ] {
            let mso = encoded_map(&mso_entries(
                &statement,
                &ids,
                VALID_SIGNED,
                VALID_FROM,
                VALID_UNTIL,
            ));
            assert!(construct(statement.clone(), mso, inners.clone(), false).is_err());
        }
    }

    #[test]
    fn permits_sorted_unrequested_digest_entries_but_still_selects_every_item() {
        let statement = v2_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[5, 7, 8, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let scope = construct(statement, mso, v2_item_inners(&[b"FR"]), false).unwrap();
        assert_eq!(scope.metadata().nationality_count, Some(1));
    }

    #[test]
    fn private_digest_ids_select_the_right_mso_entry_independent_of_item_order() {
        let statement = v2_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let birth_date = encoded_map(&item_entries(
            16,
            9,
            b"birth_date",
            cbor_text(b"1990-01-02"),
        ));
        let nationality = encoded_map(&item_entries(16, 7, b"nationality", cbor_text(b"FR")));

        let scope = construct(statement, mso, vec![birth_date, nationality], false).unwrap();
        let witness = scope.witness.as_ref().unwrap();
        assert_eq!(witness.item_digest_bytes[0], [9; 32]);
        assert_eq!(witness.item_digest_bytes[1], [7; 32]);
    }

    #[test]
    fn rejects_short_random_duplicate_item_key_v2_reordering_and_trailing_inner_cbor() {
        let statement = v2_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let valid = v2_item_inners(&[b"FR"]);

        let short_random = encoded_map(&item_entries(
            15,
            7,
            b"birth_date",
            cbor_text(b"1990-01-02"),
        ));

        let mut duplicate_entries = item_entries(16, 7, b"birth_date", cbor_text(b"1990-01-02"));
        duplicate_entries[3].0 = duplicate_entries[0].0.clone();
        let duplicate_key = encoded_map(&duplicate_entries);

        let mut reordered_entries = item_entries(16, 7, b"birth_date", cbor_text(b"1990-01-02"));
        reordered_entries.swap(2, 3);
        let reordered = encoded_map(&reordered_entries);

        let mut trailing = valid[0].clone();
        trailing.push(0xf6);

        for malformed in [short_random, duplicate_key, reordered, trailing] {
            assert!(construct(
                statement.clone(),
                mso.clone(),
                vec![malformed, valid[1].clone()],
                false,
            )
            .is_err());
        }
    }

    #[test]
    fn rejects_nonminimal_and_trailing_cbor() {
        let statement = v2_statement(true);
        let inners = v2_item_inners(&[b"FR"]);
        let mut nonminimal = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        assert_eq!(nonminimal.remove(0), 0xa6);
        nonminimal.splice(0..0, [0xb8, 0x06]);
        assert!(matches!(
            construct(statement.clone(), nonminimal, inners.clone(), false),
            Err(MdocScopeError::Cbor(
                MdocCborStreamError::NonMinimalArgument { .. }
            ))
        ));

        let mut trailing = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        trailing.push(0xf6);
        assert!(construct(statement, trailing, inners, false).is_err());
    }

    #[test]
    fn rejects_malformed_or_out_of_range_tdates() {
        let statement = v2_statement(true);
        let inners = v2_item_inners(&[b"FR"]);
        let malformed = [
            "2026-13-01T00:00:00Z",
            "2026-01-32T00:00:00Z",
            "2026-02-29T00:00:00Z",
            "2026-02-30T00:00:00Z",
            "2026-04-31T00:00:00Z",
            "1900-02-29T00:00:00Z",
            "2026-01-01T24:00:00Z",
            "2026-01-01T00:60:00Z",
            "2026-01-01T00:00:60Z",
            "2026-01-01 00:00:00Z",
            "2026-01-01T00:00:00+",
        ];
        for value in malformed {
            for position in 0..3 {
                let mut dates = [VALID_SIGNED, VALID_FROM, VALID_UNTIL];
                dates[position] = value;
                let mso = encoded_map(&mso_entries(
                    &statement,
                    &[7, 9],
                    dates[0],
                    dates[1],
                    dates[2],
                ));
                assert!(
                    construct(statement.clone(), mso, inners.clone(), false).is_err(),
                    "accepted malformed tdate {value} at validity slot {position}"
                );
            }
        }
    }

    #[test]
    fn accepts_exact_gregorian_leap_boundaries() {
        let statement = v2_statement(true);
        let inners = v2_item_inners(&[b"FR"]);
        for value in [
            "1900-02-28T00:00:00Z",
            "1996-02-29T00:00:00Z",
            "2000-02-29T00:00:00Z",
            "2400-02-29T00:00:00Z",
        ] {
            let mso = encoded_map(&mso_entries(
                &statement,
                &[7, 9],
                value,
                VALID_FROM,
                VALID_UNTIL,
            ));
            construct(statement.clone(), mso, inners.clone(), false)
                .unwrap_or_else(|error| panic!("rejected valid Gregorian date {value}: {error}"));
        }
    }

    #[test]
    fn expected_update_is_omitted_or_a_valid_tdate_never_null() {
        let statement = v2_statement(true);
        let inners = v2_item_inners(&[b"FR"]);

        let mut with_tdate =
            mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        with_tdate[5].1 = validity_info_with_expected_update(
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
            encoded_tdate("2027-02-28T12:00:00Z"),
        );
        construct(
            statement.clone(),
            encoded_map(&with_tdate),
            inners.clone(),
            false,
        )
        .unwrap();

        let mut with_null = mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        with_null[5].1 =
            validity_info_with_expected_update(VALID_SIGNED, VALID_FROM, VALID_UNTIL, vec![0xf6]);
        assert!(
            construct(statement, encoded_map(&with_null), inners, false).is_err(),
            "present expectedUpdate must be a tdate, not null"
        );
    }

    #[test]
    fn emits_every_scalar_or_array_nationality_entry_at_fixed_indices() {
        let scalar = construct_v2(&[b"FR"], false).unwrap();
        assert_eq!(scalar.metadata().nationality_count, Some(1));
        assert_eq!(nationality_emissions(&scalar), vec![(0, b'F'), (1, b'R')]);

        let array = construct_v2(&[b"FR", b"DE", b"US"], false).unwrap();
        assert_eq!(array.metadata().nationality_count, Some(3));
        assert_eq!(
            nationality_emissions(&array),
            vec![
                (0, b'F'),
                (1, b'R'),
                (2, b'D'),
                (3, b'E'),
                (4, b'U'),
                (5, b'S'),
            ]
        );
    }

    #[test]
    fn rejects_nationality_arrays_above_the_public_bound() {
        let statement = v2_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let mut inners = v2_item_inners(&[b"FR"]);
        let nationalities = (0..=MAX_PRESENTED_NATIONALITIES)
            .map(|_| cbor_text(b"FR"))
            .collect::<Vec<_>>();
        inners[1] = encoded_map(&item_entries(
            16,
            9,
            b"nationality",
            encoded_array(&nationalities),
        ));

        assert!(construct(statement, mso, inners, false).is_err());
    }

    #[test]
    fn rejects_profile_encoding_mismatches_before_witness_allocation() {
        let mut v1 = v1_statement();
        v1.items[0].mode = MdocScopeMode::AgeOver(MdocScopeBirthDateEncoding::Text);
        assert!(matches!(
            v1.validate(),
            Err(MdocScopeError::WrongShape("profile/birth_date encoding"))
        ));

        let mut v2 = v2_statement(true);
        v2.items[1].mode = MdocScopeMode::Alpha2Set(MdocScopeNationalityEncoding::Numeric);
        assert!(matches!(
            v2.validate(),
            Err(MdocScopeError::WrongShape("profile/nationality encoding"))
        ));
    }

    #[test]
    fn value_equality_requires_one_minimally_encoded_complete_cbor_value() {
        let base = MdocScopeStatement {
            request_binding: [0; 32],
            profile: MdocScopeProfile::V2,
            doc_type: b"doc".to_vec(),
            namespace: b"ns".to_vec(),
            items: vec![MdocScopeItem {
                element_identifier: b"given_name".to_vec(),
                mode: MdocScopeMode::ValueEquality(cbor_text(b"Alice")),
            }],
        };
        base.validate().unwrap();

        let mut trailing = base.clone();
        trailing.items[0].mode = MdocScopeMode::ValueEquality(vec![0x01, 0x02]);
        assert!(matches!(
            trailing.validate(),
            Err(MdocScopeError::Cbor(
                MdocCborStreamError::TrailingCbor { .. }
            ))
        ));

        let mut nonminimal = base;
        nonminimal.items[0].mode = MdocScopeMode::ValueEquality(vec![0x18, 0x01]);
        assert!(matches!(
            nonminimal.validate(),
            Err(MdocScopeError::Cbor(
                MdocCborStreamError::NonMinimalArgument { .. }
            ))
        ));
    }

    #[test]
    fn public_text_and_value_equality_text_must_be_utf8() {
        let mut statement = v2_statement(false);
        statement.doc_type = vec![0xff];
        assert!(matches!(
            statement.validate(),
            Err(MdocScopeError::WrongShape("public identifier UTF-8"))
        ));

        let mut statement = v2_statement(false);
        statement.items[0].element_identifier = vec![0xff];
        assert!(matches!(
            statement.validate(),
            Err(MdocScopeError::WrongShape("element identifier UTF-8"))
        ));

        let statement = MdocScopeStatement {
            request_binding: [0; 32],
            profile: MdocScopeProfile::V2,
            doc_type: b"doc".to_vec(),
            namespace: b"ns".to_vec(),
            items: vec![MdocScopeItem {
                element_identifier: b"name".to_vec(),
                mode: MdocScopeMode::ValueEquality(vec![0x61, 0xff]),
            }],
        };
        assert!(matches!(
            statement.validate(),
            Err(MdocScopeError::Decode("value equality"))
        ));
    }

    #[test]
    fn table_multiplicity_padding_is_freshly_blinded() {
        let scope = construct_v2(&[b"FR"], false).unwrap();
        let witness = scope.witness.as_ref().unwrap();
        let first = scope_table_trace(scope.table_log_size, &witness.table_multiplicities);
        let second = scope_table_trace(scope.table_log_size, &witness.table_multiplicities);

        let first_values = first
            .data
            .iter()
            .copied()
            .flat_map(PackedM31::to_array)
            .collect::<Vec<_>>();
        let second_values = second
            .data
            .iter()
            .copied()
            .flat_map(PackedM31::to_array)
            .collect::<Vec<_>>();
        // Fresh randomness in the padding region regenerates per call. (The
        // columns are bit-reverse ordered, so compare them wholesale; the
        // deterministic edge prefix is covered by the honest-table test.)
        assert_ne!(first_values, second_values);
    }

    #[test]
    fn payload_hash_interaction_site_is_opt_in() {
        let mut default_scope = construct_v2(&[b"FR", b"DE"], true).unwrap();
        let default_sites = default_scope.n_interaction_sites();
        let default_interaction_columns = default_scope.layout().interaction.len();
        default_scope.draw_relations(&mut Blake2sChannel::default());
        assert!(!default_scope.handles.payload_hash_fields.is_set());

        let mut bound_scope = construct_v2(&[b"FR", b"DE"], true)
            .unwrap()
            .with_payload_hash_binding();
        assert_eq!(bound_scope.n_interaction_sites(), default_sites + 1);
        let expected_columns = (default_sites + 1).div_ceil(2) * SECURE_EXTENSION_DEGREE
            + bound_scope.n_table_interaction_sites().div_ceil(2) * SECURE_EXTENSION_DEGREE;
        assert_eq!(bound_scope.layout().interaction.len(), expected_columns);
        // Pairing parity may absorb the extra site into an existing column.
        assert!(bound_scope.layout().interaction.len() >= default_interaction_columns);
        bound_scope.draw_relations(&mut Blake2sChannel::default());
        assert!(bound_scope.handles.payload_hash_fields.is_set());
    }

    #[test]
    fn honest_scope_trace_and_logup_satisfy_the_complete_component() {
        let scope = construct_v2(&[b"FR", b"DE"], true)
            .unwrap()
            .with_payload_hash_binding();
        let witness = scope.witness.as_ref().unwrap();
        let columns = scope.columns();
        let base = scope_base_trace(
            scope.metadata.log_size,
            &columns,
            witness,
            scope.handles.parsed_streams.len(),
            scope.handles.raw_streams.len(),
        );
        let preprocessed =
            scope_walk_preprocessed_columns(scope.metadata.log_size, scope.statement.items.len());
        let stream_ids = stream_specs(scope.statement.items.len())
            .into_iter()
            .map(|spec| spec.stream_id)
            .collect::<Vec<_>>();
        let parsed_relations = (0..scope.handles.parsed_streams.len())
            .map(|_| ParsedCborByteRelation::dummy())
            .collect::<Vec<_>>();
        let raw_relations = (0..scope.handles.raw_streams.len())
            .map(|_| FieldBytesRelation::dummy())
            .collect::<Vec<_>>();
        let item_digest_relations = (0..scope.statement.items.len())
            .map(|_| DigestBytesRelation::dummy())
            .collect::<Vec<_>>();
        let semantic_relation = FieldBytesRelation::dummy();
        let payload_hash_relation = FieldBytesRelation::dummy();
        let dfa_relation = MdocScopeDfaRelation::dummy();
        let state_relation = MdocScopeStateRelation::dummy();
        let digest_id_relation = MdocScopeDigestIdRelation::dummy();
        let digest_byte_relation = MdocScopeDigestByteRelation::dummy();
        let (interaction, claimed_sum) = scope_interaction_trace(
            scope.metadata.log_size,
            &columns,
            &base,
            &preprocessed,
            &stream_ids,
            &scope.raw_target_stream_ids(),
            &parsed_relations,
            &raw_relations,
            &semantic_relation,
            Some(&payload_hash_relation),
            &item_digest_relations,
            &dfa_relation,
            &state_relation,
            &digest_id_relation,
            &digest_byte_relation,
            None,
            None,
        );
        let mut ring =
            ClaimMaskRing::new(&[scope.metadata.log_size, scope.metadata.log_size]).unwrap();
        let mask = ring.take(scope.metadata.log_size).unwrap();
        let beta = QM31::from_m31_array([m31(3), m31(5), m31(7), m31(11)]);
        let (_, masked_claimed_sum) = scope_interaction_trace(
            scope.metadata.log_size,
            &columns,
            &base,
            &preprocessed,
            &stream_ids,
            &scope.raw_target_stream_ids(),
            &parsed_relations,
            &raw_relations,
            &semantic_relation,
            Some(&payload_hash_relation),
            &item_digest_relations,
            &dfa_relation,
            &state_relation,
            &digest_id_relation,
            &digest_byte_relation,
            Some(&mask),
            Some(beta),
        );
        assert_eq!(masked_claimed_sum - claimed_sum, beta * mask.target_sum());
        let trees = TreeVec::new(vec![
            preprocessed
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
            base.into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
            interaction
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
        ]);
        let trace = trees.as_cols_ref();
        let eval = MdocScopeEval {
            log_size: scope.metadata.log_size,
            stream_ids,
            program_starts: scope.programs.iter().map(|program| program.start).collect(),
            program_ends: scope.programs.iter().map(|program| program.end).collect(),
            raw_target_stream_ids: scope.raw_target_stream_ids(),
            parsed_relations,
            raw_relations,
            semantic_relation,
            payload_hash_relation: Some(payload_hash_relation),
            item_digest_relations,
            dfa_relation,
            state_relation,
            digest_id_relation,
            digest_byte_relation,
            claim_mask_beta: None,
        };
        assert_constraints_on_trace(
            &trace,
            scope.metadata.log_size,
            |row| {
                let _ = eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[test]
    fn honest_table_trace_satisfies_the_table_component() {
        let scope = construct_v2(&[b"FR", b"DE"], false).unwrap();
        let witness = scope.witness.as_ref().unwrap();
        let dfa_relation = MdocScopeDfaRelation::dummy();
        let multiplicity = scope_table_trace(scope.table_log_size, &witness.table_multiplicities);
        let table_preprocessed =
            scope_table_preprocessed_columns(scope.table_log_size, &scope.table_edges);
        let (interaction, table_claimed_sum) = scope_table_interaction_trace(
            scope.table_log_size,
            &multiplicity,
            &table_preprocessed,
            &dfa_relation,
            None,
        );
        let mut ring = ClaimMaskRing::new(&[scope.table_log_size, scope.table_log_size]).unwrap();
        let mask = ring.take(scope.table_log_size).unwrap();
        let beta = QM31::from_m31_array([m31(3), m31(5), m31(7), m31(11)]);
        let (_, masked_sum) = scope_table_interaction_trace(
            scope.table_log_size,
            &multiplicity,
            &table_preprocessed,
            &dfa_relation,
            Some((&mask, beta)),
        );
        assert_eq!(masked_sum - table_claimed_sum, beta * mask.target_sum());
        let trees = TreeVec::new(vec![
            table_preprocessed
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
            vec![multiplicity.to_cpu().values],
            interaction
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
        ]);
        let trace = trees.as_cols_ref();
        let eval = MdocScopeDfaTableEval {
            log_size: scope.table_log_size,
            dfa_relation,
            claim_mask_beta: None,
        };
        assert_constraints_on_trace(
            &trace,
            scope.table_log_size,
            |row| {
                let _ = eval.evaluate(row);
            },
            table_claimed_sum,
        );
    }

    /// Cross-component LogUp balance over the shared DFA relation: the walk's
    /// consume fractions and the table's yield fractions must cancel exactly.
    /// A tampered multiplicity leaves a nonzero residue, which the verifier
    /// rejects via the global `sum(claimed_sums) == 0` check in
    /// `air_core::verify` — the table component's own constraints stay
    /// satisfied, so this balance is the only thing catching it.
    #[test]
    fn tampered_table_multiplicity_breaks_cross_component_dfa_balance() {
        let scope = construct_v2(&[b"FR", b"DE"], false).unwrap();
        let witness = scope.witness.as_ref().unwrap();
        let dfa_relation = MdocScopeDfaRelation::dummy();

        let zero = QM31::from_u32_unchecked(0, 0, 0, 0);
        let walk_consume_sum = |rows: &[ScopeActiveRow]| {
            rows.iter().fold(zero, |sum, row| {
                let applied = row.applied;
                let tuple = [
                    m31(row.stream_slot as u32),
                    m31(applied.edge.from),
                    m31(applied.edge.to),
                    m31(applied.edge.action.index() as u32),
                    m31(applied.edge.p0),
                    m31(applied.edge.p1),
                ];
                let denominator: QM31 = dfa_relation.combine(&tuple);
                sum + denominator.inverse()
            })
        };
        let table_yield_sum = |multiplicities: &[u32]| {
            scope
                .table_edges
                .iter()
                .zip(multiplicities)
                .fold(zero, |sum, (&(slot, edge), &multiplicity)| {
                    let denominator: QM31 = dfa_relation.combine(&edge.tuple(slot).map(m31));
                    sum - denominator.inverse() * QM31::from(m31(multiplicity))
                })
        };

        let honest = walk_consume_sum(&witness.active_rows)
            + table_yield_sum(&witness.table_multiplicities);
        assert_eq!(honest, zero);

        let mut tampered = witness.table_multiplicities.clone();
        let victim = tampered
            .iter()
            .position(|&multiplicity| multiplicity != 0)
            .expect("some edge is used");
        tampered[victim] -= 1;
        let broken = walk_consume_sum(&witness.active_rows) + table_yield_sum(&tampered);
        assert_ne!(broken, zero);

        // The tampered multiplicity still satisfies the table component's own
        // constraints: only the cross-component claimed-sum balance breaks.
        let multiplicity_column = scope_table_trace(scope.table_log_size, &tampered);
        let table_preprocessed =
            scope_table_preprocessed_columns(scope.table_log_size, &scope.table_edges);
        let (interaction, tampered_claimed_sum) = scope_table_interaction_trace(
            scope.table_log_size,
            &multiplicity_column,
            &table_preprocessed,
            &dfa_relation,
            None,
        );
        let trees = TreeVec::new(vec![
            table_preprocessed
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
            vec![multiplicity_column.to_cpu().values],
            interaction
                .into_iter()
                .map(|column| column.to_cpu().values)
                .collect(),
        ]);
        let trace = trees.as_cols_ref();
        let eval = MdocScopeDfaTableEval {
            log_size: scope.table_log_size,
            dfa_relation,
            claim_mask_beta: None,
        };
        assert_constraints_on_trace(
            &trace,
            scope.table_log_size,
            |row| {
                let _ = eval.evaluate(row);
            },
            tampered_claimed_sum,
        );
    }
}
