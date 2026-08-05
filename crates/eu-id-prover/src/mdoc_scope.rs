//! Semantic issuer-scope proof for ISO 18013-5 mdoc credentials.
//!
//! This component is deliberately byte-stream based.  Each input stream is
//! first proved by [`crate::mdoc_cbor_stream::MdocCborStream`], and this AIR
//! consumes every resulting [`ParsedCborByteRelation`] tuple.  A public DFA
//! recognizes the complete byte language for:
//!
//! * the issuer COSE `Sig_structure`.
//! * the optional tag-24 MSO wrapper and the normalized MSO.
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
use air_core::relations::{field_id, FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use ciborium::value::Value;
use predicates::nat::types::MAX_PRESENTED_NATIONALITIES;
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
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
use stwo_sha256::relations::{PackedShaDigestRelation, SharedPackedShaDigestRelation};

pub(crate) const MDOC_SCOPE_MAX_ITEMS: usize = 4;
pub(crate) const MDOC_SCOPE_MIN_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_SCOPE_MAX_LOG_SIZE: u32 = 20;
pub(crate) const MDOC_SCOPE_BLIND_ROWS: usize = 256;
pub(crate) const MDOC_SCOPE_MAX_DIGEST_ID: u32 = u16::MAX as u32;
const MDOC_SCOPE_NATIONALITY_SLACK_BITS: usize = 8;
const MDOC_SCOPE_UNORDERED_MAP_DEPTH: usize = 3;
const _: () = assert!(MAX_PRESENTED_NATIONALITIES == 1usize << MDOC_SCOPE_NATIONALITY_SLACK_BITS);
const DIGEST_EXIT_REQUIRES_SELECTED_ITEMS: u32 = 1;
const DIGEST_ID_UNIVERSE_LOG_SIZE: u32 = 16;
const ITEM_DIGEST_MESSAGE_ID_BASE: u32 = 3;

pub(crate) const ISSUER_SIG_STRUCTURE_STREAM_ID: u32 = 0x4d53_0000;
pub(crate) const ISSUER_PAYLOAD_STREAM_ID: u32 = 0x4d53_0001;
pub(crate) const NORMALIZED_MSO_STREAM_ID: u32 = 0x4d53_0002;
pub(crate) const ITEM_STREAM_ID_BASE: u32 = 0x4d49_0000;
/// Existing TS13 `mso_payload_exposure` field tag. This output is the exact
/// issuerAuth payload before required tag-24 normalization.
pub(crate) const MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID: u32 = 40;

pub(crate) const fn item_outer_stream_id(index: usize) -> u32 {
    ITEM_STREAM_ID_BASE + (index as u32) * 2
}

pub(crate) const fn item_inner_stream_id(index: usize) -> u32 {
    item_outer_stream_id(index) + 1
}

/// The verifier-selected semantics for one requested issuer-signed item.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MdocScopeMode {
    AgeOver,
    /// Every element in the signed array is emitted at indices `2*i,2*i+1`.
    Alpha2Set,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocScopeItem {
    pub(crate) element_identifier: Vec<u8>,
    pub(crate) mode: MdocScopeMode,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MdocScopeStatement {
    pub(crate) request_binding: [u8; 32],
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
            match item.mode {
                MdocScopeMode::AgeOver => {
                    if std::mem::replace(&mut age, true) {
                        return Err(MdocScopeError::DuplicateMode("AgeOver"));
                    }
                }
                MdocScopeMode::Alpha2Set => {
                    if std::mem::replace(&mut nationality, true) {
                        return Err(MdocScopeError::DuplicateMode("Alpha2Set"));
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
    DuplicateDigestId(u32),
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
            Self::DuplicateDigestId(id) => write!(f, "duplicate valueDigests digestID {id}"),
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
relation!(MdocScopeDigestIdUniquenessRelation, 1);
relation!(MdocScopeDigestByteRelation, 3);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u32)]
enum ScopeAction {
    Exact = 0,
    Any,
    Argument,
    BeginBstr0,
    BeginBstr1,
    BeginBstr2,
    RawStay,
    RawExit,
    IgnoreStay,
    IgnoreExit,
    FieldByte,
    BeginArray0,
    BeginArray1,
    BeginArray2,
    NatAlphaFirst,
    NatAlphaStay,
    NatAlphaExit,
    ItemDigestId0,
    ItemDigestId1,
    ItemDigestId2,
    BeginDigestMap0,
    BeginDigestMap1,
    BeginDigestMap2,
    SelectedDigestId0,
    SelectedDigestId1,
    SelectedDigestId2,
    UnknownDigestId0,
    UnknownDigestId1,
    UnknownDigestId2,
    SelectedDigestByte,
    SelectedDigestStay,
    SelectedDigestExit,
    UnknownDigestByte,
    UnknownDigestStay,
    UnknownDigestExit,
    /// Emit a byte that is also fixed by `p1 = index*256 + byte`.
    FieldExact,
    /// Match one private ASCII decimal digit.
    AsciiDigit,
    /// Match and emit one private ASCII decimal digit (`p0=field`, `p1=index`).
    FieldDigit,
    BeginMap0,
    BeginMap1,
    BeginMap2,
    MapKeyStay0,
    MapKeyStay1,
    MapKeyStay2,
    MapKeyExit0,
    MapKeyExit1,
    MapKeyExit2,
}

const ALL_SCOPE_ACTIONS: [ScopeAction; 47] = [
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
    ScopeAction::FieldByte,
    ScopeAction::BeginArray0,
    ScopeAction::BeginArray1,
    ScopeAction::BeginArray2,
    ScopeAction::NatAlphaFirst,
    ScopeAction::NatAlphaStay,
    ScopeAction::NatAlphaExit,
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
        matches!(self, Self::RawStay | Self::RawExit)
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
    Nationality,
    DynamicItemDigestId(usize),
    DynamicDigestMap(usize),
    WrappedMso {
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
            Grammar::Nationality => self.compile_nationality(continuation),
            Grammar::DynamicItemDigestId(item) => {
                self.compile_dynamic_uint(true, *item, continuation)
            }
            Grammar::DynamicDigestMap(items) => self.compile_digest_map(*items, continuation),
            Grammar::WrappedMso { output_raw_slot } => {
                self.compile_wrapped_mso(*output_raw_slot, continuation)
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
            u32::from(items != 0) * DIGEST_EXIT_REQUIRES_SELECTED_ITEMS,
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

    fn compile_nationality(&mut self, continuation: u32) -> u32 {
        let header = 0x62u32;
        let first = ScopeAction::NatAlphaFirst;
        let stay = ScopeAction::NatAlphaStay;
        let exit = ScopeAction::NatAlphaExit;

        let element = self.state();
        let second = self.state();
        self.edge(element, second, ScopeAction::Exact, header, 0);
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
        array_start
    }

    fn compile_wrapped_mso(&mut self, output_raw_slot: usize, continuation: u32) -> u32 {
        self.compile(
            &Grammar::Sequence(vec![
                Grammar::Exact(cbor_head(6, 24)),
                Grammar::VariableBstr {
                    minimum_len: 1,
                    output_raw_slot: Some(output_raw_slot),
                },
            ]),
            continuation,
        )
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
    match field {
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
        tdate_byte(field, 10, b'T'),
        tdate_hour(field, 11),
        tdate_byte(field, 13, b':'),
        tdate_minute_or_second(field, 14),
        tdate_byte(field, 16, b':'),
        tdate_minute_or_second(field, 17),
        tdate_byte(field, 19, b'Z'),
    ])
}

fn value_grammar(item: &MdocScopeItem) -> Grammar {
    match item.mode {
        MdocScopeMode::AgeOver => {
            let date = Grammar::Sequence(vec![
                Grammar::Exact(cbor_head(3, 10)),
                fixed_private_bytes(field_id::DOB, 10),
            ]);
            Grammar::Sequence(vec![Grammar::Exact(cbor_head(6, 1004)), date])
        }
        MdocScopeMode::Alpha2Set => Grammar::Nationality,
    }
}

fn item_inner_grammar(item_index: usize, item: &MdocScopeItem) -> Grammar {
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
    let mut parts = vec![Grammar::Exact(cbor_head(5, fields.len() as u64))];
    for (key, value) in fields {
        parts.push(Grammar::Exact(key));
        parts.push(value);
    }
    Grammar::Sequence(parts)
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
    let selected_digests = Grammar::DynamicDigestMap(statement.items.len());
    let value_digests = Grammar::Sequence(vec![
        Grammar::Exact(cbor_head(5, 1)),
        exact_text(&statement.namespace),
        selected_digests,
    ]);
    let device_key_info = Grammar::UnorderedMap {
        level: 1,
        fields: vec![(cbor_text(b"deviceKey"), cose_key_grammar())],
    };
    Grammar::UnorderedMap {
        level: 0,
        fields: vec![
            (cbor_text(b"version"), exact_text(b"2.0")),
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
        compile_program(Grammar::WrappedMso { output_raw_slot: 1 }),
        compile_program(mso_grammar(statement)),
    ];
    for (index, item) in statement.items.iter().enumerate() {
        result.push(compile_program(item_outer_grammar(2 + index)));
        result.push(compile_program(item_inner_grammar(index, item)));
    }
    result
}

const MDOC_SCOPE_MAX_PUBLIC_IDENTIFIER_BYTES: usize = 256;
const MDOC_SCOPE_MAX_STREAM_BYTES: usize = 130_000;
const MDOC_SCOPE_MAX_TOTAL_STREAM_BYTES: usize = 520_000;
const MDOC_SCOPE_MAX_DFA_CONFIGURATIONS: usize = 4096;

/// Shared handles needed by the complete recursive parser/scope composition.
///
/// Recommended module order:
///
/// 1. issuer/item SHA modules, then the SHA-padded outer parsers.
/// 2. `MdocScope` (draws each raw-stream relation and `semantic_fields`).
/// 3. payload/MSO/item-inner raw parsers.
/// 4. age/nationality/validity/device-key consumers.
///
/// `air_core` draws every module before writing interactions, so the scope may
/// consume parsed handles drawn by the later raw parsers.  Relation signs are:
/// parser parsed-byte providers `-1`, scope parsed consumers `+1`. Scope raw
/// and semantic providers `-1`, raw-parser/predicate consumers `+1`. Item SHA
/// digest providers `-1`, scope digest consumers `+1`.
#[derive(Clone)]
pub(crate) struct MdocScopeHandles {
    pub(crate) parsed_streams: Vec<SharedParsedCborByteRelation>,
    pub(crate) raw_streams: Vec<SharedFieldRelation>,
    pub(crate) semantic_fields: SharedFieldRelation,
    pub(crate) payload_hash_fields: SharedFieldRelation,
    pub(crate) item_digest: SharedPackedShaDigestRelation,
}

impl MdocScopeHandles {
    pub(crate) fn fresh(
        statement: &MdocScopeStatement,
        item_digest: SharedPackedShaDigestRelation,
    ) -> Result<Self, MdocScopeError> {
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
            item_digest,
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
    /// The orchestrator supplies the issuer SHA full-stream field handle.
    ShaIssuer,
    /// The orchestrator supplies item `i`'s packed SHA full-stream field handle.
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
    _is_last: bool,
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
        ScopeAction::NatAlphaFirst => !row.header && before.remaining != 0,
        ScopeAction::NatAlphaStay | ScopeAction::NatAlphaExit => {
            let stay = action == ScopeAction::NatAlphaStay;
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
                && selected_ok
                && expected_id_ok;
            if ok {
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
            let requires_selected_items = matches!(action, ScopeAction::SelectedDigestExit)
                || edge.p0 == DIGEST_EXIT_REQUIRES_SELECTED_ITEMS;
            let ok = !row.header
                && before.remaining == 1
                && (!requires_selected_items || before.seen[..item_count].iter().all(|seen| *seen));
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
    digest_id_multiplicities: Vec<u32>,
    item_digest_bytes: Vec<[u8; 32]>,
    raw_stream_bytes: Vec<Vec<u8>>,
    #[cfg(test)]
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
        let mut digest_id_multiplicities = vec![0u32; 1 << DIGEST_ID_UNIVERSE_LOG_SIZE];
        let mut item_digest_bytes = vec![[0u8; 32]; statement.items.len()];
        #[cfg(test)]
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
                if matches!(
                    applied.edge.action,
                    ScopeAction::SelectedDigestId0
                        | ScopeAction::SelectedDigestId1
                        | ScopeAction::SelectedDigestId2
                        | ScopeAction::UnknownDigestId0
                        | ScopeAction::UnknownDigestId1
                        | ScopeAction::UnknownDigestId2
                ) {
                    let id = usize::try_from(row.argument)
                        .expect("digestID is constrained to the u16 universe");
                    digest_id_multiplicities[id] += 1;
                    if digest_id_multiplicities[id] > 1 {
                        return Err(MdocScopeError::DuplicateDigestId(id as u32));
                    }
                }
                if applied.edge.action.emits_digest_byte() {
                    let item = applied.edge.p0 as usize;
                    let byte_index = applied.edge.p1 as usize;
                    item_digest_bytes[item][byte_index] = row.byte;
                }
                #[cfg(test)]
                let nationality_index = match applied.edge.action {
                    ScopeAction::FieldByte if applied.edge.p0 == field_id::NATIONALITY => {
                        Some(applied.edge.p1)
                    }
                    ScopeAction::NatAlphaFirst => Some(applied.before.position * 2),
                    ScopeAction::NatAlphaStay | ScopeAction::NatAlphaExit => {
                        Some(applied.before.position * 2 + 1)
                    }
                    _ => None,
                };
                #[cfg(test)]
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
            digest_id_multiplicities,
            item_digest_bytes,
            raw_stream_bytes: streams,
            #[cfg(test)]
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

fn random_m31(rng: &mut impl RngCore) -> M31 {
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

fn digest_id_universe_col_id() -> PreProcessedColumnId {
    scope_col_id("digest_id_u16_universe")
}

fn scope_preprocessed_ids(item_count: usize) -> Vec<PreProcessedColumnId> {
    let mut ids = scope_table_preprocessed_ids();
    ids.extend((0..item_count).map(|item| scope_col_id(&format!("digest_item_{item}"))));
    ids.push(digest_id_universe_col_id());
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

fn digest_id_universe_column() -> MdocScopeColumnEval {
    scope_column(
        DIGEST_ID_UNIVERSE_LOG_SIZE,
        (0..=u16::MAX).map(|value| m31(u32::from(value))).collect(),
    )
}

/// All scope preprocessed columns in [`scope_preprocessed_ids`] order: the DFA
/// edge table, the walk's digest-item flags, and the fixed `u16` ID universe.
fn scope_preprocessed_columns(
    log_size: u32,
    table_log_size: u32,
    table_edges: &[(usize, DfaEdge)],
    item_count: usize,
) -> Vec<MdocScopeColumnEval> {
    let mut columns = scope_table_preprocessed_columns(table_log_size, table_edges);
    columns.extend(scope_walk_preprocessed_columns(log_size, item_count));
    columns.push(digest_id_universe_column());
    columns
}

/// Committed multiplicity column for the DFA edge table. Rows past the edge
/// list stay freshly blinded. The preprocessed `dfa_active` flag gates them out
/// of the LogUp yield.
fn scope_table_trace(table_log_size: u32, multiplicities: &[u32]) -> MdocScopeColumnEval {
    let domain = 1usize << table_log_size;
    let mut rng = rand::thread_rng();
    let mut values: Vec<M31> = (0..domain).map(|_| random_m31(&mut rng)).collect();
    for (row, &multiplicity) in multiplicities.iter().enumerate() {
        values[row] = m31(multiplicity);
    }
    scope_column(table_log_size, values)
}

fn digest_id_uniqueness_trace(multiplicities: &[u32]) -> MdocScopeColumnEval {
    assert_eq!(multiplicities.len(), 1usize << DIGEST_ID_UNIVERSE_LOG_SIZE);
    scope_column(
        DIGEST_ID_UNIVERSE_LOG_SIZE,
        multiplicities.iter().copied().map(m31).collect(),
    )
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
    seed: [u8; 32],
) -> Vec<MdocScopeColumnEval> {
    let domain = 1usize << log_size;
    let mut rng = StdRng::from_seed(seed);
    let mut values = (0..columns.total)
        .map(|_| {
            (0..domain)
                .map(|_| random_m31(&mut rng))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    for column in scope_zero_columns(columns) {
        values[column].fill(m31(0));
    }

    for (row_index, row) in witness.active_rows.iter().enumerate() {
        populate_scope_active_row(&mut values, columns, row_index, row);
        set_bits(
            &mut values,
            columns.slack_bits.clone(),
            row_index,
            row.applied.slack,
        );
        values[columns.inverse][row_index] = row.applied.inverse;
    }

    populate_scope_item_digest_values(&mut values, columns, &witness.item_digest_bytes);

    debug_assert_eq!(columns.stream_selectors.len(), stream_count);
    debug_assert_eq!(columns.raw_selectors.len(), raw_count);
    values
        .into_iter()
        .map(|column| scope_column(log_size, column))
        .collect()
}

fn scope_zero_columns(columns: &ScopeTraceColumns) -> Vec<usize> {
    let mut zero_columns = vec![columns.active, columns.first, columns.last];
    zero_columns.extend(columns.stream_selectors.clone());
    zero_columns.extend(columns.action_flags.clone());
    zero_columns.extend(columns.raw_selectors.clone());
    zero_columns
}

fn populate_scope_active_row(
    values: &mut [Vec<M31>],
    columns: &ScopeTraceColumns,
    row_index: usize,
    row: &ScopeActiveRow,
) {
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
    values[columns.have_previous_before][row_index] = m31(u32::from(applied.before.have_previous));
    values[columns.have_previous_after][row_index] = m31(u32::from(applied.after.have_previous));
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
    if applied.edge.action.emits_raw() {
        values[columns.raw_selectors.start + applied.edge.p0 as usize][row_index] = m31(1);
    }
    let (field, index) = match applied.edge.action {
        ScopeAction::FieldByte => (applied.edge.p0, applied.edge.p1),
        ScopeAction::FieldExact => (applied.edge.p0, applied.edge.p1 / 256),
        ScopeAction::FieldDigit => (applied.edge.p0, applied.edge.p1),
        ScopeAction::NatAlphaFirst => (
            field_id::NATIONALITY,
            applied.before.position.saturating_mul(2),
        ),
        ScopeAction::NatAlphaStay | ScopeAction::NatAlphaExit => (
            field_id::NATIONALITY,
            applied.before.position.saturating_mul(2) + 1,
        ),
        _ => (0, 0),
    };
    values[columns.field_id][row_index] = m31(field);
    values[columns.field_index][row_index] = m31(index);
}

fn populate_scope_item_digest_values(
    values: &mut [Vec<M31>],
    columns: &ScopeTraceColumns,
    item_digest_bytes: &[[u8; 32]],
) {
    for (item, digest) in item_digest_bytes.iter().enumerate() {
        for (byte, value) in digest.iter().copied().enumerate() {
            values[columns.digest_values.start + byte][item] = m31(u32::from(value));
        }
    }
}

trait ScopeInteractionBase {
    fn at(&self, column: usize, row: usize) -> PackedM31;
}

impl ScopeInteractionBase for [MdocScopeColumnEval] {
    fn at(&self, column: usize, row: usize) -> PackedM31 {
        self[column].data[row]
    }
}

impl ScopeInteractionBase for Vec<MdocScopeColumnEval> {
    fn at(&self, column: usize, row: usize) -> PackedM31 {
        self.as_slice().at(column, row)
    }
}

struct ScopeActiveInteractionBase {
    log_size: u32,
    values: Vec<Vec<M31>>,
    zero_columns: Vec<bool>,
}

impl ScopeActiveInteractionBase {
    fn new(log_size: u32, columns: &ScopeTraceColumns, witness: &MdocScopeWitness) -> Self {
        let active_rows = witness.active_rows.len();
        let mut values = (0..columns.total)
            .map(|_| vec![m31(0); active_rows])
            .collect::<Vec<_>>();
        for (row_index, row) in witness.active_rows.iter().enumerate() {
            populate_scope_active_row(&mut values, columns, row_index, row);
        }
        populate_scope_item_digest_values(&mut values, columns, &witness.item_digest_bytes);
        let mut zero_columns = vec![false; columns.total];
        for column in scope_zero_columns(columns) {
            zero_columns[column] = true;
        }
        Self {
            log_size,
            values,
            zero_columns,
        }
    }
}

impl ScopeInteractionBase for ScopeActiveInteractionBase {
    fn at(&self, column: usize, row: usize) -> PackedM31 {
        PackedM31::from_array(std::array::from_fn(|lane| {
            let circle_row = bit_reverse_index(row * N_LANES + lane, self.log_size);
            let source_row = circle_domain_index_to_coset_index(circle_row, self.log_size);
            self.values
                .get(column)
                .and_then(|values| values.get(source_row))
                .copied()
                .unwrap_or_else(|| {
                    let value = if self.zero_columns[column] { 0 } else { 1 };
                    m31(value)
                })
        }))
    }
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
    item_digest_relation: PackedShaDigestRelation,
    item_count: usize,
    dfa_relation: MdocScopeDfaRelation,
    state_relation: MdocScopeStateRelation,
    digest_id_relation: MdocScopeDigestIdRelation,
    digest_id_uniqueness_relation: MdocScopeDigestIdUniquenessRelation,
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

fn scope_constraint_log_degree_bound(log_size: u32, item_count: usize) -> u32 {
    debug_assert!((1..=MDOC_SCOPE_MAX_ITEMS).contains(&item_count));
    // The highest-degree constraint updates `seen`: a linear selected-id flag
    // times the degree-(item_count - 1) item selector, a linear unseen flag,
    // and the outer active gate. Its degree is item_count + 2, so the quotient
    // needs ceil(log2(item_count + 1)) extra domain bits.
    let quotient_factor = u32::try_from(item_count + 1)
        .expect("the fixed mdoc item count fits u32")
        .next_power_of_two()
        .trailing_zeros()
        .max(1);
    log_size + quotient_factor
}

impl FrameworkEval for MdocScopeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        scope_constraint_log_degree_bound(self.log_size, self.item_count)
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let item_count = self.item_count;
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
            &[ScopeAction::RawStay, ScopeAction::RawExit],
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
                ScopeAction::NatAlphaStay,
                ScopeAction::NatAlphaExit,
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
        let digest_id = selected_id.clone() + unknown_id;
        let previous_before = trace[columns.previous_id_before].clone();
        let expected_previous = previous_before.clone()
            - begin_digest_map.clone() * previous_before.clone()
            + digest_id.clone() * (arg_lo.clone() - previous_before.clone());
        eval.add_constraint(
            active.clone() * (trace[columns.previous_id_after].clone() - expected_previous),
        );
        let expected_have = have_before.clone() - begin_digest_map.clone() * have_before.clone()
            + digest_id.clone() * (one.clone() - have_before.clone());
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
        let slack_gate = begin_any.clone() + decimal_digit.clone();
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
        let stay = action_sum::<E>(
            &trace,
            &columns,
            &[
                ScopeAction::RawStay,
                ScopeAction::IgnoreStay,
                ScopeAction::NatAlphaStay,
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
            ],
        );
        let fixed_field = action(ScopeAction::FieldByte);
        let exact_field = action(ScopeAction::FieldExact);
        let digit_field = action(ScopeAction::FieldDigit);
        let nat_first = action(ScopeAction::NatAlphaFirst);
        let nat_second = action_sum::<E>(
            &trace,
            &columns,
            &[ScopeAction::NatAlphaStay, ScopeAction::NatAlphaExit],
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

        let digest_exit = action(ScopeAction::SelectedDigestExit)
            + action(ScopeAction::UnknownDigestExit) * trace[columns.p0].clone();
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
        eval.add_to_relation(RelationEntry::new(
            &self.digest_id_uniqueness_relation,
            E::EF::from(digest_id),
            std::slice::from_ref(&arg_lo),
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

        for item in 0..item_count {
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
            let mut digest_tuple = Vec::with_capacity(1 + values.len());
            digest_tuple.push(f_const::<E>(
                ITEM_DIGEST_MESSAGE_ID_BASE
                    + u32::try_from(item).expect("item digest index fits u32"),
            ));
            digest_tuple.extend(values.iter().cloned());
            eval.add_to_relation(RelationEntry::new(
                &self.item_digest_relation,
                E::EF::from(aggregate[item].clone()),
                &digest_tuple,
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

/// DFA edge-table component.
///
/// It stores preprocessed edge tuples and committed edge multiplicities.
/// Each edge yields `-active * multiplicity` into [`MdocScopeDfaRelation`].
/// The walk component consumes the same relation entries.
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

/// Fixed `u16` universe for `valueDigests` map-key uniqueness.
///
/// Every parsed map key consumes one relation entry. The committed
/// multiplicity at each public universe value provides the matching entry and
/// is constrained to a bit. Thus, no digest ID can occur more than once,
/// independent of map order or whether the key selects a requested item.
struct MdocScopeDigestIdUniverseEval {
    relation: MdocScopeDigestIdUniquenessRelation,
    claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for MdocScopeDigestIdUniverseEval {
    fn log_size(&self) -> u32 {
        DIGEST_ID_UNIVERSE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        DIGEST_ID_UNIVERSE_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(digest_id_universe_col_id());
        let multiplicity = eval.next_trace_mask();
        let one = f_const::<E>(1);
        eval.add_constraint(multiplicity.clone() * (multiplicity.clone() - one));
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            std::slice::from_ref(&value),
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn digest_id_uniqueness_interaction_trace(
    multiplicity: &MdocScopeColumnEval,
    relation: &MdocScopeDigestIdUniquenessRelation,
    claim_mask: Option<(&ClaimMaskTrace, QM31)>,
) -> (Vec<MdocScopeColumnEval>, QM31) {
    let values = digest_id_universe_column();
    let n_vec_rows = 1usize << (DIGEST_ID_UNIVERSE_LOG_SIZE - LOG_N_LANES);
    let mut logup = LogupTraceGenerator::new(DIGEST_ID_UNIVERSE_LOG_SIZE);
    match claim_mask {
        Some((mask, beta)) => {
            assert_eq!(mask.log_size(), DIGEST_ID_UNIVERSE_LOG_SIZE);
            logup.col_from_iter((0..n_vec_rows).map(|row| {
                let denominator: PackedQM31 = relation.combine(&[values.data[row]]);
                let numerator = -PackedQM31::from(multiplicity.data[row]);
                let (mask_numerator, mask_denominator) = mask.packed_fraction_at(row, beta);
                (
                    numerator * mask_denominator + mask_numerator * denominator,
                    denominator * mask_denominator,
                )
            }));
        }
        None => {
            logup.col_from_iter((0..n_vec_rows).map(|row| {
                (
                    -PackedQM31::from(multiplicity.data[row]),
                    relation.combine(&[values.data[row]]),
                )
            }));
        }
    }
    logup.finalize_last()
}

fn packed_action_sum<B: ScopeInteractionBase + ?Sized>(
    base: &B,
    columns: &ScopeTraceColumns,
    row: usize,
    actions: &[ScopeAction],
) -> PackedM31 {
    actions
        .iter()
        .fold(PackedM31::broadcast(m31(0)), |sum, action| {
            sum + base.at(columns.action_flags.start + action.index(), row)
        })
}

#[allow(clippy::too_many_arguments)]
fn scope_interaction_trace<B: ScopeInteractionBase + ?Sized>(
    log_size: u32,
    columns: &ScopeTraceColumns,
    base: &B,
    walk_preprocessed: &[MdocScopeColumnEval],
    stream_ids: &[u32],
    raw_target_stream_ids: &[u32],
    parsed_relations: &[ParsedCborByteRelation],
    raw_relations: &[FieldBytesRelation],
    semantic_relation: &FieldBytesRelation,
    payload_hash_relation: Option<&FieldBytesRelation>,
    item_digest_relation: &PackedShaDigestRelation,
    item_count: usize,
    dfa_relation: &MdocScopeDfaRelation,
    state_relation: &MdocScopeStateRelation,
    digest_id_relation: &MdocScopeDigestIdRelation,
    digest_id_uniqueness_relation: &MdocScopeDigestIdUniquenessRelation,
    digest_byte_relation: &MdocScopeDigestByteRelation,
    claim_mask_trace: Option<&ClaimMaskTrace>,
    claim_mask_beta: Option<QM31>,
) -> (Vec<MdocScopeColumnEval>, QM31) {
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::new();
    let broadcast = |value: u32| PackedM31::broadcast(m31(value));
    let base_at = |column: usize, row: usize| base.at(column, row);

    for (slot, relation) in parsed_relations.iter().enumerate() {
        sites.push(
            (0..n_vec_rows)
                .map(|row| {
                    let numerator =
                        PackedQM31::from(base_at(columns.stream_selectors.start + slot, row));
                    let mut tuple = Vec::with_capacity(parsed_cbor_tuple::ARITY);
                    tuple.push(broadcast(stream_ids[slot]));
                    tuple.push(base_at(columns.byte_index, row));
                    tuple.push(base_at(columns.byte, row));
                    tuple.extend(
                        columns
                            .parsed_meta
                            .clone()
                            .map(|column| base_at(column, row)),
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
                        -PackedQM31::from(base_at(columns.raw_selectors.start + slot, row));
                    let denominator = relation.combine(&[
                        broadcast(raw_target_stream_ids[slot]),
                        base_at(columns.position_before, row),
                        base_at(columns.byte, row),
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
                    ],
                );
                let denominator = semantic_relation.combine(&[
                    base_at(columns.field_id, row),
                    base_at(columns.field_index, row),
                    base_at(columns.byte, row),
                ]);
                (-PackedQM31::from(emit), denominator)
            })
            .collect(),
    );
    if let Some(payload_hash_relation) = payload_hash_relation {
        sites.push(
            (0..n_vec_rows)
                .map(|row| {
                    let numerator = -PackedQM31::from(base_at(columns.raw_selectors.start, row));
                    let denominator = payload_hash_relation.combine(&[
                        broadcast(MDOC_SCOPE_MSO_PAYLOAD_FIELD_ID),
                        base_at(columns.position_before, row),
                        base_at(columns.byte, row),
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
                    base_at(columns.p0, row),
                    base_at(
                        columns.parsed_meta.start + parsed_cbor_tuple::ARG_LO16 - 3,
                        row,
                    ),
                ]);
                (PackedQM31::from(selected - provider), denominator)
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let digest_key = packed_action_sum(
                    base,
                    columns,
                    row,
                    &[
                        ScopeAction::SelectedDigestId0,
                        ScopeAction::SelectedDigestId1,
                        ScopeAction::SelectedDigestId2,
                        ScopeAction::UnknownDigestId0,
                        ScopeAction::UnknownDigestId1,
                        ScopeAction::UnknownDigestId2,
                    ],
                );
                let id = base_at(
                    columns.parsed_meta.start + parsed_cbor_tuple::ARG_LO16 - 3,
                    row,
                );
                (
                    PackedQM31::from(digest_key),
                    digest_id_uniqueness_relation.combine(&[id]),
                )
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
                    base_at(columns.p0, row),
                    base_at(columns.p1, row),
                    base_at(columns.byte, row),
                ]);
                (-PackedQM31::from(emit), denominator)
            })
            .collect(),
    );

    for item in 0..item_count {
        let aggregate = &walk_preprocessed[item];
        for byte in 0..SCOPE_DIGEST_BYTES {
            sites.push(
                (0..n_vec_rows)
                    .map(|row| {
                        let numerator = PackedQM31::from(aggregate.data[row]);
                        let denominator = digest_byte_relation.combine(&[
                            broadcast(item as u32),
                            broadcast(byte as u32),
                            base_at(columns.digest_values.start + byte, row),
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
                    let values: Vec<_> = columns
                        .digest_values
                        .clone()
                        .map(|column| base_at(column, row))
                        .collect();
                    let mut digest_tuple = Vec::with_capacity(1 + values.len());
                    digest_tuple.push(broadcast(
                        ITEM_DIGEST_MESSAGE_ID_BASE
                            + u32::try_from(item).expect("item digest index fits u32"),
                    ));
                    digest_tuple.extend(values);
                    (numerator, item_digest_relation.combine(&digest_tuple))
                })
                .collect(),
        );
    }

    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let stream_slot =
                    (0..stream_ids.len()).fold(PackedM31::broadcast(m31(0)), |sum, slot| {
                        sum + base_at(columns.stream_selectors.start + slot, row)
                            * broadcast(slot as u32)
                    });
                let action_code =
                    (0..SCOPE_ACTION_COUNT).fold(PackedM31::broadcast(m31(0)), |sum, action| {
                        sum + base_at(columns.action_flags.start + action, row)
                            * broadcast(action as u32)
                    });
                let denominator = dfa_relation.combine(&[
                    stream_slot,
                    base_at(columns.state_before, row),
                    base_at(columns.state_after, row),
                    action_code,
                    base_at(columns.p0, row),
                    base_at(columns.p1, row),
                ]);
                (PackedQM31::from(base_at(columns.active, row)), denominator)
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let stream_slot =
                    (0..stream_ids.len()).fold(PackedM31::broadcast(m31(0)), |sum, slot| {
                        sum + base_at(columns.stream_selectors.start + slot, row)
                            * broadcast(slot as u32)
                    });
                let mut tuple = vec![
                    stream_slot,
                    base_at(columns.byte_index, row),
                    base_at(columns.state_before, row),
                    base_at(columns.remaining_before, row),
                    base_at(columns.position_before, row),
                    base_at(columns.previous_id_before, row),
                    base_at(columns.have_previous_before, row),
                    base_at(columns.seen_before.start, row),
                    base_at(columns.seen_before.start + 1, row),
                    base_at(columns.seen_before.start + 2, row),
                    base_at(columns.seen_before.start + 3, row),
                ];
                tuple.extend(
                    columns
                        .map_remaining_before
                        .clone()
                        .map(|column| base_at(column, row)),
                );
                tuple.extend(
                    columns
                        .map_accumulator_before
                        .clone()
                        .map(|column| base_at(column, row)),
                );
                tuple.extend(
                    columns
                        .map_full_before
                        .clone()
                        .map(|column| base_at(column, row)),
                );
                let denominator = state_relation.combine(&tuple);
                let numerator =
                    PackedQM31::from(base_at(columns.active, row) - base_at(columns.first, row));
                (numerator, denominator)
            })
            .collect(),
    );
    sites.push(
        (0..n_vec_rows)
            .map(|row| {
                let stream_slot =
                    (0..stream_ids.len()).fold(PackedM31::broadcast(m31(0)), |sum, slot| {
                        sum + base_at(columns.stream_selectors.start + slot, row)
                            * broadcast(slot as u32)
                    });
                let mut tuple = vec![
                    stream_slot,
                    base_at(columns.byte_index, row) + PackedM31::broadcast(m31(1)),
                    base_at(columns.state_after, row),
                    base_at(columns.remaining_after, row),
                    base_at(columns.position_after, row),
                    base_at(columns.previous_id_after, row),
                    base_at(columns.have_previous_after, row),
                    base_at(columns.seen_after.start, row),
                    base_at(columns.seen_after.start + 1, row),
                    base_at(columns.seen_after.start + 2, row),
                    base_at(columns.seen_after.start + 3, row),
                ];
                tuple.extend(
                    columns
                        .map_remaining_after
                        .clone()
                        .map(|column| base_at(column, row)),
                );
                tuple.extend(
                    columns
                        .map_accumulator_after
                        .clone()
                        .map(|column| base_at(column, row)),
                );
                tuple.extend(
                    columns
                        .map_full_after
                        .clone()
                        .map(|column| base_at(column, row)),
                );
                let denominator = state_relation.combine(&tuple);
                let numerator =
                    -PackedQM31::from(base_at(columns.active, row) - base_at(columns.last, row));
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
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocScopeInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) table_claimed_sum: QM31,
    pub(crate) digest_id_uniqueness_claimed_sum: QM31,
}

pub(crate) struct MdocScope {
    statement: MdocScopeStatement,
    metadata: MdocScopeProofMetadata,
    /// Derived from the statement's DFA programs on both sides. Never
    /// prover-supplied.
    table_log_size: u32,
    programs: Vec<DfaProgram>,
    table_edges: Vec<(usize, DfaEdge)>,
    handles: MdocScopeHandles,
    payload_hash_binding: bool,
    witness: Option<MdocScopeWitness>,
    trace_seed: Option<[u8; 32]>,
    dfa_relation: Option<MdocScopeDfaRelation>,
    state_relation: Option<MdocScopeStateRelation>,
    digest_id_relation: Option<MdocScopeDigestIdRelation>,
    digest_id_uniqueness_relation: Option<MdocScopeDigestIdUniquenessRelation>,
    digest_byte_relation: Option<MdocScopeDigestByteRelation>,
    claim_mask_trace: Option<ClaimMaskTrace>,
    table_claim_mask_trace: Option<ClaimMaskTrace>,
    digest_id_uniqueness_claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocScopeInteractionClaim>,
    component: Option<MdocScopeComponent>,
    table_component: Option<FrameworkComponent<MdocScopeDfaTableEval>>,
    digest_id_uniqueness_component: Option<FrameworkComponent<MdocScopeDigestIdUniverseEval>>,
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
        // The walk runs at its natural (byte-count driven) height. The DFA
        // edge table lives in its own component at its own height.
        let log_size = scope_log_size(witness.active_rows.len())?;
        let table_log_size = scope_log_size(table_edges.len())?;
        let metadata = MdocScopeProofMetadata { log_size };
        Ok(Self {
            statement,
            metadata,
            table_log_size,
            programs,
            table_edges,
            handles,
            payload_hash_binding: false,
            witness: Some(witness),
            trace_seed: Some({
                let mut seed = [0u8; 32];
                rand::thread_rng().fill_bytes(&mut seed);
                seed
            }),
            dfa_relation: None,
            state_relation: None,
            digest_id_relation: None,
            digest_id_uniqueness_relation: None,
            digest_byte_relation: None,
            claim_mask_trace: None,
            table_claim_mask_trace: None,
            digest_id_uniqueness_claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
            table_component: None,
            digest_id_uniqueness_component: None,
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
            trace_seed: None,
            dfa_relation: None,
            state_relation: None,
            digest_id_relation: None,
            digest_id_uniqueness_relation: None,
            digest_byte_relation: None,
            claim_mask_trace: None,
            table_claim_mask_trace: None,
            digest_id_uniqueness_claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            table_component: None,
            digest_id_uniqueness_component: None,
        })
    }

    pub(crate) fn metadata(&self) -> &MdocScopeProofMetadata {
        &self.metadata
    }

    pub(crate) fn with_fixed_log_size(mut self, log_size: u32) -> Result<Self, MdocScopeError> {
        if !(MDOC_SCOPE_MIN_LOG_SIZE..=MDOC_SCOPE_MAX_LOG_SIZE).contains(&log_size)
            || self.metadata.log_size > log_size
        {
            return Err(MdocScopeError::TraceTooLarge(
                self.witness
                    .as_ref()
                    .map_or(0, |witness| witness.active_rows.len()),
            ));
        }
        self.metadata.log_size = log_size;
        Ok(self)
    }

    #[cfg(test)]
    fn private_nationality_count(&self) -> Option<u16> {
        self.witness
            .as_ref()
            .and_then(|witness| witness.nationality_count)
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
    /// This method returns prover-only witness data.
    /// Proof metadata does not contain these bytes as explicit fields.
    /// Transparent proof openings remain witness-dependent.
    /// The current proof does not guarantee confidentiality.
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

    fn item_digest_relation(&self) -> PackedShaDigestRelation {
        self.handles.item_digest.get()
    }

    pub(crate) fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![
            self.metadata.log_size,
            self.table_log_size,
            DIGEST_ID_UNIVERSE_LOG_SIZE,
        ]
    }

    pub(crate) fn with_claim_masks(
        mut self,
        traces: Vec<ClaimMaskTrace>,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        let [walk, table, digest_id_uniqueness]: [ClaimMaskTrace; 3] = traces
            .try_into()
            .unwrap_or_else(|_| panic!("mdoc scope expects exactly three claim masks"));
        assert_eq!(walk.log_size(), self.metadata.log_size);
        assert_eq!(table.log_size(), self.table_log_size);
        assert_eq!(digest_id_uniqueness.log_size(), DIGEST_ID_UNIVERSE_LOG_SIZE);
        self.claim_mask_trace = Some(walk);
        self.table_claim_mask_trace = Some(table);
        self.digest_id_uniqueness_claim_mask_trace = Some(digest_id_uniqueness);
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

    /// Walk-component LogUp sites. The DFA table's yield lives in its own
    /// component (see [`Self::n_table_interaction_sites`]).
    fn n_interaction_sites(&self) -> usize {
        self.handles.parsed_streams.len()
            + self.handles.raw_streams.len()
            + 4 // semantic, digest-id binding, digest-id uniqueness, digest-byte
            + usize::from(self.payload_hash_binding)
            + self.statement.items.len() * (SCOPE_DIGEST_BYTES + 1)
            + 3 // DFA consume and state consume/provider
            + usize::from(self.claim_mask_challenge.is_some())
    }

    fn n_table_interaction_sites(&self) -> usize {
        1 + usize::from(self.claim_mask_challenge.is_some())
    }

    fn n_digest_id_uniqueness_interaction_sites(&self) -> usize {
        1 + usize::from(self.claim_mask_challenge.is_some())
    }
}

impl Air for MdocScope {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(0x4d44_4f43_5343_4f50);
        channel.mix_u64(3);
        channel.mix_u64(u64::from(self.payload_hash_binding));
        channel.mix_u64(u64::from(self.metadata.log_size));
        channel.mix_u64(u64::from(self.table_log_size));
        channel.mix_u64(u64::from(DIGEST_ID_UNIVERSE_LOG_SIZE));
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
            match item.mode {
                MdocScopeMode::AgeOver => channel.mix_u64(1),
                MdocScopeMode::Alpha2Set => channel.mix_u64(2),
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
        self.digest_id_uniqueness_relation =
            Some(MdocScopeDigestIdUniquenessRelation::draw(channel));
        self.digest_byte_relation = Some(MdocScopeDigestByteRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        let columns = self.columns();
        let mask_columns =
            usize::from(self.claim_mask_challenge.is_some()) * CLAIM_MASK_TRACE_COLUMNS;
        let mut preprocessed = vec![self.table_log_size; SCOPE_PREPROCESSED_FIXED_COLS];
        preprocessed.extend(vec![self.metadata.log_size; self.statement.items.len()]);
        preprocessed.push(DIGEST_ID_UNIVERSE_LOG_SIZE);
        let mut trace = vec![self.metadata.log_size; columns.total + mask_columns];
        trace.extend(vec![self.table_log_size; 1 + mask_columns]);
        trace.extend(vec![DIGEST_ID_UNIVERSE_LOG_SIZE; 1 + mask_columns]);
        let mut interaction = vec![
            self.metadata.log_size;
            self.n_interaction_sites().div_ceil(2) * SECURE_EXTENSION_DEGREE
        ];
        interaction.extend(vec![
            self.table_log_size;
            self.n_table_interaction_sites().div_ceil(2)
                * SECURE_EXTENSION_DEGREE
        ]);
        interaction.extend(vec![
            DIGEST_ID_UNIVERSE_LOG_SIZE;
            self.n_digest_id_uniqueness_interaction_sites()
                .div_ceil(2)
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
        vec![
            claim.claimed_sum,
            claim.table_claimed_sum,
            claim.digest_id_uniqueness_claimed_sum,
        ]
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
                item_digest_relation: self.item_digest_relation(),
                item_count: self.statement.items.len(),
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
                digest_id_uniqueness_relation: self
                    .digest_id_uniqueness_relation
                    .clone()
                    .expect("mdoc scope digest-id uniqueness relation drawn"),
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
        self.digest_id_uniqueness_component = Some(FrameworkComponent::new(
            allocator,
            MdocScopeDigestIdUniverseEval {
                relation: self
                    .digest_id_uniqueness_relation
                    .clone()
                    .expect("mdoc scope digest-id uniqueness relation drawn"),
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.digest_id_uniqueness_claimed_sum,
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
            self.digest_id_uniqueness_component
                .as_ref()
                .expect("mdoc scope digest-id uniqueness component is built"),
        ]
    }
}

impl AirProver for MdocScope {
    fn max_log_size(&self) -> u32 {
        self.metadata
            .log_size
            .max(self.table_log_size)
            .max(DIGEST_ID_UNIVERSE_LOG_SIZE)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        scope_constraint_log_degree_bound(self.metadata.log_size, self.statement.items.len())
            .max(self.table_log_size + 1)
            .max(DIGEST_ID_UNIVERSE_LOG_SIZE + 1)
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
            self.trace_seed.expect("mdoc scope trace seed is set"),
        );
        let table_trace = scope_table_trace(self.table_log_size, &witness.table_multiplicities);
        tb.extend_evals(trace);
        if let Some(mask) = &self.claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
        tb.extend_evals(vec![table_trace]);
        if let Some(mask) = &self.table_claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
        tb.extend_evals(vec![digest_id_uniqueness_trace(
            &witness.digest_id_multiplicities,
        )]);
        if let Some(mask) = &self.digest_id_uniqueness_claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let columns = self.columns();
        let witness = self
            .witness
            .as_ref()
            .expect("mdoc scope prover has a witness");
        let base = ScopeActiveInteractionBase::new(self.metadata.log_size, &columns, witness);
        let walk_preprocessed =
            scope_walk_preprocessed_columns(self.metadata.log_size, self.statement.items.len());
        let parsed_relations = self.parsed_relations();
        let raw_relations = self.raw_relations();
        let item_digest_relation = self.item_digest_relation();
        let dfa_relation = self.dfa_relation.as_ref().expect("DFA relation drawn");
        let state_relation = self.state_relation.as_ref().expect("state relation drawn");
        let digest_id_relation = self
            .digest_id_relation
            .as_ref()
            .expect("digest-id relation drawn");
        let digest_id_uniqueness_relation = self
            .digest_id_uniqueness_relation
            .as_ref()
            .expect("digest-id uniqueness relation drawn");
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
            &base,
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
            &item_digest_relation,
            self.statement.items.len(),
            dfa_relation,
            state_relation,
            digest_id_relation,
            digest_id_uniqueness_relation,
            digest_byte_relation,
            self.claim_mask_trace.as_ref(),
            self.claim_mask_beta(),
        );
        tb.extend_evals(interaction);
        let table_multiplicity =
            scope_table_trace(self.table_log_size, &witness.table_multiplicities);
        let table_preprocessed =
            scope_table_preprocessed_columns(self.table_log_size, &self.table_edges);
        let table_claim_mask = self
            .table_claim_mask_trace
            .as_ref()
            .zip(self.claim_mask_beta());
        let (table_interaction, table_claimed_sum) = scope_table_interaction_trace(
            self.table_log_size,
            &table_multiplicity,
            &table_preprocessed,
            dfa_relation,
            table_claim_mask,
        );
        tb.extend_evals(table_interaction);
        let digest_id_uniqueness_trace =
            digest_id_uniqueness_trace(&witness.digest_id_multiplicities);
        let digest_id_uniqueness_claim_mask = self
            .digest_id_uniqueness_claim_mask_trace
            .as_ref()
            .zip(self.claim_mask_beta());
        let (digest_id_uniqueness_interaction, digest_id_uniqueness_claimed_sum) =
            digest_id_uniqueness_interaction_trace(
                &digest_id_uniqueness_trace,
                digest_id_uniqueness_relation,
                digest_id_uniqueness_claim_mask,
            );
        tb.extend_evals(digest_id_uniqueness_interaction);
        self.interaction_claim = Some(MdocScopeInteractionClaim {
            claimed_sum,
            table_claimed_sum,
            digest_id_uniqueness_claimed_sum,
        });
        // The witness has now supplied both committed trees.  Components only
        // retain the public statement, relations, and claimed sums.
        self.witness.take();
        self.trace_seed.take();
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("mdoc scope component is built"),
            self.table_component
                .as_ref()
                .expect("mdoc scope DFA table component is built"),
            self.digest_id_uniqueness_component
                .as_ref()
                .expect("mdoc scope digest-id uniqueness component is built"),
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
    use stwo_constraint_framework::expr::ExprEvaluator;

    const VALID_SIGNED: &str = "2026-01-01T00:00:00Z";
    const VALID_FROM: &str = "2026-01-02T03:04:05Z";
    const VALID_UNTIL: &str = "2030-12-31T23:59:59Z";

    fn symbolic_max_degree(eval: impl FrameworkEval) -> u32 {
        eval.evaluate(ExprEvaluator::new())
            .constraint_degree_bounds()
            .into_iter()
            .max()
            .unwrap_or(0) as u32
    }

    fn symbolic_scope_eval(item_count: usize) -> MdocScopeEval {
        MdocScopeEval {
            log_size: 16,
            stream_ids: vec![1],
            program_starts: vec![0],
            program_ends: vec![1],
            raw_target_stream_ids: vec![1],
            parsed_relations: vec![ParsedCborByteRelation::dummy()],
            raw_relations: vec![FieldBytesRelation::dummy()],
            semantic_relation: FieldBytesRelation::dummy(),
            payload_hash_relation: Some(FieldBytesRelation::dummy()),
            item_digest_relation: PackedShaDigestRelation::dummy(),
            item_count,
            dfa_relation: MdocScopeDfaRelation::dummy(),
            state_relation: MdocScopeStateRelation::dummy(),
            digest_id_relation: MdocScopeDigestIdRelation::dummy(),
            digest_id_uniqueness_relation: MdocScopeDigestIdUniquenessRelation::dummy(),
            digest_byte_relation: MdocScopeDigestByteRelation::dummy(),
            claim_mask_beta: None,
        }
    }

    #[test]
    fn scope_expression_degrees_match_item_count_bounds() {
        for (item_count, expected_degree) in [(1, 3), (2, 4), (3, 5), (4, 6)] {
            let eval = symbolic_scope_eval(item_count);
            let declared = eval.max_constraint_log_degree_bound();
            let measured = symbolic_max_degree(eval);
            let required = scope_constraint_log_degree_bound(16, item_count);

            assert_eq!(measured, expected_degree, "item count {item_count}");
            assert_eq!(declared, required, "item count {item_count}");
        }
    }

    #[test]
    fn scope_dfa_table_expression_degree_matches_bound() {
        let eval = MdocScopeDfaTableEval {
            log_size: 16,
            dfa_relation: MdocScopeDfaRelation::dummy(),
            claim_mask_beta: None,
        };
        let declared = eval.max_constraint_log_degree_bound();
        let measured = symbolic_max_degree(eval);

        // ExprEvaluator records the linear numerator supplied to LogUp. The
        // framework's recurrence still receives the mandatory one-bit domain
        // headroom represented by the declared log+1 bound.
        assert_eq!(measured, 1);
        assert_eq!(declared, 17);
    }

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

    fn encoded_full_date(value: &[u8; 10]) -> Vec<u8> {
        encoded_tag(1004, &cbor_text(value))
    }

    fn encoded_nationalities(values: &[&[u8; 2]]) -> Vec<u8> {
        encoded_array(
            &values
                .iter()
                .map(|value| cbor_text(value.as_slice()))
                .collect::<Vec<_>>(),
        )
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

    fn digest_map(digest_ids: &[u64]) -> Vec<u8> {
        let entries = digest_ids
            .iter()
            .map(|id| {
                (
                    cbor_head(0, *id),
                    encoded_bstr(&[u8::try_from(id & 0xff).unwrap(); 32]),
                )
            })
            .collect::<Vec<_>>();
        encoded_map(&entries)
    }

    fn value_digests(namespace: &[u8], digest_ids: &[u64]) -> Vec<u8> {
        encoded_map(&[(cbor_text(namespace), digest_map(digest_ids))])
    }

    fn mso_entries(
        statement: &MdocScopeStatement,
        digest_ids: &[u64],
        signed: &str,
        valid_from: &str,
        valid_until: &str,
    ) -> Vec<(Vec<u8>, Vec<u8>)> {
        vec![
            (cbor_text(b"version"), cbor_text(b"2.0")),
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

    fn product_statement(nationality: bool) -> MdocScopeStatement {
        let mut items = vec![MdocScopeItem {
            element_identifier: b"birth_date".to_vec(),
            mode: MdocScopeMode::AgeOver,
        }];
        if nationality {
            items.push(MdocScopeItem {
                element_identifier: b"nationality".to_vec(),
                mode: MdocScopeMode::Alpha2Set,
            });
        }
        MdocScopeStatement {
            request_binding: [0x42; 32],
            doc_type: b"eu.europa.ec.eudi.pid.1".to_vec(),
            namespace: b"eu.europa.ec.eudi.pid.1".to_vec(),
            items,
        }
    }

    fn product_item_inners(nationalities: &[&[u8; 2]]) -> Vec<Vec<u8>> {
        let birth_date = encoded_map(&item_entries(
            16,
            7,
            b"birth_date",
            encoded_full_date(b"1990-01-02"),
        ));
        let nationality_value = encoded_nationalities(nationalities);
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
        let handles = MdocScopeHandles::fresh(&statement, SharedPackedShaDigestRelation::new())?;
        MdocScope::new(statement, issuer, items, handles)
    }

    fn construct_product(
        nationalities: &[&[u8; 2]],
        wrapped_mso: bool,
    ) -> Result<MdocScope, MdocScopeError> {
        let statement = product_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        construct(
            statement,
            mso,
            product_item_inners(nationalities),
            wrapped_mso,
        )
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
                    ScopeAction::NatAlphaFirst => row.applied.before.position * 2,
                    ScopeAction::NatAlphaStay | ScopeAction::NatAlphaExit => {
                        row.applied.before.position * 2 + 1
                    }
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
    fn product_rejects_direct_mso_and_exposes_wrapped_parser_order() {
        assert!(construct_product(&[b"FR", b"DE"], false).is_err());
        let wrapped = construct_product(&[b"FR", b"DE"], true).unwrap();

        assert_eq!(wrapped.private_nationality_count(), Some(2));
        assert_eq!(wrapped.parser_stream_bytes().len(), 7);
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
    fn accepts_reordered_top_validity_and_cose_maps() {
        let statement = product_statement(true);
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
            product_item_inners(&[b"FR"]),
            true,
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong_cose_sig_structure_context_protected_or_external_aad() {
        let statement = product_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let payload = encoded_tag(24, &encoded_bstr(&mso));
        let inners = product_item_inners(&[b"FR"]);
        for issuer in [
            sig_structure(b"Signature", &[0xa1, 0x01, 0x26], &[], &payload),
            sig_structure(b"Signature1", &[0xa1, 0x01, 0x27], &[], &payload),
            sig_structure(b"Signature1", &[0xa1, 0x01, 0x26], &[0], &payload),
        ] {
            let handles =
                MdocScopeHandles::fresh(&statement, SharedPackedShaDigestRelation::new()).unwrap();
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
        let statement = product_statement(true);
        let inners = product_item_inners(&[b"FR"]);

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
                true,
            )
            .is_err());
        }
    }

    #[test]
    fn accepts_unordered_digest_ids_but_rejects_duplicates_missing_and_oversized_ids() {
        let statement = product_statement(true);
        let inners = product_item_inners(&[b"FR"]);
        let unordered = encoded_map(&mso_entries(
            &statement,
            &[9, 7],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        construct(statement.clone(), unordered, inners.clone(), true).unwrap();

        for ids in [vec![7, 7], vec![7], vec![7, u64::from(u16::MAX) + 1]] {
            let mso = encoded_map(&mso_entries(
                &statement,
                &ids,
                VALID_SIGNED,
                VALID_FROM,
                VALID_UNTIL,
            ));
            assert!(construct(statement.clone(), mso, inners.clone(), true).is_err());
        }

        // Both selected and unrequested entries use the same uniqueness
        // relation. A repeated unrequested ID must fail too.
        let duplicate_unrequested = encoded_map(&mso_entries(
            &statement,
            &[7, 5, 5, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        assert!(matches!(
            construct(statement, duplicate_unrequested, inners, true),
            Err(MdocScopeError::DuplicateDigestId(5))
        ));
    }

    #[test]
    fn permits_unordered_unrequested_digest_entries_but_still_selects_every_item() {
        let statement = product_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[9, 5, 8, 7],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let scope = construct(statement, mso, product_item_inners(&[b"FR"]), true).unwrap();
        assert_eq!(scope.private_nationality_count(), Some(1));
    }

    #[test]
    fn private_digest_ids_select_the_right_mso_entry_independent_of_item_order() {
        let statement = product_statement(true);
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
            encoded_full_date(b"1990-01-02"),
        ));
        let nationality = encoded_map(&item_entries(
            16,
            7,
            b"nationality",
            encoded_nationalities(&[b"FR"]),
        ));

        let scope = construct(statement, mso, vec![birth_date, nationality], true).unwrap();
        let witness = scope.witness.as_ref().unwrap();
        assert_eq!(witness.item_digest_bytes[0], [9; 32]);
        assert_eq!(witness.item_digest_bytes[1], [7; 32]);
    }

    #[test]
    fn rejects_short_random_duplicate_item_key_v2_reordering_and_trailing_inner_cbor() {
        let statement = product_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let valid = product_item_inners(&[b"FR"]);

        let short_random = encoded_map(&item_entries(
            15,
            7,
            b"birth_date",
            encoded_full_date(b"1990-01-02"),
        ));

        let mut duplicate_entries =
            item_entries(16, 7, b"birth_date", encoded_full_date(b"1990-01-02"));
        duplicate_entries[3].0 = duplicate_entries[0].0.clone();
        let duplicate_key = encoded_map(&duplicate_entries);

        let mut reordered_entries =
            item_entries(16, 7, b"birth_date", encoded_full_date(b"1990-01-02"));
        reordered_entries.swap(2, 3);
        let reordered = encoded_map(&reordered_entries);

        let mut trailing = valid[0].clone();
        trailing.push(0xf6);

        for malformed in [short_random, duplicate_key, reordered, trailing] {
            assert!(construct(
                statement.clone(),
                mso.clone(),
                vec![malformed, valid[1].clone()],
                true,
            )
            .is_err());
        }
    }

    #[test]
    fn rejects_nonminimal_and_trailing_cbor() {
        let statement = product_statement(true);
        let inners = product_item_inners(&[b"FR"]);
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
            construct(statement.clone(), nonminimal, inners.clone(), true),
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
        assert!(construct(statement, trailing, inners, true).is_err());
    }

    #[test]
    fn rejects_malformed_or_out_of_range_tdates() {
        let statement = product_statement(true);
        let inners = product_item_inners(&[b"FR"]);
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
                    construct(statement.clone(), mso, inners.clone(), true).is_err(),
                    "accepted malformed tdate {value} at validity slot {position}"
                );
            }
        }
    }

    #[test]
    fn accepts_exact_gregorian_leap_boundaries() {
        let statement = product_statement(true);
        let inners = product_item_inners(&[b"FR"]);
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
            construct(statement.clone(), mso, inners.clone(), true)
                .unwrap_or_else(|error| panic!("rejected valid Gregorian date {value}: {error}"));
        }
    }

    #[test]
    fn expected_update_is_omitted_or_a_valid_tdate_never_null() {
        let statement = product_statement(true);
        let inners = product_item_inners(&[b"FR"]);

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
            true,
        )
        .unwrap();

        let mut with_null = mso_entries(&statement, &[7, 9], VALID_SIGNED, VALID_FROM, VALID_UNTIL);
        with_null[5].1 =
            validity_info_with_expected_update(VALID_SIGNED, VALID_FROM, VALID_UNTIL, vec![0xf6]);
        assert!(
            construct(statement, encoded_map(&with_null), inners, true).is_err(),
            "present expectedUpdate must be a tdate, not null"
        );
    }

    #[test]
    fn emits_every_array_nationality_entry_at_fixed_indices() {
        let array = construct_product(&[b"FR", b"DE", b"US"], true).unwrap();
        assert_eq!(array.private_nationality_count(), Some(3));
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
    fn rejects_bare_birth_date_and_scalar_nationality() {
        let statement = product_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let valid = product_item_inners(&[b"FR"]);
        let bare_birth_date = encoded_map(&item_entries(
            16,
            7,
            b"birth_date",
            cbor_text(b"1990-01-02"),
        ));
        let scalar_nationality =
            encoded_map(&item_entries(16, 9, b"nationality", cbor_text(b"FR")));

        assert!(construct(
            statement.clone(),
            mso.clone(),
            vec![bare_birth_date, valid[1].clone()],
            true,
        )
        .is_err());
        assert!(construct(
            statement,
            mso,
            vec![valid[0].clone(), scalar_nationality],
            true,
        )
        .is_err());
    }

    #[test]
    fn rejects_nationality_arrays_above_the_public_bound() {
        let statement = product_statement(true);
        let mso = encoded_map(&mso_entries(
            &statement,
            &[7, 9],
            VALID_SIGNED,
            VALID_FROM,
            VALID_UNTIL,
        ));
        let mut inners = product_item_inners(&[b"FR"]);
        let nationalities = (0..=MAX_PRESENTED_NATIONALITIES)
            .map(|_| cbor_text(b"FR"))
            .collect::<Vec<_>>();
        inners[1] = encoded_map(&item_entries(
            16,
            9,
            b"nationality",
            encoded_array(&nationalities),
        ));

        assert!(construct(statement, mso, inners, true).is_err());
    }

    #[test]
    fn public_identifiers_must_be_utf8() {
        let mut statement = product_statement(false);
        statement.doc_type = vec![0xff];
        assert!(matches!(
            statement.validate(),
            Err(MdocScopeError::WrongShape("public identifier UTF-8"))
        ));

        let mut statement = product_statement(false);
        statement.items[0].element_identifier = vec![0xff];
        assert!(matches!(
            statement.validate(),
            Err(MdocScopeError::WrongShape("element identifier UTF-8"))
        ));
    }

    #[test]
    fn table_multiplicity_padding_is_freshly_blinded() {
        let scope = construct_product(&[b"FR"], true).unwrap();
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
        // columns are bit-reverse ordered, so compare them wholesale. The
        // deterministic edge prefix is covered by the honest-table test.)
        assert_ne!(first_values, second_values);
    }

    #[test]
    fn payload_hash_interaction_site_is_opt_in() {
        let mut default_scope = construct_product(&[b"FR", b"DE"], true).unwrap();
        let default_sites = default_scope.n_interaction_sites();
        let default_interaction_columns = default_scope.layout().interaction.len();
        default_scope.draw_relations(&mut Blake2sChannel::default());
        assert!(!default_scope.handles.payload_hash_fields.is_set());

        let mut bound_scope = construct_product(&[b"FR", b"DE"], true)
            .unwrap()
            .with_payload_hash_binding();
        assert_eq!(bound_scope.n_interaction_sites(), default_sites + 1);
        let expected_columns = (default_sites + 1).div_ceil(2) * SECURE_EXTENSION_DEGREE
            + bound_scope.n_table_interaction_sites().div_ceil(2) * SECURE_EXTENSION_DEGREE
            + bound_scope
                .n_digest_id_uniqueness_interaction_sites()
                .div_ceil(2)
                * SECURE_EXTENSION_DEGREE;
        assert_eq!(bound_scope.layout().interaction.len(), expected_columns);
        // Pairing parity may absorb the extra site into an existing column.
        assert!(bound_scope.layout().interaction.len() >= default_interaction_columns);
        bound_scope.draw_relations(&mut Blake2sChannel::default());
        assert!(bound_scope.handles.payload_hash_fields.is_set());
    }

    #[test]
    fn honest_scope_trace_and_logup_satisfy_the_complete_component() {
        let scope = construct_product(&[b"FR", b"DE"], true)
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
            [0x42; 32],
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
        let item_digest_relation = PackedShaDigestRelation::dummy();
        let semantic_relation = FieldBytesRelation::dummy();
        let payload_hash_relation = FieldBytesRelation::dummy();
        let dfa_relation = MdocScopeDfaRelation::dummy();
        let state_relation = MdocScopeStateRelation::dummy();
        let digest_id_relation = MdocScopeDigestIdRelation::dummy();
        let digest_id_uniqueness_relation = MdocScopeDigestIdUniquenessRelation::dummy();
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
            &item_digest_relation,
            scope.statement.items.len(),
            &dfa_relation,
            &state_relation,
            &digest_id_relation,
            &digest_id_uniqueness_relation,
            &digest_byte_relation,
            None,
            None,
        );
        let compact_base =
            ScopeActiveInteractionBase::new(scope.metadata.log_size, &columns, witness);
        let (compact_interaction, compact_claimed_sum) = scope_interaction_trace(
            scope.metadata.log_size,
            &columns,
            &compact_base,
            &preprocessed,
            &stream_ids,
            &scope.raw_target_stream_ids(),
            &parsed_relations,
            &raw_relations,
            &semantic_relation,
            Some(&payload_hash_relation),
            &item_digest_relation,
            scope.statement.items.len(),
            &dfa_relation,
            &state_relation,
            &digest_id_relation,
            &digest_id_uniqueness_relation,
            &digest_byte_relation,
            None,
            None,
        );
        assert_eq!(compact_claimed_sum, claimed_sum);
        assert_eq!(compact_interaction.len(), interaction.len());
        for (compact, full) in compact_interaction.iter().zip(interaction.iter()) {
            assert_eq!(
                compact
                    .data
                    .iter()
                    .flat_map(|value| value.to_array())
                    .collect::<Vec<_>>(),
                full.data
                    .iter()
                    .flat_map(|value| value.to_array())
                    .collect::<Vec<_>>(),
            );
        }
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
            &item_digest_relation,
            scope.statement.items.len(),
            &dfa_relation,
            &state_relation,
            &digest_id_relation,
            &digest_id_uniqueness_relation,
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
            item_digest_relation,
            item_count: scope.statement.items.len(),
            dfa_relation,
            state_relation,
            digest_id_relation,
            digest_id_uniqueness_relation,
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
        let scope = construct_product(&[b"FR", b"DE"], true).unwrap();
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

    #[test]
    fn digest_id_universe_accepts_bits_and_rejects_multiplicity_two() {
        let relation = MdocScopeDigestIdUniquenessRelation::dummy();
        let mut multiplicities = vec![0u32; 1 << DIGEST_ID_UNIVERSE_LOG_SIZE];
        for id in [5usize, 7, 9] {
            multiplicities[id] = 1;
        }

        let assert_trace = |multiplicities: &[u32]| {
            let multiplicity = digest_id_uniqueness_trace(multiplicities);
            let (interaction, claimed_sum) =
                digest_id_uniqueness_interaction_trace(&multiplicity, &relation, None);
            let trees = TreeVec::new(vec![
                vec![digest_id_universe_column().to_cpu().values],
                vec![multiplicity.to_cpu().values],
                interaction
                    .into_iter()
                    .map(|column| column.to_cpu().values)
                    .collect(),
            ]);
            let trace = trees.as_cols_ref();
            let eval = MdocScopeDigestIdUniverseEval {
                relation: relation.clone(),
                claim_mask_beta: None,
            };
            assert_constraints_on_trace(
                &trace,
                DIGEST_ID_UNIVERSE_LOG_SIZE,
                |row| {
                    let _ = eval.evaluate(row);
                },
                claimed_sum,
            );
        };

        assert_trace(&multiplicities);
        multiplicities[5] = 2;
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                assert_trace(&multiplicities);
            }))
            .is_err(),
            "the Boolean universe multiplicity constraint must reject two uses of one ID",
        );
    }

    #[test]
    fn duplicate_selected_or_unknown_digest_id_breaks_uniqueness_balance() {
        let relation = MdocScopeDigestIdUniquenessRelation::dummy();
        let zero = QM31::from_u32_unchecked(0, 0, 0, 0);
        let inverse = |id: u32| {
            <MdocScopeDigestIdUniquenessRelation as Relation<M31, QM31>>::combine(
                &relation,
                &[m31(id)],
            )
            .inverse()
        };
        let consume = |ids: &[u32]| ids.iter().copied().fold(zero, |sum, id| sum + inverse(id));
        let provide = |ids: &[u32]| ids.iter().copied().fold(zero, |sum, id| sum - inverse(id));

        let honest_ids = [7, 5, 9];
        assert_eq!(consume(&honest_ids) + provide(&honest_ids), zero);

        // This models selected(7), unknown(7), selected(9). The provider can
        // yield each universe value at most once, so the repeated 7 remains.
        assert_ne!(consume(&[7, 7, 9]) + provide(&[7, 9]), zero);
        // A repeated unrequested entry is rejected by the same relation.
        assert_ne!(consume(&[7, 5, 5, 9]) + provide(&[7, 5, 9]), zero);
    }

    /// Confirms the cross-component LogUp balance for the shared DFA relation.
    ///
    /// Walk consumes must cancel table yields.
    /// A changed multiplicity leaves a nonzero residue.
    /// The global claimed-sum check rejects this residue.
    #[test]
    fn tampered_table_multiplicity_breaks_cross_component_dfa_balance() {
        let scope = construct_product(&[b"FR", b"DE"], true).unwrap();
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
            scope.table_edges.iter().zip(multiplicities).fold(
                zero,
                |sum, (&(slot, edge), &multiplicity)| {
                    let denominator: QM31 = dfa_relation.combine(&edge.tuple(slot).map(m31));
                    sum - denominator.inverse() * QM31::from(m31(multiplicity))
                },
            )
        };

        let honest =
            walk_consume_sum(&witness.active_rows) + table_yield_sum(&witness.table_multiplicities);
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
