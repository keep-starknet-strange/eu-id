//! Sponge-chain glue for the composed statement (M6): HashIo *bridges* and a
//! public-prefix *producer* that stitch the three SHAKE-256 chains together.
//!
//! All three chains and every mldsa component draw the SAME
//! [`crate::binding::HashIoRelation`] (re-exported from stwo-keccak), so a byte
//! yielded (+) on one stream and required (−) on another balances through the
//! global LogUp. These small components move bytes between streams:
//!
//! - [`PublicPrefixProducer`] — yields fixed PUBLIC bytes (tr ‖ 0x00 ‖ 0x00) into
//!   the µ-absorb stream. Byte values are preprocessed constants (public); no
//!   consume side. Mirrors `stwo_keccak::sponge::io_provider`'s absorb-yield.
//! - [`Bridge`] — for each `i` requires `(src_stream, src_off+i, byte)` (−) and
//!   yields `(dst_stream, dst_off+i, byte)` (+), where `byte` is ONE committed
//!   trace cell used on BOTH sides (so the moved byte is provably identical; no
//!   value constraint needed). Used for µ→c̃, w1Encode→c̃, c̃→SIB seams. A variant
//!   with `src_relation = MsgLink` bridges the message-byte producer into µ-absorb.
//!
//! Every constraint here is degree ≤ 2 (enabler boolean + degree-1 HashIo/MsgLink
//! uses), so `max_constraint_log_degree_bound == log_size + 1`.

#![allow(clippy::needless_range_loop)]

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use air_core::relations::FieldBytesRelation;

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::binding::{HashIoRelation, MsgLinkRelation};

// =============================================================================
// Public-prefix producer: yields fixed PUBLIC bytes into a stream.
// =============================================================================

/// A component that yields a list of PUBLIC bytes into `dst_stream` at positions
/// `dst_off + i`. The bytes are Eval CONSTANTS (both sides construct the Eval
/// from public data — the `io_provider` pattern), so the yielded tuples are
/// pinned to the public values with no committable cell to forge. Single packed
/// row (`LOG_N_LANES`), lane-0 enabler.
#[derive(Clone)]
pub struct PublicPrefixEval {
    pub dst_stream: u32,
    pub dst_off: u32,
    pub bytes: Vec<u8>,
    pub hash_io: HashIoRelation,
}

/// Fixed log-size of the lane-0 link components (prefix producer).
pub const LINK_LOG_SIZE: u32 = stwo::prover::backend::simd::m31::LOG_N_LANES;

impl PublicPrefixEval {
    /// Interaction columns: one paired QM31 fraction column per two bytes.
    pub fn n_interaction_cols(&self) -> usize {
        self.bytes.len().div_ceil(2) * SECURE_EXTENSION_DEGREE
    }
    /// Base trace: the lane-0 enabler column.
    pub fn gen_base(&self) -> Vec<ColEval> {
        let rows = 1usize << LINK_LOG_SIZE;
        let mut enabler = vec![m31(0); rows];
        enabler[0] = m31(1);
        vec![col_eval(LINK_LOG_SIZE, enabler)]
    }
    pub fn gen_interaction(&self) -> (Vec<ColEval>, SecureField) {
        let entries: Vec<(bool, SecureField)> = self
            .bytes
            .iter()
            .enumerate()
            .map(|(i, &b)| {
                let tuple = [m31(self.dst_stream), m31(self.dst_off + i as u32), m31(b as u32)];
                (true, self.hash_io.combine(&tuple))
            })
            .collect();
        gen_lane0_fracs(&entries)
    }
}

impl FrameworkEval for PublicPrefixEval {
    fn log_size(&self) -> u32 {
        LINK_LOG_SIZE
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        LINK_LOG_SIZE + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let en = E::EF::from(enabler);
        for (i, &b) in self.bytes.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.hash_io,
                en.clone(),
                &[
                    E::F::from(m31(self.dst_stream)),
                    E::F::from(m31(self.dst_off + i as u32)),
                    E::F::from(m31(b as u32)),
                ],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type PublicPrefixComponent = FrameworkComponent<PublicPrefixEval>;

/// Pair-batched lane-0 fraction column builder (`(is_yield, denom)` per entry).
fn gen_lane0_fracs(entries: &[(bool, SecureField)]) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    let mut gen = LogupTraceGenerator::new(LINK_LOG_SIZE);
    let fracs: Vec<(PackedQM31, PackedQM31)> = entries
        .iter()
        .map(|&(pos, d)| {
            let mut n = [zero; N_LANES];
            let mut dl = [one; N_LANES];
            n[0] = if pos { one } else { -one };
            dl[0] = d;
            (PackedQM31::from_array(n), PackedQM31::from_array(dl))
        })
        .collect();
    let mut i = 0;
    while i + 2 <= fracs.len() {
        let mut col = gen.new_col();
        let (n0, d0) = fracs[i];
        let (n1, d1) = fracs[i + 1];
        col.write_frac(0, n0 * d1 + n1 * d0, d0 * d1);
        col.finalize_col();
        i += 2;
    }
    if i < fracs.len() {
        let mut col = gen.new_col();
        let (n, d) = fracs[i];
        col.write_frac(0, n, d);
        col.finalize_col();
    }
    gen.finalize_last()
}

// =============================================================================
// Public-message producer: yields a PUBLIC byte stream into µ-absorb (S4).
// =============================================================================

/// FNV-1a 64-bit over the producer's shape + content, for I-5 content-encoded
/// preprocessed ids: two producers with different public messages can never
/// alias under air-core tree-0 first-writer-wins dedup.
fn fnv1a64(dst_off: u32, bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut eat = |b: u8| {
        hash ^= u64::from(b);
        hash = hash.wrapping_mul(0x100_0000_01b3);
    };
    for b in dst_off.to_le_bytes() {
        eat(b);
    }
    for b in (bytes.len() as u64).to_le_bytes() {
        eat(b);
    }
    for &b in bytes {
        eat(b);
    }
    hash
}

/// A TALL public-byte producer (S4): one row per message byte, yielding
/// `(dst_stream, dst_off + i, byte)` (+) into the shared HashIo relation —
/// exactly what the msg bridge's dest side does, with NO source consumption
/// and NO committed byte cells. The byte values and positions are PREPROCESSED
/// content (the message is a PUBLIC statement input).
///
/// Soundness (which mechanism is load-bearing): the absorbed message is bound
/// to the statement by (1) `mix_public` mixing the statement's message bytes
/// into Fiat–Shamir, and (2) the in-circuit ML-DSA verification itself — an
/// adversary committing preprocessed content for a different message M′ must
/// exhibit a signature valid for M′, i.e. forge ML-DSA. The host-side
/// preprocessed-root pin (mdoc recomputes tree-0 per statement) additionally
/// pins the committed bytes to the statement fail-closed. The fnv-content ids
/// only prevent cross-instance dedup aliasing (I-5); they are not the binding.
///
/// Every constraint is degree ≤ 2 (`max_constraint_log_degree_bound ==
/// log_size + 1` — engine requirement).
#[derive(Clone)]
pub struct PubMsgEval {
    /// Instance namespace ("" = single-instance ids).
    pub ns: String,
    pub log_size: u32,
    pub dst_stream: u32,
    pub dst_off: u32,
    pub bytes: Vec<u8>,
    pub hash_io: HashIoRelation,
}

/// Base column count of the public-message producer (`enabler` only).
pub const PUBMSG_BASE_COLS: usize = 1;
/// Interaction columns (one yield, unbatched).
pub const PUBMSG_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;
/// Preprocessed column count (`active`, `pos`, `byte`).
pub const PUBMSG_PREPROCESSED_COLS: usize = 3;

impl PubMsgEval {
    fn pre_id(&self, name: &str) -> PreProcessedColumnId {
        // I-5: encode shape + content (fnv of dst_off ‖ len ‖ bytes).
        PreProcessedColumnId {
            id: format!(
                "{}mldsa_pubmsg_{:016x}_{name}",
                ns_prefix(&self.ns),
                fnv1a64(self.dst_off, &self.bytes)
            ),
        }
    }
    pub fn preprocessed_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![self.pre_id("active"), self.pre_id("pos"), self.pre_id("byte")]
    }
    pub fn gen_preprocessed(&self) -> Vec<ColEval> {
        let rows = 1usize << self.log_size;
        let mut active = vec![m31(0); rows];
        let mut pos = vec![m31(0); rows];
        let mut byte = vec![m31(0); rows];
        for (i, &b) in self.bytes.iter().enumerate() {
            active[i] = m31(1);
            pos[i] = m31(self.dst_off + i as u32);
            byte[i] = m31(b as u32);
        }
        vec![active, pos, byte]
            .into_iter()
            .map(|v| col_eval(self.log_size, v))
            .collect()
    }
    /// Base trace: the enabler column (mirrors the preprocessed `active`).
    pub fn gen_base(&self) -> Vec<ColEval> {
        let rows = 1usize << self.log_size;
        let mut enabler = vec![m31(0); rows];
        for i in 0..self.bytes.len() {
            enabler[i] = m31(1);
        }
        vec![col_eval(self.log_size, enabler)]
    }
    pub fn gen_interaction(&self) -> (Vec<ColEval>, SecureField) {
        gen_single_yield(
            self.log_size,
            &self.hash_io,
            self.bytes.len(),
            |i| {
                [
                    m31(self.dst_stream),
                    m31(self.dst_off + i as u32),
                    m31(self.bytes[i] as u32),
                ]
            },
            true, // yield (+) into the absorb stream (the sponge consumes with −)
        )
    }
}

impl FrameworkEval for PubMsgEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(self.pre_id("active"));
        let pos = eval.get_preprocessed_column(self.pre_id("pos"));
        let byte = eval.get_preprocessed_column(self.pre_id("byte"));
        let enabler = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let tuple = [E::F::from(m31(self.dst_stream)), pos, byte];
        eval.add_to_relation(RelationEntry::base(&self.hash_io, active, &tuple));
        let _ = enabler;
        eval.finalize_logup();
        eval
    }
}

pub type PubMsgComponent = FrameworkComponent<PubMsgEval>;

// =============================================================================
// Bridge: require a byte on a source stream, yield it on a destination stream.
// =============================================================================

/// Which relation the bridge REQUIRES on its source side.
#[derive(Clone)]
pub enum SrcRelation {
    /// `(src_stream, src_off+i, byte)` on the shared HashIo relation.
    HashIo(HashIoRelation, u32, u32),
    /// `(field_id, byte_index, byte)` on the MsgLink relation (the msg producer).
    MsgLink(MsgLinkRelation, u32),
    /// `(field_id, byte_index, byte)` on the SHARED [`FieldBytesRelation`] (the
    /// hosted-mode message source: the host's SHA field-exposure yields the
    /// Sig_structure bytes under this relation). Same tuple shape as `MsgLink`.
    FieldBytes(FieldBytesRelation, u32),
}

/// Instance-namespace prefix for preprocessed ids. Empty namespace keeps the
/// legacy (single-instance) id format; a non-empty namespace makes the ids of
/// two hosted ML-DSA instances disjoint so air-core tree-0 first-writer-wins
/// dedup cannot alias one instance's shape-dependent columns to the other's.
pub(crate) fn ns_prefix(ns: &str) -> String {
    if ns.is_empty() { String::new() } else { format!("{ns}/") }
}

fn bridge_pre_id(ns: &str, tag: &str, name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId { id: format!("{}mldsa_bridge_{tag}_{name}", ns_prefix(ns)) }
}

/// A HashIo bridge: for each of `len` rows, requires the source tuple (−) and
/// yields `(dst_stream, dst_off+i, byte)` (+), where `byte` is a single committed
/// trace cell used on both sides.
#[derive(Clone)]
pub struct BridgeEval {
    pub tag: &'static str,
    /// Instance namespace ("" = legacy single-instance ids).
    pub ns: String,
    pub log_size: u32,
    pub src: SrcRelation,
    pub dst_stream: u32,
    pub dst_off: u32,
    pub len: usize,
    pub hash_io: HashIoRelation,
}

impl BridgeEval {
    fn active_col(&self) -> PreProcessedColumnId {
        bridge_pre_id(&self.ns, self.tag, "active")
    }
    fn idx_col(&self) -> PreProcessedColumnId {
        bridge_pre_id(&self.ns, self.tag, "idx")
    }
    pub fn preprocessed_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![self.active_col(), self.idx_col()]
    }
    pub fn gen_preprocessed(&self) -> Vec<ColEval> {
        let rows = 1usize << self.log_size;
        let mut active = vec![m31(0); rows];
        let mut idx = vec![m31(0); rows];
        for i in 0..self.len {
            active[i] = m31(1);
            idx[i] = m31(i as u32);
        }
        vec![active, idx].into_iter().map(|v| col_eval(self.log_size, v)).collect()
    }
    /// Base trace: enabler + the moved byte per row.
    pub fn gen_base(&self, bytes: &[u8]) -> Vec<ColEval> {
        assert_eq!(bytes.len(), self.len, "bridge byte count mismatch");
        let rows = 1usize << self.log_size;
        let mut enabler = vec![m31(0); rows];
        let mut byte = vec![m31(0); rows];
        for (i, &b) in bytes.iter().enumerate() {
            enabler[i] = m31(1);
            byte[i] = m31(b as u32);
        }
        vec![enabler, byte].into_iter().map(|v| col_eval(self.log_size, v)).collect()
    }
    pub fn gen_interaction(&self, bytes: &[u8]) -> (Vec<ColEval>, SecureField) {
        // Two fractions per row: source require (−), dest yield (+).
        let zero = SecureField::from(m31(0));
        let one = SecureField::one();
        let row_lookup = circle_row_to_coset(self.log_size);
        let vec_rows = 1usize << (self.log_size - stwo::prover::backend::simd::m31::LOG_N_LANES);
        let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();
        let mut claimed = zero;
        let push = |frac: &dyn Fn(usize) -> (SecureField, SecureField),
                    entries: &mut Vec<(Vec<PackedQM31>, Vec<PackedQM31>)>,
                    claimed: &mut SecureField| {
            let mut nums = Vec::with_capacity(vec_rows);
            let mut dens = Vec::with_capacity(vec_rows);
            for vr in 0..vec_rows {
                let mut n = [zero; N_LANES];
                let mut d = [one; N_LANES];
                for lane in 0..N_LANES {
                    let coset = row_lookup[vr * N_LANES + lane];
                    let (num, den) = frac(coset);
                    n[lane] = num;
                    d[lane] = den;
                    *claimed += num / den;
                }
                nums.push(PackedQM31::from_array(n));
                dens.push(PackedQM31::from_array(d));
            }
            entries.push((nums, dens));
        };
        // source require. Sign is per-relation convention: HashIo/MsgLink
        // producers yield (+) so the bridge requires (−); the stwo-sha256
        // field provider emits its FieldBytes tuples with (−) (see
        // `constraints.rs`' `-selector` yield), so the bridge requires (+).
        push(&|coset| {
            if coset < self.len {
                let b = m31(bytes[coset] as u32);
                let (sign, den) = match &self.src {
                    SrcRelation::HashIo(r, s, off) => {
                        (-one, r.combine(&[m31(*s), m31(off + coset as u32), b]))
                    }
                    SrcRelation::MsgLink(r, fid) => {
                        (-one, r.combine(&[m31(*fid), m31(coset as u32), b]))
                    }
                    SrcRelation::FieldBytes(r, fid) => {
                        (one, r.combine(&[m31(*fid), m31(coset as u32), b]))
                    }
                };
                (sign, den)
            } else {
                (zero, one)
            }
        }, &mut entries, &mut claimed);
        // dest yield (+).
        push(&|coset| {
            if coset < self.len {
                let b = m31(bytes[coset] as u32);
                let den = self.hash_io.combine(&[m31(self.dst_stream), m31(self.dst_off + coset as u32), b]);
                (one, den)
            } else {
                (zero, one)
            }
        }, &mut entries, &mut claimed);

        let mut logup = LogupTraceGenerator::new(self.log_size);
        for chunk in entries.chunks(1) {
            logup.col_from_fn(|vr| (chunk[0].0[vr], chunk[0].1[vr]));
        }
        let (trace, claimed_sum) = logup.finalize_last();
        debug_assert_eq!(claimed_sum, claimed, "bridge logup claimed sum mismatch");
        (trace, claimed_sum)
    }
}

impl FrameworkEval for BridgeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(self.active_col());
        let idx = eval.get_preprocessed_column(self.idx_col());
        let enabler = eval.next_trace_mask();
        let byte = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));

        // Source require (−active).
        match &self.src {
            SrcRelation::HashIo(r, s, off) => {
                let pos = E::F::from(m31(*off)) + idx.clone();
                let tuple = [E::F::from(m31(*s)), pos, byte.clone()];
                eval.add_to_relation(RelationEntry::base(r, -active.clone(), &tuple));
            }
            SrcRelation::MsgLink(r, fid) => {
                let tuple = [E::F::from(m31(*fid)), idx.clone(), byte.clone()];
                eval.add_to_relation(RelationEntry::base(r, -active.clone(), &tuple));
            }
            SrcRelation::FieldBytes(r, fid) => {
                // (+active): the stwo-sha256 field provider emits with (−);
                // see the sign note in `gen_interaction`.
                let tuple = [E::F::from(m31(*fid)), idx.clone(), byte.clone()];
                eval.add_to_relation(RelationEntry::base(r, active.clone(), &tuple));
            }
        }
        // Dest yield (+active).
        let dpos = E::F::from(m31(self.dst_off)) + idx;
        let dtuple = [E::F::from(m31(self.dst_stream)), dpos, byte];
        eval.add_to_relation(RelationEntry::base(&self.hash_io, active, &dtuple));

        let _ = enabler;
        eval.finalize_logup();
        eval
    }
}

pub type BridgeComponent = FrameworkComponent<BridgeEval>;

// =============================================================================
// Squeeze sink: consume (−) the unused tail of a sponge's squeeze stream.
// =============================================================================

/// A sponge squeezes `n_squeeze · 136` bytes and YIELDS every one on its squeeze
/// stream. Downstream consumers (bridges / the FSM) only require the useful
/// prefix; the remaining yielded bytes need a consumer or the LogUp is
/// unbalanced. `SqueezeSink` requires `(stream, off+i, byte)` (−) for the tail
/// `off..off+len`, committing each `byte` as a trace cell. The sink's bytes are
/// the sponge's actual squeezed bytes (public-derivable from the witness), so it
/// is not a soundness surface — it only closes the balance.
#[derive(Clone)]
pub struct SqueezeSinkEval {
    pub tag: &'static str,
    /// Instance namespace ("" = legacy single-instance ids).
    pub ns: String,
    pub log_size: u32,
    pub stream: u32,
    pub off: u32,
    pub len: usize,
    pub hash_io: HashIoRelation,
}

impl SqueezeSinkEval {
    fn active_col(&self) -> PreProcessedColumnId {
        PreProcessedColumnId { id: format!("{}mldsa_sink_{}_active", ns_prefix(&self.ns), self.tag) }
    }
    fn pos_col(&self) -> PreProcessedColumnId {
        PreProcessedColumnId { id: format!("{}mldsa_sink_{}_pos", ns_prefix(&self.ns), self.tag) }
    }
    pub fn preprocessed_ids(&self) -> Vec<PreProcessedColumnId> {
        vec![self.active_col(), self.pos_col()]
    }
    pub fn gen_preprocessed(&self) -> Vec<ColEval> {
        let rows = 1usize << self.log_size;
        let mut active = vec![m31(0); rows];
        let mut pos = vec![m31(0); rows];
        for i in 0..self.len {
            active[i] = m31(1);
            pos[i] = m31(self.off + i as u32);
        }
        vec![active, pos].into_iter().map(|v| col_eval(self.log_size, v)).collect()
    }
    pub fn gen_base(&self, bytes: &[u8]) -> Vec<ColEval> {
        assert_eq!(bytes.len(), self.len, "sink byte count mismatch");
        let rows = 1usize << self.log_size;
        let mut enabler = vec![m31(0); rows];
        let mut byte = vec![m31(0); rows];
        for (i, &b) in bytes.iter().enumerate() {
            enabler[i] = m31(1);
            byte[i] = m31(b as u32);
        }
        vec![enabler, byte].into_iter().map(|v| col_eval(self.log_size, v)).collect()
    }
    pub fn gen_interaction(&self, bytes: &[u8]) -> (Vec<ColEval>, SecureField) {
        gen_single_yield(
            self.log_size,
            &self.hash_io,
            self.len,
            |i| [m31(self.stream), m31(self.off + i as u32), m31(bytes[i] as u32)],
            false, // require (−)
        )
    }
}

impl FrameworkEval for SqueezeSinkEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(self.active_col());
        let pos = eval.get_preprocessed_column(self.pos_col());
        let enabler = eval.next_trace_mask();
        let byte = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let tuple = [E::F::from(m31(self.stream)), pos, byte];
        eval.add_to_relation(RelationEntry::base(&self.hash_io, -active, &tuple));
        let _ = enabler;
        eval.finalize_logup();
        eval
    }
}

pub type SqueezeSinkComponent = FrameworkComponent<SqueezeSinkEval>;

/// Base column count of a squeeze sink (`enabler`, `byte`).
pub const SINK_BASE_COLS: usize = 2;
/// Interaction columns for a squeeze sink (one require, unbatched).
pub const SINK_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

/// Base column count of a bridge (`enabler`, `byte`).
pub const BRIDGE_BASE_COLS: usize = 2;
/// Base column count of a public-prefix producer (`enabler` only).
pub const PREFIX_BASE_COLS: usize = 1;
/// Interaction columns for a bridge (source require + dest yield, unbatched).
pub const BRIDGE_INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;

/// A single-yield logup helper (one `+`/`−` fraction per active row). Builds the
/// packed numerator/denominator columns up front (the fraction closure passed to
/// `col_from_fn` must be `Sync`, so the per-coset tuple work is done here first).
fn gen_single_yield(
    log_size: u32,
    hash_io: &HashIoRelation,
    len: usize,
    tuple_of: impl Fn(usize) -> [M31; 3],
    yield_positive: bool,
) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    let signed = if yield_positive { one } else { -one };
    let row_lookup = circle_row_to_coset(log_size);
    let vec_rows = 1usize << (log_size - stwo::prover::backend::simd::m31::LOG_N_LANES);

    let mut nums = Vec::with_capacity(vec_rows);
    let mut dens = Vec::with_capacity(vec_rows);
    let mut claimed = zero;
    for vr in 0..vec_rows {
        let mut n = [zero; N_LANES];
        let mut d = [one; N_LANES];
        for lane in 0..N_LANES {
            let coset = row_lookup[vr * N_LANES + lane];
            if coset < len {
                n[lane] = signed;
                d[lane] = hash_io.combine(&tuple_of(coset));
                claimed += signed / d[lane];
            }
        }
        nums.push(PackedQM31::from_array(n));
        dens.push(PackedQM31::from_array(d));
    }
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vr| (nums[vr], dens[vr]));
    let (trace, claimed_sum) = logup.finalize_last();
    debug_assert_eq!(claimed_sum, claimed, "prefix logup claimed sum mismatch");
    (trace, claimed_sum)
}
