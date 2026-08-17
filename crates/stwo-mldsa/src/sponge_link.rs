//! Sponge-chain glue for the composed statement: HashIo *bridges* and
//! public-byte links that stitch the SHAKE-256 chains together.
//!
//! All chain components draw the same [`crate::binding::HashIoRelation`],
//! which is re-exported from stwo-keccak. A byte
//! yielded (+) on one stream and required (−) on another balances through the
//! global LogUp. These components move bytes between streams:
//!
//! - [`PublicPrefixEval`] provides or requires fixed public bytes on a HashIo
//!   stream. It feeds verifier-native `tr ‖ 0x00 ‖ 0x00` into a private
//!   µ-absorb, or verifier-native µ directly into c̃-absorb for public messages.
//! - [`BridgeEval`] requires `(src_stream, src_off+i, byte)` (−) and
//!   yields `(dst_stream, dst_off+i, byte)` (+), where `byte` is one committed
//!   trace cell used on both sides. This constrains the two values to be equal.
//!   Bridges connect private µ→c̃, w1Encode→c̃, and c̃→SIB
//!   seams. A variant with `src_relation = MsgLink` bridges private/standalone
//!   message bytes into µ-absorb.
//!
//! Every constraint here has degree 2 or less, so
//! `max_constraint_log_degree_bound == log_size + 1`.

#![allow(clippy::needless_range_loop)]

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use air_core::relations::FieldBytesRelation;

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::binding::{HashIoRelation, MsgLinkRelation};

// =============================================================================
// Public-prefix producer: yields fixed PUBLIC bytes into a stream.
// =============================================================================

/// A component that provides (`yield_positive = true`) or requires
/// (`yield_positive = false`) a list of PUBLIC bytes on `dst_stream` at
/// positions `dst_off + i`. The bytes are Eval CONSTANTS (both sides construct
/// the Eval from public data with the `io_provider` pattern. Thus, the tuples are
/// pinned to the public values with no committable cell to forge. Single packed
/// row (`LOG_N_LANES`), lane-0 enabler.
#[derive(Clone)]
pub struct PublicPrefixEval {
    pub dst_stream: u32,
    pub dst_off: u32,
    pub bytes: Vec<u8>,
    /// Number of relation entries compiled into the component. It equals
    /// `bytes.len()` for fixed inputs and the profile capacity for the
    /// variable public device message. Inactive entries use zero numerator and
    /// a canonical zero byte.
    pub entry_capacity: usize,
    pub yield_positive: bool,
    pub hash_io: HashIoRelation,
}

/// Fixed log-size of the lane-0 link components (prefix producer).
pub const LINK_LOG_SIZE: u32 = stwo::prover::backend::simd::m31::LOG_N_LANES;

impl PublicPrefixEval {
    /// Interaction columns: ONE batched accumulator column for all bytes.
    ///
    /// Every denominator is an Eval CONSTANT (the yielded tuples are public
    /// bytes at fixed positions), so batching the whole entry list into a
    /// single `finalize_logup_batched(len)` column keeps the batched
    /// constraint at degree ≤ 2. The numerator `enabler` has degree 1 and the
    /// denominator products have degree 0.
    pub fn n_interaction_cols(&self) -> usize {
        SECURE_EXTENSION_DEGREE
    }
    /// Base trace: the lane-0 enabler column.
    pub fn gen_base(&self) -> Vec<ColEval> {
        let rows = 1usize << LINK_LOG_SIZE;
        let mut enabler = vec![m31(0); rows];
        enabler[0] = m31(1);
        vec![col_eval(LINK_LOG_SIZE, enabler)]
    }
    pub fn gen_interaction(&self) -> (Vec<ColEval>, SecureField) {
        assert!(
            self.bytes.len() <= self.entry_capacity,
            "public prefix exceeds its fixed entry capacity"
        );
        let one = SecureField::one();
        let zero = SecureField::from(m31(0));
        let signed = if self.yield_positive { one } else { -one };
        let entries: Vec<(SecureField, SecureField)> = (0..self.entry_capacity)
            .map(|i| {
                let active = i < self.bytes.len();
                let b = self.bytes.get(i).copied().unwrap_or(0);
                let tuple = [
                    m31(self.dst_stream),
                    m31(self.dst_off + i as u32),
                    m31(b as u32),
                ];
                (
                    if active { signed } else { zero },
                    self.hash_io.combine(&tuple),
                )
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
        assert!(
            self.bytes.len() <= self.entry_capacity,
            "public prefix exceeds its fixed entry capacity"
        );
        let enabler = eval.next_trace_mask();
        let one = E::F::from(M31::one());
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let en = E::EF::from(enabler);
        let signed_en = if self.yield_positive { en } else { -en };
        for i in 0..self.entry_capacity {
            let active = E::EF::from(E::F::from(m31(u32::from(i < self.bytes.len()))));
            let b = self.bytes.get(i).copied().unwrap_or(0);
            eval.add_to_relation(RelationEntry::new(
                &self.hash_io,
                signed_en.clone() * active,
                &[
                    E::F::from(m31(self.dst_stream)),
                    E::F::from(m31(self.dst_off + i as u32)),
                    E::F::from(m31(b as u32)),
                ],
            ));
        }
        // Batch ALL entries into one accumulator column (see
        // `n_interaction_cols` for the degree argument).
        eval.finalize_logup_batched(self.entry_capacity);
        eval
    }
}

/// All-batched lane-0 fraction column builder (`(numerator, denom)` per entry):
/// folds the whole entry list into ONE column, exactly like
/// `finalize_logup_batched(entries.len())`. Start from the first fraction,
/// then `num = d·num + n·den, den = den·d`.
fn gen_lane0_fracs(entries: &[(SecureField, SecureField)]) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    let mut gen = LogupTraceGenerator::new(LINK_LOG_SIZE);
    let (mut num, mut den) = entries[0];
    for &(n, d) in &entries[1..] {
        num = d * num + n * den;
        den *= d;
    }
    let mut n_lanes = [zero; N_LANES];
    let mut d_lanes = [one; N_LANES];
    n_lanes[0] = num;
    d_lanes[0] = den;
    let mut col = gen.new_col();
    col.write_frac(
        0,
        PackedQM31::from_array(n_lanes),
        PackedQM31::from_array(d_lanes),
    );
    col.finalize_col();
    gen.finalize_last()
}

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
    /// `(field_id, byte_index, byte)` on the shared [`FieldBytesRelation`].
    /// The host yields the `Sig_structure` bytes on this relation.
    FieldBytes(FieldBytesRelation, u32),
}

/// Prefix for instance-local preprocessed identifiers.
///
/// An empty namespace adds no prefix. A non-empty namespace prevents two
/// hosted instances from using the same shape-dependent column identifiers.
pub(crate) fn ns_prefix(ns: &str) -> String {
    if ns.is_empty() {
        String::new()
    } else {
        format!("{ns}/")
    }
}

fn prefix_active_id(log_size: u32, len: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_prefix_shape/log{log_size}/len{len}/active"),
    }
}

fn prefix_affine_id(log_size: u32, len: usize, offset: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_prefix_shape/log{log_size}/len{len}/offset{offset}/index"),
    }
}

/// Number of preprocessed bridge columns: an index, plus an active mask when
/// the bridge does not fill its trace domain.
pub(crate) fn bridge_preprocessed_column_count(log_size: u32, len: usize) -> usize {
    let rows = 1usize << log_size;
    assert!(len <= rows, "bridge length exceeds its trace domain");
    1 + usize::from(len < rows)
}

/// A HashIo bridge: for each of `len` rows, requires the source tuple (−) and
/// yields `(dst_stream, dst_off+i, byte)` (+), where `byte` is a single committed
/// trace cell used on both sides.
#[derive(Clone)]
pub struct BridgeEval {
    pub tag: &'static str,
    /// Instance namespace. An empty value adds no prefix.
    pub ns: String,
    pub log_size: u32,
    pub src: SrcRelation,
    pub dst_stream: u32,
    pub dst_off: u32,
    pub len: usize,
    pub hash_io: HashIoRelation,
}

impl BridgeEval {
    fn uses_active_column(&self) -> bool {
        bridge_preprocessed_column_count(self.log_size, self.len) == 2
    }
    fn active_col(&self) -> PreProcessedColumnId {
        prefix_active_id(self.log_size, self.len)
    }
    fn idx_col(&self) -> PreProcessedColumnId {
        prefix_affine_id(self.log_size, self.len, 0)
    }
    pub fn preprocessed_ids(&self) -> Vec<PreProcessedColumnId> {
        let mut ids = Vec::with_capacity(bridge_preprocessed_column_count(self.log_size, self.len));
        if self.uses_active_column() {
            ids.push(self.active_col());
        }
        ids.push(self.idx_col());
        ids
    }
    pub fn gen_preprocessed(&self) -> Vec<ColEval> {
        let rows = 1usize << self.log_size;
        let mut idx = vec![m31(0); rows];
        for i in 0..self.len {
            idx[i] = m31(i as u32);
        }
        let mut cols =
            Vec::with_capacity(bridge_preprocessed_column_count(self.log_size, self.len));
        if self.uses_active_column() {
            let mut active = vec![m31(0); rows];
            active[..self.len].fill(m31(1));
            cols.push(active);
        }
        cols.push(idx);
        cols.into_iter()
            .map(|v| col_eval(self.log_size, v))
            .collect()
    }
    /// Base trace: the moved byte per row.
    pub fn gen_base(&self, bytes: &[u8]) -> Vec<ColEval> {
        assert_eq!(bytes.len(), self.len, "bridge byte count mismatch");
        let rows = 1usize << self.log_size;
        let mut byte = vec![m31(0); rows];
        for (i, &b) in bytes.iter().enumerate() {
            byte[i] = m31(b as u32);
        }
        vec![col_eval(self.log_size, byte)]
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
                    // Debug-only cross-check of `finalize_last`'s sum; skipped
                    // in release so the per-lane inversion is not wasted.
                    if cfg!(debug_assertions) {
                        *claimed += num / den;
                    }
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
        push(
            &|coset| {
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
            },
            &mut entries,
            &mut claimed,
        );
        // dest yield (+).
        push(
            &|coset| {
                if coset < self.len {
                    let b = m31(bytes[coset] as u32);
                    let den = self.hash_io.combine(&[
                        m31(self.dst_stream),
                        m31(self.dst_off + coset as u32),
                        b,
                    ]);
                    (one, den)
                } else {
                    (zero, one)
                }
            },
            &mut entries,
            &mut claimed,
        );

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
        let active = if self.uses_active_column() {
            eval.get_preprocessed_column(self.active_col())
        } else {
            E::F::from(M31::one())
        };
        let idx = eval.get_preprocessed_column(self.idx_col());
        let byte = eval.next_trace_mask();

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

        eval.finalize_logup();
        eval
    }
}

// =============================================================================
// Squeeze sink: consume (−) the unused tail of a sponge's squeeze stream.
// =============================================================================

/// A sponge squeezes `n_squeeze · 136` bytes and YIELDS every one on its squeeze
/// stream. Downstream consumers (bridges / the FSM) only require the useful
/// prefix; the remaining yielded bytes need a consumer or the LogUp is
/// unbalanced. `SqueezeSink` requires `(stream, off+i, byte)` (−) for the tail
/// `off..off+len`, committing each `byte` as a trace cell. The sink's bytes are
/// the sponge's actual squeezed bytes (public-derivable from the witness), so it
/// only closes the LogUp balance.
#[derive(Clone)]
pub struct SqueezeSinkEval {
    pub tag: &'static str,
    /// Instance namespace. An empty value adds no prefix.
    pub ns: String,
    pub log_size: u32,
    pub stream: u32,
    pub off: u32,
    pub len: usize,
    pub hash_io: HashIoRelation,
}

impl SqueezeSinkEval {
    fn active_col(&self) -> PreProcessedColumnId {
        prefix_active_id(self.log_size, self.len)
    }
    fn pos_col(&self) -> PreProcessedColumnId {
        prefix_affine_id(self.log_size, self.len, self.off)
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
        vec![active, pos]
            .into_iter()
            .map(|v| col_eval(self.log_size, v))
            .collect()
    }
    pub fn gen_base(&self, bytes: &[u8]) -> Vec<ColEval> {
        assert_eq!(bytes.len(), self.len, "sink byte count mismatch");
        let rows = 1usize << self.log_size;
        let mut byte = vec![m31(0); rows];
        for (i, &b) in bytes.iter().enumerate() {
            byte[i] = m31(b as u32);
        }
        vec![col_eval(self.log_size, byte)]
    }
    pub fn gen_interaction(&self, bytes: &[u8]) -> (Vec<ColEval>, SecureField) {
        gen_single_yield(
            self.log_size,
            &self.hash_io,
            self.len,
            |i| {
                [
                    m31(self.stream),
                    m31(self.off + i as u32),
                    m31(bytes[i] as u32),
                ]
            },
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
        let byte = eval.next_trace_mask();
        let tuple = [E::F::from(m31(self.stream)), pos, byte];
        eval.add_to_relation(RelationEntry::base(&self.hash_io, -active, &tuple));
        eval.finalize_logup();
        eval
    }
}

/// Base column count of a squeeze sink (`byte`).
pub const SINK_BASE_COLS: usize = 1;
/// Interaction columns for a squeeze sink (one require, unbatched).
pub const SINK_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

/// Base column count of a bridge (`byte`).
pub const BRIDGE_BASE_COLS: usize = 1;
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
                // Debug-only cross-check of `finalize_last`'s sum; skipped in
                // release so the per-lane inversion is not wasted work.
                if cfg!(debug_assertions) {
                    claimed += signed / d[lane];
                }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn bridge(tag: &'static str, log_size: u32, len: usize) -> BridgeEval {
        let hash_io = HashIoRelation::dummy();
        BridgeEval {
            tag,
            ns: "test".to_string(),
            log_size,
            src: SrcRelation::HashIo(hash_io.clone(), 1, 2),
            dst_stream: 3,
            dst_off: 4,
            len,
            hash_io,
        }
    }

    #[test]
    fn full_domain_bridge_uses_literal_active_value() {
        let bridge = bridge("full", 6, 64);

        assert!(!bridge.uses_active_column());
        assert_eq!(bridge.preprocessed_ids(), vec![bridge.idx_col()]);
        assert_eq!(bridge.gen_preprocessed().len(), 1);
        assert_eq!(bridge.gen_base(&vec![7; bridge.len]).len(), 1);
        assert_eq!(BRIDGE_BASE_COLS, 1);
    }

    #[test]
    fn partial_domain_bridge_keeps_active_mask() {
        let bridge = bridge("partial", 6, 48);

        assert!(bridge.uses_active_column());
        assert_eq!(
            bridge.preprocessed_ids(),
            vec![bridge.active_col(), bridge.idx_col()]
        );
        assert_eq!(bridge.gen_preprocessed().len(), 2);
        assert_eq!(bridge.gen_base(&vec![9; bridge.len]).len(), 1);
    }

    #[test]
    fn equal_prefix_shapes_share_physical_preprocessing() {
        let first = bridge("first", 6, 48);
        let mut second = bridge("second", 6, 48);
        second.ns = "another-instance".to_string();
        assert_eq!(first.preprocessed_ids(), second.preprocessed_ids());

        let sink = SqueezeSinkEval {
            tag: "same-shape",
            ns: "sink-instance".to_string(),
            log_size: 6,
            stream: 9,
            off: 0,
            len: 48,
            hash_io: HashIoRelation::dummy(),
        };
        assert_eq!(sink.preprocessed_ids(), first.preprocessed_ids());
    }

    #[test]
    fn squeeze_sink_commits_only_bytes() {
        let sink = SqueezeSinkEval {
            tag: "tail",
            ns: "test".to_string(),
            log_size: 7,
            stream: 1,
            off: 64,
            len: 72,
            hash_io: HashIoRelation::dummy(),
        };

        assert_eq!(sink.gen_base(&vec![11; sink.len]).len(), 1);
        assert_eq!(SINK_BASE_COLS, 1);
    }
}
