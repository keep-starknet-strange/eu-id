//! Table-provider components for the spread-form Keccak AIR. Each preprocessed
//! lookup table gets a component that holds the table as preprocessed columns
//! plus multiplicity trace column(s), and *yields* its relation(s) with
//! `-multiplicity`. The consumers (`keccak_round`, `sponge`) *use* the same
//! relations with `+1`, so the LogUp balance holds iff every used tuple is a
//! genuine table row.
//!
//! Three table families:
//! - **Dense** — one `2^16`-row table `(key, spread(xor), andnot)` serving BOTH
//!   the `xor3` and `andnot` relations. Both key a 16-bit base-4 digit value, so
//!   they share the dense key space; merging halves M3b's dominant `2^16` fixed
//!   commitment. Carries two multiplicity columns (one per relation) and yields
//!   both relations.
//! - **Conv** — `2^8`-row `(byte, spread(byte))` byte↔spread table.
//! - **Split(r)** — `2^8`-row `(spread_byte, spread_hi, spread_lo)` spread split.

use num_traits::Zero;
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::keccak_round::InteractionClaimData as RoundData;
use crate::relations::{KeccakRelations, SplitRelation};
use crate::tables::{
    build_conv_table, build_dense_table, build_split_table, LOG_SIZE_DENSE, LOG_SIZE_SPLIT,
    SPLIT_SHIFTS,
};
use crate::utils::unspread_u32;

/// Identifies one table so its preprocessed column ids, log size, rows, width,
/// multiplicity count, and relation(s) are all consistent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableKind {
    Dense,
    Conv,
    Split(u32),
}

impl TableKind {
    pub const ALL: [TableKind; 9] = [
        TableKind::Dense,
        TableKind::Conv,
        TableKind::Split(1),
        TableKind::Split(2),
        TableKind::Split(3),
        TableKind::Split(4),
        TableKind::Split(5),
        TableKind::Split(6),
        TableKind::Split(7),
    ];

    fn tag(&self) -> String {
        match self {
            TableKind::Dense => "keccak_dense".to_string(),
            TableKind::Conv => "keccak_conv".to_string(),
            TableKind::Split(r) => format!("keccak_split_{r}"),
        }
    }

    pub fn log_size(&self) -> u32 {
        match self {
            TableKind::Dense => LOG_SIZE_DENSE,
            TableKind::Conv | TableKind::Split(_) => LOG_SIZE_SPLIT,
        }
    }

    /// Number of preprocessed columns (Dense=3, Conv=2, Split=3).
    pub fn n_cols(&self) -> usize {
        match self {
            TableKind::Conv => 2,
            TableKind::Dense | TableKind::Split(_) => 3,
        }
    }

    /// Number of relations yielded (and multiplicity columns): Dense=2, else 1.
    pub fn n_relations(&self) -> usize {
        match self {
            TableKind::Dense => 2,
            _ => 1,
        }
    }

    /// Rows as `Vec<Vec<u32>>` (each inner vec of length `n_cols`).
    fn rows(&self) -> Vec<Vec<u32>> {
        match self {
            TableKind::Dense => build_dense_table()
                .into_iter()
                .map(|r| r.to_vec())
                .collect(),
            TableKind::Conv => build_conv_table().into_iter().map(|r| r.to_vec()).collect(),
            TableKind::Split(r) => build_split_table(*r)
                .into_iter()
                .map(|r| r.to_vec())
                .collect(),
        }
    }

    /// The preprocessed column ids (`n_cols` of them).
    pub fn column_ids(&self) -> Vec<PreProcessedColumnId> {
        let t = self.tag();
        (0..self.n_cols())
            .map(|c| PreProcessedColumnId {
                id: format!("{t}_{c}"),
            })
            .collect()
    }
}

/// All preprocessed column ids for the nine tables, in a fixed order.
pub fn all_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    TableKind::ALL.iter().flat_map(|k| k.column_ids()).collect()
}

/// Log sizes matching `all_preprocessed_column_ids()` one-for-one.
pub fn all_preprocessed_log_sizes() -> Vec<u32> {
    TableKind::ALL
        .iter()
        .flat_map(|k| vec![k.log_size(); k.n_cols()])
        .collect()
}

/// Generate the preprocessed trace (`n_cols` columns per table).
pub fn generate_preprocessed_trace(
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut evals = Vec::new();
    for kind in TableKind::ALL {
        let domain = CanonicCoset::new(kind.log_size()).circle_domain();
        let rows = kind.rows();
        for col in 0..kind.n_cols() {
            let column: BaseColumn = rows.iter().map(|r| BaseField::from(r[col])).collect();
            evals.push(CircleEvaluation::new(domain, column));
        }
    }
    evals
}

// ── Multiplicities: count table-row hits from the round + sponge lookup data ──

/// Total preprocessed cell count across all nine tables (for the acceptance
/// report): `2^16·3 (dense) + 2^8·2 (conv) + 7·2^8·3 (split)`.
pub const PREPROCESSED_CELLS: usize =
    (1 << LOG_SIZE_DENSE) * 3 + (1 << LOG_SIZE_SPLIT) * 2 + 7 * (1 << LOG_SIZE_SPLIT) * 3;

/// Per-table multiplicity vectors. The Dense table has two (xor3, andnot); every
/// other table has one. Indexed as `TableKind::ALL`, flattened by relation.
pub struct TableMultiplicities {
    /// `per_table[i]` is a vec of `n_relations` multiplicity vectors.
    pub per_table: Vec<Vec<Vec<u32>>>,
}

const DENSE_I: usize = 0;
const CONV_I: usize = 1;

impl TableMultiplicities {
    pub fn from_round(data: &RoundData) -> Self {
        let mut per_table: Vec<Vec<Vec<u32>>> = TableKind::ALL
            .iter()
            .map(|k| vec![vec![0u32; 1 << k.log_size()]; k.n_relations()])
            .collect();

        // Dense/xor3: relation 0, row index = key.
        for lk in &data.lookup_data.xor3 {
            for tuple in lk {
                let key = tuple[0].to_array();
                for k in key.iter().take(N_LANES) {
                    per_table[DENSE_I][0][k.0 as usize] += 1;
                }
            }
        }
        // Dense/andnot: relation 1, row index = u.
        for lk in &data.lookup_data.andnot {
            for tuple in lk {
                let u = tuple[0].to_array();
                for uu in u.iter().take(N_LANES) {
                    per_table[DENSE_I][1][uu.0 as usize] += 1;
                }
            }
        }
        // split_r: row index = byte = unspread(spread_byte); table by shift tag.
        for lk in &data.lookup_data.split {
            for tuple in lk {
                let shift = tuple[0].to_array()[0].0; // constant across lanes
                let table_i = split_table_index(shift);
                let sb = tuple[1].to_array();
                for s in sb.iter().take(N_LANES) {
                    per_table[table_i][0][unspread_u32(s.0) as usize] += 1;
                }
            }
        }

        Self { per_table }
    }

    /// Fold in the sponge's lane-0 lookups: the multi-block absorb XOR3 (dense
    /// relation 0) and the byte↔spread conv uses. Counted once (lane 0 only).
    pub fn add_sponge(&mut self, xor_blocks: &[Vec<[PackedM31; 2]>], conv: &[[PackedM31; 2]]) {
        for block in xor_blocks {
            for tuple in block {
                let key = tuple[0].to_array()[0].0 as usize;
                self.per_table[DENSE_I][0][key] += 1;
            }
        }
        for tuple in conv {
            let byte = tuple[0].to_array()[0].0 as usize;
            self.per_table[CONV_I][0][byte] += 1;
        }
    }
}

fn split_table_index(r: u32) -> usize {
    // TableKind::ALL is [Dense, Conv, Split(1..7)]; Split(r) is at index 1 + r.
    debug_assert!(SPLIT_SHIFTS.contains(&r));
    1 + r as usize
}

/// Multiplicity trace: `n_relations` base columns per table.
pub fn generate_trace(
    mult: &TableMultiplicities,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut cols = Vec::new();
    for (kind, mults) in TableKind::ALL.iter().zip(&mult.per_table) {
        let domain = CanonicCoset::new(kind.log_size()).circle_domain();
        for m in mults {
            let col: BaseColumn = m.iter().map(|&v| BaseField::from(v)).collect();
            cols.push(CircleEvaluation::new(domain, col));
        }
    }
    cols
}

// ── Interaction: one paired yield fraction column per table ──

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sums: Vec<SecureField>,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&self.claimed_sums);
    }
}

pub fn generate_interaction_trace(
    rel: &KeccakRelations,
    mult: &TableMultiplicities,
) -> (
    InteractionClaim,
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
) {
    let mut all_cols = Vec::new();
    let mut claimed_sums = Vec::new();

    for (kind, mults) in TableKind::ALL.iter().zip(&mult.per_table) {
        let rows = kind.rows();
        let log_size = kind.log_size();
        let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
        let mut gen = LogupTraceGenerator::new(log_size);

        match kind {
            TableKind::Dense => {
                // Two yields (xor3, andnot) over the shared rows, pair-batched.
                let mut col = gen.new_col();
                for vr in 0..n_vec_rows {
                    let base = vr * N_LANES;
                    let pack = |c: usize| {
                        PackedM31::from_array(std::array::from_fn(|l| M31::from(rows[base + l][c])))
                    };
                    let key = pack(0);
                    let xor_out = pack(1);
                    let andnot_out = pack(2);
                    let d0: PackedQM31 = rel.xor3.combine(&[key, xor_out]);
                    let d1: PackedQM31 = rel.andnot.combine(&[key, andnot_out]);
                    let n0 = packed_neg_mult(&mults[0], vr);
                    let n1 = packed_neg_mult(&mults[1], vr);
                    col.write_frac(vr, n0 * d1 + n1 * d0, d0 * d1);
                }
                col.finalize_col();
            }
            _ => {
                let mut col = gen.new_col();
                for vr in 0..n_vec_rows {
                    let num = packed_neg_mult(&mults[0], vr);
                    let den = packed_row_denom(kind, rel, &rows, vr);
                    col.write_frac(vr, num, den);
                }
                col.finalize_col();
            }
        }

        let (trace, sum) = gen.finalize_last();
        all_cols.extend(trace);
        claimed_sums.push(sum);
    }

    (InteractionClaim { claimed_sums }, all_cols)
}

fn packed_neg_mult(mults: &[u32], vr: usize) -> PackedQM31 {
    let base = vr * N_LANES;
    let arr: [M31; N_LANES] = std::array::from_fn(|l| M31::from(mults[base + l]));
    -PackedQM31::from(PackedM31::from_array(arr))
}

fn packed_row_denom(
    kind: &TableKind,
    rel: &KeccakRelations,
    rows: &[Vec<u32>],
    vr: usize,
) -> PackedQM31 {
    let base = vr * N_LANES;
    let n = kind.n_cols();
    let pack =
        |c: usize| PackedM31::from_array(std::array::from_fn(|l| M31::from(rows[base + l][c])));
    match kind {
        TableKind::Conv => rel.conv.combine(&[pack(0), pack(1)]),
        TableKind::Split(r) => {
            let sr: &SplitRelation = &rel.split[(*r - 1) as usize];
            let cols: Vec<PackedM31> = (0..n).map(pack).collect();
            sr.combine(&cols)
        }
        TableKind::Dense => unreachable!("dense handled inline"),
    }
}

// ── Components (one FrameworkEval per table) ──

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct Claim {
    pub log_size: u32,
}

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub kind: TableKind,
    pub relations: KeccakRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let ids = self.kind.column_ids();
        let cols: Vec<E::F> = ids
            .iter()
            .map(|id| eval.get_preprocessed_column(id.clone()))
            .collect();
        match self.kind {
            TableKind::Dense => {
                // (key, xor_out, andnot_out) yields xor3 and andnot.
                let m_xor = eval.next_trace_mask();
                let m_and = eval.next_trace_mask();
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.xor3,
                    -E::EF::from(m_xor),
                    &[cols[0].clone(), cols[1].clone()],
                ));
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.andnot,
                    -E::EF::from(m_and),
                    &[cols[0].clone(), cols[2].clone()],
                ));
            }
            TableKind::Conv => {
                let mult = eval.next_trace_mask();
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.conv,
                    -E::EF::from(mult),
                    &cols,
                ));
            }
            TableKind::Split(r) => {
                let mult = eval.next_trace_mask();
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.split[(r - 1) as usize],
                    -E::EF::from(mult),
                    &cols,
                ));
            }
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;

/// The `claimed_sums` of the tables sum with the consumers to zero.
pub fn total_claimed_sum(claim: &InteractionClaim) -> SecureField {
    claim
        .claimed_sums
        .iter()
        .fold(SecureField::zero(), |a, &s| a + s)
}
