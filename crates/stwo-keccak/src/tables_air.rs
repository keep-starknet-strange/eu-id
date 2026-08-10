//! Table-provider components for the spread-form Keccak AIR. Each preprocessed
//! lookup table gets a component that holds the table as preprocessed columns
//! plus multiplicity trace columns. It yields each relation with a negative
//! multiplicity. The carrier and sponge use the same relations with positive
//! multiplicities. Thus, the LogUp balance holds only for valid table rows.
//!
//! Three table families:
//! - **Dense:** one `2^16`-row `(key, spread(xor))` table serving the `xor3`
//!   relation. The chi step's `andnot` lookup retargets onto this same table
//!   (see [`crate::tables`]); no dedicated `andnot` relation or column.
//! - **Conv:** `2^8`-row `(byte, spread(byte))` byte↔spread table.
//! - **Split(r):** `2^8`-row `(spread_byte, spread_hi)` spread split;
//!   `spread_lo = spread_byte − spread_hi·4^r` is derived at the lookup site.

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

    /// Number of preprocessed columns: 2 for every table kind (Dense:
    /// key+xor_out; Conv: byte+spread; Split: spread_byte+spread_hi — the
    /// andnot output and split's spread_lo are both derived, not committed).
    pub fn n_cols(&self) -> usize {
        2
    }

    /// Number of relations yielded (and multiplicity columns): 1 for every
    /// table kind (the dense table's andnot lookup retargets onto its own
    /// xor3 relation, so it no longer needs a second relation/column).
    pub fn n_relations(&self) -> usize {
        1
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
                id: if matches!((self, c), (TableKind::Conv, 1) | (TableKind::Split(_), 0)) {
                    "keccak_spread_byte_8".to_string()
                } else {
                    format!("{t}_{c}")
                },
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

/// Per-table multiplicity vectors. Every table has one relation; the dense
/// table includes both xor3 and retargeted and-not lookups in that relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableMultiplicities {
    /// `per_table[i]` is a vec of `n_relations` multiplicity vectors.
    pub per_table: Vec<Vec<Vec<u32>>>,
}

const DENSE_I: usize = 0;
const CONV_I: usize = 1;

impl TableMultiplicities {
    /// Count only the 24 round rows in each 25-row carrier block. Header and
    /// padding lookup numerators are zero, so the table must not count them.
    pub fn from_carrier_round(data: &RoundData, n_perms: usize) -> Self {
        let mut per_table: Vec<Vec<Vec<u32>>> = TableKind::ALL
            .iter()
            .map(|kind| vec![vec![0u32; 1 << kind.log_size()]; kind.n_relations()])
            .collect();
        let active = |row: usize| {
            row < n_perms * crate::carrier::ROWS_PER_PERMUTATION
                && !row.is_multiple_of(crate::carrier::ROWS_PER_PERMUTATION)
        };

        for lookup in &data.lookup_data.xor3 {
            for (vector_row, tuple) in lookup.iter().enumerate() {
                for (lane, key) in tuple[0].to_array().iter().enumerate() {
                    if active(vector_row * N_LANES + lane) {
                        per_table[DENSE_I][0][key.0 as usize] += 1;
                    }
                }
            }
        }
        // Retargeted onto the xor3 relation (see `write_andnot`): tuple[0] is
        // now a genuine xor3 key, so it folds into the same bucket as above.
        for lookup in &data.lookup_data.andnot {
            for (vector_row, tuple) in lookup.iter().enumerate() {
                for (lane, key) in tuple[0].to_array().iter().enumerate() {
                    if active(vector_row * N_LANES + lane) {
                        per_table[DENSE_I][0][key.0 as usize] += 1;
                    }
                }
            }
        }
        for lookup in &data.lookup_data.split {
            for (vector_row, tuple) in lookup.iter().enumerate() {
                let shift = tuple[0].to_array()[0].0;
                let table_index = split_table_index(shift);
                for (lane, value) in tuple[1].to_array().iter().enumerate() {
                    if active(vector_row * N_LANES + lane) {
                        per_table[table_index][0][unspread_u32(value.0) as usize] += 1;
                    }
                }
            }
        }

        Self { per_table }
    }

    pub fn add(&mut self, other: &Self) {
        assert_eq!(self.per_table.len(), other.per_table.len());
        for (tables, other_tables) in self.per_table.iter_mut().zip(&other.per_table) {
            assert_eq!(tables.len(), other_tables.len());
            for (values, other_values) in tables.iter_mut().zip(other_tables) {
                assert_eq!(values.len(), other_values.len());
                for (value, other_value) in values.iter_mut().zip(other_values) {
                    *value += *other_value;
                }
            }
        }
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

        let mut col = gen.new_col();
        for vr in 0..n_vec_rows {
            let num = packed_neg_mult(&mults[0], vr);
            let den = packed_row_denom(kind, rel, &rows, vr);
            col.write_frac(vr, num, den);
        }
        col.finalize_col();

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
    let pack =
        |c: usize| PackedM31::from_array(std::array::from_fn(|l| M31::from(rows[base + l][c])));
    match kind {
        TableKind::Dense => rel.xor3.combine(&[pack(0), pack(1)]),
        TableKind::Conv => rel.conv.combine(&[pack(0), pack(1)]),
        TableKind::Split(r) => {
            let sr: &SplitRelation = &rel.split[(*r - 1) as usize];
            let spread_byte = pack(0);
            let spread_hi = pack(1);
            // spread_lo = spread_byte - spread_hi * 4^r (derived, not committed).
            let spread_lo = spread_byte - spread_hi * M31::from(1u32 << (2 * r));
            sr.combine(&[spread_byte, spread_hi, spread_lo])
        }
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
        let mult = eval.next_trace_mask();
        match self.kind {
            TableKind::Dense => {
                // (key, xor_out) yields xor3; the chi step's andnot lookup
                // retargets onto this same relation (see `crate::tables`).
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.xor3,
                    -E::EF::from(mult),
                    &cols,
                ));
            }
            TableKind::Conv => {
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.conv,
                    -E::EF::from(mult),
                    &cols,
                ));
            }
            TableKind::Split(r) => {
                // spread_lo = spread_byte - spread_hi * 4^r (derived, not
                // committed): cols is [spread_byte, spread_hi].
                let spread_lo = cols[0].clone() - cols[1].clone() * M31::from(1u32 << (2 * r));
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.split[(r - 1) as usize],
                    -E::EF::from(mult),
                    &[cols[0].clone(), cols[1].clone(), spread_lo],
                ));
            }
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spread_byte_tables_share_one_physical_column() {
        let shared = TableKind::Conv.column_ids()[1].clone();
        for shift in 1..=7 {
            assert_eq!(TableKind::Split(shift).column_ids()[0], shared);
        }
        // Dense(2) + Conv(1 new + 1 shared) + Split(7 new, sharing 1 column) = 11.
        assert_eq!(
            all_preprocessed_column_ids()
                .into_iter()
                .map(|id| id.id)
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            11
        );
    }
}
