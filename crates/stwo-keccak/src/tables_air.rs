//! Table-provider components for the spread-form sponge AIR.
//!
//! Each component commits one multiplicity column. It uses a fixed table as
//! preprocessed input and yields the matching lookup relation with negative
//! multiplicity. The sponge uses the relation with positive multiplicity.

use serde::{Deserialize, Serialize};
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

use crate::relations::KeccakRelations;
use crate::tables::{build_conv_table, build_xor3_table, LOG_SIZE_CONV, LOG_SIZE_XOR3};

/// Identifies one table and defines its columns, size, and rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableKind {
    Xor3,
    Conv,
}

impl TableKind {
    pub const ALL: [TableKind; 2] = [TableKind::Xor3, TableKind::Conv];

    fn tag(&self) -> &'static str {
        match self {
            TableKind::Xor3 => "keccak_xor3",
            TableKind::Conv => "keccak_conv",
        }
    }

    pub fn log_size(&self) -> u32 {
        match self {
            TableKind::Xor3 => LOG_SIZE_XOR3,
            TableKind::Conv => LOG_SIZE_CONV,
        }
    }

    /// Both fixed tables contain a key and a value.
    pub fn n_cols(&self) -> usize {
        2
    }

    fn rows(&self) -> Vec<[u32; 2]> {
        match self {
            TableKind::Xor3 => build_xor3_table(),
            TableKind::Conv => build_conv_table(),
        }
    }

    /// The preprocessed column ids (`n_cols` of them).
    pub fn column_ids(&self) -> Vec<PreProcessedColumnId> {
        let tag = self.tag();
        (0..self.n_cols())
            .map(|c| PreProcessedColumnId {
                id: format!("{tag}_{c}"),
            })
            .collect()
    }
}

/// All preprocessed column IDs in a fixed order.
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

/// Total cells in the two preprocessed tables.
pub const PREPROCESSED_CELLS: usize = (1 << LOG_SIZE_XOR3) * 2 + (1 << LOG_SIZE_CONV) * 2;

/// Multiplicity of each fixed table row.
pub struct TableMultiplicities {
    xor3: Vec<u32>,
    conv: Vec<u32>,
}

impl TableMultiplicities {
    /// Count the sponge's XOR and byte-conversion lookups once per tuple.
    pub fn from_sponge(
        xor_blocks: &[Vec<[PackedM31; 2]>],
        conv_lookups: &[[PackedM31; 2]],
    ) -> Self {
        let mut xor3 = vec![0u32; 1 << LOG_SIZE_XOR3];
        let mut conv = vec![0u32; 1 << LOG_SIZE_CONV];
        for block in xor_blocks {
            for tuple in block {
                let key = tuple[0].to_array()[0].0 as usize;
                xor3[key] += 1;
            }
        }
        for tuple in conv_lookups {
            let byte = tuple[0].to_array()[0].0 as usize;
            conv[byte] += 1;
        }
        Self { xor3, conv }
    }

    fn for_kind(&self, kind: TableKind) -> &[u32] {
        match kind {
            TableKind::Xor3 => &self.xor3,
            TableKind::Conv => &self.conv,
        }
    }
}

/// One multiplicity trace column per table.
pub fn generate_trace(
    mult: &TableMultiplicities,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let mut cols = Vec::new();
    for kind in TableKind::ALL {
        let domain = CanonicCoset::new(kind.log_size()).circle_domain();
        let col: BaseColumn = mult
            .for_kind(kind)
            .iter()
            .map(|&value| BaseField::from(value))
            .collect();
        cols.push(CircleEvaluation::new(domain, col));
    }
    cols
}

// ── Interaction: one yield fraction column per table ──

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct InteractionClaim {
    pub claimed_sums: Vec<SecureField>,
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

    for kind in TableKind::ALL {
        let rows = kind.rows();
        let log_size = kind.log_size();
        let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
        let mut gen = LogupTraceGenerator::new(log_size);
        let mut col = gen.new_col();
        for vector_row in 0..n_vec_rows {
            let numerator = packed_neg_mult(mult.for_kind(kind), vector_row);
            let denominator = packed_row_denom(kind, rel, &rows, vector_row);
            col.write_frac(vector_row, numerator, denominator);
        }
        col.finalize_col();

        let (trace, sum) = gen.finalize_last();
        all_cols.extend(trace);
        claimed_sums.push(sum);
    }

    (InteractionClaim { claimed_sums }, all_cols)
}

fn packed_neg_mult(mults: &[u32], vector_row: usize) -> PackedQM31 {
    let base = vector_row * N_LANES;
    let arr: [M31; N_LANES] = std::array::from_fn(|l| M31::from(mults[base + l]));
    -PackedQM31::from(PackedM31::from_array(arr))
}

fn packed_row_denom(
    kind: TableKind,
    rel: &KeccakRelations,
    rows: &[[u32; 2]],
    vector_row: usize,
) -> PackedQM31 {
    let base = vector_row * N_LANES;
    let pack =
        |c: usize| PackedM31::from_array(std::array::from_fn(|l| M31::from(rows[base + l][c])));
    match kind {
        TableKind::Xor3 => rel.xor3.combine(&[pack(0), pack(1)]),
        TableKind::Conv => rel.conv.combine(&[pack(0), pack(1)]),
    }
}

// ── Components (one FrameworkEval per table) ──

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
            TableKind::Xor3 => {
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
    fn table_geometry_is_canonical() {
        assert_eq!(TableKind::ALL, [TableKind::Xor3, TableKind::Conv]);
        assert_eq!(TableKind::Xor3.log_size(), LOG_SIZE_XOR3);
        assert_eq!(TableKind::Conv.log_size(), LOG_SIZE_CONV);
        assert_eq!(TableKind::Xor3.n_cols(), 2);
        assert_eq!(TableKind::Conv.n_cols(), 2);
        assert_eq!(
            all_preprocessed_column_ids()
                .into_iter()
                .map(|column| column.id)
                .collect::<Vec<_>>(),
            [
                "keccak_xor3_0",
                "keccak_xor3_1",
                "keccak_conv_0",
                "keccak_conv_1",
            ]
        );
        assert_eq!(
            all_preprocessed_log_sizes(),
            [LOG_SIZE_XOR3, LOG_SIZE_XOR3, LOG_SIZE_CONV, LOG_SIZE_CONV]
        );
        assert_eq!(generate_preprocessed_trace().len(), 4);
        assert_eq!(PREPROCESSED_CELLS, 131_584);
    }

    #[test]
    fn sponge_multiplicities_count_each_tuple_once() {
        let packed = |value: u32| PackedM31::from(M31::from(value));
        let xor_blocks = vec![
            vec![[packed(7), packed(1)], [packed(7), packed(1)]],
            vec![[packed(11), packed(5)]],
        ];
        let conv_lookups = vec![[packed(3), packed(5)], [packed(255), packed(21_845)]];

        let multiplicities = TableMultiplicities::from_sponge(&xor_blocks, &conv_lookups);

        assert_eq!(multiplicities.xor3[7], 2);
        assert_eq!(multiplicities.xor3[11], 1);
        assert_eq!(multiplicities.xor3.iter().sum::<u32>(), 3);
        assert_eq!(multiplicities.conv[3], 1);
        assert_eq!(multiplicities.conv[255], 1);
        assert_eq!(multiplicities.conv.iter().sum::<u32>(), 2);
        assert_eq!(generate_trace(&multiplicities).len(), 2);
    }
}
