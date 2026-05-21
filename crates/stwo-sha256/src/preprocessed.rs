//! Preprocessed-trace generator for every SHA-256 lookup table.
//!
//! Builds the `CircleEvaluation`s that fill tree[0] (the preprocessed
//! tree) and the parallel `PreProcessedColumnId` list that the
//! [`stwo_constraint_framework::TraceLocationAllocator`] expects.
//!
//! Emission order **must match** `crate::components::all_preprocessed_column_ids`
//! exactly; the verifier looks up each preprocessed column by ID and the
//! prover's commitment is a single tree over the concatenated columns —
//! drift between the two breaks the verifier's mask reads.
//!
//! ## Domain & ordering convention
//!
//! Every table's data is written into a [`BaseColumn`] via
//! `(0..rows).map(|i| f(i)).collect::<BaseColumn>()` — `f(i)` is the
//! row-`i` content of the table per `crate::tables`. The resulting column
//! is wrapped as `CircleEvaluation::new(CanonicCoset::new(log_size).circle_domain(), col)`
//! with the `BitReversedOrder` type tag, matching the standard Stwo
//! preprocessed-table convention (see `stwo::examples::blake::preprocessed_columns`).
//!
//! The matching multiplicity columns built by `crate::stark` use the same
//! index convention, so producer and consumer balance correctly.
//!
//! ## Wired tables
//!
//! - 8 σ/Σ decode (`Σ0-S, Σ0-S', Σ1-S, Σ1-S', σ0-S, σ0-S', σ1-S, σ1-S'`)
//! - 1 packed Maj/Ch
//! - 1 xor_8
//! - 4 round-side split-and-pack
//! - 4 σ-side split-and-pack
//!
//! Total committed columns:
//! `8·5 + 5 + 3 + 4·4 + 4·3 = 40 + 5 + 3 + 16 + 12 = 76`.

use stwo::core::fields::m31::BaseField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::components::{
    all_preprocessed_column_ids, DECODE_TABLES, ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::tables::{
    build_decode_table, build_maj_ch_table, build_round_split_pack_table,
    build_sigma_split_pack_table, build_xor_8_table, RoundPartition,
};

/// `log2` of the row count for every 2¹⁶-row table.
pub const LOG_SIZE_16: u32 = 16;

/// `log2` of the row count of the packed Maj/Ch table at group width `W`.
#[inline]
pub const fn maj_ch_log_size(group_width: u32) -> u32 {
    3 * group_width
}

/// Aggregate of one preprocessed-tree commit input: the column
/// evaluations, their stable IDs, and their log sizes — all three of
/// length 76 and aligned index-for-index.
pub type PreprocessedTrace = (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
);

/// Generate the entire preprocessed trace plus its column IDs and log
/// sizes — in the canonical order
/// `crate::components::all_preprocessed_column_ids` documents.
///
/// The returned `Vec`s line up index-for-index:
/// `trace[i]`'s column ID is `ids[i]` and its log size is `log_sizes[i]`.
pub fn generate_preprocessed_trace(group_width: u32) -> PreprocessedTrace {
    let mut evals = Vec::new();
    let mut log_sizes = Vec::new();

    // ---- 8 σ/Σ decode tables, in canonical order ----
    for &(f, h) in DECODE_TABLES {
        let rows = build_decode_table(f, h);
        let domain = CanonicCoset::new(LOG_SIZE_16).circle_domain();
        // Five columns: key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi.
        let key_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.key)).collect();
        let omain_lo: BaseColumn = rows.iter().map(|r| BaseField::from(r.o_main_lo)).collect();
        let omain_hi: BaseColumn = rows.iter().map(|r| BaseField::from(r.o_main_hi)).collect();
        let o2_lo: BaseColumn = rows
            .iter()
            .map(|r| BaseField::from(r.o2_partial_lo))
            .collect();
        let o2_hi: BaseColumn = rows
            .iter()
            .map(|r| BaseField::from(r.o2_partial_hi))
            .collect();
        for col in [key_col, omain_lo, omain_hi, o2_lo, o2_hi] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(LOG_SIZE_16);
        }
        let _ = f;
        let _ = h;
    }

    // ---- 1 packed Maj/Ch table ----
    {
        let log_size = maj_ch_log_size(group_width);
        let domain = CanonicCoset::new(log_size).circle_domain();
        let rows = build_maj_ch_table(group_width);
        let a_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.a)).collect();
        let b_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.b)).collect();
        let c_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.c)).collect();
        let maj_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.maj_val)).collect();
        let ch_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.ch_val)).collect();
        for col in [a_col, b_col, c_col, maj_col, ch_col] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(log_size);
        }
    }

    // ---- 1 xor_8 table ----
    {
        let domain = CanonicCoset::new(LOG_SIZE_16).circle_domain();
        let rows = build_xor_8_table();
        let x_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.x)).collect();
        let y_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.y)).collect();
        let z_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.z)).collect();
        for col in [x_col, y_col, z_col] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(LOG_SIZE_16);
        }
    }

    // ---- 4 round-side split-and-pack tables ----
    for &(p, h) in ROUND_SPLIT_TABLES {
        let domain = CanonicCoset::new(LOG_SIZE_16).circle_domain();
        let groups = match p {
            RoundPartition::Sigma0AndMaj => crate::partitions::SIGMA0_GROUPS,
            RoundPartition::Sigma1AndCh => crate::partitions::SIGMA1_GROUPS,
        };
        let s_mask = p.s_mask();
        let rows = build_round_split_pack_table(&groups, s_mask, h);
        // Per construction, round-side rows expose exactly 3 packed groups
        // (the half's intersection with the partition's 6 groups).
        debug_assert!(rows.iter().all(|r| r.groups.len() == 3));
        let key_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.key)).collect();
        let g0_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[0])).collect();
        let g1_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[1])).collect();
        let g2_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[2])).collect();
        for col in [key_col, g0_col, g1_col, g2_col] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(LOG_SIZE_16);
        }
    }

    // ---- 4 σ-side split-and-pack tables ----
    for &(p, h) in SIGMA_SPLIT_TABLES {
        let domain = CanonicCoset::new(LOG_SIZE_16).circle_domain();
        let rows = build_sigma_split_pack_table(p.parts(), h);
        debug_assert!(rows.iter().all(|r| r.groups.len() == 2));
        let key_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.key)).collect();
        let s_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[0])).collect();
        let sp_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[1])).collect();
        for col in [key_col, s_col, sp_col] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(LOG_SIZE_16);
        }
    }

    let ids = all_preprocessed_column_ids(group_width);
    debug_assert_eq!(
        ids.len(),
        evals.len(),
        "ID list length must match emitted preprocessed column count"
    );
    debug_assert_eq!(log_sizes.len(), evals.len());

    (evals, ids, log_sizes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::partitions::MAX_ROUND_GROUP_BITS;

    /// Total column count: 8·5 + 5 + 3 + 4·4 + 4·3 = 76. Catches any
    /// regression in the per-table layout.
    #[test]
    fn total_preprocessed_columns_is_76() {
        let (evals, ids, log_sizes) = generate_preprocessed_trace(MAX_ROUND_GROUP_BITS);
        assert_eq!(evals.len(), 76);
        assert_eq!(ids.len(), 76);
        assert_eq!(log_sizes.len(), 76);
    }

    /// First eight tables (40 columns) are decode tables at log_size = 16.
    /// Next 5 columns are Maj/Ch at log_size = 3W. The rest are at 16.
    #[test]
    fn log_sizes_lay_out_correctly() {
        let w = MAX_ROUND_GROUP_BITS;
        let (_, _, log_sizes) = generate_preprocessed_trace(w);
        for (i, &ls) in log_sizes.iter().enumerate() {
            let expected = if (40..45).contains(&i) { 3 * w } else { 16 };
            assert_eq!(ls, expected, "column {i} log_size mismatch");
        }
    }
}
