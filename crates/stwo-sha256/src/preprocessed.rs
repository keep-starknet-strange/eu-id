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
//! - 4 range tables (`Range_2`, `Range_4`, `Range_5`, `Range_16`)
//! - 1 `is_first_row` selector at the main `Sha256Eval` trace's `log_n_rows`
//!   — value `1` at storage index `Layout::block_slot(0, log_n_rows) = 0`,
//!   zero elsewhere. The AIR pins `is_first_block ≡ is_first_row`, which
//!   anchors the §10.3 chain at block 0's IV binding (research/sha256-air-design.md §11 L2).
//!
//! Total committed columns:
//! `8·5 + 5 + 3 + 4·4 + 4·3 + 4·1 + 1 = 40 + 5 + 3 + 16 + 12 + 4 + 1 = 81`.

use stwo::core::fields::m31::BaseField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::components::{
    all_preprocessed_column_ids, range_log_size, DECODE_TABLES, RANGE_TABLES, ROUND_SPLIT_TABLES,
    SIGMA_SPLIT_TABLES,
};
use crate::tables::{
    build_decode_table, build_maj_ch_table, build_round_split_pack_table,
    build_sigma_split_pack_table, build_xor_8_table, RoundPartition,
};
use crate::tables_local::{range_16, range_2, range_4, range_5};
use crate::trace::Layout;

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
///
/// `log_n_rows` is the main `Sha256Eval` trace's `log_size`; the
/// `is_first_row` selector column is sized to it and is `1` at storage
/// index `Layout::block_slot(0, log_n_rows) = 0`, `0` elsewhere.
pub fn generate_preprocessed_trace(group_width: u32, log_n_rows: u32) -> PreprocessedTrace {
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

    // ---- 4 range tables (Range_2, Range_4, Range_5, Range_16) ----
    //
    // Each `Range_k` has row content `[0, 1, …, k-1]`. Producers `< 2^4`
    // are padded with leading value `0` up to `2^LOG_N_LANES = 16` rows;
    // the consumer never fires lookups on those padding slots, so they
    // do not perturb the LogUp balance (the matching multiplicity column
    // holds zeros for the padded suffix — see `range_k_multiplicities`).
    for &kind in RANGE_TABLES {
        let log_size = range_log_size(kind);
        let domain = CanonicCoset::new(log_size).circle_domain();
        let rows = range_rows(kind);
        let n_rows = 1usize << log_size;
        debug_assert!(rows.len() <= n_rows);
        let col: BaseColumn = (0..n_rows)
            .map(|i| BaseField::from(rows.get(i).copied().unwrap_or(0)))
            .collect();
        evals.push(CircleEvaluation::new(domain, col));
        log_sizes.push(log_size);
    }

    // ---- 1 `is_first_row` selector at the main trace's log_size ----
    //
    // Value `1` at the storage index that block 0 occupies (which is `0`
    // by `Layout::block_slot(0, log_n_rows)`), `0` elsewhere. The AIR
    // consumes this in `Sha256Eval::evaluate` to pin
    // `is_first_block ≡ is_first_row`, anchoring the §10.3 chain on
    // block 0's IV binding (closes design §11 L2).
    {
        let domain = CanonicCoset::new(log_n_rows).circle_domain();
        let n_rows = 1usize << log_n_rows;
        let first_slot = Layout::block_slot(0, log_n_rows);
        debug_assert_eq!(first_slot, 0);
        let col: BaseColumn = (0..n_rows)
            .map(|i| {
                if i == first_slot {
                    BaseField::from(1u32)
                } else {
                    BaseField::from(0u32)
                }
            })
            .collect();
        evals.push(CircleEvaluation::new(domain, col));
        log_sizes.push(log_n_rows);
    }

    let ids = all_preprocessed_column_ids();
    debug_assert_eq!(
        ids.len(),
        evals.len(),
        "ID list length must match emitted preprocessed column count"
    );
    debug_assert_eq!(log_sizes.len(), evals.len());

    (evals, ids, log_sizes)
}

/// Row content of one `Range_k` preprocessed table — the values `[0, k)`
/// from `crate::tables_local`. Returned in canonical order so the
/// preprocessed trace and the multiplicity column line up by index.
fn range_rows(kind: crate::components::RangeKind) -> Vec<u32> {
    use crate::components::RangeKind;
    match kind {
        RangeKind::Range2 => range_2(),
        RangeKind::Range4 => range_4(),
        RangeKind::Range5 => range_5(),
        RangeKind::Range16 => range_16(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::partitions::MAX_ROUND_GROUP_BITS;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;
    use stwo::prover::backend::Column;

    /// Total column count: 8·5 + 5 + 3 + 4·4 + 4·3 + 4·1 + 1 = 81. Catches
    /// any regression in the per-table layout. The trailing `+ 1` is the
    /// `is_first_row` selector emitted at the main trace's `log_n_rows`.
    #[test]
    fn total_preprocessed_columns_is_81() {
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, log_sizes) = generate_preprocessed_trace(MAX_ROUND_GROUP_BITS, log_n_rows);
        assert_eq!(evals.len(), 81);
        assert_eq!(ids.len(), 81);
        assert_eq!(log_sizes.len(), 81);
    }

    /// First eight tables (40 columns) are decode tables at log_size = 16.
    /// Next 5 columns are Maj/Ch at log_size = 3W. The next 33 columns are
    /// xor_8 + round/σ split-pack at log_size 16. Then 4 `Range_k` columns
    /// — three at `LOG_N_LANES = 4` (for Range_2/4/5, padded to 16 rows)
    /// and one at log_size 16 (Range_16, 2¹⁶ rows). The trailing column
    /// (index 80) is `is_first_row` at the main trace's `log_n_rows`.
    #[test]
    fn log_sizes_lay_out_correctly() {
        let w = MAX_ROUND_GROUP_BITS;
        let log_n_rows = LOG_N_LANES;
        let (_, _, log_sizes) = generate_preprocessed_trace(w, log_n_rows);
        for (i, &ls) in log_sizes.iter().enumerate() {
            let expected = if (40..45).contains(&i) {
                3 * w
            } else if (76..79).contains(&i) {
                LOG_N_LANES
            } else if i == 80 {
                log_n_rows
            } else {
                16
            };
            assert_eq!(ls, expected, "column {i} log_size mismatch");
        }
    }

    /// The `is_first_row` selector is `1` at storage index 0 and `0`
    /// elsewhere. This pins the `is_first_block ≡ is_first_row` constraint
    /// in `Sha256Eval` to a single anchor at block 0's slot (which
    /// `Layout::block_slot(0, log_n_rows)` resolves to index 0).
    #[test]
    fn is_first_row_selector_is_one_at_index_zero() {
        let log_n_rows = LOG_N_LANES;
        let (evals, _, _) = generate_preprocessed_trace(MAX_ROUND_GROUP_BITS, log_n_rows);
        // The selector is the last column (index 80).
        let selector = evals.last().expect("at least one preprocessed column");
        let n_rows = 1usize << log_n_rows;
        for i in 0..n_rows {
            let expected = if i == 0 { 1u32 } else { 0u32 };
            assert_eq!(
                selector.values.at(i),
                BaseField::from(expected),
                "is_first_row[{i}] mismatch",
            );
        }
    }
}
