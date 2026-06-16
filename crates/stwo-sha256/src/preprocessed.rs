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
//!   anchors the §10.3 chain at block 0's IV binding (docs/research/sha256-air-design.md §11 L2).
//!
//! Total committed columns (round-side split-pack is now 5 cols each at
//! `W = 6` — `key + 4` packed sub-groups):
//! `8·5 + 5 + 3 + 4·5 + 4·3 + 4·1 + 1 = 40 + 5 + 3 + 20 + 12 + 4 + 1 = 85`.

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
/// length 85 (see [`tests::total_preprocessed_columns_is_85`]) and aligned
/// index-for-index.
pub type PreprocessedTrace = (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
);

/// Log sizes of every preprocessed column, in canonical order —
/// **metadata only**, allocating no `BaseColumn`/`CircleEvaluation`.
///
/// This is the verifier's entry point. To re-commit `tree[0]` the verifier
/// needs only the per-column log sizes (and the IDs, from
/// [`all_preprocessed_column_ids`]) — never the column *data*. Calling
/// [`generate_preprocessed_trace`] on the verify path would rebuild every
/// lookup table (millions of rows for Maj/Ch at `2^(3W)`) only to discard
/// the evaluations.
///
/// The returned vector is identical, index-for-index, to the `log_sizes`
/// that [`generate_preprocessed_trace`] returns and to the `log_size()` of
/// each emitted column's domain — pinned by
/// [`tests::metadata_log_sizes_match_built_columns`].
pub fn preprocessed_log_sizes(group_width: u32, log_n_rows: u32) -> Vec<u32> {
    let mut log_sizes = Vec::new();
    // 8 σ/Σ decode tables × 5 columns, each at LOG_SIZE_16.
    for _ in DECODE_TABLES {
        log_sizes.extend(std::iter::repeat_n(LOG_SIZE_16, 5));
    }
    // 1 packed Maj/Ch table × 5 columns at maj_ch_log_size(group_width).
    log_sizes.extend(std::iter::repeat_n(maj_ch_log_size(group_width), 5));
    // 1 xor_8 table × 3 columns at LOG_SIZE_16.
    log_sizes.extend(std::iter::repeat_n(LOG_SIZE_16, 3));
    // 4 round-side split-pack tables × 5 columns at LOG_SIZE_16.
    for _ in ROUND_SPLIT_TABLES {
        log_sizes.extend(std::iter::repeat_n(LOG_SIZE_16, 5));
    }
    // 4 σ-side split-pack tables × 3 columns at LOG_SIZE_16.
    for _ in SIGMA_SPLIT_TABLES {
        log_sizes.extend(std::iter::repeat_n(LOG_SIZE_16, 3));
    }
    // 4 range tables × 1 column, each at its own range_log_size(kind).
    for &kind in RANGE_TABLES {
        log_sizes.push(range_log_size(kind));
    }
    // 1 is_first_row selector at the main trace's log_n_rows.
    log_sizes.push(log_n_rows);
    log_sizes
}

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
        // Per construction, round-side rows expose exactly 4 packed groups
        // (the half's intersection with the partition's 8 W=6 groups).
        debug_assert!(rows.iter().all(|r| r.groups.len() == 4));
        let key_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.key)).collect();
        let g0_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[0])).collect();
        let g1_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[1])).collect();
        let g2_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[2])).collect();
        let g3_col: BaseColumn = rows.iter().map(|r| BaseField::from(r.groups[3])).collect();
        for col in [key_col, g0_col, g1_col, g2_col, g3_col] {
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

    /// Total column count: 8·5 + 5 + 3 + 4·5 + 4·3 + 4·1 + 1 = 85. Catches
    /// any regression in the per-table layout. The trailing `+ 1` is the
    /// `is_first_row` selector emitted at the main trace's `log_n_rows`.
    /// (Round-side split-pack is 5 cols each at `W = 6`: `key + 4` groups.)
    #[test]
    fn total_preprocessed_columns_is_85() {
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, log_sizes) = generate_preprocessed_trace(MAX_ROUND_GROUP_BITS, log_n_rows);
        assert_eq!(evals.len(), 85);
        assert_eq!(ids.len(), 85);
        assert_eq!(log_sizes.len(), 85);
    }

    /// First eight tables (40 columns) are decode tables at log_size = 16.
    /// Next 5 columns are Maj/Ch at log_size = 3W. The next 35 columns are
    /// xor_8 (3) + round split-pack (4×5) + σ split-pack (4×3) at log_size
    /// 16. Then 4 `Range_k` columns — three at `LOG_N_LANES = 4` (for
    /// Range_2/4/5, padded to 16 rows) and one at log_size 16 (Range_16,
    /// 2¹⁶ rows). The trailing column (index 84) is `is_first_row` at the
    /// main trace's `log_n_rows`.
    #[test]
    fn log_sizes_lay_out_correctly() {
        let w = MAX_ROUND_GROUP_BITS;
        let log_n_rows = LOG_N_LANES;
        let (_, _, log_sizes) = generate_preprocessed_trace(w, log_n_rows);
        for (i, &ls) in log_sizes.iter().enumerate() {
            let expected = if (40..45).contains(&i) {
                3 * w
            } else if (80..83).contains(&i) {
                LOG_N_LANES
            } else if i == 84 {
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
        // The selector is the last column (index 84).
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

    /// The metadata-only [`preprocessed_log_sizes`] must agree, index-for-
    /// index, with both the `log_sizes` vector and the actual committed
    /// column domains that [`generate_preprocessed_trace`] produces. This
    /// pins the verifier's re-derived sizes (it calls `preprocessed_log_sizes`
    /// directly, never building the columns) to what the prover commits, so
    /// the two cannot silently drift.
    #[test]
    fn metadata_log_sizes_match_built_columns() {
        let w = MAX_ROUND_GROUP_BITS;
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, built_log_sizes) = generate_preprocessed_trace(w, log_n_rows);
        let meta = preprocessed_log_sizes(w, log_n_rows);

        assert_eq!(meta, built_log_sizes, "metadata vs builder log_sizes");
        assert_eq!(meta.len(), evals.len());
        assert_eq!(meta.len(), ids.len());
        for (i, ev) in evals.iter().enumerate() {
            assert_eq!(
                ev.domain.log_size(),
                meta[i],
                "column {i}: committed domain log_size disagrees with metadata",
            );
        }
    }

    /// [`preprocessed_log_sizes`] is pure metadata (no table build), so its
    /// shape is checked cheaply across the whole `group_width` range and for
    /// large `log_n_rows`: 85 columns, the Maj/Ch block (cols 40..45) sized
    /// to `3·W`, and the trailing selector sized to `log_n_rows`.
    #[test]
    fn metadata_log_sizes_shape_for_all_widths() {
        for w in MAX_ROUND_GROUP_BITS..=crate::tables::MAX_GROUP_WIDTH {
            for log_n_rows in [LOG_N_LANES, 20, 30] {
                let meta = preprocessed_log_sizes(w, log_n_rows);
                assert_eq!(meta.len(), 85, "w={w}, l={log_n_rows}");
                for &ls in &meta[40..45] {
                    assert_eq!(ls, 3 * w, "Maj/Ch log_size at w={w}");
                }
                assert_eq!(*meta.last().unwrap(), log_n_rows, "selector log_size");
            }
        }
    }

    /// Guard against silent field-order drift in the emitted preprocessed
    /// columns (audit P3): emission order (here) and the column-ID order
    /// (`components::*_column_ids`) are two hand-written lists coupled only
    /// by position, so a swap like `o_main_lo` ↔ `o_main_hi` or `g0` ↔ `g1`
    /// compiles and passes the count-only check while silently mislabelling
    /// the verifier's mask data. Each family's columns are re-derived from
    /// the table rows in the *documented* order and compared position-for-
    /// position against what `generate_preprocessed_trace` emits.
    #[test]
    fn emitted_columns_match_documented_field_order() {
        use crate::partitions::{SigmaFn, SIGMA0_GROUPS};
        use crate::tables::{Half, Half16, LowerSigmaPartition};

        let w = MAX_ROUND_GROUP_BITS;
        let (evals, _, _) = generate_preprocessed_trace(w, LOG_N_LANES);

        let col_eq = |idx: usize, expected: &[u32], label: &str| {
            let ev = &evals[idx];
            assert_eq!(ev.values.len(), expected.len(), "{label}: length");
            for (i, &e) in expected.iter().enumerate() {
                assert_eq!(ev.values.at(i), BaseField::from(e), "{label}[{i}]");
            }
        };

        // decode table 0 (DECODE_TABLES[0] = Σ0,S) → cols 0..5.
        let d = build_decode_table(SigmaFn::Sigma0, Half::S);
        col_eq(
            0,
            &d.iter().map(|r| r.key).collect::<Vec<_>>(),
            "decode.key",
        );
        col_eq(
            1,
            &d.iter().map(|r| r.o_main_lo).collect::<Vec<_>>(),
            "decode.o_main_lo",
        );
        col_eq(
            2,
            &d.iter().map(|r| r.o_main_hi).collect::<Vec<_>>(),
            "decode.o_main_hi",
        );
        col_eq(
            3,
            &d.iter().map(|r| r.o2_partial_lo).collect::<Vec<_>>(),
            "decode.o2_lo",
        );
        col_eq(
            4,
            &d.iter().map(|r| r.o2_partial_hi).collect::<Vec<_>>(),
            "decode.o2_hi",
        );

        // xor_8 → cols 45..48.
        let xr = build_xor_8_table();
        col_eq(45, &xr.iter().map(|r| r.x).collect::<Vec<_>>(), "xor.x");
        col_eq(46, &xr.iter().map(|r| r.y).collect::<Vec<_>>(), "xor.y");
        col_eq(47, &xr.iter().map(|r| r.z).collect::<Vec<_>>(), "xor.z");

        // round-side split-pack table 0 (Σ0&Maj, Lo) → cols 48..53 (5 cols
        // at W=6: key + 4 sub-groups).
        let rsp = build_round_split_pack_table(
            &SIGMA0_GROUPS,
            RoundPartition::Sigma0AndMaj.s_mask(),
            Half16::Lo,
        );
        col_eq(
            48,
            &rsp.iter().map(|r| r.key).collect::<Vec<_>>(),
            "round_split.key",
        );
        col_eq(
            49,
            &rsp.iter().map(|r| r.groups[0]).collect::<Vec<_>>(),
            "round_split.g0",
        );
        col_eq(
            50,
            &rsp.iter().map(|r| r.groups[1]).collect::<Vec<_>>(),
            "round_split.g1",
        );
        col_eq(
            51,
            &rsp.iter().map(|r| r.groups[2]).collect::<Vec<_>>(),
            "round_split.g2",
        );
        col_eq(
            52,
            &rsp.iter().map(|r| r.groups[3]).collect::<Vec<_>>(),
            "round_split.g3",
        );

        // σ-side split-pack table 0 (LowerSigma0, Lo) → cols 68..71 (after
        // the 4 round-side tables now occupy cols 48..68).
        let ssp =
            build_sigma_split_pack_table(LowerSigmaPartition::LowerSigma0.parts(), Half16::Lo);
        col_eq(
            68,
            &ssp.iter().map(|r| r.key).collect::<Vec<_>>(),
            "sigma_split.key",
        );
        col_eq(
            69,
            &ssp.iter().map(|r| r.groups[0]).collect::<Vec<_>>(),
            "sigma_split.s",
        );
        col_eq(
            70,
            &ssp.iter().map(|r| r.groups[1]).collect::<Vec<_>>(),
            "sigma_split.sp",
        );

        // Maj/Ch → cols 40..45: (a, b, c, maj, ch). Re-deriving the full
        // 2^(3W) table would be wasteful, so pin the column order via two
        // representative rows (row index = (a·2^W + b)·2^W + c, natural order):
        //   row 1        = (0,0,1): maj=0, ch=1
        //   row 2^(2W)+1 = (1,0,1): maj=1, ch=0
        let n2 = (1usize << w) * (1usize << w);
        let check_maj_ch = |row: usize, a: u32, b: u32, c: u32, maj: u32, ch: u32| {
            assert_eq!(
                evals[40].values.at(row),
                BaseField::from(a),
                "maj_ch.a[{row}]"
            );
            assert_eq!(
                evals[41].values.at(row),
                BaseField::from(b),
                "maj_ch.b[{row}]"
            );
            assert_eq!(
                evals[42].values.at(row),
                BaseField::from(c),
                "maj_ch.c[{row}]"
            );
            assert_eq!(
                evals[43].values.at(row),
                BaseField::from(maj),
                "maj_ch.maj[{row}]"
            );
            assert_eq!(
                evals[44].values.at(row),
                BaseField::from(ch),
                "maj_ch.ch[{row}]"
            );
        };
        check_maj_ch(1, 0, 0, 1, 0, 1);
        check_maj_ch(n2 + 1, 1, 0, 1, 1, 0);
    }
}
