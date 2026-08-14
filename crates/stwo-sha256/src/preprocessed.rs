//! Preprocessed trace construction for the SHA-256 AIR.
//!
//! This module constructs the active range tables, round selectors, and
//! parallel `PreProcessedColumnId` list for tree 0.
//!
//! Emission order must match `crate::components::all_preprocessed_column_ids`.
//! The verifier finds each preprocessed column by ID.
//! The prover commits the concatenated columns in one tree.
//! An order mismatch gives the verifier incorrect mask values.
//!
//! Each table maps its row function into a [`BaseColumn`]. A
//! `CircleEvaluation` then uses the canonical coset and `BitReversedOrder`.
//! This is the standard Stwo preprocessed-table convention.
//!
//! The matching multiplicity columns built by `crate::stark` use the same
//! index convention, so producer and consumer balance correctly.
//!
//! ## Wired tables
//!
//! The active AIR computes Sigma, Maj, and Ch from Boolean bit planes. Its
//! standalone preprocessed trace contains:
//!
//! - 4 range tables (`Range_2`, `Range_4`, `Range_5`, `Range_8`)
//! - 1 `is_first_row` selector at the main `Sha256Eval` trace's `log_n_rows`
//!   — value `1` at storage index `Layout::row_slot(0, log_n_rows) = 0`,
//!   zero elsewhere. The AIR requires a message start on that row, which
//!   anchors block 0's IV binding.
//! - 9 block-cyclic columns for the three seed rows plus 64 round rows.
//!
//! Total committed columns: `4·1 + 1 + 9 = 14`.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use stwo::core::fields::m31::BaseField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::components::{
    all_preprocessed_column_ids, range_log_size, shared_table_preprocessed_column_ids,
    SharedProducer, RANGE_TABLES,
};
use crate::tables_local::{range_2, range_4, range_5, range_8};
use crate::trace::Layout;

/// `log2` of the row count for every 2¹⁶-row table.
pub const LOG_SIZE_16: u32 = 16;

/// Preprocessed tree input with evaluations, IDs, and log sizes.
///
/// Each vector contains 14 aligned entries.
/// See `tests::total_preprocessed_columns_is_14`.
pub type PreprocessedTrace = (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
);

pub fn shared_table_preprocessed_log_sizes() -> Vec<u32> {
    // Each Class D column uses blinded log size `L + 1`.
    // The upper half is the reserved dummy region.
    // Each producer emits value columns before its dummy selector.
    let mut log_sizes = Vec::new();
    for &kind in RANGE_TABLES {
        // 1 value col + 1 is_dummy.
        log_sizes.extend(std::iter::repeat_n(
            SharedProducer::Range(kind).blind_log_size(),
            2,
        ));
    }
    log_sizes
}

/// Process-lifetime cache of the shared-table preprocessed trace.
///
/// The cached content is static.
/// Fixed table layouts define the value cells and `is_dummy` selector.
/// Per-proof randomness exists only in the committed multiplicity trace.
/// One process can reuse the same evaluations, IDs, and log sizes.
/// This avoids repeated construction of four doubled range tables.
static SHARED_TABLE_PREPROCESSED_CACHE: OnceLock<PreprocessedTrace> = OnceLock::new();

pub fn generate_shared_table_preprocessed_trace() -> PreprocessedTrace {
    SHARED_TABLE_PREPROCESSED_CACHE
        .get_or_init(|| {
            let (evals, _ids, _log_sizes) = generate_shared_table_preprocessed_trace_uncached();
            let ids = shared_table_preprocessed_column_ids();
            let log_sizes = shared_table_preprocessed_log_sizes();
            debug_assert_eq!(evals.len(), ids.len());
            debug_assert_eq!(evals.len(), log_sizes.len());
            (evals, ids, log_sizes)
        })
        .clone()
}

type PreprocessedTraceCacheKey = (u32, u32);
static PREPROCESSED_TRACE_CACHE: OnceLock<
    Mutex<HashMap<PreprocessedTraceCacheKey, PreprocessedTrace>>,
> = OnceLock::new();

/// Log sizes of every preprocessed column in canonical order.
///
/// This is the verifier's entry point. To re-commit `tree[0]` the verifier
/// needs only the per-column log sizes and the IDs from
/// [`all_preprocessed_column_ids`]. It does not need the column data. Calling
/// [`generate_preprocessed_trace`] on the verify path would rebuild every column.
/// The returned vector is identical, index-for-index, to the `log_sizes`
/// that [`generate_preprocessed_trace`] returns and to the `log_size()` of
/// each emitted column's domain — pinned by
/// `tests::metadata_log_sizes_match_built_columns`.
pub fn preprocessed_log_sizes(log_n_rows: u32) -> Vec<u32> {
    preprocessed_log_sizes_with_range_min(log_n_rows, 0)
}

pub(crate) fn preprocessed_log_sizes_with_range_min(
    log_n_rows: u32,
    range_min_log_size: u32,
) -> Vec<u32> {
    let mut log_sizes = Vec::new();
    // 4 range tables × 1 column, each at its own range_log_size(kind).
    for &kind in RANGE_TABLES {
        log_sizes.push(range_log_size(kind).max(range_min_log_size));
    }
    // 1 is_first_row selector at the main trace's log_n_rows.
    log_sizes.push(log_n_rows);
    // 9 round-cyclic columns at the main trace's log_n_rows.
    log_sizes.extend(std::iter::repeat_n(log_n_rows, 9));
    log_sizes
}

/// Generate the entire preprocessed trace plus its column IDs and log
/// sizes — in the canonical order
/// `crate::components::all_preprocessed_column_ids` documents.
///
/// The returned `Vec`s line up index-for-index:
/// `trace[i]`'s column ID is `ids[i]` and its log size is `log_sizes[i]`.
///
/// `log_n_rows` is the main `Sha256Eval` trace's `log_size`. The
/// The `is_first_row` selector has the same size. It is one at
/// `Layout::row_slot(0, log_n_rows)` and zero elsewhere.
pub fn generate_preprocessed_trace(log_n_rows: u32) -> PreprocessedTrace {
    generate_preprocessed_trace_with_range_min(log_n_rows, 0)
}

pub(crate) fn generate_preprocessed_trace_with_range_min(
    log_n_rows: u32,
    range_min_log_size: u32,
) -> PreprocessedTrace {
    let cache = PREPROCESSED_TRACE_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let key = (log_n_rows, range_min_log_size);
    {
        let cache = cache.lock().expect("SHA preprocessed cache poisoned");
        if let Some(trace) = cache.get(&key) {
            return trace.clone();
        }
    }

    let trace = generate_preprocessed_trace_uncached(log_n_rows, range_min_log_size);
    let mut cache = cache.lock().expect("SHA preprocessed cache poisoned");
    cache.entry(key).or_insert_with(|| trace.clone()).clone()
}

fn generate_preprocessed_trace_uncached(
    log_n_rows: u32,
    range_min_log_size: u32,
) -> PreprocessedTrace {
    let mut evals = Vec::new();
    let mut log_sizes = Vec::new();

    // ---- 4 range tables (Range_2, Range_4, Range_5, Range_8) ----
    //
    // Each `Range_k` has row content `[0, 1, …, k-1]`.
    // Small producers add trailing zero rows up to the SIMD minimum.
    // Consumers do not use the padding rows.
    // Matching multiplicities are zero in the padding suffix.
    for &kind in RANGE_TABLES {
        let log_size = range_log_size(kind).max(range_min_log_size);
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
    // by `Layout::row_slot(0, log_n_rows)`), `0` elsewhere. The AIR
    // consumes this in `Sha256Eval::evaluate` to pin
    // `msg_start ≡ is_first_row`, anchoring the §10.3 chain on
    // block 0's IV binding (closes design §11 L2).
    {
        let domain = CanonicCoset::new(log_n_rows).circle_domain();
        let n_rows = 1usize << log_n_rows;
        let first_slot = Layout::row_slot(0, log_n_rows);
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

    // ---- 9 block-cyclic columns at the main trace's log_n_rows ----
    //
    // Each column depends on the position in a 67-row block: three seed rows
    // followed by 64 rounds.
    // `Layout::row_slot` defines the natural-to-storage mapping.
    // Fill a natural-order buffer, then scatter it through that mapping.
    // The order matches `components::round_cyclic_column_ids`:
    // `k_lo, k_hi, block_start, r0, r15, r63, is_schedule, is_round,
    // round_index`.
    {
        use crate::constants::{K, N_ROUNDS};
        use crate::trace::{ROWS_PER_BLOCK, STATE_SEED_ROWS};
        let domain = CanonicCoset::new(log_n_rows).circle_domain();
        let n_rows = 1usize << log_n_rows;
        for column in 0..9 {
            let mut vals = vec![BaseField::from(0u32); n_rows];
            for natural in 0..n_rows {
                let position = natural % ROWS_PER_BLOCK;
                let is_round = position >= STATE_SEED_ROWS;
                let t = position.saturating_sub(STATE_SEED_ROWS);
                let value = match column {
                    0 => u32::from(is_round) * (K[t] & 0xffff),
                    1 => u32::from(is_round) * (K[t] >> 16),
                    2 => u32::from(position == 0),
                    3 => u32::from(is_round && t == 0),
                    4 => u32::from(is_round && t == 15),
                    5 => u32::from(is_round && t == N_ROUNDS - 1),
                    6 => u32::from(is_round && t >= 16),
                    7 => u32::from(is_round),
                    8 => u32::from(is_round) * t as u32,
                    _ => unreachable!(),
                };
                vals[Layout::row_slot(natural, log_n_rows)] = BaseField::from(value);
            }
            let col: BaseColumn = vals.into_iter().collect();
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(log_n_rows);
        }
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

/// Reserved dummy-key base for the Class-D blinded upper half. Must equal
/// `shared_tables::DUMMY_KEY_BASE` so the preprocessed value column matches the
/// interaction fraction's row content (identical denominators). Honest split-
/// pack / range consumers emit 16-bit values `< 2^16`, so keys `≥ 2^16` are
/// unreachable (see `shared_tables::DUMMY_KEY_BASE`).
const DUMMY_KEY_BASE: u32 = 1 << 16;

/// Append the Class-D dummy upper half to a `2^L`-row natural-order value
/// column, producing a `2^(L+1)`-row blinded column. `dummy(j)` gives the
/// unreachable content of dummy row `j`.
fn blind_value_col(real: Vec<u32>, dummy: impl Fn(usize) -> u32) -> BaseColumn {
    let real_len = real.len();
    debug_assert!(real_len.is_power_of_two());
    real.into_iter()
        .chain((0..real_len).map(dummy))
        .map(BaseField::from)
        .collect()
}

/// The Class-D `is_dummy` selector column: `0` over the real lower half
/// `[0, 2^L)`, `1` over the reserved dummy upper half `[2^L, 2^(L+1))`.
fn is_dummy_col(real_len: usize) -> BaseColumn {
    (0..2 * real_len)
        .map(|i| BaseField::from(if i < real_len { 0u32 } else { 1u32 }))
        .collect()
}

fn generate_shared_table_preprocessed_trace_uncached() -> PreprocessedTrace {
    let mut evals = Vec::new();
    let mut log_sizes = Vec::new();

    for &kind in RANGE_TABLES {
        let producer = SharedProducer::Range(kind);
        let blind_log = producer.blind_log_size();
        let domain = CanonicCoset::new(blind_log).circle_domain();
        let rows = range_rows(kind);
        let real_len = 1usize << (blind_log - 1);
        // Real lower half: `[0, k)` then zero padding up to `2^L` (matches
        // `shared_tables::range_blind_rows`). Dummy upper half: `2^16 + j`.
        let real: Vec<u32> = (0..real_len)
            .map(|i| rows.get(i).copied().unwrap_or(0))
            .collect();
        let value_col = blind_value_col(real, |j| DUMMY_KEY_BASE + j as u32);
        evals.push(CircleEvaluation::new(domain, value_col));
        log_sizes.push(blind_log);
        evals.push(CircleEvaluation::new(domain, is_dummy_col(real_len)));
        log_sizes.push(blind_log);
    }

    (
        evals,
        shared_table_preprocessed_column_ids(),
        shared_table_preprocessed_log_sizes(),
    )
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
        RangeKind::Range8 => range_8(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;
    use stwo::prover::backend::Column;

    /// Total column count: 4·1 + 1 + 9 = 14. Split-pack tables removed —
    /// only the 4 `Range_k` value columns, the `is_first_row` selector, and
    /// the 9 round-cyclic columns remain.
    #[test]
    fn total_preprocessed_columns_is_14() {
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, log_sizes) = generate_preprocessed_trace(log_n_rows);
        assert_eq!(evals.len(), 14);
        assert_eq!(ids.len(), 14);
        assert_eq!(log_sizes.len(), 14);
    }

    /// Columns 0..4 are the 4 `Range_k` value columns in `RANGE_TABLES` order
    /// — Range_2/4/5 at `LOG_N_LANES = 4` (padded to 16 rows) and Range_8 at
    /// log_size 8 (2⁸ rows). Columns 4..14 are the `is_first_row` selector
    /// and 9 round-cyclic columns at the main trace's `log_n_rows`.
    #[test]
    fn log_sizes_lay_out_correctly() {
        let log_n_rows = LOG_N_LANES;
        let (_, _, log_sizes) = generate_preprocessed_trace(log_n_rows);
        for (i, &ls) in log_sizes.iter().enumerate() {
            let expected = if i < 3 {
                LOG_N_LANES // Range_2/4/5
            } else if i == 3 {
                8 // Range_8
            } else {
                log_n_rows // is_first_row + 9 round-cyclic
            };
            assert_eq!(ls, expected, "column {i} log_size mismatch");
        }
    }

    /// The `is_first_row` selector is `1` at storage index 0 and `0`
    /// elsewhere. This pins the `msg_start ≡ is_first_row` constraint
    /// in `Sha256Eval` to a single anchor at block 0's slot (which
    /// `Layout::row_slot(0, log_n_rows)` resolves to index 0).
    #[test]
    fn is_first_row_selector_is_one_at_index_zero() {
        let log_n_rows = LOG_N_LANES;
        let (evals, _, _) = generate_preprocessed_trace(log_n_rows);
        // The selector is column 4 (after the 4 Range_k value columns,
        // followed by the 9 round-cyclic columns).
        let selector = &evals[4];
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
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, built_log_sizes) = generate_preprocessed_trace(log_n_rows);
        let meta = preprocessed_log_sizes(log_n_rows);

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

    /// The shape has 14 columns. The last ten selector and cyclic columns use
    /// `log_n_rows`.
    #[test]
    fn metadata_log_sizes_shape() {
        for log_n_rows in [LOG_N_LANES, 20, 30] {
            let meta = preprocessed_log_sizes(log_n_rows);
            assert_eq!(meta.len(), 14, "l={log_n_rows}");
            assert_eq!(
                meta[4..].iter().filter(|&&l| l == log_n_rows).count(),
                10,
                "selector + cyclic log_sizes"
            );
        }
    }

    /// Confirm the field order of emitted preprocessed columns.
    ///
    /// Emission order and column ID order are separate lists.
    /// A one-sided swap can preserve the column count but change verifier data.
    /// This test rebuilds each family in its documented order.
    /// It then compares each position with `generate_preprocessed_trace`.
    #[test]
    fn emitted_columns_match_documented_field_order() {
        use crate::components::RANGE_TABLES;

        let (evals, _, _) = generate_preprocessed_trace(LOG_N_LANES);

        // Split-pack tables are gone: the standalone preprocessed trace now
        // leads with the 4 `Range_k` value columns, in `RANGE_TABLES` order.
        // Each column holds `range_rows(kind)` (`[0, k)`) padded with zeros
        // up to its (SIMD-floor) domain.
        for (idx, &kind) in RANGE_TABLES.iter().enumerate() {
            let rows = range_rows(kind);
            let ev = &evals[idx];
            for (i, &e) in rows.iter().enumerate() {
                assert_eq!(ev.values.at(i), BaseField::from(e), "range[{idx}][{i}]");
            }
        }
    }

    /// Class-D shape of the shared preprocessed trace: every producer gains an
    /// `is_dummy` selector and a doubled domain. After the split-pack removal
    /// the shared trace is range-only. Structure and content checks:
    /// - 8 columns (4 range × (value + is_dummy)).
    /// - every id is in the `sha_shared_` namespace.
    /// - each value and selector column has the masked log size `L + 1`.
    /// - each value column's REAL lower half matches the regular (standalone)
    ///   table content. The dummy upper half holds unreachable keys `≥ 2^16`.
    #[test]
    fn shared_table_columns_are_class_d_blinded_with_distinct_ids() {
        use crate::components::{RANGE_TABLES, SHARED_ID_PREFIX};
        let (regular_evals, _regular_ids, _regular_log_sizes) =
            generate_preprocessed_trace(LOG_N_LANES);
        let (shared_evals, shared_ids, shared_log_sizes) =
            generate_shared_table_preprocessed_trace();

        assert_eq!(
            shared_evals.len(),
            8,
            "4 range × (value + is_dummy) columns"
        );
        assert_eq!(shared_ids.len(), shared_evals.len());
        assert_eq!(shared_log_sizes.len(), shared_evals.len());

        for id in &shared_ids {
            assert!(
                id.id.starts_with(SHARED_ID_PREFIX),
                "shared table id {} must use the sha_shared namespace",
                id.id,
            );
        }

        // The regular trace leads with the 4 range value columns. The shared
        // trace pairs each with an `is_dummy` selector at a blinded domain of
        // at least log9. Its equal-size lower/upper halves are respectively
        // honest-table padding and unreachable dummy rows.
        let mut si = 0; // shared index
        for (ri, &kind) in RANGE_TABLES.iter().enumerate() {
            let producer = SharedProducer::Range(kind);
            assert_eq!(shared_log_sizes[si], producer.blind_log_size());
            let real_len = 1usize << (producer.blind_log_size() - 1);
            assert_eq!(
                shared_evals[si].values.len(),
                2 * real_len,
                "blinded value column has equal real and dummy halves",
            );
            assert_eq!(
                &shared_evals[si].values.as_slice()[..regular_evals[ri].values.len()],
                regular_evals[ri].values.as_slice(),
                "shared real prefix matches the standalone table"
            );
            assert!(
                shared_evals[si].values.as_slice()[regular_evals[ri].values.len()..real_len]
                    .iter()
                    .all(|value| *value == BaseField::from(0u32)),
                "extra real rows are unreachable zero-multiplicity padding"
            );
            si += 1;
            // is_dummy selector.
            assert_eq!(shared_log_sizes[si], shared_log_sizes[si - 1]);
            si += 1;
        }
        assert_eq!(si, shared_evals.len());
    }
}
