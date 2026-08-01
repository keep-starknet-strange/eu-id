//! Preprocessed-trace generator for every SHA-256 lookup table.
//!
//! This module builds the `CircleEvaluation` values for tree 0 and their
//! `PreProcessedColumnId` values.
//!
//! The emission order must match
//! [`crate::components::all_preprocessed_column_ids`]. A different order gives
//! the verifier the wrong column for a mask read.
//!
//! ## Domain and ordering
//!
//! Each table writes row `i` to a [`BaseColumn`] in natural order. The
//! resulting `CircleEvaluation` uses `BitReversedOrder`.
//!
//! Multiplicity columns use the same row convention.
//!
//! ## Wired columns
//!
//! The standalone trace commits these preprocessed columns:
//!
//! - 4 range-table value columns (`Range_2`, `Range_4`, `Range_5`, `Range_8`)
//! - 2 boundary selectors at the main `Sha256Eval` trace's `log_n_rows`:
//!   `is_first_row` marks the first seed row and `is_first_round` marks round
//!   zero of block zero.
//! - 8 block-cyclic columns at the main trace's `log_n_rows`.
//! - 1 active-row selector for the 16-row digest bridge.

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
    all_preprocessed_column_ids, range_log_size, shared_table_preprocessed_column_ids, RANGE_TABLES,
};
use crate::constants::N_ROUNDS;
use crate::tables_local::{range_2, range_4, range_5, range_8};
use crate::trace::{Layout, ROWS_PER_BLOCK, STATE_SEED_ROWS};

/// Aggregate of one preprocessed-tree commit input: the column
/// evaluations, their stable IDs, and their log sizes — all three of
/// length 15 (see [`tests::total_preprocessed_columns_is_15`]) and aligned
/// index-for-index.
pub type PreprocessedTrace = (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Vec<PreProcessedColumnId>,
    Vec<u32>,
);

pub fn shared_table_preprocessed_log_sizes() -> Vec<u32> {
    // Class D: every shared producer's preprocessed columns (value/group cells
    // + the `is_dummy` selector) live at the blinded log size `L + 1` (doubled
    // domain, upper half = reserved dummy region). Order matches
    // `shared_table_preprocessed_column_ids`: per producer, value cols then the
    // dummy selector.
    let mut log_sizes = Vec::new();
    for &kind in RANGE_TABLES {
        // 1 value col + 1 is_dummy.
        log_sizes.extend(std::iter::repeat_n(range_log_size(kind) + 1, 2));
    }
    log_sizes
}

/// Process-lifetime cache of the shared-table preprocessed trace.
///
/// Its content is fully static — the value/group cells and the `is_dummy`
/// selector depend only on the fixed table layouts, never on any per-proof
/// witness or randomness (the Class-D fresh blind multiplicities live in the
/// *committed* multiplicity trace built by `shared_table_trace`, not here). So
/// the identical `(evals, ids, log_sizes)` triple is reusable across every
/// prove or verify operation in one process. Without this cache, each proof,
/// fingerprint calculation, and verifier root calculation rebuilds all four
/// doubled tables.
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

static PREPROCESSED_TRACE_CACHE: OnceLock<Mutex<HashMap<u32, PreprocessedTrace>>> = OnceLock::new();

/// Log sizes of every preprocessed column, in canonical order —
/// **metadata only**, allocating no `BaseColumn`/`CircleEvaluation`.
///
/// This is the verifier's entry point. To re-commit `tree[0]` the verifier
/// needs only the per-column log sizes (and the IDs, from
/// [`all_preprocessed_column_ids`]) — never the column *data*. Calling
/// [`generate_preprocessed_trace`] on the verify path would rebuild static
/// table/selector columns only to discard the evaluations.
///
/// The returned vector is identical, index-for-index, to the `log_sizes`
/// that [`generate_preprocessed_trace`] returns and to the `log_size()` of
/// each emitted column's domain — pinned by
/// [`tests::metadata_log_sizes_match_built_columns`].
pub fn preprocessed_log_sizes(log_n_rows: u32) -> Vec<u32> {
    let mut log_sizes = Vec::new();
    // 4 range tables × 1 column, each at its own range_log_size(kind).
    for &kind in RANGE_TABLES {
        log_sizes.push(range_log_size(kind));
    }
    // Two boundary selectors and eight block-cyclic columns.
    log_sizes.extend(std::iter::repeat_n(log_n_rows, 10));
    log_sizes.push(crate::digest_bridge::DIGEST_BRIDGE_LOG_SIZE);
    log_sizes
}

/// Generate the entire preprocessed trace plus its column IDs and log
/// sizes — in the canonical order
/// `crate::components::all_preprocessed_column_ids` documents.
///
/// The returned `Vec`s line up index-for-index:
/// `trace[i]`'s column ID is `ids[i]` and its log size is `log_sizes[i]`.
///
/// `log_n_rows` is the main `Sha256Eval` trace's `log_size`. Both boundary
/// selector columns use the main trace domain.
pub fn generate_preprocessed_trace(log_n_rows: u32) -> PreprocessedTrace {
    let cache = PREPROCESSED_TRACE_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    {
        let cache = cache.lock().expect("SHA preprocessed cache poisoned");
        if let Some(trace) = cache.get(&log_n_rows) {
            return trace.clone();
        }
    }

    let trace = generate_preprocessed_trace_uncached(log_n_rows);
    let mut cache = cache.lock().expect("SHA preprocessed cache poisoned");
    cache
        .entry(log_n_rows)
        .or_insert_with(|| trace.clone())
        .clone()
}

fn generate_preprocessed_trace_uncached(log_n_rows: u32) -> PreprocessedTrace {
    let mut evals = Vec::new();
    let mut log_sizes = Vec::new();

    // ---- 4 range tables (Range_2, Range_4, Range_5, Range_8) ----
    //
    // Each `Range_k` has row content `[0, 1, …, k-1]`. Producers `< 2^4`
    // are padded with trailing value `0` up to `2^LOG_N_LANES = 16` rows;
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

    for natural_hot in [0, STATE_SEED_ROWS] {
        evals.push(selector_eval(log_n_rows, natural_hot));
        log_sizes.push(log_n_rows);
    }

    // ---- 8 block-cyclic columns at the main trace's log_n_rows ----
    for col in round_cyclic_evals(log_n_rows) {
        evals.push(col);
        log_sizes.push(log_n_rows);
    }

    evals.push(selector_eval(
        crate::digest_bridge::DIGEST_BRIDGE_LOG_SIZE,
        0,
    ));
    log_sizes.push(crate::digest_bridge::DIGEST_BRIDGE_LOG_SIZE);

    let ids = all_preprocessed_column_ids();
    debug_assert_eq!(
        ids.len(),
        evals.len(),
        "ID list length must match emitted preprocessed column count"
    );
    debug_assert_eq!(log_sizes.len(), evals.len());

    (evals, ids, log_sizes)
}

fn selector_eval(
    log_n_rows: u32,
    natural_hot: usize,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let domain = CanonicCoset::new(log_n_rows).circle_domain();
    let n_rows = 1usize << log_n_rows;
    let hot_slot = Layout::row_slot(natural_hot, log_n_rows);
    let col: BaseColumn = (0..n_rows)
        .map(|slot| BaseField::from(u32::from(slot == hot_slot)))
        .collect();
    CircleEvaluation::new(domain, col)
}

/// The eight block-cyclic columns at `log_n_rows`, in
/// [`crate::components::round_cyclic_column_ids`] order.
fn round_cyclic_evals(
    log_n_rows: u32,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    use crate::constants::{K, N_ROUNDS};
    let domain = CanonicCoset::new(log_n_rows).circle_domain();
    let n_rows = 1usize << log_n_rows;
    let fns: [Box<dyn Fn(usize) -> u32>; 8] = [
        Box::new(|position| round_at(position).map_or(0, |t| K[t] & 0xFFFF)),
        Box::new(|position| round_at(position).map_or(0, |t| K[t] >> 16)),
        Box::new(|position| u32::from(round_at(position) == Some(0))),
        Box::new(|position| u32::from(round_at(position) == Some(15))),
        Box::new(|position| u32::from(round_at(position) == Some(N_ROUNDS - 1))),
        Box::new(|position| u32::from(round_at(position).is_some_and(|t| t >= 16))),
        Box::new(|position| u32::from(round_at(position).is_some())),
        Box::new(|position| round_at(position).unwrap_or(0) as u32),
    ];
    fns.into_iter()
        .map(|f| {
            let mut vals = vec![BaseField::from(0u32); n_rows];
            for natural in 0..n_rows {
                vals[Layout::row_slot(natural, log_n_rows)] =
                    BaseField::from(f(natural % ROWS_PER_BLOCK));
            }
            let col: BaseColumn = vals.into_iter().collect();
            CircleEvaluation::new(domain, col)
        })
        .collect()
}

#[inline]
fn round_at(position: usize) -> Option<usize> {
    position
        .checked_sub(STATE_SEED_ROWS)
        .filter(|&round| round < N_ROUNDS)
}

/// Reserved dummy-key base for the Class-D blinded upper half. Must equal
/// `shared_tables::DUMMY_KEY_BASE` so the preprocessed value column matches the
/// interaction fraction's row content (identical denominators). Honest range
/// consumers emit 16-bit values `< 2^16`, so keys `≥ 2^16` are
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
        let log_size = range_log_size(kind);
        let blind_log = log_size + 1;
        let domain = CanonicCoset::new(blind_log).circle_domain();
        let rows = range_rows(kind);
        let real_len = 1usize << log_size;
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

    /// Total column count: 4 table columns + 10 main selectors + 1 digest
    /// bridge selector.
    #[test]
    fn total_preprocessed_columns_is_15() {
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, log_sizes) = generate_preprocessed_trace(log_n_rows);
        assert_eq!(evals.len(), 15);
        assert_eq!(ids.len(), 15);
        assert_eq!(log_sizes.len(), 15);
    }

    /// The first four columns are `Range_k`: three at `LOG_N_LANES = 4`
    /// (for Range_2/4/5, padded to 16 rows) and one at log size 8
    /// (Range_8). The next ten columns use the main trace log size. The final
    /// column uses the 16-row digest bridge size.
    #[test]
    fn log_sizes_lay_out_correctly() {
        let log_n_rows = LOG_N_LANES;
        let (_, _, log_sizes) = generate_preprocessed_trace(log_n_rows);
        for (i, &ls) in log_sizes.iter().enumerate() {
            let expected = if i < 3 {
                LOG_N_LANES
            } else if i == 14 {
                crate::digest_bridge::DIGEST_BRIDGE_LOG_SIZE
            } else if i >= 4 {
                log_n_rows
            } else {
                range_log_size(crate::components::RangeKind::Range8)
            };
            assert_eq!(ls, expected, "column {i} log_size mismatch");
        }
    }

    /// The `is_first_row` selector is `1` at storage index zero and `0`
    /// elsewhere. This anchors the enabled row prefix at block zero.
    #[test]
    fn is_first_row_selector_is_one_at_index_zero() {
        let log_n_rows = LOG_N_LANES;
        let (evals, _, _) = generate_preprocessed_trace(log_n_rows);
        // The selector is column 4. The first-round selector follows it.
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

    #[test]
    fn first_round_and_digest_bridge_selectors_have_one_active_row() {
        let log_n_rows = 8;
        let (evals, _, _) = generate_preprocessed_trace(log_n_rows);
        let first_round = &evals[5];
        let hot = Layout::row_slot(STATE_SEED_ROWS, log_n_rows);
        for slot in 0..(1usize << log_n_rows) {
            assert_eq!(
                first_round.values.at(slot),
                BaseField::from(u32::from(slot == hot)),
                "first-round selector at slot {slot}",
            );
        }
        let bridge = &evals[14];
        for slot in 0..(1usize << crate::digest_bridge::DIGEST_BRIDGE_LOG_SIZE) {
            assert_eq!(
                bridge.values.at(slot),
                BaseField::from(u32::from(slot == 0)),
                "digest-bridge selector at slot {slot}",
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

    /// [`preprocessed_log_sizes`] is pure metadata. Check its shape for small
    /// and large traces.
    #[test]
    fn metadata_log_sizes_shape() {
        for log_n_rows in [LOG_N_LANES, 20, 30] {
            let meta = preprocessed_log_sizes(log_n_rows);
            assert_eq!(meta.len(), 15, "l={log_n_rows}");
            assert_eq!(
                meta[4..14].iter().filter(|&&l| l == log_n_rows).count(),
                10,
                "selector + cyclic log_sizes"
            );
        }
    }

    /// Guard against field-order drift in the emitted preprocessed columns.
    /// Emission order here and the column-ID order
    /// (`components::*_column_ids`) are two hand-written lists coupled only
    /// by position. The range columns are re-derived from their table rows and
    /// compared position-for-position against the emitted columns.
    #[test]
    fn emitted_columns_match_documented_field_order() {
        let (evals, _, _) = generate_preprocessed_trace(LOG_N_LANES);

        let col_eq = |idx: usize, expected: &[u32], label: &str| {
            let ev = &evals[idx];
            assert_eq!(ev.values.len(), expected.len(), "{label}: length");
            for (i, &e) in expected.iter().enumerate() {
                assert_eq!(ev.values.at(i), BaseField::from(e), "{label}[{i}]");
            }
        };

        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            let log_size = range_log_size(kind);
            let mut expected = range_rows(kind);
            expected.resize(1usize << log_size, 0);
            col_eq(i, &expected, kind.tag());
        }
    }

    /// Class-D shape of the shared preprocessed trace: every producer gains an
    /// `is_dummy` selector and a doubled domain. Structure and content checks:
    /// - 8 columns (4 range producers × value + `is_dummy`).
    /// - every id is in the `sha_shared_` namespace.
    /// - every value/selector column is at the blinded log size `L + 1`.
    /// - each value column's REAL lower half matches the regular (standalone)
    ///   table content; the dummy upper half holds unreachable keys `≥ 2^16`.
    /// - each `is_dummy` selector is `0` over the lower half, `1` over the upper.
    #[test]
    fn shared_table_columns_are_class_d_blinded_with_distinct_ids() {
        use crate::components::SHARED_ID_PREFIX;
        let (regular_evals, _regular_ids, regular_log_sizes) =
            generate_preprocessed_trace(LOG_N_LANES);
        let (shared_evals, shared_ids, shared_log_sizes) =
            generate_shared_table_preprocessed_trace();

        assert_eq!(shared_evals.len(), 8, "4·2 Class-D columns");
        assert_eq!(shared_ids.len(), shared_evals.len());
        assert_eq!(shared_log_sizes.len(), shared_evals.len());

        for id in &shared_ids {
            assert!(
                id.id.starts_with(SHARED_ID_PREFIX),
                "shared table id {} must use the sha_shared namespace",
                id.id,
            );
        }

        // Walk producers in the same table-major order the generator emits,
        // consuming (value cols..., is_dummy) per producer and the regular
        // trace's value cols in lockstep.
        let mut si = 0; // shared index
        let check_value =
            |shared: &CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>,
             regular: &CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>| {
                let real_len = regular.values.len();
                assert_eq!(
                    shared.values.len(),
                    2 * real_len,
                    "blinded value column doubles the regular domain",
                );
                for i in 0..real_len {
                    assert_eq!(shared.values.at(i), regular.values.at(i), "real row {i}");
                    assert_eq!(
                        shared.values.at(real_len + i),
                        BaseField::from(DUMMY_KEY_BASE + i as u32),
                        "dummy row {i}",
                    );
                }
            };
        for (ri, _) in RANGE_TABLES.iter().enumerate() {
            assert_eq!(shared_log_sizes[si], regular_log_sizes[ri] + 1);
            check_value(&shared_evals[si], &regular_evals[ri]);
            let real_len = regular_evals[ri].values.len();
            si += 1;
            for i in 0..real_len {
                assert_eq!(shared_evals[si].values.at(i), BaseField::from(0u32));
                assert_eq!(
                    shared_evals[si].values.at(real_len + i),
                    BaseField::from(1u32),
                );
            }
            si += 1;
        }
        assert_eq!(si, shared_evals.len());

        // Range8 is exact (no real padding): rows 0..=255 are its byte keys;
        // rows 256..=511 are the Class-D dummy half with unreachable keys.
        let range8 = RANGE_TABLES
            .iter()
            .position(|&kind| kind == crate::components::RangeKind::Range8)
            .expect("Range8 is registered");
        let values = &shared_evals[2 * range8];
        let is_dummy = &shared_evals[2 * range8 + 1];
        for (row, value, dummy) in [
            (0, 0, 0),
            (255, 255, 0),
            (256, DUMMY_KEY_BASE, 1),
            (511, DUMMY_KEY_BASE + 255, 1),
        ] {
            assert_eq!(values.values.at(row), BaseField::from(value));
            assert_eq!(is_dummy.values.at(row), BaseField::from(dummy));
        }
    }
}
