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
//! Total committed columns (round-side split-pack is 5 cols each at
//! `W = 6` — `key + 4` packed sub-groups; the trailing `+ 9` is the
//! round-cyclic block of the rotated one-row-per-round layout):
//! `8·5 + 5 + 3 + 4·5 + 4·3 + 4·1 + 1 + 9 = 94`.

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
    RANGE_TABLES, ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::tables::{build_round_split_pack_table, build_sigma_split_pack_table, RoundPartition};
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
/// length 94 (see [`tests::total_preprocessed_columns_is_94`]) and aligned
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
    for _ in ROUND_SPLIT_TABLES {
        // 5 value cols + 1 is_dummy, all at LOG_SIZE_16 + 1.
        log_sizes.extend(std::iter::repeat_n(LOG_SIZE_16 + 1, 6));
    }
    for _ in SIGMA_SPLIT_TABLES {
        // 3 value cols + 1 is_dummy.
        log_sizes.extend(std::iter::repeat_n(LOG_SIZE_16 + 1, 4));
    }
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
/// prove/verify in one process, mirroring [`PREPROCESSED_TRACE_CACHE`]. Without
/// this, `write_preprocessed` + `preprocessed_column_fingerprints` (prove) and
/// the verifier root recompute each rebuilt all 12 doubled tables from scratch.
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

static PREPROCESSED_TRACE_CACHE: OnceLock<Mutex<HashMap<(u32, u32), PreprocessedTrace>>> =
    OnceLock::new();

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
    let _ = group_width;
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
/// `log_n_rows` is the main `Sha256Eval` trace's `log_size`; the
/// `is_first_row` selector column is sized to it and is `1` at storage
/// index `Layout::block_slot(0, log_n_rows) = 0`, `0` elsewhere.
pub fn generate_preprocessed_trace(group_width: u32, log_n_rows: u32) -> PreprocessedTrace {
    let cache = PREPROCESSED_TRACE_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let key = (group_width, log_n_rows);
    {
        let cache = cache.lock().expect("SHA preprocessed cache poisoned");
        if let Some(trace) = cache.get(&key) {
            return trace.clone();
        }
    }

    let trace = generate_preprocessed_trace_uncached(group_width, log_n_rows);
    let mut cache = cache.lock().expect("SHA preprocessed cache poisoned");
    cache.entry(key).or_insert_with(|| trace.clone()).clone()
}

fn generate_preprocessed_trace_uncached(group_width: u32, log_n_rows: u32) -> PreprocessedTrace {
    let mut evals = Vec::new();
    let mut log_sizes = Vec::new();

    let _ = group_width;

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

    // ---- 9 round-cyclic columns at the main trace's log_n_rows ----
    //
    // Each is a function of `t = natural_row mod 64` alone. Values are laid
    // out in storage order: storage slot `s` holds `f(natural(s) mod 64)`,
    // where `natural ↔ storage` is the same `Layout::row_slot` bijection the
    // trace writer uses — computed here by filling a natural-order buffer
    // and scattering through `row_slot`. Order matches
    // `components::round_cyclic_column_ids`:
    // `k_lo, k_hi, is_round_0, _1, _2, _3, _15, _63, is_schedule`.
    for col in round_cyclic_evals(log_n_rows) {
        evals.push(col);
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

/// The 9 round-cyclic columns of the rotated layout at `log_n_rows`, in
/// [`crate::components::round_cyclic_column_ids`] order. Each is a function
/// of `t = natural_row mod 64` alone, scattered into storage order via
/// [`Layout::row_slot`] — shared by the single-instance preprocessed trace
/// and the multi-slot consumer trace.
fn round_cyclic_evals(
    log_n_rows: u32,
) -> Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    use crate::constants::{K, N_ROUNDS};
    let domain = CanonicCoset::new(log_n_rows).circle_domain();
    let n_rows = 1usize << log_n_rows;
    let fns: [Box<dyn Fn(usize) -> u32>; 9] = [
        Box::new(|t| K[t] & 0xFFFF),
        Box::new(|t| K[t] >> 16),
        Box::new(|t| u32::from(t == 0)),
        Box::new(|t| u32::from(t == 1)),
        Box::new(|t| u32::from(t == 2)),
        Box::new(|t| u32::from(t == 3)),
        Box::new(|t| u32::from(t == 15)),
        Box::new(|t| u32::from(t == N_ROUNDS - 1)),
        Box::new(|t| u32::from(t >= 16)),
    ];
    fns.into_iter()
        .map(|f| {
            let mut vals = vec![BaseField::from(0u32); n_rows];
            for natural in 0..n_rows {
                vals[Layout::row_slot(natural, log_n_rows)] =
                    BaseField::from(f(natural % N_ROUNDS));
            }
            let col: BaseColumn = vals.into_iter().collect();
            CircleEvaluation::new(domain, col)
        })
        .collect()
}

/// One selector column at `log_n_rows`: `1` exactly at the natural rows for
/// which `hot` returns true, scattered into storage order.
fn selector_eval(
    log_n_rows: u32,
    hot: impl Fn(usize) -> bool,
) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
    let domain = CanonicCoset::new(log_n_rows).circle_domain();
    let n_rows = 1usize << log_n_rows;
    let mut vals = vec![BaseField::from(0u32); n_rows];
    for natural in 0..n_rows {
        if hot(natural) {
            vals[Layout::row_slot(natural, log_n_rows)] = BaseField::from(1u32);
        }
    }
    let col: BaseColumn = vals.into_iter().collect();
    CircleEvaluation::new(domain, col)
}

/// The multi-slot consumer's preprocessed trace, in
/// [`crate::components::multi_consumer_preprocessed_column_ids`] order:
/// `slot_starts` (1 at every slot region's first row), the 9 round-cyclic
/// columns, then one `slot_sel` region selector per slot. All at
/// `log_n_rows`.
pub fn generate_multi_consumer_preprocessed_trace(
    log_n_rows: u32,
    config: &crate::slots::MultiSlotConfig,
) -> PreprocessedTrace {
    let slot_rows = config.slot_rows();
    let n_slots = config.n_slots();
    assert!(
        n_slots * slot_rows <= (1usize << log_n_rows),
        "multi-slot schedule does not fit the trace"
    );

    let mut evals = Vec::with_capacity(10 + n_slots);
    let mut log_sizes = Vec::with_capacity(10 + n_slots);

    evals.push(selector_eval(log_n_rows, |natural| {
        natural % slot_rows == 0 && natural / slot_rows < n_slots
    }));
    log_sizes.push(log_n_rows);

    for col in round_cyclic_evals(log_n_rows) {
        evals.push(col);
        log_sizes.push(log_n_rows);
    }

    for s in 0..n_slots {
        evals.push(selector_eval(log_n_rows, |natural| {
            natural / slot_rows == s
        }));
        log_sizes.push(log_n_rows);
    }

    let ids = crate::components::multi_consumer_preprocessed_column_ids(
        log_n_rows,
        config.slot_log,
        n_slots,
    );
    debug_assert_eq!(ids.len(), evals.len());
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
        .chain((0..real_len).map(|j| dummy(j)))
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

    for &(p, h) in ROUND_SPLIT_TABLES {
        let blind_log = LOG_SIZE_16 + 1;
        let domain = CanonicCoset::new(blind_log).circle_domain();
        let groups = match p {
            RoundPartition::Sigma0AndMaj => crate::partitions::SIGMA0_GROUPS,
            RoundPartition::Sigma1AndCh => crate::partitions::SIGMA1_GROUPS,
        };
        let s_mask = p.s_mask();
        let rows = build_round_split_pack_table(&groups, s_mask, h);
        let real_len = rows.len();
        // Dummy rows carry unreachable key `2^16 + j` and zero groups — the
        // exact content `shared_tables::round_split_blind_rows` combines, so the
        // producer's preprocessed key and its interaction denominator agree.
        let key_col = blind_value_col(rows.iter().map(|r| r.key).collect(), |j| {
            DUMMY_KEY_BASE + j as u32
        });
        let g0_col = blind_value_col(rows.iter().map(|r| r.groups[0]).collect(), |_| 0);
        let g1_col = blind_value_col(rows.iter().map(|r| r.groups[1]).collect(), |_| 0);
        let g2_col = blind_value_col(rows.iter().map(|r| r.groups[2]).collect(), |_| 0);
        let g3_col = blind_value_col(rows.iter().map(|r| r.groups[3]).collect(), |_| 0);
        for col in [key_col, g0_col, g1_col, g2_col, g3_col] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(blind_log);
        }
        evals.push(CircleEvaluation::new(domain, is_dummy_col(real_len)));
        log_sizes.push(blind_log);
    }

    for &(p, h) in SIGMA_SPLIT_TABLES {
        let blind_log = LOG_SIZE_16 + 1;
        let domain = CanonicCoset::new(blind_log).circle_domain();
        let rows = build_sigma_split_pack_table(p.parts(), h);
        let real_len = rows.len();
        let key_col = blind_value_col(rows.iter().map(|r| r.key).collect(), |j| {
            DUMMY_KEY_BASE + j as u32
        });
        let s_col = blind_value_col(rows.iter().map(|r| r.groups[0]).collect(), |_| 0);
        let sp_col = blind_value_col(rows.iter().map(|r| r.groups[1]).collect(), |_| 0);
        for col in [key_col, s_col, sp_col] {
            evals.push(CircleEvaluation::new(domain, col));
            log_sizes.push(blind_log);
        }
        evals.push(CircleEvaluation::new(domain, is_dummy_col(real_len)));
        log_sizes.push(blind_log);
    }

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
        RangeKind::Range16 => range_16(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::partitions::MAX_ROUND_GROUP_BITS;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;
    use stwo::prover::backend::Column;

    /// Total column count: 4·5 + 4·3 + 4·1 + 1 + 9 = 46. Catches
    /// any regression in the per-table layout. The trailing `+ 1` is the
    /// `is_first_row` selector emitted at the main trace's `log_n_rows`.
    /// (Round-side split-pack is 5 cols each at `W = 6`: `key + 4` groups.)
    #[test]
    fn total_preprocessed_columns_is_46() {
        let log_n_rows = LOG_N_LANES;
        let (evals, ids, log_sizes) = generate_preprocessed_trace(MAX_ROUND_GROUP_BITS, log_n_rows);
        assert_eq!(evals.len(), 46);
        assert_eq!(ids.len(), 46);
        assert_eq!(log_sizes.len(), 46);
    }

    /// Split-pack columns occupy 0..32 at log_size 16. Then 4 `Range_k`
    /// columns — three at `LOG_N_LANES = 4` (for Range_2/4/5, padded to 16
    /// rows) and one at log_size 16 (Range_16, 2¹⁶ rows). The trailing
    /// column (index 36) is `is_first_row` at the main trace's `log_n_rows`.
    #[test]
    fn log_sizes_lay_out_correctly() {
        let w = MAX_ROUND_GROUP_BITS;
        let log_n_rows = LOG_N_LANES;
        let (_, _, log_sizes) = generate_preprocessed_trace(w, log_n_rows);
        for (i, &ls) in log_sizes.iter().enumerate() {
            let expected = if (32..35).contains(&i) {
                LOG_N_LANES
            } else if i >= 36 {
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
        // The selector is column 36 (followed by the 9 round-cyclic columns).
        let selector = &evals[36];
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
    /// large `log_n_rows`: 46 columns, with the trailing selector/cyclic
    /// columns sized to `log_n_rows`.
    #[test]
    fn metadata_log_sizes_shape_for_all_widths() {
        for w in MAX_ROUND_GROUP_BITS..=crate::tables::MAX_GROUP_WIDTH {
            for log_n_rows in [LOG_N_LANES, 20, 30] {
                let meta = preprocessed_log_sizes(w, log_n_rows);
                assert_eq!(meta.len(), 46, "w={w}, l={log_n_rows}");
                assert_eq!(
                    meta[36..].iter().filter(|&&l| l == log_n_rows).count(),
                    10,
                    "selector + cyclic log_sizes"
                );
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
        use crate::partitions::SIGMA0_GROUPS;
        use crate::tables::{Half16, LowerSigmaPartition};

        let (evals, _, _) = generate_preprocessed_trace(MAX_ROUND_GROUP_BITS, LOG_N_LANES);

        let col_eq = |idx: usize, expected: &[u32], label: &str| {
            let ev = &evals[idx];
            assert_eq!(ev.values.len(), expected.len(), "{label}: length");
            for (i, &e) in expected.iter().enumerate() {
                assert_eq!(ev.values.at(i), BaseField::from(e), "{label}[{i}]");
            }
        };

        // round-side split-pack table 0 (Σ0&Maj, Lo) → cols 0..5 (5 cols
        // at W=6: key + 4 sub-groups).
        let rsp = build_round_split_pack_table(
            &SIGMA0_GROUPS,
            RoundPartition::Sigma0AndMaj.s_mask(),
            Half16::Lo,
        );
        col_eq(
            0,
            &rsp.iter().map(|r| r.key).collect::<Vec<_>>(),
            "round_split.key",
        );
        col_eq(
            1,
            &rsp.iter().map(|r| r.groups[0]).collect::<Vec<_>>(),
            "round_split.g0",
        );
        col_eq(
            2,
            &rsp.iter().map(|r| r.groups[1]).collect::<Vec<_>>(),
            "round_split.g1",
        );
        col_eq(
            3,
            &rsp.iter().map(|r| r.groups[2]).collect::<Vec<_>>(),
            "round_split.g2",
        );
        col_eq(
            4,
            &rsp.iter().map(|r| r.groups[3]).collect::<Vec<_>>(),
            "round_split.g3",
        );

        // σ-side split-pack table 0 (LowerSigma0, Lo) → cols 20..23 (after
        // the 4 round-side tables occupy cols 0..20).
        let ssp =
            build_sigma_split_pack_table(LowerSigmaPartition::LowerSigma0.parts(), Half16::Lo);
        col_eq(
            20,
            &ssp.iter().map(|r| r.key).collect::<Vec<_>>(),
            "sigma_split.key",
        );
        col_eq(
            21,
            &ssp.iter().map(|r| r.groups[0]).collect::<Vec<_>>(),
            "sigma_split.s",
        );
        col_eq(
            22,
            &ssp.iter().map(|r| r.groups[1]).collect::<Vec<_>>(),
            "sigma_split.sp",
        );
    }

    /// Class-D shape of the shared preprocessed trace: every producer gains an
    /// `is_dummy` selector and a doubled domain. Structure and content checks:
    /// - 48 columns (4·6 round-split + 4·4 σ-split + 4·2 range = 24+16+8).
    /// - every id is in the `sha_shared_` namespace.
    /// - every value/selector column is at the blinded log size `L + 1`.
    /// - each value column's REAL lower half matches the regular (standalone)
    ///   table content; the dummy upper half holds unreachable keys `≥ 2^16`.
    /// - each `is_dummy` selector is `0` over the lower half, `1` over the upper.
    #[test]
    fn shared_table_columns_are_class_d_blinded_with_distinct_ids() {
        use crate::components::SHARED_ID_PREFIX;
        let (regular_evals, _regular_ids, regular_log_sizes) =
            generate_preprocessed_trace(MAX_ROUND_GROUP_BITS, LOG_N_LANES);
        let (shared_evals, shared_ids, shared_log_sizes) =
            generate_shared_table_preprocessed_trace();

        assert_eq!(shared_evals.len(), 48, "4·6 + 4·4 + 4·2 Class-D columns");
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
        let mut ri = 0; // regular index
        let check_value =
            |shared: &CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>,
             regular: &CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>| {
                // Blinded column is exactly twice the regular height.
                assert_eq!(
                    shared.values.len(),
                    2 * regular.values.len(),
                    "blinded value column doubles the regular domain",
                );
            };
        let n_value_cols = [(ROUND_SPLIT_TABLES.len(), 5), (SIGMA_SPLIT_TABLES.len(), 3)];
        for &(n_tables, cols) in &n_value_cols {
            for _ in 0..n_tables {
                for _ in 0..cols {
                    assert_eq!(shared_log_sizes[si], regular_log_sizes[ri] + 1);
                    check_value(&shared_evals[si], &regular_evals[ri]);
                    si += 1;
                    ri += 1;
                }
                // is_dummy selector for this producer.
                assert_eq!(shared_log_sizes[si], shared_log_sizes[si - 1]);
                si += 1;
            }
        }
        for _ in RANGE_TABLES {
            assert_eq!(shared_log_sizes[si], regular_log_sizes[ri] + 1);
            check_value(&shared_evals[si], &regular_evals[ri]);
            si += 1;
            ri += 1;
            // is_dummy selector.
            si += 1;
        }
        assert_eq!(si, shared_evals.len());
    }
}
