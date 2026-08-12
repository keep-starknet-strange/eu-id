//! Producer-side lookup components.
//!
//! The main `crate::constraints::Sha256Eval` consumes each lookup row.
//! It calls `add_to_relation(rel, +1, …)` for each use.
//! A producer yields the same row with a negative use count.
//! These terms make the LogUp sum zero.
//!
//! Each table here is a small `FrameworkEval` with one preprocessed-column
//! group (the table's row content) plus one main-trace **multiplicity**
//! column per relation it serves. It emits `add_to_relation(rel,
//! −multiplicity_cell, &row_cells)`, then `finalize_logup_in_pairs()`.
//!
//! The standalone path uses four [`RangeKEval`] components.
//! Each `RangeKind::{Range2, Range4, Range5, Range8}` channel has one component.
//! The first three tables bound carries to two, four, or five values.
//! `Range8` bounds terminal digest bytes to 256 values.
//!
//! Each table has one value column and one multiplicity column.
//! Small tables use the minimum SIMD domain.
//! See [`range_log_size`] and [`crate::preprocessed`].
//!
//! Every preprocessed-column ID is namespaced under the `"sha256_"` prefix
//! to prevent a collision with ECDSA-stream tables. The `id()` constructors
//! stay next to their evaluators. This structure keeps the trace generator and
//! evaluator in the same order.

use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, Relation, RelationEntry};

use crate::tables_local::RANGE_8;

// Re-export shorthand so the `stark` module imports types from one place.
pub use crate::relations::Sha256Relations;

// ---------------------------------------------------------------------------
// Preprocessed-column ID conventions
// ---------------------------------------------------------------------------

/// Stable namespace prefix for every SHA-256 preprocessed column ID.
/// Keeps these from colliding with the ECDSA stream's tables when the
/// integration crate combines both AIRs into one proof.
pub const ID_PREFIX: &str = "sha256_";
pub const SHARED_ID_PREFIX: &str = "sha_shared_";

fn id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{ID_PREFIX}{name}"),
    }
}

fn shared_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{SHARED_ID_PREFIX}{name}"),
    }
}

/// Which `Range_k` table a producer or consumer fires against. The lookup
/// pins one value into `[0, k)`.
///
/// `Range2`, `Range4`, and `Range5` check addition carries. A `k`-addend carry
/// is in `[0, k)`. `Range8` checks only terminal digest bytes. The addition
/// helper rejects `Range8` because no addition carry uses that range.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RangeKind {
    /// Carries from 2-addend mod-2³² adds (`T2`, `e_new`, `a_new`, finalization).
    Range2,
    /// Carries from the 4-addend message-schedule recurrence.
    Range4,
    /// Carries from the 5-addend `T1` round add.
    Range5,
    /// Terminal digest bytes.
    /// **Not** used for mod-2³² add carries — those land in
    /// `Range2`/`Range4`/`Range5` per the headroom audit. See the enum
    /// doc-comment for the rationale.
    Range8,
}

impl RangeKind {
    /// The exclusive upper bound `k` of the range `[0, k)`.
    #[inline]
    pub const fn bound(self) -> u32 {
        match self {
            RangeKind::Range2 => crate::headroom::RANGE_2,
            RangeKind::Range4 => crate::headroom::RANGE_4,
            RangeKind::Range5 => crate::headroom::RANGE_5,
            RangeKind::Range8 => RANGE_8,
        }
    }

    /// Short tag used in preprocessed-column IDs (`"range_2"`, etc.).
    #[inline]
    pub const fn tag(self) -> &'static str {
        match self {
            RangeKind::Range2 => "range_2",
            RangeKind::Range4 => "range_4",
            RangeKind::Range5 => "range_5",
            RangeKind::Range8 => "range_8",
        }
    }
}

/// `log2` of the row count committed for a `Range_k` producer.
///
/// Stwo's SIMD backend requires `log_size ≥ LOG_N_LANES`. Extend small tables
/// to `2^LOG_N_LANES = 16` rows. Extra rows contain value zero and
/// multiplicity zero, so they do not affect the LogUp balance.
#[inline]
pub fn range_log_size(kind: RangeKind) -> u32 {
    let k = kind.bound();
    let needed = k.next_power_of_two().trailing_zeros();
    needed.max(LOG_N_LANES)
}

/// Preprocessed-column ID of one `Range_k` table (the single value column).
pub fn range_column_id(kind: RangeKind) -> PreProcessedColumnId {
    id(kind.tag())
}

pub fn shared_range_column_id(kind: RangeKind) -> PreProcessedColumnId {
    shared_id(kind.tag())
}

/// Class D `is_dummy` selector ID for a blinded shared table.
///
/// The selector is one in the reserved upper half `[2^L, 2^(L+1))`.
/// It is zero in the real lower half `[0, 2^L)`.
/// The stable producer tag prevents aliasing.
/// The `sha_shared_` namespace prevents collisions with standalone tables.
pub fn shared_producer_dummy_column_id(producer: SharedProducer) -> PreProcessedColumnId {
    shared_id(&format!("{}_isdummy", producer.tag()))
}

/// Preprocessed-column ID of the single-cell `is_first_row` selector
/// committed at the main `Sha256Eval` trace's `log_n_rows`. The selector
/// is `1` at storage index `Layout::block_slot(0, log_n_rows) = 0` and
/// `0` elsewhere. `Sha256Eval` reads it via `eval.get_preprocessed_column`
/// and pins `msg_start ≡ is_first_row`, anchoring the §10.3 chain
/// on block 0's IV binding (docs/research/sha256-air-design.md §11 L2).
pub fn is_first_row_column_id() -> PreProcessedColumnId {
    id("is_first_row")
}

/// IDs for the nine cyclic columns in the three-seed-row layout.
/// The order is K limbs, block start, round 0/15/63, schedule gate, round
/// gate, and round index.
/// This order matches `crate::preprocessed::generate_preprocessed_trace`.
pub fn round_cyclic_column_ids() -> [PreProcessedColumnId; 9] {
    [
        id("k_lo"),
        id("k_hi"),
        id("block_start"),
        id("is_round_0"),
        id("is_round_15"),
        id("is_round_63"),
        id("is_schedule"),
        id("is_round"),
        id("round_index"),
    ]
}

/// Tiny helper: emit one `RelationEntry` with the given multiplicity, then
/// finalize. Generic over `R: Relation<E::F, E::EF>` so each table can pick
/// its relation type without a `dyn` indirection.
fn emit<E: EvalAtRow, R: Relation<E::F, E::EF>>(
    eval: &mut E,
    rel: &R,
    mult: E::F,
    values: &[E::F],
) {
    eval.add_to_relation(RelationEntry::base(rel, mult, values));
}

/// Class D blinded yield for one shared-table row.
///
/// Emits ONE gated entry against the relation: numerator `-(1 − is_dummy)·mult`
/// at the row key.
///
/// A real row has `is_dummy = 0` and numerator `-mult`.
/// A dummy row has `is_dummy = 1` and numerator zero.
/// Thus, a dummy row does not change the LogUp sum.
/// Fresh upper-half values remain in the committed multiplicity column.
/// One gated fraction replaces the earlier two-fraction form.
///
/// The trusted preprocessed data supplies `is_dummy`.
/// A prover cannot enable a dummy row as a real key.
/// Every dummy row has a zero numerator.
/// Honest consumers cannot use dummy keys of at least `2^16`.
///
/// The verifier reconstructs both the key and the gate.
/// The claimed sum has no free term.
///
/// Degree: `(1 − is_dummy)·mult` = preprocessed × trace = degree 2, within the
/// `D ≤ 3` budget under `max_constraint_log_degree_bound = blind_log_size + 1`.
/// One fraction per producer (down from two) also LOWERS the batched LogUp
/// denominator degree relative to the pair form.
fn emit_blind<E: EvalAtRow, R: Relation<E::F, E::EF>>(
    eval: &mut E,
    rel: &R,
    mult: E::F,
    is_dummy: E::F,
    values: &[E::F],
) {
    // `-(1 − is_dummy)·mult`, kept in the base field (degree 2: preprocessed ×
    // trace). `base` promotes the base-field numerator to `E::EF`.
    let one = <E::F as num_traits::One>::one();
    eval.add_to_relation(RelationEntry::base(rel, -((one - is_dummy) * mult), values));
}

// ---------------------------------------------------------------------------
// Range_k component
// ---------------------------------------------------------------------------

/// Producer for one `RangeKind::{Range2, Range4, Range5, Range8}` lookup table.
///
/// Reads one preprocessed value column (the row content
/// `crate::tables_local::range_k()`, padded with value `0` up to
/// `2^range_log_size(kind)` rows for `k < 2^LOG_N_LANES`) and one
/// multiplicity column. Yields each row at `-multiplicity` against the
/// matching range relation.
///
/// **Soundness role.**
/// The consumer emits one relation use for each carry.
/// See `crate::constraints::emit_mod_2_32_add_linear`.
/// It also emits `Range_8` uses for each real `h_out` byte.
///
/// This component supplies the matching LogUp values.
/// The relation pins carries to their audited ranges.
/// It also pins digest bytes to `[0, 2⁸)`.
/// The AIR recomposes each byte pair into an `h_out` limb.
#[derive(Clone)]
pub struct RangeKEval {
    pub log_size: u32,
    pub kind: RangeKind,
    pub relations: Sha256Relations,
    pub shared_tables: bool,
    /// Post-tree-1 claimed-sum mask challenge. When present, four additional
    /// trace columns hold one private `QM31` mask per row.
    pub claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for RangeKEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(if self.shared_tables {
            shared_range_column_id(self.kind)
        } else {
            range_column_id(self.kind)
        });
        let mult = eval.next_trace_mask();
        let neg = -mult;

        use crate::relations::*;
        let values = [value];
        match self.kind {
            RangeKind::Range2 => {
                emit::<E, Range2Relation>(&mut eval, &self.relations.range.range_2, neg, &values)
            }
            RangeKind::Range4 => {
                emit::<E, Range4Relation>(&mut eval, &self.relations.range.range_4, neg, &values)
            }
            RangeKind::Range5 => {
                emit::<E, Range5Relation>(&mut eval, &self.relations.range.range_5, neg, &values)
            }
            RangeKind::Range8 => {
                emit::<E, Range8Relation>(&mut eval, &self.relations.range.range_8, neg, &values)
            }
        }

        if let Some(beta) = self.claim_mask_beta {
            air_core::claim_mask::add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

// ---------------------------------------------------------------------------
// Paired shared-table producer component (R2 fraction batching)
// ---------------------------------------------------------------------------

/// One shared SHA producer table, identified by its lookup.
///
/// One component can contain two producers with the same `log_size`.
/// `finalize_logup_in_pairs` puts their fractions in one `SecureField` column.
/// This pair halves the committed interaction width.
/// The values, multiplicities, relations, and fractions match standalone
/// `RangeKEval`.
/// Only the column package changes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SharedProducer {
    Range(RangeKind),
}

impl SharedProducer {
    /// `log2` of this producer's *real* table row count (lower half).
    pub fn log_size(self) -> u32 {
        match self {
            SharedProducer::Range(kind) => range_log_size(kind),
        }
    }

    /// Class D row count, one log above the real width.
    ///
    /// The upper half contains reserved dummy keys and fresh multiplicities.
    /// Every producer column uses this size.
    pub fn blind_log_size(self) -> u32 {
        (self.log_size() + 1).max(air_core::claim_mask::CLAIM_MASK_MIN_LOG_SIZE)
    }

    /// Stable per-producer tag, matching its preprocessed-column family.
    pub fn tag(self) -> &'static str {
        match self {
            SharedProducer::Range(kind) => kind.tag(),
        }
    }

    /// Read this producer's shared preprocessed columns + its multiplicity
    /// column and push its single `add_to_relation` entry. Does NOT finalize —
    /// the owning [`SharedProducerPairEval`] finalizes once for the pair, so
    /// consecutive producers share one interaction column.
    fn emit_entry<E: EvalAtRow>(self, eval: &mut E, relations: &Sha256Relations) {
        use crate::relations::*;
        match self {
            SharedProducer::Range(kind) => {
                let value = eval.get_preprocessed_column(shared_range_column_id(kind));
                let is_dummy = eval.get_preprocessed_column(shared_producer_dummy_column_id(self));
                let mult = eval.next_trace_mask();
                let values = [value];
                match kind {
                    RangeKind::Range2 => emit_blind::<E, Range2Relation>(
                        eval,
                        &relations.range.range_2,
                        mult,
                        is_dummy,
                        &values,
                    ),
                    RangeKind::Range4 => emit_blind::<E, Range4Relation>(
                        eval,
                        &relations.range.range_4,
                        mult,
                        is_dummy,
                        &values,
                    ),
                    RangeKind::Range5 => emit_blind::<E, Range5Relation>(
                        eval,
                        &relations.range.range_5,
                        mult,
                        is_dummy,
                        &values,
                    ),
                    RangeKind::Range8 => emit_blind::<E, Range8Relation>(
                        eval,
                        &relations.range.range_8,
                        mult,
                        is_dummy,
                        &values,
                    ),
                }
            }
        }
    }
}

/// One component owning one or two same-`log_size` shared-SHA producers whose
/// fractions pair into a single interaction column. A one-producer group is
/// the odd remainder and behaves exactly like the corresponding producer eval.
#[derive(Clone)]
pub struct SharedProducerPairEval {
    pub log_size: u32,
    /// 1 or 2 producers, all of `log_size`. Read in this order. The trace and
    /// interaction generators must lay their multiplicity/fraction columns in
    /// the same order (see `shared_tables::PRODUCER_PAIRS`).
    pub producers: Vec<SharedProducer>,
    pub relations: Sha256Relations,
    /// Post-tree-1 claimed-sum mask challenge. When present, four additional
    /// trace columns hold one private `QM31` mask per row.
    pub claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for SharedProducerPairEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        for &producer in &self.producers {
            producer.emit_entry(&mut eval, &self.relations);
        }
        if let Some(beta) = self.claim_mask_beta {
            air_core::claim_mask::add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

// ---------------------------------------------------------------------------
// Aggregate IDs
// ---------------------------------------------------------------------------

/// Every preprocessed-column ID committed by this crate, in the exact
/// order [`crate::preprocessed::generate_preprocessed_trace`] emits the
/// matching `CircleEvaluation`s. The list mirrors the per-component
/// `*_column_ids` getters concatenated in **table-major** order — keep
/// both sides in sync or the verifier will read the wrong column.
pub fn all_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    let mut out = Vec::new();
    // 4 range tables, in `RANGE_TABLES` order.
    for &kind in RANGE_TABLES {
        out.push(range_column_id(kind));
    }
    // One `is_first_row` selector uses the main `Sha256Eval` size.
    // The consumer reads it with `get_preprocessed_column`.
    // No producer owns this column.
    out.push(is_first_row_column_id());
    // 9 round-cyclic columns of the rotated layout (K limbs + round
    // indicators + schedule gate), also consumer-read via
    // `get_preprocessed_column` and sized to the main trace.
    out.extend(round_cyclic_column_ids());
    out
}

pub fn consumer_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    let mut out = Vec::new();
    out.push(is_first_row_column_id());
    out.extend(round_cyclic_column_ids());
    out
}

pub fn shared_table_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    // Each Class D producer contributes its value columns first.
    // Its `is_dummy` selector follows those columns.
    // `SharedProducer::emit_entry` reads the same order.
    // `generate_shared_table_preprocessed_trace` also emits this order.
    let mut out = Vec::new();
    for &kind in RANGE_TABLES {
        let producer = SharedProducer::Range(kind);
        out.push(shared_range_column_id(kind));
        out.push(shared_producer_dummy_column_id(producer));
    }
    out
}

/// The 4 range-check tables in canonical order. Shared across `components`,
/// `preprocessed`, `multiplicities`, and `interaction` so an enum drift is
/// caught at one site.
pub const RANGE_TABLES: &[RangeKind] = &[
    RangeKind::Range2,
    RangeKind::Range4,
    RangeKind::Range5,
    RangeKind::Range8,
];
