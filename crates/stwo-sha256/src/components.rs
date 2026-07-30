//! Producer-side components for every preprocessed lookup table the
//! SHA-256 AIR consumes.
//!
//! The main `crate::constraints::Sha256Eval` is the **consumer**: it fires
//! `add_to_relation(rel, +1, …)` on each lookup. For the LogUp protocol
//! to balance to zero, every consumed row must be produced — yielded with
//! a negative multiplicity equal to how many times the consumer used it.
//!
//! Each table here is a small `FrameworkEval` with one preprocessed-column
//! group (the table's row content) plus one main-trace **multiplicity**
//! column per relation it serves. It emits `add_to_relation(rel,
//! −multiplicity_cell, &row_cells)`, then `finalize_logup_in_pairs()`.
//!
//! Producer components:
//!
//! - [`RangeKEval`] × 4 — one per `Range_k` channel (`k ∈ {2, 4, 5, 16}`);
//!   `k` rows × 1 preprocessed column (the value) + 1 multiplicity. Each
//!   producer's `log_size = ceil(log2(k))`, padded with row-`0`
//!   repetition for `k ∉ {1, 2, 4, 16}`; see [`range_log_size`] and
//!   [`crate::preprocessed`].
//!
//! Every preprocessed-column ID is namespaced under the `"sha256_"` prefix
//! so it cannot collide with other modules' tables in a combined workspace
//! proof. The `id()` constructors live next to their evaluators so the
//! matching trace generator (`crate::preprocessed`) and the evaluator stay
//! in lock-step.

use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, Relation, RelationEntry,
};

use crate::tables_local::RANGE_8;

// Re-export shorthand so the `stark` module imports types from one place.
pub use crate::relations::Sha256Relations;

// ---------------------------------------------------------------------------
// Preprocessed-column ID conventions
// ---------------------------------------------------------------------------

/// Stable namespace prefix for every SHA-256 preprocessed column ID.
/// Keeps these from colliding with other modules' tables when the integration
/// crate combines multiple AIRs into one proof.
pub const ID_PREFIX: &str = "sha256_";
pub const SHARED_ID_PREFIX: &str = "sha_shared_";

fn id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{ID_PREFIX}{name}"),
    }
}

fn consumer_id(instance_namespace: &str, name: &str) -> PreProcessedColumnId {
    if instance_namespace.is_empty() {
        return id(name);
    }
    let mut encoded_namespace = String::new();
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for &byte in instance_namespace.as_bytes() {
        encoded_namespace.push(HEX[usize::from(byte >> 4)] as char);
        encoded_namespace.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    id(&format!(
        "instance_{}_{}_{}",
        instance_namespace.len(),
        encoded_namespace,
        name
    ))
}

fn shared_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{SHARED_ID_PREFIX}{name}"),
    }
}

/// Which `Range_k` table a producer or consumer fires against. The lookup
/// pins one value into `[0, k)`.
///
/// **N1 — `Range8` is reserved for byte checks.**
/// `Range2`/`Range4`/`Range5` size mod-2³² add-carry checks (per the
/// `crate::headroom` audit, the carry of a `k`-addend add lives in
/// `[0, k)`). `Range8`, by contrast, is the 2⁸-row table used for terminal
/// digest bytes and exposed message bytes. Passing `Range8`
/// to `crate::constraints::emit_mod_2_32_add_linear` is rejected by an
/// explicit `panic!` because no mod-2³² add carry uses the byte range.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RangeKind {
    /// Carries from 2-addend mod-2³² adds (`T2`, `e_new`, `a_new`, finalization).
    Range2,
    /// Carries from the 4-addend message-schedule recurrence.
    Range4,
    /// Carries from the 5-addend `T1` round add.
    Range5,
    /// Terminal bytes (notably the final block's `h_out` digest bytes).
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
/// Stwo's SIMD backend requires `log_size ≥ LOG_N_LANES` (one packed lane
/// minimum), so the small `Range_2`/`Range_4`/`Range_5` tables are padded
/// up to `2^LOG_N_LANES = 16` rows. Padding rows hold value `0` with
/// multiplicity `0`; they do not contribute to the LogUp balance because
/// the consumer only fires lookups on real carries.
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

/// Class-D `is_dummy` selector id for a shared producer's blinded table
/// (Q-015 §4b / p4c Class D). `1` over the reserved dummy-key upper half
/// `[2^L, 2^(L+1))`, `0` over the real lower half `[0, 2^L)`. Keyed by the
/// producer's stable tag so no two producers alias, and namespaced under
/// `sha_shared_` so it never collides with the standalone tables.
pub fn shared_producer_dummy_column_id(producer: SharedProducer) -> PreProcessedColumnId {
    shared_id(&format!("{}_isdummy", producer.tag()))
}

/// Preprocessed-column ID of the single-cell `is_first_row` selector
/// committed at the main `Sha256Eval` trace's `log_n_rows`. The selector
/// is `1` at storage index `Layout::block_slot(0, log_n_rows) = 0` and
/// `0` elsewhere. `Sha256Eval` reads it via `eval.get_preprocessed_column`
/// and pins `is_first_block ≡ is_first_row`, anchoring the §10.3 chain
/// on block 0's IV binding (docs/research/sha256-air-design.md §11 L2).
pub fn is_first_row_column_id() -> PreProcessedColumnId {
    is_first_row_column_id_ns("")
}

pub(crate) fn is_first_row_column_id_ns(instance_namespace: &str) -> PreProcessedColumnId {
    consumer_id(instance_namespace, "is_first_row")
}

/// Preprocessed-column ID of the multi-slot `slot_starts` selector — the
/// multi-message replacement for [`is_first_row_column_id`]: `1` at the
/// first row of every slot region, `0` elsewhere. The ID encodes the full
/// schedule (`n_slots`, `slot_log`, `log_n_rows`) so two different
/// schedules can never alias one committed column (I-5); the fingerprint
/// guard and air-core's id-content invariant fail closed on drift.
pub fn slot_starts_column_id(
    log_n_rows: u32,
    slot_log: u32,
    n_slots: usize,
) -> PreProcessedColumnId {
    id(&format!("slot_starts_{n_slots}x{slot_log}_log{log_n_rows}"))
}

/// Preprocessed-column ID of the multi-slot region selector for slot `s`:
/// `1` on every row of slot `s`'s region, `0` elsewhere (including the
/// tail). Gates per-slot digest/field attribution; schedule-encoded like
/// [`slot_starts_column_id`].
pub fn slot_sel_column_id(
    s: usize,
    log_n_rows: u32,
    slot_log: u32,
    n_slots: usize,
) -> PreProcessedColumnId {
    id(&format!(
        "slot_sel_{s}_{n_slots}x{slot_log}_log{log_n_rows}"
    ))
}

/// Preprocessed IDs of a multi-slot shared-tables consumer, in commit
/// order: `slot_starts`, the 9 round-cyclic columns, then one `slot_sel`
/// per slot. Multi-slot consumers exist only in shared-tables mode, so
/// there is no producer-table prefix. The default round-cyclic IDs are
/// log-content-dependent but id-shared — safe here because a composition
/// mixing default SHA consumers at different `log_n_rows` trips air-core's
/// preprocessed id-content invariant (fail closed at prove time). A standalone
/// consumer that must compose at a different size can opt into disjoint
/// consumer IDs with `Sha256{Prover,Verifier}::with_instance_namespace`.
pub fn multi_consumer_preprocessed_column_ids(
    log_n_rows: u32,
    slot_log: u32,
    n_slots: usize,
) -> Vec<PreProcessedColumnId> {
    let mut out = Vec::with_capacity(10 + n_slots);
    out.push(slot_starts_column_id(log_n_rows, slot_log, n_slots));
    out.extend(round_cyclic_column_ids());
    for s in 0..n_slots {
        out.push(slot_sel_column_id(s, log_n_rows, slot_log, n_slots));
    }
    out
}

/// IDs of the 9 round-cyclic preprocessed columns of the rotated
/// one-row-per-round layout, all at the main trace's `log_n_rows` and all
/// functions of `t = natural_row mod 64` alone: `k_lo`/`k_hi` (the round
/// constant `K[t]`'s 16-bit limbs), the `is_round_{0,1,2,3,15,63}`
/// indicators (working-state boundary selects, padding-row gate,
/// finalization gate), and `is_schedule` (`t ≥ 16` — the schedule-family
/// gate). Emission order here matches
/// `crate::preprocessed::generate_preprocessed_trace`.
pub fn round_cyclic_column_ids() -> [PreProcessedColumnId; 9] {
    round_cyclic_column_ids_ns("")
}

pub(crate) fn round_cyclic_column_ids_ns(instance_namespace: &str) -> [PreProcessedColumnId; 9] {
    [
        consumer_id(instance_namespace, "k_lo"),
        consumer_id(instance_namespace, "k_hi"),
        consumer_id(instance_namespace, "is_round_0"),
        consumer_id(instance_namespace, "is_round_1"),
        consumer_id(instance_namespace, "is_round_2"),
        consumer_id(instance_namespace, "is_round_3"),
        consumer_id(instance_namespace, "is_round_15"),
        consumer_id(instance_namespace, "is_round_63"),
        consumer_id(instance_namespace, "is_schedule"),
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

/// Class-D blinded yield of one shared-table producer row (Q-015 §4b).
///
/// Emits ONE gated entry against the relation: numerator `-(1 − is_dummy)·mult`
/// at the row key.
///
/// On a real row (`is_dummy = 0`) the numerator is `-mult` — identical to the
/// unblinded producer. On a dummy row (`is_dummy = 1`) the numerator is
/// identically `0`, so the dummy row contributes nothing to the LogUp sum for
/// ANY committed `m`. The fresh random blind multiplicities on the reserved
/// upper half therefore stay in the COMMITTED multiplicity column exactly as
/// before (same masking: same blind region, same column, same openings masked)
/// while costing no second fraction — this is what the earlier cancelling PAIR
/// (`-mult` and `+is_dummy·mult`) achieved at twice the interaction/quotient
/// cost.
///
/// Soundness: `is_dummy` is PREPROCESSED (trusted), so a malicious prover
/// cannot un-gate a dummy row to emit a real key — on the whole dummy region
/// the emitted numerator is forced to `0`. Dummy keys (`≥ 2^16`, unreachable by
/// honest consumers) therefore remain unreachable, and the resulting LogUp
/// balance is exactly that of the unblinded table. Both the key and the gate
/// come from committed/preprocessed data the verifier reconstructs, so there is
/// no free claimed-sum term (P4b blind_claim-hole caution).
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

/// Producer for one `Range_k` lookup table (`k ∈ {2, 4, 5, 8}`).
///
/// Reads one preprocessed value column (the row content
/// `crate::tables_local::range_k()`, padded with value `0` up to
/// `2^range_log_size(kind)` rows for `k < 2^LOG_N_LANES`) and one
/// multiplicity column. Yields each row at `-multiplicity` against the
/// matching range relation.
///
/// **Soundness role.** Together with the consumer-side
/// `add_to_relation(rel, +1, &[carry])` calls inside
/// `crate::constraints::emit_mod_2_32_add_linear` and the terminal
/// `Range_8` lookups on every real-block `h_out` byte (inlined in
/// `Sha256Eval::evaluate` via `wire_range_check`), this component
/// completes the LogUp loop that pins each carry into `[0, k)` and the
/// digest bytes into `[0, 2⁸)` — closing the soundness gap the headroom
/// audit (`crate::headroom`) reduces to.
#[derive(Clone)]
pub struct RangeKEval {
    pub log_size: u32,
    pub kind: RangeKind,
    pub relations: Sha256Relations,
    pub shared_tables: bool,
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

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type RangeKComponent = FrameworkComponent<RangeKEval>;

// ---------------------------------------------------------------------------
// Paired shared-table producer component (R2 fraction batching)
// ---------------------------------------------------------------------------

/// One shared-SHA producer table, identified by which lookup it serves. Used
/// to co-locate two same-`log_size` producers in a single component so their
/// LogUp fractions pair into one `SecureField` interaction column
/// (`finalize_logup_in_pairs`), halving the committed interaction width for
/// the paired half. The producer's preprocessed columns, multiplicity column,
/// relation, and fraction are byte-for-byte identical to the standalone
/// `RangeKEval` form — only the column packaging changes.
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

    /// Class-D committed row count: one log above the real width. The upper
    /// half is the reserved dummy-key region carrying fresh random blind
    /// multiplicities (Q-015 §4b / p4c Class D). Every committed column of this
    /// producer — preprocessed value/group cells, `is_dummy` selector,
    /// multiplicity trace, interaction fraction — lives at this size.
    pub fn blind_log_size(self) -> u32 {
        self.log_size() + 1
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
/// fractions pair into a single interaction column. A one-producer instance is
/// the odd remainder and behaves exactly like the corresponding standalone
/// producer eval.
#[derive(Clone)]
pub struct SharedProducerPairEval {
    pub log_size: u32,
    /// 1 or 2 producers, all of `log_size`. Read in this order; the trace and
    /// interaction generators must lay their multiplicity/fraction columns in
    /// the same order (see `shared_tables::PRODUCER_PAIRS`).
    pub producers: Vec<SharedProducer>,
    pub relations: Sha256Relations,
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
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type SharedProducerPairComponent = FrameworkComponent<SharedProducerPairEval>;

// ---------------------------------------------------------------------------
// Aggregate IDs
// ---------------------------------------------------------------------------

/// Every preprocessed-column ID committed by this crate, in the exact
/// order [`crate::preprocessed::generate_preprocessed_trace`] emits the
/// matching `CircleEvaluation`s. The list mirrors the per-component
/// `*_column_ids` getters concatenated in **table-major** order — keep
/// both sides in sync or the verifier will read the wrong column.
pub fn all_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    all_preprocessed_column_ids_ns("")
}

pub(crate) fn all_preprocessed_column_ids_ns(
    instance_namespace: &str,
) -> Vec<PreProcessedColumnId> {
    let mut out = Vec::new();
    // 4 range tables, in `RANGE_TABLES` order.
    for &kind in RANGE_TABLES {
        out.push(range_column_id(kind));
    }
    // 1 `is_first_row` selector sized to the main `Sha256Eval` trace. Read
    // by the consumer eval via `get_preprocessed_column` (not by any
    // producer component), so it lives at the tail of the ID list and is
    // not allocated to a producer component.
    out.push(is_first_row_column_id_ns(instance_namespace));
    // 9 round-cyclic columns of the rotated layout (K limbs + round
    // indicators + schedule gate), also consumer-read via
    // `get_preprocessed_column` and sized to the main trace.
    out.extend(round_cyclic_column_ids_ns(instance_namespace));
    out
}

pub fn consumer_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    consumer_preprocessed_column_ids_ns("")
}

pub(crate) fn consumer_preprocessed_column_ids_ns(
    instance_namespace: &str,
) -> Vec<PreProcessedColumnId> {
    let mut out = Vec::new();
    out.push(is_first_row_column_id_ns(instance_namespace));
    out.extend(round_cyclic_column_ids_ns(instance_namespace));
    out
}

pub fn shared_table_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    // Class D: each producer contributes its value column followed by
    // its `is_dummy` selector, in the exact order `SharedProducer::emit_entry`
    // reads them (value cols via `get_preprocessed_column`, then the dummy
    // selector). `crate::preprocessed::generate_shared_table_preprocessed_trace`
    // emits the matching `CircleEvaluation`s in this same per-producer order.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_instance_namespace_preserves_exact_legacy_ids() {
        let expected = [
            "sha256_range_2",
            "sha256_range_4",
            "sha256_range_5",
            "sha256_range_8",
            "sha256_is_first_row",
            "sha256_k_lo",
            "sha256_k_hi",
            "sha256_is_round_0",
            "sha256_is_round_1",
            "sha256_is_round_2",
            "sha256_is_round_3",
            "sha256_is_round_15",
            "sha256_is_round_63",
            "sha256_is_schedule",
        ];
        assert_eq!(
            all_preprocessed_column_ids_ns("")
                .iter()
                .map(|id| id.id.as_str())
                .collect::<Vec<_>>(),
            expected
        );
        assert_eq!(
            all_preprocessed_column_ids_ns(""),
            all_preprocessed_column_ids()
        );
        assert_eq!(
            consumer_preprocessed_column_ids_ns(""),
            consumer_preprocessed_column_ids()
        );
        assert_eq!(round_cyclic_column_ids_ns(""), round_cyclic_column_ids());
        assert_eq!(is_first_row_column_id_ns(""), is_first_row_column_id());
    }

    #[test]
    fn instance_namespace_id_encoding_is_injective_and_consumer_only() {
        let namespaced = all_preprocessed_column_ids_ns("A/\0");
        let other = all_preprocessed_column_ids_ns("A_/\0");
        assert_ne!(namespaced, other);
        assert_eq!(namespaced[4].id, "sha256_instance_3_412f00_is_first_row");
        assert_eq!(namespaced[5].id, "sha256_instance_3_412f00_k_lo");

        let legacy = all_preprocessed_column_ids();
        assert_eq!(
            &namespaced[..RANGE_TABLES.len()],
            &legacy[..RANGE_TABLES.len()],
            "standalone table-provider IDs stay globally deduplicable"
        );
        assert!(shared_table_preprocessed_column_ids()
            .iter()
            .all(|id| id.id.starts_with(SHARED_ID_PREFIX) && !id.id.contains("412f00")));
    }
}
