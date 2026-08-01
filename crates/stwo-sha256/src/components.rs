//! Producer components for the SHA-256 preprocessed lookup tables.
//!
//! [`crate::constraints::Sha256Eval`] consumes each lookup with positive
//! multiplicity. A producer yields the same row with the matching negative
//! multiplicity. The total LogUp sum must be zero.
//!
//! Each table has preprocessed row columns and one multiplicity column for each
//! relation. It emits `add_to_relation(rel, -multiplicity, &row_cells)` and
//! then calls `finalize_logup_in_pairs()`.
//!
//! Producer components:
//!
//! - [`RangeKEval`] × 4, one for each [`RangeKind`]. Each producer has one
//!   preprocessed value column and one multiplicity column. Small tables use
//!   trailing value-0 rows to meet the SIMD minimum; see [`range_log_size`]
//!   and [`crate::preprocessed`].
//!
//! Each preprocessed-column ID uses the `"sha256_"` namespace. This namespace
//! prevents collisions with other proof modules.

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
/// `Range2`/`Range4`/`Range5` size mod-2³² add-carry checks (per the
/// `crate::headroom` audit, the carry of a `k`-addend add lives in
/// `[0, k)`). `Range8`, by contrast, is the 2⁸-row table used for terminal
/// digest bytes. Passing `Range8` to
/// `crate::constraints::emit_mod_2_32_add_linear` is rejected by an explicit
/// `panic!` because no mod-2³² add carry uses the byte range.
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

/// Class-D `is_dummy` selector ID for a shared producer's blinded table.
/// It is `1` over the reserved dummy-key upper half
/// `[2^L, 2^(L+1))`, `0` over the real lower half `[0, 2^L)`. Keyed by the
/// blinded log size because equal-sized producers have the same selector.
/// This lets the preprocessing tree commit one physical selector for all
/// equal-sized tables.
pub fn shared_producer_dummy_column_id(producer: SharedProducer) -> PreProcessedColumnId {
    shared_id(&format!("dummy_log_{}", producer.blind_log_size()))
}

/// Preprocessed-column ID of the single-cell `is_first_row` selector
/// committed at the main `Sha256Eval` trace's `log_n_rows`. The selector
/// is `1` at natural row zero and `0` elsewhere. `Sha256Eval` reads it via
/// `eval.get_preprocessed_column`. It anchors the enabled row prefix at block
/// zero.
pub fn is_first_row_column_id() -> PreProcessedColumnId {
    is_first_row_column_id_ns("")
}

pub(crate) fn is_first_row_column_id_ns(instance_namespace: &str) -> PreProcessedColumnId {
    consumer_id(instance_namespace, "is_first_row")
}

/// Preprocessed-column ID of the first round-row selector. The selector is
/// one at natural row [`crate::trace::STATE_SEED_ROWS`] and zero elsewhere.
pub fn is_first_round_column_id() -> PreProcessedColumnId {
    is_first_round_column_id_ns("")
}

pub(crate) fn is_first_round_column_id_ns(instance_namespace: &str) -> PreProcessedColumnId {
    consumer_id(instance_namespace, "is_first_round")
}

/// Preprocessed active-row selector for the 16-row digest bridge.
pub fn digest_bridge_active_column_id() -> PreProcessedColumnId {
    digest_bridge_active_column_id_ns("")
}

pub(crate) fn digest_bridge_active_column_id_ns(instance_namespace: &str) -> PreProcessedColumnId {
    consumer_id(instance_namespace, "digest_bridge_active")
}

/// IDs of the eight block-cyclic preprocessed columns, all at the main
/// trace's `log_n_rows`. A block has three seed rows followed by 64 round
/// rows. Round constants and selectors are zero on seed rows. Emission order
/// here matches
/// `crate::preprocessed::generate_preprocessed_trace`.
pub fn round_cyclic_column_ids() -> [PreProcessedColumnId; 8] {
    round_cyclic_column_ids_ns("")
}

pub(crate) fn round_cyclic_column_ids_ns(instance_namespace: &str) -> [PreProcessedColumnId; 8] {
    [
        consumer_id(instance_namespace, "k_lo"),
        consumer_id(instance_namespace, "k_hi"),
        consumer_id(instance_namespace, "is_round_0"),
        consumer_id(instance_namespace, "is_round_15"),
        consumer_id(instance_namespace, "is_round_63"),
        consumer_id(instance_namespace, "is_schedule"),
        consumer_id(instance_namespace, "is_round"),
        consumer_id(instance_namespace, "round_index"),
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

/// Class-D blinded yield of one shared-table producer row.
///
/// Emits ONE gated entry against the relation: numerator `-(1 − is_dummy)·mult`
/// at the row key.
///
/// On a real row (`is_dummy = 0`), the numerator is `-mult`. On a dummy row
/// (`is_dummy = 1`), the numerator is
/// identically `0`, so the dummy row contributes nothing to the LogUp sum for
/// any committed `m`. Random blind multiplicities stay in the committed
/// multiplicity column but do not need a second fraction.
///
/// `is_dummy` is preprocessed, so a prover cannot enable a dummy row. The
/// emitted numerator is `0` in the complete dummy region. Honest consumers
/// cannot emit dummy keys (`≥ 2^16`). The verifier reconstructs the key and
/// gate, so no free claimed-sum term exists.
///
/// Degree: `(1 − is_dummy)·mult` = preprocessed × trace = degree 2, within the
/// `D ≤ 3` budget under `max_constraint_log_degree_bound = blind_log_size + 1`.
/// Each producer emits one fraction.
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
/// `Range_8` lookups on the final digest bytes in `crate::digest_bridge`, this component
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

// ---------------------------------------------------------------------------
// Paired shared-table producer component
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
    /// multiplicities. Every committed column of this
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
    // Two boundary selectors sized to the main `Sha256Eval` trace. Read
    // by the consumer eval via `get_preprocessed_column` (not by any
    // producer component), so it lives at the tail of the ID list and is
    // not allocated to a producer component.
    out.push(is_first_row_column_id_ns(instance_namespace));
    out.push(is_first_round_column_id_ns(instance_namespace));
    // Eight block-cyclic columns (K limbs, round indicators, schedule and
    // round gates, and round index), also consumer-read via
    // `get_preprocessed_column` and sized to the main trace.
    out.extend(round_cyclic_column_ids_ns(instance_namespace));
    out.push(digest_bridge_active_column_id_ns(instance_namespace));
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
    out.push(is_first_round_column_id_ns(instance_namespace));
    out.extend(round_cyclic_column_ids_ns(instance_namespace));
    out.push(digest_bridge_active_column_id_ns(instance_namespace));
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
    fn empty_instance_namespace_preserves_exact_unnamespaced_ids() {
        let expected = [
            "sha256_range_2",
            "sha256_range_4",
            "sha256_range_5",
            "sha256_range_8",
            "sha256_is_first_row",
            "sha256_is_first_round",
            "sha256_k_lo",
            "sha256_k_hi",
            "sha256_is_round_0",
            "sha256_is_round_15",
            "sha256_is_round_63",
            "sha256_is_schedule",
            "sha256_is_round",
            "sha256_round_index",
            "sha256_digest_bridge_active",
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
        assert_eq!(is_first_round_column_id_ns(""), is_first_round_column_id());
        assert_eq!(
            digest_bridge_active_column_id_ns(""),
            digest_bridge_active_column_id()
        );
    }

    #[test]
    fn instance_namespace_id_encoding_is_injective_and_consumer_only() {
        let namespaced = all_preprocessed_column_ids_ns("A/\0");
        let other = all_preprocessed_column_ids_ns("A_/\0");
        assert_ne!(namespaced, other);
        assert_eq!(namespaced[4].id, "sha256_instance_3_412f00_is_first_row");
        assert_eq!(namespaced[5].id, "sha256_instance_3_412f00_is_first_round");
        assert_eq!(namespaced[6].id, "sha256_instance_3_412f00_k_lo");

        let unnamespaced = all_preprocessed_column_ids();
        assert_eq!(
            &namespaced[..RANGE_TABLES.len()],
            &unnamespaced[..RANGE_TABLES.len()],
            "standalone table-provider IDs stay globally deduplicable"
        );
        assert!(shared_table_preprocessed_column_ids()
            .iter()
            .all(|id| id.id.starts_with(SHARED_ID_PREFIX) && !id.id.contains("412f00")));
    }

    #[test]
    fn equal_blinded_domains_share_the_dummy_selector() {
        let range2 = shared_producer_dummy_column_id(SharedProducer::Range(RangeKind::Range2));
        let range4 = shared_producer_dummy_column_id(SharedProducer::Range(RangeKind::Range4));
        let range5 = shared_producer_dummy_column_id(SharedProducer::Range(RangeKind::Range5));
        let range8 = shared_producer_dummy_column_id(SharedProducer::Range(RangeKind::Range8));
        assert_eq!(range2, range4);
        assert_eq!(range2, range5);
        assert_ne!(range2, range8);
    }
}
