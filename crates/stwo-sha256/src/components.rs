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
//! Wired components (23 total, one `Sha256Eval` consumer + 22 producers):
//!
//! - [`SigmaDecodeEval`] × 8 — one per (function, side) of the σ/Σ decode
//!   tables; each has 2¹⁶ rows × 5 preprocessed columns + 1 multiplicity.
//! - [`MajChEval`] × 1 — the packed Maj/Ch table; 2^(3·W) rows, 5
//!   preprocessed columns (`a, b, c, maj, ch`), 2 multiplicities (one
//!   for Maj, one for Ch).
//! - [`Xor8Eval`] × 1 — the generic byte XOR table; 2¹⁶ rows × 3
//!   preprocessed columns + 1 multiplicity.
//! - [`RoundSplitPackEval`] × 4 — one per (partition, half) of the
//!   round-side split-and-pack; 2¹⁶ rows × 4 preprocessed (key + 3
//!   packed groups) + 1 multiplicity.
//! - [`SigmaSplitPackEval`] × 4 — one per (σ-partition, half); 2¹⁶ rows
//!   × 3 preprocessed (key + 2 packed) + 1 multiplicity.
//! - [`RangeKEval`] × 4 — one per `Range_k` channel (`k ∈ {2, 4, 5, 16}`);
//!   `k` rows × 1 preprocessed column (the value) + 1 multiplicity. Each
//!   producer's `log_size = ceil(log2(k))`, padded with row-`0`
//!   repetition for `k ∉ {1, 2, 4, 16}`; see [`range_log_size`] and
//!   [`crate::preprocessed`].
//!
//! Every preprocessed-column ID is namespaced under the `"sha256_"` prefix
//! so it cannot collide with the ECDSA-stream tables in a future combined
//! workspace proof. The `id()` constructors live next to their evaluators
//! so the matching trace generator (`crate::preprocessed`) and the
//! evaluator stay in lock-step.

use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, Relation, RelationEntry,
};

use crate::partitions::SigmaFn;
use crate::tables::{Half, Half16, LowerSigmaPartition, RoundPartition};
use crate::tables_local::RANGE_16;

// Re-export shorthand so the `stark` module imports types from one place.
pub use crate::relations::Sha256Relations;

// ---------------------------------------------------------------------------
// Preprocessed-column ID conventions
// ---------------------------------------------------------------------------

/// Stable namespace prefix for every SHA-256 preprocessed column ID.
/// Keeps these from colliding with the ECDSA stream's tables when the
/// integration crate combines both AIRs into one proof.
pub const ID_PREFIX: &str = "sha256_";

fn id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{ID_PREFIX}{name}"),
    }
}

/// Tag the (function, half) of one σ/Σ decode table.
fn decode_tag(f: SigmaFn, half: Half) -> &'static str {
    match (f, half) {
        (SigmaFn::Sigma0, Half::S) => "sigma0_s",
        (SigmaFn::Sigma0, Half::SComplement) => "sigma0_sp",
        (SigmaFn::Sigma1, Half::S) => "sigma1_s",
        (SigmaFn::Sigma1, Half::SComplement) => "sigma1_sp",
        (SigmaFn::LowerSigma0, Half::S) => "lsigma0_s",
        (SigmaFn::LowerSigma0, Half::SComplement) => "lsigma0_sp",
        (SigmaFn::LowerSigma1, Half::S) => "lsigma1_s",
        (SigmaFn::LowerSigma1, Half::SComplement) => "lsigma1_sp",
    }
}

fn round_split_tag(p: RoundPartition, h: Half16) -> &'static str {
    match (p, h) {
        (RoundPartition::Sigma0AndMaj, Half16::Lo) => "sp_sigma0_lo",
        (RoundPartition::Sigma0AndMaj, Half16::Hi) => "sp_sigma0_hi",
        (RoundPartition::Sigma1AndCh, Half16::Lo) => "sp_sigma1_lo",
        (RoundPartition::Sigma1AndCh, Half16::Hi) => "sp_sigma1_hi",
    }
}

fn sigma_split_tag(p: LowerSigmaPartition, h: Half16) -> &'static str {
    match (p, h) {
        (LowerSigmaPartition::LowerSigma0, Half16::Lo) => "sp_lsigma0_lo",
        (LowerSigmaPartition::LowerSigma0, Half16::Hi) => "sp_lsigma0_hi",
        (LowerSigmaPartition::LowerSigma1, Half16::Lo) => "sp_lsigma1_lo",
        (LowerSigmaPartition::LowerSigma1, Half16::Hi) => "sp_lsigma1_hi",
    }
}

/// Which `Range_k` table a producer or consumer fires against. The lookup
/// pins one value into `[0, k)`.
///
/// **N1 — `Range16` is reserved for terminal-limb checks.**
/// `Range2`/`Range4`/`Range5` size mod-2³² add-carry checks (per the
/// `crate::headroom` audit, the carry of a `k`-addend add lives in
/// `[0, k)`). `Range16`, by contrast, is the 2¹⁶-row table used only for
/// terminal 16-bit limb checks — the final block's `h_out` digest limbs
/// today (`crate::constraints::Sha256Eval::evaluate`). Passing `Range16`
/// to `crate::constraints::emit_mod_2_32_add_linear` is rejected by an
/// explicit `panic!` because no mod-2³² add carry needs a 16-bit range.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RangeKind {
    /// Carries from 2-addend mod-2³² adds (`T2`, `e_new`, `a_new`, finalization).
    Range2,
    /// Carries from the 4-addend message-schedule recurrence.
    Range4,
    /// Carries from the 5-addend `T1` round add.
    Range5,
    /// Terminal 16-bit limbs (notably the final block's `h_out` digest).
    /// **Not** used for mod-2³² add carries — those land in
    /// `Range2`/`Range4`/`Range5` per the headroom audit. See the enum
    /// doc-comment for the rationale.
    Range16,
}

impl RangeKind {
    /// The exclusive upper bound `k` of the range `[0, k)`.
    #[inline]
    pub const fn bound(self) -> u32 {
        match self {
            RangeKind::Range2 => crate::headroom::RANGE_2,
            RangeKind::Range4 => crate::headroom::RANGE_4,
            RangeKind::Range5 => crate::headroom::RANGE_5,
            RangeKind::Range16 => RANGE_16,
        }
    }

    /// Short tag used in preprocessed-column IDs (`"range_2"`, etc.).
    #[inline]
    pub const fn tag(self) -> &'static str {
        match self {
            RangeKind::Range2 => "range_2",
            RangeKind::Range4 => "range_4",
            RangeKind::Range5 => "range_5",
            RangeKind::Range16 => "range_16",
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

/// Preprocessed-column ID of the single-cell `is_first_row` selector
/// committed at the main `Sha256Eval` trace's `log_n_rows`. The selector
/// is `1` at storage index `Layout::block_slot(0, log_n_rows) = 0` and
/// `0` elsewhere. `Sha256Eval` reads it via `eval.get_preprocessed_column`
/// and pins `is_first_block ≡ is_first_row`, anchoring the §10.3 chain
/// on block 0's IV binding (docs/research/sha256-air-design.md §11 L2).
pub fn is_first_row_column_id() -> PreProcessedColumnId {
    id("is_first_row")
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
    [
        id("k_lo"),
        id("k_hi"),
        id("is_round_0"),
        id("is_round_1"),
        id("is_round_2"),
        id("is_round_3"),
        id("is_round_15"),
        id("is_round_63"),
        id("is_schedule"),
    ]
}

/// IDs of the 5 preprocessed columns of one decode table.
/// Order matches `crate::relations::SIGMA_DECODE_REL_SIZE`'s row shape:
/// `(key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi)`.
pub fn decode_column_ids(f: SigmaFn, half: Half) -> [PreProcessedColumnId; 5] {
    let t = decode_tag(f, half);
    [
        id(&format!("decode_{t}_key")),
        id(&format!("decode_{t}_omain_lo")),
        id(&format!("decode_{t}_omain_hi")),
        id(&format!("decode_{t}_o2_lo")),
        id(&format!("decode_{t}_o2_hi")),
    ]
}

/// IDs of the 5 preprocessed columns of the packed Maj/Ch table.
/// Order: `(a, b, c, maj, ch)`.
pub fn maj_ch_column_ids() -> [PreProcessedColumnId; 5] {
    [
        id("maj_ch_a"),
        id("maj_ch_b"),
        id("maj_ch_c"),
        id("maj_ch_maj"),
        id("maj_ch_ch"),
    ]
}

/// IDs of the 3 preprocessed columns of the xor_8 table.
/// Order: `(x, y, z)`.
pub fn xor_8_column_ids() -> [PreProcessedColumnId; 3] {
    [id("xor_8_x"), id("xor_8_y"), id("xor_8_z")]
}

/// IDs of the 5 preprocessed columns of one round-side split-and-pack
/// table. Order: `(key, g0, g1, g2, g3)` matching
/// `crate::relations::ROUND_SPLIT_PACK_REL_SIZE` (the four W=6 sub-groups
/// in this half).
pub fn round_split_pack_column_ids(p: RoundPartition, h: Half16) -> [PreProcessedColumnId; 5] {
    let t = round_split_tag(p, h);
    [
        id(&format!("{t}_key")),
        id(&format!("{t}_g0")),
        id(&format!("{t}_g1")),
        id(&format!("{t}_g2")),
        id(&format!("{t}_g3")),
    ]
}

/// IDs of the 3 preprocessed columns of one σ-side split-and-pack table.
/// Order: `(key, packed_s, packed_s_complement)` matching
/// `crate::relations::SIGMA_SPLIT_PACK_REL_SIZE`.
pub fn sigma_split_pack_column_ids(p: LowerSigmaPartition, h: Half16) -> [PreProcessedColumnId; 3] {
    let t = sigma_split_tag(p, h);
    [
        id(&format!("{t}_key")),
        id(&format!("{t}_s")),
        id(&format!("{t}_sp")),
    ]
}

// ---------------------------------------------------------------------------
// σ/Σ decode-table component
// ---------------------------------------------------------------------------

/// Producer for one of the eight σ/Σ decode tables.
///
/// Reads its 5 preprocessed columns and 1 multiplicity column, yields each
/// row at `-multiplicity` against the matching `Sigma{0,1}{,Lower}Decode{S,SPrime}`
/// relation tag. The relation is selected via `f` × `half`.
#[derive(Clone)]
pub struct SigmaDecodeEval {
    pub log_size: u32,
    pub f: SigmaFn,
    pub half: Half,
    pub relations: Sha256Relations,
}

impl FrameworkEval for SigmaDecodeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = decode_column_ids(self.f, self.half);
        let key = eval.get_preprocessed_column(cols[0].clone());
        let o_main_lo = eval.get_preprocessed_column(cols[1].clone());
        let o_main_hi = eval.get_preprocessed_column(cols[2].clone());
        let o2_partial_lo = eval.get_preprocessed_column(cols[3].clone());
        let o2_partial_hi = eval.get_preprocessed_column(cols[4].clone());
        let mult = eval.next_trace_mask();

        let values = [key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi];

        // Select the matching relation handle, kept generic by branching
        // through a small `dyn Relation`-style closure. Stwo's
        // `add_to_relation` is generic on `R: Relation<…>`; we can't pass
        // a `&dyn Relation` so we inline the 8-way match.
        let neg_mult = -E::EF::from(mult);
        use crate::relations::*;
        match (self.f, self.half) {
            (SigmaFn::Sigma0, Half::S) => emit::<E, Sigma0DecodeS>(
                &mut eval,
                &self.relations.sigma_decode.sigma0_s,
                neg_mult,
                &values,
            ),
            (SigmaFn::Sigma0, Half::SComplement) => emit::<E, Sigma0DecodeSPrime>(
                &mut eval,
                &self.relations.sigma_decode.sigma0_s_complement,
                neg_mult,
                &values,
            ),
            (SigmaFn::Sigma1, Half::S) => emit::<E, Sigma1DecodeS>(
                &mut eval,
                &self.relations.sigma_decode.sigma1_s,
                neg_mult,
                &values,
            ),
            (SigmaFn::Sigma1, Half::SComplement) => emit::<E, Sigma1DecodeSPrime>(
                &mut eval,
                &self.relations.sigma_decode.sigma1_s_complement,
                neg_mult,
                &values,
            ),
            (SigmaFn::LowerSigma0, Half::S) => emit::<E, LowerSigma0DecodeS>(
                &mut eval,
                &self.relations.sigma_decode.lower_sigma0_s,
                neg_mult,
                &values,
            ),
            (SigmaFn::LowerSigma0, Half::SComplement) => emit::<E, LowerSigma0DecodeSPrime>(
                &mut eval,
                &self.relations.sigma_decode.lower_sigma0_s_complement,
                neg_mult,
                &values,
            ),
            (SigmaFn::LowerSigma1, Half::S) => emit::<E, LowerSigma1DecodeS>(
                &mut eval,
                &self.relations.sigma_decode.lower_sigma1_s,
                neg_mult,
                &values,
            ),
            (SigmaFn::LowerSigma1, Half::SComplement) => emit::<E, LowerSigma1DecodeSPrime>(
                &mut eval,
                &self.relations.sigma_decode.lower_sigma1_s_complement,
                neg_mult,
                &values,
            ),
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Tiny helper: emit one `RelationEntry` with the given multiplicity, then
/// finalize. Generic over `R: Relation<E::F, E::EF>` so each table can pick
/// its relation type without a `dyn` indirection.
fn emit<E: EvalAtRow, R: Relation<E::F, E::EF>>(
    eval: &mut E,
    rel: &R,
    mult: E::EF,
    values: &[E::F],
) {
    eval.add_to_relation(RelationEntry::new(rel, mult, values));
}

pub type SigmaDecodeComponent = FrameworkComponent<SigmaDecodeEval>;

// ---------------------------------------------------------------------------
// Packed Maj/Ch component
// ---------------------------------------------------------------------------

/// Producer for the packed Maj/Ch lookup table at group-width `W`.
///
/// One physical table, two relations: Maj keys on `(a, b, c, maj)`, Ch
/// keys on `(a, b, c, ch)`. The component reads 5 preprocessed columns
/// (`a, b, c, maj, ch`) and 2 multiplicity columns (one per relation),
/// emitting two `add_to_relation` calls per row.
#[derive(Clone)]
pub struct MajChEval {
    pub log_size: u32,
    pub relations: Sha256Relations,
}

impl FrameworkEval for MajChEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = maj_ch_column_ids();
        let a = eval.get_preprocessed_column(cols[0].clone());
        let b = eval.get_preprocessed_column(cols[1].clone());
        let c = eval.get_preprocessed_column(cols[2].clone());
        let maj_val = eval.get_preprocessed_column(cols[3].clone());
        let ch_val = eval.get_preprocessed_column(cols[4].clone());

        let mult_maj = eval.next_trace_mask();
        let mult_ch = eval.next_trace_mask();

        eval.add_to_relation(RelationEntry::new(
            &self.relations.maj,
            -E::EF::from(mult_maj),
            &[a.clone(), b.clone(), c.clone(), maj_val],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.relations.ch,
            -E::EF::from(mult_ch),
            &[a, b, c, ch_val],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type MajChComponent = FrameworkComponent<MajChEval>;

// ---------------------------------------------------------------------------
// xor_8 component
// ---------------------------------------------------------------------------

/// Producer for the generic 2¹⁶-row byte-XOR table.
#[derive(Clone)]
pub struct Xor8Eval {
    pub log_size: u32,
    pub relations: Sha256Relations,
}

impl FrameworkEval for Xor8Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = xor_8_column_ids();
        let x = eval.get_preprocessed_column(cols[0].clone());
        let y = eval.get_preprocessed_column(cols[1].clone());
        let z = eval.get_preprocessed_column(cols[2].clone());
        let mult = eval.next_trace_mask();

        #[cfg(not(feature = "gkr-spike"))]
        eval.add_to_relation(RelationEntry::new(
            &self.relations.xor_8,
            -E::EF::from(mult),
            &[x, y, z],
        ));
        #[cfg(feature = "gkr-spike")]
        let _ = (x, y, z, mult);

        #[cfg(not(feature = "gkr-spike"))]
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type Xor8Component = FrameworkComponent<Xor8Eval>;

// ---------------------------------------------------------------------------
// Round-side split-and-pack component
// ---------------------------------------------------------------------------

/// Producer for one of the four round-side split-and-pack tables.
#[derive(Clone)]
pub struct RoundSplitPackEval {
    pub log_size: u32,
    pub partition: RoundPartition,
    pub half: Half16,
    pub relations: Sha256Relations,
}

impl FrameworkEval for RoundSplitPackEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = round_split_pack_column_ids(self.partition, self.half);
        let key = eval.get_preprocessed_column(cols[0].clone());
        let g0 = eval.get_preprocessed_column(cols[1].clone());
        let g1 = eval.get_preprocessed_column(cols[2].clone());
        let g2 = eval.get_preprocessed_column(cols[3].clone());
        let g3 = eval.get_preprocessed_column(cols[4].clone());
        let mult = eval.next_trace_mask();
        let values = [key, g0, g1, g2, g3];
        let neg = -E::EF::from(mult);
        use crate::relations::*;
        match (self.partition, self.half) {
            (RoundPartition::Sigma0AndMaj, Half16::Lo) => emit::<E, Sigma0SplitPackLo>(
                &mut eval,
                &self.relations.split_pack.sigma0_lo,
                neg,
                &values,
            ),
            (RoundPartition::Sigma0AndMaj, Half16::Hi) => emit::<E, Sigma0SplitPackHi>(
                &mut eval,
                &self.relations.split_pack.sigma0_hi,
                neg,
                &values,
            ),
            (RoundPartition::Sigma1AndCh, Half16::Lo) => emit::<E, Sigma1SplitPackLo>(
                &mut eval,
                &self.relations.split_pack.sigma1_lo,
                neg,
                &values,
            ),
            (RoundPartition::Sigma1AndCh, Half16::Hi) => emit::<E, Sigma1SplitPackHi>(
                &mut eval,
                &self.relations.split_pack.sigma1_hi,
                neg,
                &values,
            ),
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type RoundSplitPackComponent = FrameworkComponent<RoundSplitPackEval>;

// ---------------------------------------------------------------------------
// σ-side split-and-pack component
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct SigmaSplitPackEval {
    pub log_size: u32,
    pub partition: LowerSigmaPartition,
    pub half: Half16,
    pub relations: Sha256Relations,
}

impl FrameworkEval for SigmaSplitPackEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = sigma_split_pack_column_ids(self.partition, self.half);
        let key = eval.get_preprocessed_column(cols[0].clone());
        let packed_s = eval.get_preprocessed_column(cols[1].clone());
        let packed_sp = eval.get_preprocessed_column(cols[2].clone());
        let mult = eval.next_trace_mask();
        let values = [key, packed_s, packed_sp];
        let neg = -E::EF::from(mult);
        use crate::relations::*;
        match (self.partition, self.half) {
            (LowerSigmaPartition::LowerSigma0, Half16::Lo) => emit::<E, LowerSigma0SplitPackLo>(
                &mut eval,
                &self.relations.split_pack.lower_sigma0_lo,
                neg,
                &values,
            ),
            (LowerSigmaPartition::LowerSigma0, Half16::Hi) => emit::<E, LowerSigma0SplitPackHi>(
                &mut eval,
                &self.relations.split_pack.lower_sigma0_hi,
                neg,
                &values,
            ),
            (LowerSigmaPartition::LowerSigma1, Half16::Lo) => emit::<E, LowerSigma1SplitPackLo>(
                &mut eval,
                &self.relations.split_pack.lower_sigma1_lo,
                neg,
                &values,
            ),
            (LowerSigmaPartition::LowerSigma1, Half16::Hi) => emit::<E, LowerSigma1SplitPackHi>(
                &mut eval,
                &self.relations.split_pack.lower_sigma1_hi,
                neg,
                &values,
            ),
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type SigmaSplitPackComponent = FrameworkComponent<SigmaSplitPackEval>;

// ---------------------------------------------------------------------------
// Range_k component
// ---------------------------------------------------------------------------

/// Producer for one `Range_k` lookup table (`k ∈ {2, 4, 5, 16}`).
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
/// `Range_16` lookups on every real-block `h_out` limb (inlined in
/// `Sha256Eval::evaluate` via `wire_range_check`), this component
/// completes the LogUp loop that pins each carry into `[0, k)` and the
/// digest limbs into `[0, 2¹⁶)` — closing the soundness gap the headroom
/// audit (`crate::headroom`) reduces to.
#[derive(Clone)]
pub struct RangeKEval {
    pub log_size: u32,
    pub kind: RangeKind,
    pub relations: Sha256Relations,
}

impl FrameworkEval for RangeKEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(range_column_id(self.kind));
        let mult = eval.next_trace_mask();
        let neg = -E::EF::from(mult);

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
            RangeKind::Range16 => {
                emit::<E, Range16Relation>(&mut eval, &self.relations.range.range_16, neg, &values)
            }
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type RangeKComponent = FrameworkComponent<RangeKEval>;

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
    // 8 decode tables in the order `Sha256Relations::draw`/`SigmaDecodeRelations::draw` uses.
    for (f, h) in DECODE_TABLES {
        out.extend(decode_column_ids(*f, *h));
    }
    // 1 Maj/Ch table — column IDs depend only on table identity, not on
    // `group_width` (which sets the table's row count, not its columns).
    out.extend(maj_ch_column_ids());
    // 1 xor_8 table.
    out.extend(xor_8_column_ids());
    // 4 round-side split-pack tables, then 4 σ-side.
    for (p, h) in ROUND_SPLIT_TABLES {
        out.extend(round_split_pack_column_ids(*p, *h));
    }
    for (p, h) in SIGMA_SPLIT_TABLES {
        out.extend(sigma_split_pack_column_ids(*p, *h));
    }
    // 4 range tables, in `RANGE_TABLES` order.
    for &kind in RANGE_TABLES {
        out.push(range_column_id(kind));
    }
    // 1 `is_first_row` selector sized to the main `Sha256Eval` trace. Read
    // by the consumer eval via `get_preprocessed_column` (not by any
    // producer component), so it lives at the tail of the ID list and is
    // not allocated to any of the 22 producer components.
    out.push(is_first_row_column_id());
    // 9 round-cyclic columns of the rotated layout (K limbs + round
    // indicators + schedule gate), also consumer-read via
    // `get_preprocessed_column` and sized to the main trace.
    out.extend(round_cyclic_column_ids());
    out
}

/// The 8 decode tables in the canonical (function, side) ordering. Shared
/// across `components`, `preprocessed`, `multiplicities`, and `interaction`.
pub const DECODE_TABLES: &[(SigmaFn, Half)] = &[
    (SigmaFn::Sigma0, Half::S),
    (SigmaFn::Sigma0, Half::SComplement),
    (SigmaFn::Sigma1, Half::S),
    (SigmaFn::Sigma1, Half::SComplement),
    (SigmaFn::LowerSigma0, Half::S),
    (SigmaFn::LowerSigma0, Half::SComplement),
    (SigmaFn::LowerSigma1, Half::S),
    (SigmaFn::LowerSigma1, Half::SComplement),
];

/// The 4 round-side split-pack tables.
pub const ROUND_SPLIT_TABLES: &[(RoundPartition, Half16)] = &[
    (RoundPartition::Sigma0AndMaj, Half16::Lo),
    (RoundPartition::Sigma0AndMaj, Half16::Hi),
    (RoundPartition::Sigma1AndCh, Half16::Lo),
    (RoundPartition::Sigma1AndCh, Half16::Hi),
];

/// The 4 σ-side split-pack tables.
pub const SIGMA_SPLIT_TABLES: &[(LowerSigmaPartition, Half16)] = &[
    (LowerSigmaPartition::LowerSigma0, Half16::Lo),
    (LowerSigmaPartition::LowerSigma0, Half16::Hi),
    (LowerSigmaPartition::LowerSigma1, Half16::Lo),
    (LowerSigmaPartition::LowerSigma1, Half16::Hi),
];

/// The 4 range-check tables in canonical order. Shared across `components`,
/// `preprocessed`, `multiplicities`, and `interaction` so an enum drift is
/// caught at one site.
pub const RANGE_TABLES: &[RangeKind] = &[
    RangeKind::Range2,
    RangeKind::Range4,
    RangeKind::Range5,
    RangeKind::Range16,
];

#[cfg(test)]
mod tests {
    use super::*;

    /// The per-table column-ID arrays are load-bearing: their order is what
    /// the verifier's preprocessed-mask reads resolve against (via the
    /// `TraceLocationAllocator`), so it must stay in lock-step with the
    /// emission order in `crate::preprocessed`. That emission side is guarded
    /// by `preprocessed::tests::emitted_columns_match_documented_field_order`;
    /// this pins the ID side to its documented strings, so a one-sided
    /// reorder here fails fast instead of silently mislabelling a column for
    /// the verifier.
    #[test]
    fn column_ids_follow_documented_order() {
        assert_eq!(
            decode_column_ids(SigmaFn::Sigma0, Half::S),
            [
                id("decode_sigma0_s_key"),
                id("decode_sigma0_s_omain_lo"),
                id("decode_sigma0_s_omain_hi"),
                id("decode_sigma0_s_o2_lo"),
                id("decode_sigma0_s_o2_hi"),
            ],
        );
        assert_eq!(
            maj_ch_column_ids(),
            [
                id("maj_ch_a"),
                id("maj_ch_b"),
                id("maj_ch_c"),
                id("maj_ch_maj"),
                id("maj_ch_ch"),
            ],
        );
        assert_eq!(
            xor_8_column_ids(),
            [id("xor_8_x"), id("xor_8_y"), id("xor_8_z")],
        );
        assert_eq!(
            round_split_pack_column_ids(RoundPartition::Sigma0AndMaj, Half16::Lo),
            [
                id("sp_sigma0_lo_key"),
                id("sp_sigma0_lo_g0"),
                id("sp_sigma0_lo_g1"),
                id("sp_sigma0_lo_g2"),
                id("sp_sigma0_lo_g3"),
            ],
        );
        assert_eq!(
            sigma_split_pack_column_ids(LowerSigmaPartition::LowerSigma0, Half16::Lo),
            [
                id("sp_lsigma0_lo_key"),
                id("sp_lsigma0_lo_s"),
                id("sp_lsigma0_lo_sp"),
            ],
        );
    }
}
