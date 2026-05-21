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
//! Wired components (19 total, one `Sha256Eval` consumer + 18 producers):
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
//!
//! Every preprocessed-column ID is namespaced under the `"sha256_"` prefix
//! so it cannot collide with the ECDSA-stream tables in a future combined
//! workspace proof. The `id()` constructors live next to their evaluators
//! so the matching trace generator (`crate::preprocessed`) and the
//! evaluator stay in lock-step.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, Relation, RelationEntry,
};

use crate::partitions::SigmaFn;
use crate::tables::{Half, Half16, LowerSigmaPartition, RoundPartition};

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

/// IDs of the 4 preprocessed columns of one round-side split-and-pack
/// table. Order: `(key, g0, g1, g2)` matching
/// `crate::relations::ROUND_SPLIT_PACK_REL_SIZE`.
pub fn round_split_pack_column_ids(p: RoundPartition, h: Half16) -> [PreProcessedColumnId; 4] {
    let t = round_split_tag(p, h);
    [
        id(&format!("{t}_key")),
        id(&format!("{t}_g0")),
        id(&format!("{t}_g1")),
        id(&format!("{t}_g2")),
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

        eval.add_to_relation(RelationEntry::new(
            &self.relations.xor_8,
            -E::EF::from(mult),
            &[x, y, z],
        ));

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
        let mult = eval.next_trace_mask();
        let values = [key, g0, g1, g2];
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
// Aggregate IDs
// ---------------------------------------------------------------------------

/// Every preprocessed-column ID committed by this crate, in the exact
/// order [`crate::preprocessed::generate_preprocessed_trace`] emits the
/// matching `CircleEvaluation`s. The list mirrors the per-component
/// `*_column_ids` getters concatenated in **table-major** order — keep
/// both sides in sync or the verifier will read the wrong column.
pub fn all_preprocessed_column_ids(group_width: u32) -> Vec<PreProcessedColumnId> {
    let mut out = Vec::new();
    // 8 decode tables in the order `Sha256Relations::draw`/`SigmaDecodeRelations::draw` uses.
    for (f, h) in DECODE_TABLES {
        out.extend(decode_column_ids(*f, *h));
    }
    // 1 Maj/Ch table (always at `group_width >= MAX_ROUND_GROUP_BITS`).
    let _ = group_width;
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

#[allow(dead_code)]
fn _ensure_imports_in_scope() {
    // Touch `One` / `SecureField` / `M31` so an aggressive unused-imports
    // pass doesn't strip them — they're hot when the FrameworkEval
    // implementations expand the relation macros.
    let _ = SecureField::from(M31::from(0u32));
    let _ = <SecureField as One>::one();
}
