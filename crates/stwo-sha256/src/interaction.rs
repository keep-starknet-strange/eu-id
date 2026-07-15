//! LogUp interaction-trace generator for every SHA-256 component.
//!
//! The main `Sha256Eval` consumer and its range-table producers each emit an
//! interaction trace. When the digest provider
//! is exposed, `Sha256Eval` *also* yields the final-block digest on the
//! `Sha256Digest` channel — the one provider-side term it contributes — which
//! is why its claimed sum is non-zero on its own in that mode. Each is built by
//! walking that component's fractions row-by-row through
//! [`stwo_constraint_framework::LogupTraceGenerator`] — consecutive
//! fractions share an interaction column in batches matching the
//! component's finalizer: [`crate::constraints::LOGUP_BATCH`] = 4 for the
//! `Sha256Eval` consumer (`eval.finalize_logup_batched(4)`, D ≤ 5 budget),
//! pairs for the producer components (`eval.finalize_logup_in_pairs()`).
//!
//! **Sum-to-zero invariant.** For a valid proof, the total of every
//! component's `claimed_sum` must be zero — every consumer "use" cancels
//! against the producer's "yield" at the same row key. The verifier
//! checks this implicitly through the cumulative-sum constraint inside
//! each component plus the OODS-evaluation balance across the proof.
//!
//! Lookup orders **must** match the order `Sha256Eval::evaluate` /
//! `components::*::evaluate` fire `add_to_relation`. Drift between this
//! generator and the AIR evaluator silently invalidates the proof
//! (denominator mismatch ⇒ verifier rejects).
//!
//! Performance choice: this implementation uses the **scalar**
//! `write_frac` path one row at a time. The reference `xor_8_8` example
//! does SIMD packing for its 2¹⁶-row tables; we follow the simpler
//! single-row path here for correctness; SIMD-packing the producers is
//! a benchmark-driven future micro-optimisation.

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::ColumnVec;
use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedSecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use crate::components::{range_log_size, RangeKind, RANGE_TABLES};
use crate::constants::DIGEST_BYTES;
use crate::constraints::LOGUP_BATCH;
use crate::field_exposure::{word_be_bytes, FieldExposure};
use crate::multiplicities::range_k_multiplicities;
use crate::relations::Sha256Relations;
use crate::trace::{h_out_digest_bytes, Layout};
use crate::types::Sha256Witness;

/// Lookup sites the main `Sha256Eval` fires per **row**, **excluding** the
/// optional digest yield. Breakdown (W=6), matching the firing order in
/// [`write_round_row_lookups`] and `crate::constraints::Sha256Eval::evaluate`:
///
/// ```text
///   2 (schedule `Range_4` carry pair; t ≥ 16 rows)
/// +  8 (round carry range-checks; every row)
/// + 16 (finalization carries, t = 63 rows)
/// + 32 (terminal `Range_8` digest bytes, t = 63 rows)
/// = 58
/// ```
///
/// A site that does not fire on a given row holds the neutral fraction `(0, 1)`.
pub const SHA_LOOKUPS_PER_ROW_BASE: usize = 58;

/// Total lookup sites `Sha256Eval` fires per row. The digest provider adds
/// exactly one width-32 yield site when `expose_digest` is set; the
/// credential-field provider adds one `Range8` byte range-check (the
/// `[0, 256)` pin) per exposed byte column — once for block-0 legacy exposure,
/// once per target block for multi-block exposure — plus one width-3 yield per
/// exposed window byte (all firing on `t = 15` rows, selector-gated to each
/// byte's target block). All are zero for the standalone AIR. Both the
/// interaction generator here and `crate::air`'s interaction-column sizing
/// read this so the two never drift.
#[inline]
pub fn sha_lookups_per_row(expose_digest: bool, field_exposure: &FieldExposure) -> usize {
    let base = SHA_LOOKUPS_PER_ROW_BASE;
    let field_range_sites = if field_exposure.is_empty() {
        0
    } else if field_exposure.needs_block_witness() {
        field_exposure.n_byte_columns() * field_exposure.target_blocks().len()
    } else {
        field_exposure.n_byte_columns()
    };
    base + usize::from(expose_digest) + field_range_sites + field_exposure.n_yields()
}

/// Total lookup sites the multi-slot merged `Sha256Eval` fires per row:
/// the 58 base sites, one digest yield site per digest-exposing slot, then
/// each slot's field sites — in the emission order of the multi branch of
/// `Sha256Eval::evaluate`. Read by both the interaction generator and the
/// column sizing so the three never drift.
#[inline]
pub fn sha_multi_lookups_per_row(config: &crate::slots::MultiSlotConfig) -> usize {
    SHA_LOOKUPS_PER_ROW_BASE
        + config.n_digest_slots()
        + config
            .slots
            .iter()
            .map(|spec| field_exposure_sites(&spec.field_exposure))
            .sum::<usize>()
}

// ---------------------------------------------------------------------------
// Per-component claim
// ---------------------------------------------------------------------------

/// One component's slot in the aggregate interaction claim. `claimed_sum`
/// is what the verifier checks each component's interaction column
/// cumulatively reaches; the total over every component must be zero.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ComponentClaim {
    pub claimed_sum: SecureField,
}

impl ComponentClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// Aggregate of every component's claim, in proving / verifying order.
///
/// Field order **must** match the order components are added to the proof
/// (`crate::stark::commit_base_trace` / `crate::stark::component_provers`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InteractionClaim {
    pub sha256: ComponentClaim,
    pub range: Vec<ComponentClaim>, // 4: Range_2, Range_4, Range_5, Range_8
}

impl InteractionClaim {
    /// Sum of every component's claimed sum. The verifier checks this is
    /// zero — modulo cross-component LogUp wiring outside this crate
    /// (currently none). Used as the soundness backbone.
    pub fn total(&self) -> SecureField {
        let mut s = self.sha256.claimed_sum;
        for c in &self.range {
            s += c.claimed_sum;
        }
        s
    }

    /// Mix every claimed sum into the channel — must happen at the same
    /// place in the proving and verifying flow so the post-mix challenges
    /// agree.
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.sha256.mix_into(channel);
        for c in &self.range {
            c.mix_into(channel);
        }
    }
}

// ---------------------------------------------------------------------------
// Generic helpers
// ---------------------------------------------------------------------------

/// One (numerator, denominator) at a particular row. Numerator carries
/// the lookup's multiplicity (positive on the consumer side, negative on
/// the producer); denominator is `combine(values) = sum α^i · v_i − z`.
pub(crate) type Frac = (SecureField, SecureField);

/// Build one interaction trace for a component from its list of
/// row-iterators. `lookups[k]` is the k-th lookup the component fires —
/// a `Vec<Frac>` of length `2^log_size` giving the row-by-row fraction.
///
/// Consecutive lookups share one interaction column in chunks of `batch`,
/// folded exactly like the framework's `finalize_logup_batched(batch)`:
/// start from the chunk's first fraction, then fold each next `(n, d)` as
/// `num = d·num + n·den; den = den·d`. A short tail chunk (including a
/// singleton) folds the same way over fewer fractions. The chunking runs
/// over the same emission order as the component's `add_to_relation`
/// calls, so `batch` MUST equal the component's finalizer batch size
/// ([`crate::constraints::LOGUP_BATCH`] for the consumer, 2 for the
/// pair-finalized producers).
pub(crate) fn build_interaction_columns(
    log_size: u32,
    batch: usize,
    lookups: Vec<Vec<Frac>>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    debug_assert!(log_size >= LOG_N_LANES, "log_size < LOG_N_LANES");
    debug_assert!(batch > 0, "batch size must be positive");
    let n_rows = 1usize << log_size;
    for (i, l) in lookups.iter().enumerate() {
        debug_assert_eq!(
            l.len(),
            n_rows,
            "lookup {i} has {} rows ≠ {n_rows}",
            l.len()
        );
    }

    let mut gen = LogupTraceGenerator::new(log_size);

    for chunk in lookups.chunks(batch) {
        let mut col = gen.new_col();
        for vec_row in 0..(n_rows / N_LANES) {
            let mut num_arr = [SecureField::zero(); N_LANES];
            let mut den_arr = [SecureField::one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (mut num, mut den) = chunk[0][row];
                for lookup in &chunk[1..] {
                    let (n, d) = lookup[row];
                    // num/den + n/d = (d·num + n·den) / (den·d)
                    num = d * num + n * den;
                    den *= d;
                }
                num_arr[lane] = num;
                den_arr[lane] = den;
            }
            col.write_frac(
                vec_row,
                PackedSecureField::from_array(num_arr),
                PackedSecureField::from_array(den_arr),
            );
        }
        col.finalize_col();
    }

    gen.finalize_last()
}

/// Build one (numerator = -mult, denominator = combine(row)) per row of a
/// producer-side table. The values arg gives the row content as
/// `[F; N]` per row.
pub(crate) fn producer_frac_column<R, const N: usize>(
    rel: &R,
    mults: &[u32],
    rows: impl Iterator<Item = [BaseField; N]>,
) -> Vec<Frac>
where
    R: Relation<BaseField, SecureField>,
{
    let mut out = Vec::with_capacity(mults.len());
    for (m, row) in mults.iter().zip(rows) {
        let denom = rel.combine(&row);
        let num = -SecureField::from(BaseField::from(*m));
        out.push((num, denom));
    }
    out
}

/// Class-D blinded producer fraction (Q-015 §4b). Mirrors the SINGLE gated
/// `add_to_relation` entry `crate::components::emit_blind` fires per row —
/// numerator `-(1 − is_dummy)·mult` — over the doubled (blinded) domain.
/// Returns one `Vec<Frac>` of length `mults.len() = 2^(L+1)`: on a real row
/// (`idx < real_len`) the numerator is `-mult`, identical to the unblinded emit;
/// on a dummy row (`idx ≥ real_len`, `is_dummy = 1`) the numerator is `0`, so
/// the fresh random blind multiplicity committed there never enters the LogUp
/// sum — yet stays in the committed multiplicity column as the mask. The caller
/// pushes one such fraction per producer so `build_interaction_columns` pairs
/// two producers' fractions into one interaction column (down from one column
/// per producer in the old cancelling-pair form).
pub(crate) fn producer_blind_frac_column<R, const N: usize>(
    rel: &R,
    mults: &[u32],
    real_len: usize,
    rows: impl Iterator<Item = [BaseField; N]>,
) -> Vec<Frac>
where
    R: Relation<BaseField, SecureField>,
{
    let mut out = Vec::with_capacity(mults.len());
    for (idx, (m, row)) in mults.iter().zip(rows).enumerate() {
        let denom = rel.combine(&row);
        // Dummy rows are gated to a zero numerator; real rows yield `-mult`.
        let num = if idx >= real_len {
            SecureField::zero()
        } else {
            -SecureField::from(BaseField::from(*m))
        };
        out.push((num, denom));
    }
    out
}

// (Padding helper removed — every per-table producer column is sized
// exactly to its `log_size` by construction, and the consumer-side
// builder pre-allocates `n_rows` per lookup with the zero-fraction
// default.)

// ---------------------------------------------------------------------------
// Producer-side per-table interaction columns
// ---------------------------------------------------------------------------

/// Build the interaction trace for one `Range_k` producer.
fn range_k_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    kind: RangeKind,
    field_exposure: &FieldExposure,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = range_log_size(kind);
    let mults = range_k_multiplicities(witness, kind, field_exposure);
    let n_rows = 1usize << log_size;
    let k = kind.bound() as usize;
    // Producer rows are `[0, 1, …, k-1, 0, 0, …]` — leading `k` real values
    // then zero padding up to `n_rows`. The matching multiplicity for any
    // padding slot is `0` (see `range_k_multiplicities`), so they do not
    // contribute to the LogUp balance.
    let row_iter = (0..n_rows).map(|i| {
        let value = if i < k { i as u32 } else { 0u32 };
        [BaseField::from(value)]
    });
    let frac = match kind {
        RangeKind::Range2 => producer_frac_column(&relations.range.range_2, &mults, row_iter),
        RangeKind::Range4 => producer_frac_column(&relations.range.range_4, &mults, row_iter),
        RangeKind::Range5 => producer_frac_column(&relations.range.range_5, &mults, row_iter),
        RangeKind::Range8 => producer_frac_column(&relations.range.range_8, &mults, row_iter),
    };
    // Single fraction — one column regardless of batch; the producer
    // component finalizes in pairs, so pass 2.
    build_interaction_columns(log_size, 2, vec![frac])
}

// ---------------------------------------------------------------------------
// Consumer-side (Sha256Eval) interaction trace
// ---------------------------------------------------------------------------

/// Build the interaction trace for the main `Sha256Eval` consumer.
///
/// Mirrors the *exact* `add_to_relation` order `Sha256Eval::evaluate`
/// fires. Each lookup produces one fraction column at log_size = the
/// trace's log_size. Chunks of [`LOGUP_BATCH`] = 4 consecutive lookups
/// share an interaction column, matching `finalize_logup_batched(4)`.
///
/// The cell values for each lookup come from the main trace at the row
/// representing the block. Padding rows contribute `(0, 1)` (zero
/// numerator, unit denominator) so they don't perturb the sum — the
/// `enabler` column the AIR multiplies into every constraint takes care
/// of the algebraic side.
fn sha256_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_size: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1usize << log_size;
    let n_blocks = witness.blocks.len();
    // `is_last_block` matches the AIR gate `enabler · is_round_63 ·
    // (1 − enabler_next)`: set on the final block's t = 63 row only when a
    // padding successor exists (guaranteed by `crate::trace::min_log_size`).
    // The field provider gates on the symmetric `is_first_block` (block 0),
    // which needs no padding successor.
    let has_padding = n_blocks * crate::trace::ROWS_PER_BLOCK < n_rows;
    let last_block_idx = n_blocks.saturating_sub(1);

    // One fraction vector per lookup site (`lookup_idx`), each of length
    // `n_rows`, default-filled with the neutral `(0, 1)`; real rows
    // overwrite the sites that fire on them. See
    // [`SHA_LOOKUPS_PER_ROW_BASE`] for the per-row site breakdown.
    let lookups_per_row = sha_lookups_per_row(expose_digest, field_exposure);
    let mut all_lookups: Vec<Vec<Frac>> = (0..lookups_per_row)
        .map(|_| vec![(SecureField::zero(), SecureField::one()); n_rows])
        .collect();

    for (block_idx, block) in witness.blocks.iter().enumerate() {
        let is_last_block = block_idx == last_block_idx && has_padding;
        for t in 0..crate::constants::N_ROUNDS {
            let slot = Layout::round_row_slot(block_idx, t, log_size);
            let mut cursor = 0usize;
            write_round_row_lookups(
                &mut all_lookups,
                &mut cursor,
                slot,
                block,
                t,
                relations,
                expose_digest,
                is_last_block,
                field_exposure,
                block_idx,
            );
            debug_assert_eq!(cursor, lookups_per_row, "row lookup miscount");
        }
    }

    build_interaction_columns(log_size, LOGUP_BATCH, all_lookups)
}

/// Write every lookup site for one `(block, round t)` row at its trace
/// slot, in **exactly** the `Sha256Eval::evaluate` firing order. Bumps
/// `cursor` past each site so the same site index always lands at the same
/// fraction column across rows; sites that do not fire on this row keep
/// their neutral `(0, 1)` fill and the cursor skips over them.
#[allow(clippy::too_many_arguments)]
fn write_round_row_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    block: &crate::types::BlockWitness,
    t: usize,
    relations: &Sha256Relations,
    expose_digest: bool,
    is_last_block: bool,
    field_exposure: &FieldExposure,
    block_idx: usize,
) {
    // ---- 1. Schedule carry range-checks (2 sites; t ≥ 16 rows) ----
    if t >= 16 {
        let entry = &block.schedule_entries[t - 16];
        write_carry_range_pair(
            all,
            cursor,
            slot,
            relations,
            RangeKind::Range4,
            entry.carries,
        );
    } else {
        *cursor += 2;
    }

    // ---- 2. Round carry range-checks (8 sites; every real row) ----
    let round = &block.rounds[t];

    // Carry range-checks for the four mod-2³² adds of this round.
    write_carry_range_pair(
        all,
        cursor,
        slot,
        relations,
        RangeKind::Range5,
        round.t1_carries,
    );
    write_carry_range_pair(
        all,
        cursor,
        slot,
        relations,
        RangeKind::Range2,
        round.t2_carries,
    );
    write_carry_range_pair(
        all,
        cursor,
        slot,
        relations,
        RangeKind::Range2,
        round.e_new_carries,
    );
    write_carry_range_pair(
        all,
        cursor,
        slot,
        relations,
        RangeKind::Range2,
        round.a_new_carries,
    );

    // ---- 3/4. Finalization carries + terminal `Range_8` bytes (t = 63 rows) ----
    if t == crate::constants::N_ROUNDS - 1 {
        for c in &block.finalization_carries {
            write_carry_range_pair(all, cursor, slot, relations, RangeKind::Range2, *c);
        }
        for byte in h_out_digest_bytes(&block.h_out) {
            write_range_check(all, cursor, slot, relations, RangeKind::Range8, byte);
        }
    } else {
        *cursor += 16 + DIGEST_BYTES;
    }

    // ---- 5. Digest yield (provider side, final block's t = 63 row) ----
    if expose_digest {
        if t == crate::constants::N_ROUNDS - 1 {
            let bytes = h_out_digest_bytes(&block.h_out);
            let values: [BaseField; DIGEST_BYTES] =
                std::array::from_fn(|i| BaseField::from(bytes[i]));
            let denom = relations.digest.digest.combine(&values);
            let num = -SecureField::from(BaseField::from(u32::from(is_last_block)));
            all[*cursor][slot] = (num, denom);
        }
        *cursor += 1;
    }

    // ---- 6. Credential-field range-checks + yields (target block t = 15 rows) ----
    //
    // Same order as the constraint side: 7a. one `Range8` per exposed byte
    // column — once for block-0 legacy exposure, once per target block for
    // multi-block exposure (each gated by `block_idx == target`) — then 7b. one
    // width-3 yield per window byte (numerator `−selector`, selector =
    // `block_idx == y.block_idx`).
    if !field_exposure.is_empty() {
        if t == 15 {
            write_field_row_lookups(
                all,
                cursor,
                slot,
                block,
                block_idx,
                field_exposure,
                &relations.field.field,
                relations,
                true,
            );
        } else {
            *cursor += sha_lookups_per_row(false, field_exposure) - SHA_LOOKUPS_PER_ROW_BASE;
        }
    }
}

/// Number of lookup sites one field exposure adds per row (range-checks +
/// yields) — the field term of [`sha_lookups_per_row`], shared with the
/// multi-slot sizing.
pub(crate) fn field_exposure_sites(field_exposure: &FieldExposure) -> usize {
    sha_lookups_per_row(false, field_exposure) - SHA_LOOKUPS_PER_ROW_BASE
}

/// Write one exposure's field sites (range-checks then yields, the
/// `Sha256Eval` firing order) for a `t = 15` row of `block`, targeting
/// `field_rel` for the yields. `hot` gates whether this row's block is
/// eligible at all — the multi-slot writer passes `false` for rows of OTHER
/// slots (the sites keep their neutral fill but the cursor still advances).
#[allow(clippy::too_many_arguments)]
fn write_field_row_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    block: &crate::types::BlockWitness,
    block_idx: usize,
    field_exposure: &FieldExposure,
    field_rel: &crate::relations::Sha256Field,
    relations: &Sha256Relations,
    hot: bool,
) {
    if !hot {
        *cursor += field_exposure_sites(field_exposure);
        return;
    }
    let word_bytes: Vec<[u32; crate::constants::WORD_BYTES]> = field_exposure
        .decomposed_words()
        .iter()
        .map(|&w| {
            let limb = block.schedule[w];
            word_be_bytes(limb.lo, limb.hi)
        })
        .collect();

    if field_exposure.needs_block_witness() {
        for target_block in field_exposure.target_blocks() {
            let selector =
                SecureField::from(BaseField::from(u32::from(block_idx == *target_block)));
            for bytes in &word_bytes {
                for &b in bytes {
                    all[*cursor][slot] = (selector, combine_range(relations, RangeKind::Range8, b));
                    *cursor += 1;
                }
            }
        }
    } else {
        let selector = SecureField::from(BaseField::from(u32::from(block_idx == 0)));
        for bytes in &word_bytes {
            for &b in bytes {
                all[*cursor][slot] = (selector, combine_range(relations, RangeKind::Range8, b));
                *cursor += 1;
            }
        }
    }
    for y in field_exposure.yields() {
        let selector = SecureField::from(BaseField::from(u32::from(block_idx == y.block_idx)));
        let slot_idx = field_exposure.yield_column_slot(y);
        let word_slot = slot_idx / crate::constants::WORD_BYTES;
        let byte_in_word = slot_idx % crate::constants::WORD_BYTES;
        let value = word_bytes[word_slot][byte_in_word];
        let tuple = [
            BaseField::from(y.field_id),
            BaseField::from(y.byte_index),
            BaseField::from(value),
        ];
        let denom = field_rel.combine(&tuple);
        all[*cursor][slot] = (-selector, denom);
        *cursor += 1;
    }
}

/// Combine a single-value lookup against the `Range_k` channel for `kind`.
fn combine_range(relations: &Sha256Relations, kind: RangeKind, value: u32) -> SecureField {
    let v = [BaseField::from(value)];
    match kind {
        RangeKind::Range2 => relations.range.range_2.combine(&v),
        RangeKind::Range4 => relations.range.range_4.combine(&v),
        RangeKind::Range5 => relations.range.range_5.combine(&v),
        RangeKind::Range8 => relations.range.range_8.combine(&v),
    }
}

/// Emit one consumer-side range-check fraction at the trace slot.
fn write_range_check(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    relations: &Sha256Relations,
    kind: RangeKind,
    value: u32,
) {
    let denom = combine_range(relations, kind, value);
    all[*cursor][slot] = (SecureField::one(), denom);
    *cursor += 1;
}

/// Emit the `(carry_lo, carry_hi)` pair of one mod-2³² add as two
/// consumer-side `Range_k` fractions (matches
/// `crate::constraints::emit_mod_2_32_add_linear`).
fn write_carry_range_pair(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    relations: &Sha256Relations,
    kind: RangeKind,
    carries: crate::types::AddCarries,
) {
    write_range_check(all, cursor, slot, relations, kind, carries.lo);
    write_range_check(all, cursor, slot, relations, kind, carries.hi);
}

// ---------------------------------------------------------------------------
// Public: top-level interaction-trace generation
// ---------------------------------------------------------------------------

/// Generate the interaction trace for every component in this proof.
///
/// Returns the per-component trees of `CircleEvaluation`s (flattened into
/// one `Vec<Vec<…>>` in component order) plus the aggregate
/// [`InteractionClaim`].
pub fn generate_interaction_trace(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
    group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    generate_interaction_trace_inner(
        relations,
        witness,
        sha256_log_size,
        group_width,
        expose_digest,
        field_exposure,
        true,
    )
}

pub fn generate_consumer_interaction_trace(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
    group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    generate_interaction_trace_inner(
        relations,
        witness,
        sha256_log_size,
        group_width,
        expose_digest,
        field_exposure,
        false,
    )
}

/// Interaction trace of the multi-slot merged consumer (shared-tables mode:
/// no producer components). Mirrors the multi branch of
/// `Sha256Eval::evaluate` exactly: per row, the 58 base sites (via
/// [`write_round_row_lookups`] with digest/field off), then one digest
/// yield site per digest-exposing slot in slot order (live on the OWN
/// slot's final-block t = 63 row), then each slot's field sites in slot
/// order (live on the OWN slot's t = 15 rows only).
pub fn generate_multi_consumer_interaction_trace(
    relations: &Sha256Relations,
    slot_relations: &[crate::relations::SlotIoRelations],
    witnesses: &[&Sha256Witness],
    log_size: u32,
    config: &crate::slots::MultiSlotConfig,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    assert_eq!(witnesses.len(), config.n_slots());
    assert_eq!(slot_relations.len(), config.n_slots());
    let n_rows = 1usize << log_size;
    let slot_rows = config.slot_rows();
    let lookups_per_row = sha_multi_lookups_per_row(config);
    let empty_exposure = FieldExposure::empty();
    let mut all_lookups: Vec<Vec<Frac>> = (0..lookups_per_row)
        .map(|_| vec![(SecureField::zero(), SecureField::one()); n_rows])
        .collect();

    for (s, witness) in witnesses.iter().enumerate() {
        assert!(
            witness.blocks.len() * crate::trace::ROWS_PER_BLOCK < slot_rows,
            "slot {s} must keep in-slot padding"
        );
        let last_block_idx = witness.blocks.len() - 1;
        for (block_idx, block) in witness.blocks.iter().enumerate() {
            let is_last_block = block_idx == last_block_idx;
            for t in 0..crate::constants::N_ROUNDS {
                let natural =
                    config.slot_start_row(s) + block_idx * crate::trace::ROWS_PER_BLOCK + t;
                let slot = Layout::row_slot(natural, log_size);
                let mut cursor = 0usize;
                write_round_row_lookups(
                    &mut all_lookups,
                    &mut cursor,
                    slot,
                    block,
                    t,
                    relations,
                    false,
                    false,
                    &empty_exposure,
                    block_idx,
                );
                debug_assert_eq!(cursor, SHA_LOOKUPS_PER_ROW_BASE);
                // Per-slot digest sites, slot order.
                for (k, spec) in config.slots.iter().enumerate() {
                    if !spec.expose_digest {
                        continue;
                    }
                    if k == s && t == crate::constants::N_ROUNDS - 1 {
                        let bytes = h_out_digest_bytes(&block.h_out);
                        let values: [BaseField; DIGEST_BYTES] =
                            std::array::from_fn(|i| BaseField::from(bytes[i]));
                        let denom = slot_relations[k].digest.digest.combine(&values);
                        let num = -SecureField::from(BaseField::from(u32::from(is_last_block)));
                        all_lookups[cursor][slot] = (num, denom);
                    }
                    cursor += 1;
                }
                // Per-slot field sites, slot order. Rows of other slots (and
                // non-t=15 rows) keep the neutral fill; the cursor advances
                // identically on every row.
                for (k, spec) in config.slots.iter().enumerate() {
                    if spec.field_exposure.is_empty() {
                        continue;
                    }
                    write_field_row_lookups(
                        &mut all_lookups,
                        &mut cursor,
                        slot,
                        block,
                        block_idx,
                        &spec.field_exposure,
                        &slot_relations[k].field.field,
                        relations,
                        k == s && t == 15,
                    );
                }
                debug_assert_eq!(cursor, lookups_per_row, "multi row lookup miscount");
            }
        }
    }

    let (evals, claimed_sum) = build_interaction_columns(log_size, LOGUP_BATCH, all_lookups);
    let claim = InteractionClaim {
        sha256: ComponentClaim { claimed_sum },
        range: Vec::new(),
    };
    (evals, claim)
}

fn generate_interaction_trace_inner(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
    _group_width: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    let mut combined = Vec::new();

    // Sha256Eval consumer first — its slot in the proof's component list.
    // `expose_digest` adds the cross-component digest yield to this component's
    // fractions; `field_exposure` adds one credential-field yield per exposed
    // byte (and hence to its claimed sum).
    let (sha_trace, sha_sum) = sha256_interaction(
        relations,
        witness,
        sha256_log_size,
        expose_digest,
        field_exposure,
    );
    combined.extend(sha_trace);
    let sha256 = ComponentClaim {
        claimed_sum: sha_sum,
    };

    // 4 range producers (Range_2, Range_4, Range_5, Range_8).
    let mut range = Vec::with_capacity(4);
    if include_table_providers {
        for &kind in RANGE_TABLES {
            let (t, s) = range_k_interaction(relations, witness, kind, field_exposure);
            combined.extend(t);
            range.push(ComponentClaim { claimed_sum: s });
        }
    }

    let claim = InteractionClaim { sha256, range };
    (combined, claim)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::partitions::MAX_ROUND_GROUP_BITS;
    use crate::trace::min_log_size;
    use crate::witness::compute_sha256_witness;
    use stwo::core::channel::Blake2sChannel;

    /// With the digest provider **off**, the SHA module's claimed sums still
    /// net to zero — the standalone consumer ⇄ producer balance is untouched,
    /// so a standalone SHA proof keeps self-verifying.
    #[test]
    fn digest_provider_off_keeps_module_self_balanced() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            MAX_ROUND_GROUP_BITS,
            false,
            &FieldExposure::empty(),
        );
        assert_eq!(
            claim.total(),
            SecureField::zero(),
            "standalone SHA module must self-balance when the digest is not exposed",
        );
    }

    /// A malicious split can preserve `limb = 256·b_hi + b_lo` in M31 by
    /// moving one radix unit between the two cells. The Range8 lookup must be
    /// what rejects that otherwise constraint-preserving representation.
    #[test]
    fn range_8_rejects_recomposition_preserving_out_of_range_digest_byte() {
        let witness = compute_sha256_witness(b"abc");
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, producer_sum) = range_k_interaction(
            &relations,
            &witness,
            RangeKind::Range8,
            &FieldExposure::empty(),
        );
        let bytes: Vec<BaseField> = witness
            .blocks
            .iter()
            .flat_map(|block| h_out_digest_bytes(&block.h_out))
            .map(BaseField::from)
            .collect();
        let reciprocal = |value: BaseField| -> SecureField {
            let denominator: SecureField = relations.range.range_8.combine(&[value]);
            assert_ne!(denominator, SecureField::zero());
            SecureField::one() / denominator
        };
        let honest_consumer = bytes
            .iter()
            .copied()
            .fold(SecureField::zero(), |sum, byte| sum + reciprocal(byte));
        assert_eq!(producer_sum + honest_consumer, SecureField::zero());

        let (byte_hi, byte_lo) = (bytes[0], bytes[1]);
        let radix = BaseField::from(1u32 << 8);
        let (forged_hi, forged_lo) = if byte_hi.0 < 255 {
            (byte_hi + BaseField::from(1u32), byte_lo - radix)
        } else {
            (byte_hi - BaseField::from(1u32), byte_lo + radix)
        };
        assert_eq!(
            radix * byte_hi + byte_lo,
            radix * forged_hi + forged_lo,
            "the forged split must preserve the limb recomposition",
        );
        assert!(forged_hi.0 < 256);
        assert!(forged_lo.0 >= 256, "one forged cell must miss Range8");

        let forged_consumer = honest_consumer - reciprocal(byte_hi) - reciprocal(byte_lo)
            + reciprocal(forged_hi)
            + reciprocal(forged_lo);
        assert_ne!(
            producer_sum + forged_consumer,
            SecureField::zero(),
            "an out-of-range byte split must not balance the Range8 provider",
        );
    }

    /// With the digest provider **on**, the module yields the 32 final-block
    /// digest bytes. Every other lookup still self-cancels, so the module's
    /// claimed-sum total is exactly the outstanding provider term
    /// `−1/combine(digest)`. A synthetic consumer that *requires* the same
    /// digest tuple contributes `+1/combine(digest)` — exactly the claimed sum
    /// of a consumer interaction column that fires `+1` on the final-block row
    /// and `0` elsewhere — and the two cancel. This is the producer-half
    /// balance check, at the claimed-sum level (no full proof needed).
    #[test]
    fn digest_provider_balances_against_synthetic_consumer() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            MAX_ROUND_GROUP_BITS,
            true,
            &FieldExposure::empty(),
        );
        let module_total = claim.total();

        // Synthesize the consumer term: +1 / combine(final-block digest bytes),
        // using the same drawn relation the provider yielded against.
        let last = witness.blocks.last().expect("at least one block");
        let bytes = h_out_digest_bytes(&last.h_out);
        let values: [BaseField; DIGEST_BYTES] = std::array::from_fn(|i| BaseField::from(bytes[i]));
        let denom: SecureField = relations.digest.digest.combine(&values);
        assert_ne!(
            denom,
            SecureField::zero(),
            "digest combine must be invertible under the drawn challenges",
        );
        let consumer = SecureField::one() / denom;

        // The yield leaves the module unbalanced on its own (the whole point:
        // the digest term enters the global balance)...
        assert_ne!(
            module_total,
            SecureField::zero(),
            "exposing the digest must leave an outstanding provider term",
        );
        // ...and the synthetic consumer cancels it exactly.
        assert_eq!(
            module_total + consumer,
            SecureField::zero(),
            "digest provider must balance a consumer requiring the same bytes",
        );
    }

    /// A consumer requiring a *different* digest (one bit flipped) does not
    /// cancel the provider's yield — the balance closes only for the exact
    /// bytes SHA computed. This is the binding's core property (a signature
    /// over the wrong hash is rejected) exercised at the digest-provider level.
    #[test]
    fn digest_provider_rejects_mismatched_consumer() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            MAX_ROUND_GROUP_BITS,
            true,
            &FieldExposure::empty(),
        );

        let last = witness.blocks.last().unwrap();
        let mut bytes = h_out_digest_bytes(&last.h_out);
        bytes[0] ^= 1; // flip one bit of the first digest byte
        let values: [BaseField; DIGEST_BYTES] = std::array::from_fn(|i| BaseField::from(bytes[i]));
        let denom: SecureField = relations.digest.digest.combine(&values);
        let wrong_consumer = SecureField::one() / denom;

        assert_ne!(
            claim.total() + wrong_consumer,
            SecureField::zero(),
            "a consumer requiring different bytes must not balance the digest yield",
        );
    }

    // ---- credential-field provider ----

    use air_core::relations::field_id;

    /// A credential-shaped 11-byte preimage (`docs/credential-format.md`):
    /// `"EUID" | ver | year(2007) | month(3) | day(15) | nat(276=0x0114)`. The
    /// DOB window is `c[5..9]`, the nationality window `c[9..11]`.
    const SAMPLE_CREDENTIAL: [u8; 11] = [b'E', b'U', b'I', b'D', 1, 0x07, 0xD7, 3, 15, 0x01, 0x14];

    /// Sum a synthetic consumer that *requires* each `(field_id, byte_index,
    /// value)` tuple over the same drawn field relation the provider yielded
    /// against: `+1 / combine(tuple)` per byte.
    fn synthetic_field_consumer(
        relations: &Sha256Relations,
        tuples: &[(u32, u32, u32)],
    ) -> SecureField {
        let mut acc = SecureField::zero();
        for &(f, b, v) in tuples {
            let tuple = [BaseField::from(f), BaseField::from(b), BaseField::from(v)];
            let denom: SecureField = relations.field.field.combine(&tuple);
            assert_ne!(denom, SecureField::zero(), "combine must be invertible");
            acc += SecureField::one() / denom;
        }
        acc
    }

    /// The credential-field provider smoke test: with **only** the DOB window exposed, the
    /// SHA module yields the four DOB bytes, and a synthetic consumer requiring
    /// exactly `(DOB, i, c[5+i])` cancels the module's outstanding provider term.
    /// Balancing for the credential's *actual* DOB bytes is the proof that SHA
    /// exposed the bytes that were hashed.
    #[test]
    fn field_provider_dob_window_balances_against_synthetic_consumer() {
        let c = SAMPLE_CREDENTIAL;
        let witness = compute_sha256_witness(&c);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[(field_id::DOB, 5, 4)]);

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            MAX_ROUND_GROUP_BITS,
            false,
            &exposure,
        );
        let module_total = claim.total();

        let dob: Vec<(u32, u32, u32)> = (0..4)
            .map(|i| (field_id::DOB, i as u32, c[5 + i] as u32))
            .collect();
        let consumer = synthetic_field_consumer(&relations, &dob);

        // The yield leaves the module unbalanced on its own...
        assert_ne!(
            module_total,
            SecureField::zero(),
            "exposing the DOB window must leave an outstanding provider term",
        );
        // ...and the synthetic DOB consumer cancels it exactly.
        assert_eq!(
            module_total + consumer,
            SecureField::zero(),
            "DOB field provider must balance a consumer requiring the same bytes",
        );
    }

    /// Both windows exposed at once: a consumer requiring all six bytes (DOB +
    /// nationality) balances. Confirms one shared channel carries both fields,
    /// keyed by `field_id`.
    #[test]
    fn field_provider_balances_full_credential_exposure() {
        let c = SAMPLE_CREDENTIAL;
        let witness = compute_sha256_witness(&c);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, 9, 2),
        ]);

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            MAX_ROUND_GROUP_BITS,
            false,
            &exposure,
        );

        let mut tuples: Vec<(u32, u32, u32)> = (0..4)
            .map(|i| (field_id::DOB, i as u32, c[5 + i] as u32))
            .collect();
        tuples.push((field_id::NATIONALITY, 0, c[9] as u32));
        tuples.push((field_id::NATIONALITY, 1, c[10] as u32));
        let consumer = synthetic_field_consumer(&relations, &tuples);

        assert_eq!(
            claim.total() + consumer,
            SecureField::zero(),
            "field provider must balance a consumer requiring every exposed byte",
        );
    }

    /// A consumer requiring a *different* field byte (DOB day off by one) does
    /// not cancel the provider's yield — the balance closes only for the exact
    /// credential bytes SHA hashed. This is the DOB binding's core property
    /// (proving age from a date other than the signed one is rejected) at the
    /// credential-field provider level.
    #[test]
    fn field_provider_rejects_mismatched_consumer() {
        let c = SAMPLE_CREDENTIAL;
        let witness = compute_sha256_witness(&c);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[(field_id::DOB, 5, 4)]);

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            MAX_ROUND_GROUP_BITS,
            false,
            &exposure,
        );

        // Require the DOB window but with the day byte tampered (15 → 16).
        let mut dob: Vec<(u32, u32, u32)> = (0..4)
            .map(|i| (field_id::DOB, i as u32, c[5 + i] as u32))
            .collect();
        dob[3].2 += 1;
        let wrong_consumer = synthetic_field_consumer(&relations, &dob);

        assert_ne!(
            claim.total() + wrong_consumer,
            SecureField::zero(),
            "a consumer requiring a different DOB byte must not balance the yield",
        );
    }
}
