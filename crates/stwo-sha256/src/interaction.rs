//! LogUp interaction-trace generator for every SHA-256 component.
//!
//! The main `Sha256Eval` consumer emits one interaction trace.
//! Four `Range_k` table producers emit their interaction traces.
//! An enabled digest provider also yields the final digest through `Sha256Digest`.
//! This extra yield makes the isolated SHA claim sum nonzero.
//! [`LogupTraceGenerator`] builds each trace from row fractions.
//! Consecutive fractions share a column in batches.
//!
//! Single-fraction producers use pairs.
//! `Sha256Eval` uses [`SHA_CONSUMER_LOGUP_BATCH`].
//!
//! **Sum-to-zero invariant.**
//! Each consumer use cancels a producer yield at the same row key.
//! Their `claimed_sum` values total zero in a balanced composition.
//! Component constraints and the proof OODS balance enforce this invariant.
//!
//! Lookup orders **must** match the order `Sha256Eval::evaluate` /
//! `components::*::evaluate` fire `add_to_relation`. Drift between this
//! generator and the AIR evaluator silently invalidates the proof
//! (denominator mismatch ⇒ verifier rejects).
//!
//! This implementation uses the scalar `write_frac` path one row at a time.
//! The simple scalar path is the active implementation.

use air_core::claim_mask::ClaimMaskTrace;
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
use crate::field_exposure::{word_be_bytes, FieldExposure};
use crate::multiplicities::range_k_multiplicities;
use crate::relations::Sha256Relations;
use crate::trace::{h_out_digest_bytes, Layout};
use crate::types::Sha256Witness;

/// Lookup sites the main `Sha256Eval` fires per **row**, **excluding** the
/// optional digest yield. Breakdown (W=6), matching the firing order in
/// `write_round_row_lookups` and `crate::constraints::Sha256Eval::evaluate`:
///
/// ```text
///   2 (schedule family: Range_4 carry pair; t ≥ 16 rows)
/// +  8 (round family: 4 carry pairs = 8; every row)
/// + 16 (finalization carries, t = 63 rows)
/// + 32 (terminal `Range_8` digest bytes, t = 63 rows)
/// = 58
/// ```
///
/// Committed boolean bit planes calculate Σ0, Σ1, Maj, Ch, and the σ inputs.
/// Recomposition binds these results to the words.
/// The lookup set contains only addition carry checks and terminal byte range
/// checks.
///
/// A site that does not fire on a given row holds the neutral fraction `(0, 1)`.
pub const SHA_LOOKUPS_PER_ROW_BASE: usize = 58;

/// Number of `Sha256Eval` fractions in one interaction column.
///
/// A batch of four reduces the consumer column count.
/// The resulting constraint has degree five or less.
/// It requires `max_constraint_log_degree_bound = log_size + 2`.
/// The witness builder, evaluator, and column sizing use this constant.
pub const SHA_CONSUMER_LOGUP_BATCH: usize = 4;

/// Total lookup sites `Sha256Eval` fires per row. The digest provider adds
/// exactly one width-32 yield site when `expose_digest` is set. The
/// credential-field provider adds one width-3 yield per exposed window byte
/// plus 64 sites for an optional full padded-message stream. These sites act on
/// `t = 15` rows).
/// Existing W bit planes determine the byte value, so it adds no range
/// lookups. Both this generator and `crate::air`'s
/// interaction-column sizing read this so the two never drift.
#[inline]
pub fn sha_lookups_per_row(expose_digest: bool, field_exposure: &FieldExposure) -> usize {
    SHA_LOOKUPS_PER_ROW_BASE + usize::from(expose_digest) + field_exposure.n_yields()
}

// ---------------------------------------------------------------------------
// Per-component claim
// ---------------------------------------------------------------------------

/// One component's slot in the aggregate interaction claim. `claimed_sum`
/// is what the verifier checks each component's interaction column
/// cumulatively reaches. The total over every component must be zero.
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
/// Field order **must** match the component order in the proof
/// (`crate::stark::commit_base_trace` / `crate::stark::component_provers`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InteractionClaim {
    pub sha256: ComponentClaim,
    pub range: Vec<ComponentClaim>, // 4: Range_2, Range_4, Range_5, Range_8
}

impl InteractionClaim {
    /// Sum all component claim sums.
    ///
    /// Cross-component consumers can cancel enabled SHA provider terms.
    /// A complete proof requires a zero global LogUp sum.
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
/// the producer). Denominator is `combine(values) = sum α^i · v_i − z`.
pub(crate) type Frac = (SecureField, SecureField);

pub(crate) fn claim_mask_fraction_column(trace: &ClaimMaskTrace, beta: SecureField) -> Vec<Frac> {
    let rows = 1usize << trace.log_size();
    (0..rows)
        .map(|row| {
            let mask = SecureField::from_m31_array(std::array::from_fn(|coordinate| {
                trace.columns()[coordinate].values.as_slice()[row]
            }));
            (mask * beta, SecureField::one())
        })
        .collect()
}

/// Build one interaction trace for a component from its list of
/// row-iterators. `lookups[k]` is the k-th lookup the component fires —
/// a `Vec<Frac>` of length `2^log_size` giving the row-by-row fraction.
///
/// Pairs of consecutive lookups share one interaction column, matching
/// `finalize_logup_batched(batch)`. A final short chunk (count not a
/// multiple of `batch`) gets its own column.
///
/// The per-chunk `(num, den)` uses the same left-fold as the constraint
/// framework's `finalize_logup_batched`: starting from the chunk's first
/// fraction, `num = num·dₖ + nₖ·den; den = den·dₖ`. This yields
/// `num = Σᵢ nᵢ·∏_{j≠i} dⱼ`, `den = ∏ dⱼ`, so the witness column matches the
/// eval-side accumulator exactly (identical in exact field arithmetic
/// regardless of accumulation order).
pub(crate) fn build_interaction_columns(
    log_size: u32,
    lookups: Vec<Vec<Frac>>,
    batch: usize,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    debug_assert!(log_size >= LOG_N_LANES, "log_size < LOG_N_LANES");
    debug_assert!(batch >= 1, "batch must be ≥ 1");
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

    // Walk lookups in chunks of `batch` — each chunk shares one interaction
    // column. A trailing short chunk gets its own column.
    for chunk in lookups.chunks(batch) {
        let mut col = gen.new_col();
        for vec_row in 0..(n_rows / N_LANES) {
            let mut num_arr = [SecureField::zero(); N_LANES];
            let mut den_arr = [SecureField::one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (mut num, mut den) = chunk[0][row];
                for lo in &chunk[1..] {
                    let (n, d) = lo[row];
                    num = num * d + n * den;
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

/// Build one Class D blinded producer fraction column.
///
/// This mirrors the gated entry from `crate::components::emit_blind`.
/// Its numerator is `-(1 − is_dummy)·mult`.
/// A real row uses numerator `-mult`.
/// A dummy row uses numerator zero.
/// Thus, dummy multiplicities remain committed but do not enter the LogUp sum.
/// The caller pairs two producer fractions in one interaction column.
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
        // Dummy rows have a zero numerator. Real rows yield `-mult`.
        let num = if idx >= real_len {
            SecureField::zero()
        } else {
            -SecureField::from(BaseField::from(*m))
        };
        out.push((num, denom));
    }
    out
}

// Each producer column uses its exact `log_size`.
// The consumer builder initializes `n_rows` neutral fractions per lookup.

// ---------------------------------------------------------------------------
// Producer-side per-table interaction columns
// ---------------------------------------------------------------------------

/// Build the interaction trace for one `Range_k` producer.
fn range_k_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    kind: RangeKind,
    log_size: u32,
    claim_mask: Option<(&ClaimMaskTrace, SecureField)>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mut mults = range_k_multiplicities(witness, kind);
    let n_rows = 1usize << log_size;
    mults.resize(n_rows, 0);
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
    let mut lookups = vec![frac];
    if let Some((trace, beta)) = claim_mask {
        lookups.push(claim_mask_fraction_column(trace, beta));
    }
    build_interaction_columns(log_size, lookups, 2)
}

// ---------------------------------------------------------------------------
// Consumer-side (Sha256Eval) interaction trace
// ---------------------------------------------------------------------------

/// Build the interaction trace for the main `Sha256Eval` consumer.
///
/// Mirrors the *exact* `add_to_relation` order `Sha256Eval::evaluate`
/// fires. Each lookup produces one fraction column at log_size = the
/// trace's log_size. Pairs share an interaction column.
///
/// Lookup cells come from the corresponding main trace row.
/// Padding rows contribute the neutral fraction `(0, 1)`.
/// They do not change the sum.
/// The AIR uses `enabler` for the matching constraint gates.
fn sha256_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    log_size: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    claim_mask: Option<(&ClaimMaskTrace, SecureField)>,
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
    // `n_rows`, default-filled with the neutral `(0, 1)`. Real rows
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

    if let Some((trace, beta)) = claim_mask {
        all_lookups.push(claim_mask_fraction_column(trace, beta));
    }
    build_interaction_columns(log_size, all_lookups, SHA_CONSUMER_LOGUP_BATCH)
}

/// Write every lookup site for one `(block, round t)` row at its trace
/// slot, in **exactly** the `Sha256Eval::evaluate` firing order. Bumps
/// `cursor` past each site so the same site index always lands at the same
/// fraction column across rows. Sites that do not fire on this row keep
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
    // ---- 1. Schedule family: Range_4 carry pair on rows t ≥ 16 ----
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

    // ---- 2. Round family carry range-checks (4 pairs, every real row) ----
    let round = &block.rounds[t];

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

    // ---- 4/5. Finalization carries + terminal `Range_8` bytes (t = 63 rows) ----
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

    // ---- 6. Digest yield (provider side, final block's t = 63 row) ----
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

    // ---- 7. Credential-field yields (target block t = 15 rows) ----
    //
    // Same order as the constraint side: fixed windows first, then the
    // optional 64-byte padded stream for every real block.
    if !field_exposure.is_empty() {
        if t == 15 {
            for y in field_exposure.yields() {
                let selector =
                    SecureField::from(BaseField::from(u32::from(block_idx == y.block_idx)));
                let limb = block.schedule[y.word_idx];
                let value = word_be_bytes(limb.lo, limb.hi)[y.byte_in_word];
                let tuple = [
                    BaseField::from(y.field_id),
                    BaseField::from(y.byte_index),
                    BaseField::from(value),
                ];
                let denom = relations.field.field.combine(&tuple);
                all[*cursor][slot] = (-selector, denom);
                *cursor += 1;
            }
            if let Some(field_id) = field_exposure.padded_stream_field_id() {
                for byte_in_block in 0..crate::constants::BLOCK_BYTES {
                    let word_idx = byte_in_block / crate::constants::WORD_BYTES;
                    let byte_in_word = byte_in_block % crate::constants::WORD_BYTES;
                    let limb = block.schedule[word_idx];
                    let value = word_be_bytes(limb.lo, limb.hi)[byte_in_word];
                    let tuple = [
                        BaseField::from(field_id),
                        BaseField::from(
                            (block_idx * crate::constants::BLOCK_BYTES + byte_in_block) as u32,
                        ),
                        BaseField::from(value),
                    ];
                    let denom = relations.field.field.combine(&tuple);
                    all[*cursor][slot] = (-SecureField::from(BaseField::from(1u32)), denom);
                    *cursor += 1;
                }
            }
        } else {
            *cursor += sha_lookups_per_row(false, field_exposure) - SHA_LOOKUPS_PER_ROW_BASE;
        }
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
#[allow(clippy::too_many_arguments)]
pub fn generate_interaction_trace(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
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
        expose_digest,
        field_exposure,
        true,
        None,
    )
}

pub fn generate_consumer_interaction_trace(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
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
        expose_digest,
        field_exposure,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn generate_interaction_trace_with_claim_masks(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
    claim_masks: &[ClaimMaskTrace],
    beta: SecureField,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    generate_interaction_trace_inner(
        relations,
        witness,
        sha256_log_size,
        expose_digest,
        field_exposure,
        include_table_providers,
        Some((claim_masks, beta)),
    )
}

#[allow(clippy::too_many_arguments)]
fn generate_interaction_trace_inner(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
    claim_masks: Option<(&[ClaimMaskTrace], SecureField)>,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    let mut combined = Vec::new();

    // Sha256Eval consumer first — its slot in the proof's component list.
    // `expose_digest` adds the cross-component digest yield to this component's
    // fractions. `field_exposure` adds one credential-field yield per exposed
    // byte (and hence to its claimed sum).
    let (sha_trace, sha_sum) = sha256_interaction(
        relations,
        witness,
        sha256_log_size,
        expose_digest,
        field_exposure,
        claim_masks.map(|(traces, beta)| (&traces[0], beta)),
    );
    combined.extend(sha_trace);
    let sha256 = ComponentClaim {
        claimed_sum: sha_sum,
    };

    // 4 range producers (Range_2, Range_4, Range_5, Range_8).
    let mut range = Vec::with_capacity(4);
    if include_table_providers {
        for &kind in RANGE_TABLES {
            let claim_index = range.len() + 1;
            let masked = claim_masks.map(|(traces, beta)| (&traces[claim_index], beta));
            let log_size = if masked.is_some() {
                range_log_size(kind).max(air_core::claim_mask::CLAIM_MASK_MIN_LOG_SIZE)
            } else {
                range_log_size(kind)
            };
            let (t, s) = range_k_interaction(relations, witness, kind, log_size, masked);
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
    use crate::trace::min_log_size;
    use crate::witness::compute_sha256_witness;
    use stwo::core::channel::Blake2sChannel;

    /// Confirm that the disabled digest provider preserves a zero claim sum.
    ///
    /// The standalone consumer and producers remain balanced.
    #[test]
    fn digest_provider_off_keeps_module_self_balanced() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
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
    /// moving one radix unit between the two cells. The Range8 lookup rejects
    /// that otherwise constraint-preserving representation.
    #[test]
    fn range_8_rejects_recomposition_preserving_out_of_range_digest_byte() {
        let witness = compute_sha256_witness(b"abc");
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, producer_sum) = range_k_interaction(
            &relations,
            &witness,
            RangeKind::Range8,
            range_log_size(RangeKind::Range8),
            None,
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

    /// Confirm that a synthetic digest consumer balances the enabled provider.
    ///
    /// The provider yields 32 final digest bytes.
    /// Its outstanding term is `−1/combine(digest)`.
    /// The matching consumer contributes `+1/combine(digest)`.
    /// All other lookups cancel within the SHA module.
    #[test]
    fn digest_provider_balances_against_synthetic_consumer() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
            true,
            &FieldExposure::empty(),
        );
        let module_total = claim.total();

        // Synthesize the consumer term with the provider relation:
        // +1 / combine(final-block digest bytes).
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

    /// A consumer with a different digest does not cancel the provider yield.
    /// The balance closes only for the digest that SHA computed. This test
    /// checks that binding property at the digest-provider level.
    #[test]
    fn digest_provider_rejects_mismatched_consumer() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());

        let (_, claim) = generate_interaction_trace(
            &relations,
            &witness,
            log_size,
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

    // ---- field provider ----

    use air_core::relations::field_id;

    /// A generic preimage with sample windows at offsets 5..9 and 9..11.
    const SAMPLE_MESSAGE: [u8; 11] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

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

    /// Confirm that a DOB consumer balances the exact exposed bytes.
    ///
    /// The SHA module yields four DOB bytes.
    /// A synthetic consumer requires `(DOB, i, c[5+i])`.
    /// The exact tuple cancels the provider term.
    #[test]
    fn field_provider_dob_window_balances_against_synthetic_consumer() {
        let c = SAMPLE_MESSAGE;
        let witness = compute_sha256_witness(&c);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[(field_id::DOB, 5, 4)]);

        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);
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
    fn field_provider_balances_all_exposed_windows() {
        let c = SAMPLE_MESSAGE;
        let witness = compute_sha256_witness(&c);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, 9, 2),
        ]);

        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);

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

    /// A multi-block window is bound to its exact absolute byte offset and
    /// big-endian word-byte order. Neither a one-byte shift nor reversing the
    /// requested bytes can cancel the provider claim.
    #[test]
    fn field_provider_preserves_multi_block_shift_and_byte_order() {
        let message: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
        let witness = compute_sha256_witness(&message);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[(field_id::DOB, 62, 6)]);

        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);
        let module_total = claim.total();
        let tuples = |bytes: &[u8]| {
            bytes
                .iter()
                .enumerate()
                .map(|(i, &byte)| (field_id::DOB, i as u32, u32::from(byte)))
                .collect::<Vec<_>>()
        };

        let exact = synthetic_field_consumer(&relations, &tuples(&message[62..68]));
        assert_eq!(
            module_total + exact,
            SecureField::zero(),
            "virtual field bytes must equal the exact cross-block message window",
        );

        let shifted = synthetic_field_consumer(&relations, &tuples(&message[61..67]));
        assert_ne!(
            module_total + shifted,
            SecureField::zero(),
            "a one-byte-shifted window must not balance",
        );

        let mut reversed = message[62..68].to_vec();
        reversed.reverse();
        let reversed = synthetic_field_consumer(&relations, &tuples(&reversed));
        assert_ne!(
            module_total + reversed,
            SecureField::zero(),
            "reversing big-endian field bytes must not balance",
        );
    }

    /// Confirm that a different DOB byte cannot balance the provider.
    ///
    /// The balance closes only for the exact bytes that SHA hashed.
    /// This property rejects an age proof from a different date.
    #[test]
    fn field_provider_rejects_mismatched_consumer() {
        let c = SAMPLE_MESSAGE;
        let witness = compute_sha256_witness(&c);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::from_preimage_windows(&[(field_id::DOB, 5, 4)]);

        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);

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

    fn padded_stream_tuples(witness: &Sha256Witness, field_id: u32) -> Vec<(u32, u32, u32)> {
        witness
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(block_idx, block)| {
                block.schedule[..crate::constants::N_INPUT_WORDS]
                    .iter()
                    .flat_map(move |word| word_be_bytes(word.lo, word.hi))
                    .enumerate()
                    .map(move |(byte_in_block, byte)| {
                        (
                            field_id,
                            (block_idx * crate::constants::BLOCK_BYTES + byte_in_block) as u32,
                            byte,
                        )
                    })
            })
            .collect()
    }

    #[test]
    fn padded_stream_balances_exact_sha_compression_input() {
        const STREAM_FIELD_ID: u32 = 99;
        let message: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
        let witness = compute_sha256_witness(&message);
        assert_eq!(witness.blocks.len(), 3);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::empty().with_padded_stream(STREAM_FIELD_ID);

        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);
        let tuples = padded_stream_tuples(&witness, STREAM_FIELD_ID);
        assert_eq!(
            tuples.len(),
            witness.blocks.len() * crate::constants::BLOCK_BYTES,
        );
        assert_eq!(
            claim.total() + synthetic_field_consumer(&relations, &tuples),
            SecureField::zero(),
            "stream consumer must see every padded SHA input byte at its absolute index",
        );
    }

    #[test]
    fn padded_stream_rejects_byte_index_and_value_tampering() {
        const STREAM_FIELD_ID: u32 = 99;
        let message: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
        let witness = compute_sha256_witness(&message);
        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let exposure = FieldExposure::empty().with_padded_stream(STREAM_FIELD_ID);
        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);

        let mut wrong_value = padded_stream_tuples(&witness, STREAM_FIELD_ID);
        wrong_value[crate::constants::BLOCK_BYTES].2 ^= 1;
        assert_ne!(
            claim.total() + synthetic_field_consumer(&relations, &wrong_value),
            SecureField::zero(),
            "changing a streamed byte must leave the relation unbalanced",
        );

        let mut wrong_index = padded_stream_tuples(&witness, STREAM_FIELD_ID);
        wrong_index[crate::constants::BLOCK_BYTES].1 += 1;
        assert_ne!(
            claim.total() + synthetic_field_consumer(&relations, &wrong_index),
            SecureField::zero(),
            "changing an absolute stream index must leave the relation unbalanced",
        );

        let mut missing_block = padded_stream_tuples(&witness, STREAM_FIELD_ID);
        missing_block.truncate(missing_block.len() - crate::constants::BLOCK_BYTES);
        assert_ne!(
            claim.total() + synthetic_field_consumer(&relations, &missing_block),
            SecureField::zero(),
            "omitting an emitted SHA block must leave the relation unbalanced",
        );
    }
}
