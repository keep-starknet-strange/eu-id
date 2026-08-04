//! LogUp interaction-trace generator for every SHA-256 component.
//!
//! The main `Sha256Eval` consumer emits one interaction trace.
//! Four `Range_k` table producers emit their interaction traces.
//! An enabled digest provider also yields each final digest through the keyed
//! `PackedShaDigest` relation.
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
use crate::multiplicities::range_k_multiplicities;
use crate::relations::{Sha256Relations, PACKED_SHA_STREAM_FIELD_BASE};
use crate::trace::{h_out_digest_bytes, word_be_bytes, Layout};
use crate::types::PackedSha256Witness;

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

/// Total lookup sites `Sha256Eval` fires per row. The packed digest provider
/// adds one width-33 yield site and the complete padded-message provider adds
/// 64 width-3 yield sites. Both providers are fixed-width and fire only on
/// their gated boundary rows. The evaluator and interaction writer share this
/// count and the same lookup order.
#[inline]
pub fn sha_lookups_per_row(expose_digest: bool, expose_field: bool) -> usize {
    SHA_LOOKUPS_PER_ROW_BASE + usize::from(expose_digest) + usize::from(expose_field) * 64
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
    witness: &PackedSha256Witness,
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
    witness: &PackedSha256Witness,
    log_size: u32,
    expose_digest: bool,
    expose_field: bool,
    claim_mask: Option<(&ClaimMaskTrace, SecureField)>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1usize << log_size;

    // One fraction vector per lookup site (`lookup_idx`), each of length
    // `n_rows`, default-filled with the neutral `(0, 1)`. Real rows
    // overwrite the sites that fire on them. See
    // [`SHA_LOOKUPS_PER_ROW_BASE`] for the per-row site breakdown.
    let lookups_per_row = sha_lookups_per_row(expose_digest, expose_field);
    let mut all_lookups: Vec<Vec<Frac>> = (0..lookups_per_row)
        .map(|_| vec![(SecureField::zero(), SecureField::one()); n_rows])
        .collect();

    let mut global_block = 0usize;
    for (message_idx, message) in witness.messages.iter().enumerate() {
        for (block_idx, block) in message.blocks.iter().enumerate() {
            let is_msg_last = block_idx + 1 == message.blocks.len();
            for t in 0..crate::constants::N_ROUNDS {
                let slot = Layout::round_row_slot(global_block, t, log_size);
                let mut cursor = 0usize;
                write_round_row_lookups(
                    &mut all_lookups,
                    &mut cursor,
                    slot,
                    block,
                    t,
                    relations,
                    expose_digest,
                    expose_field,
                    is_msg_last,
                    message_idx,
                    block_idx,
                );
                debug_assert_eq!(cursor, lookups_per_row, "row lookup miscount");
            }
            global_block += 1;
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
    expose_field: bool,
    is_msg_last: bool,
    message_idx: usize,
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

    // ---- 6. Keyed digest yield (provider side, final block's t = 63 row) ----
    if expose_digest {
        if t == crate::constants::N_ROUNDS - 1 {
            let bytes = h_out_digest_bytes(&block.h_out);
            let values: [BaseField; DIGEST_BYTES] =
                std::array::from_fn(|i| BaseField::from(bytes[i]));
            let mut tuple = [BaseField::zero(); 1 + DIGEST_BYTES];
            tuple[0] = BaseField::from(message_idx as u32);
            tuple[1..].copy_from_slice(&values);
            let denom = relations.packed_digest.combine(&tuple);
            let num = -SecureField::from(BaseField::from(u32::from(is_msg_last)));
            all[*cursor][slot] = (num, denom);
        }
        *cursor += 1;
    }

    // ---- 7. Full padded-message stream (provider, block's t = 15 row) ----
    //
    // Every packed message gets its own field namespace. The byte index is
    // local to that message and resets at every message boundary.
    if expose_field {
        if t == 15 {
            for byte_in_block in 0..crate::constants::BLOCK_BYTES {
                let word_idx = byte_in_block / crate::constants::WORD_BYTES;
                let byte_in_word = byte_in_block % crate::constants::WORD_BYTES;
                let limb = block.schedule[word_idx];
                let value = word_be_bytes(limb.lo, limb.hi)[byte_in_word];
                let tuple = [
                    BaseField::from(PACKED_SHA_STREAM_FIELD_BASE + message_idx as u32),
                    BaseField::from(
                        (block_idx * crate::constants::BLOCK_BYTES + byte_in_block) as u32,
                    ),
                    BaseField::from(value),
                ];
                let denom = relations.field.field.combine(&tuple);
                all[*cursor][slot] = (-SecureField::one(), denom);
                *cursor += 1;
            }
        } else {
            *cursor += 64;
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
    witness: &PackedSha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    expose_field: bool,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    generate_interaction_trace_inner(
        relations,
        witness,
        sha256_log_size,
        expose_digest,
        expose_field,
        true,
        None,
    )
}

pub fn generate_consumer_interaction_trace(
    relations: &Sha256Relations,
    witness: &PackedSha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    expose_field: bool,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    generate_interaction_trace_inner(
        relations,
        witness,
        sha256_log_size,
        expose_digest,
        expose_field,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn generate_interaction_trace_with_claim_masks(
    relations: &Sha256Relations,
    witness: &PackedSha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    expose_field: bool,
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
        expose_field,
        include_table_providers,
        Some((claim_masks, beta)),
    )
}

#[allow(clippy::too_many_arguments)]
fn generate_interaction_trace_inner(
    relations: &Sha256Relations,
    witness: &PackedSha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    expose_field: bool,
    include_table_providers: bool,
    claim_masks: Option<(&[ClaimMaskTrace], SecureField)>,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    let mut combined = Vec::new();

    // Sha256Eval consumer first — its slot in the proof's component list.
    // `expose_digest` adds one keyed digest yield per message. `expose_field`
    // adds the fixed 64-byte stream yield for every packed block.
    let (sha_trace, sha_sum) = sha256_interaction(
        relations,
        witness,
        sha256_log_size,
        expose_digest,
        expose_field,
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
    use crate::witness::compute_packed_sha256_witness;
    use stwo::core::channel::Blake2sChannel;

    fn packed(messages: &[&[u8]]) -> PackedSha256Witness {
        compute_packed_sha256_witness(messages).expect("test messages are valid")
    }

    fn inverse<R, const N: usize>(relation: &R, tuple: &[BaseField; N]) -> SecureField
    where
        R: Relation<BaseField, SecureField>,
    {
        let denominator: SecureField = relation.combine(tuple);
        assert_ne!(denominator, SecureField::zero());
        SecureField::one() / denominator
    }

    fn digest_consumer(relations: &Sha256Relations, witness: &PackedSha256Witness) -> SecureField {
        witness
            .messages
            .iter()
            .enumerate()
            .map(|(message_idx, message)| {
                let bytes = h_out_digest_bytes(
                    &message.blocks.last().expect("message has one block").h_out,
                );
                let mut tuple = [BaseField::zero(); 1 + DIGEST_BYTES];
                tuple[0] = BaseField::from(message_idx as u32);
                for (index, byte) in bytes.iter().enumerate() {
                    tuple[index + 1] = BaseField::from(*byte);
                }
                inverse(&relations.packed_digest, &tuple)
            })
            .sum()
    }

    fn stream_consumer(relations: &Sha256Relations, witness: &PackedSha256Witness) -> SecureField {
        witness
            .messages
            .iter()
            .enumerate()
            .flat_map(|(message_idx, message)| {
                message
                    .blocks
                    .iter()
                    .enumerate()
                    .flat_map(move |(block_idx, block)| {
                        block.schedule[..crate::constants::N_INPUT_WORDS]
                            .iter()
                            .flat_map(|word| word_be_bytes(word.lo, word.hi))
                            .enumerate()
                            .map(move |(byte_in_block, byte)| {
                                let tuple = [
                                    BaseField::from(
                                        PACKED_SHA_STREAM_FIELD_BASE + message_idx as u32,
                                    ),
                                    BaseField::from(
                                        (block_idx * crate::constants::BLOCK_BYTES + byte_in_block)
                                            as u32,
                                    ),
                                    BaseField::from(byte),
                                ];
                                inverse(&relations.field.field, &tuple)
                            })
                    })
            })
            .sum()
    }

    #[test]
    fn packed_lookup_width_is_fixed() {
        assert_eq!(sha_lookups_per_row(false, false), 58);
        assert_eq!(sha_lookups_per_row(true, false), 59);
        assert_eq!(sha_lookups_per_row(false, true), 122);
        assert_eq!(sha_lookups_per_row(true, true), 123);
    }

    #[test]
    fn four_message_consumer_balances_without_optional_providers() {
        let messages: [&[u8]; 4] = [b"issuer", b"mso", b"revocation", b"item"];
        let witness = packed(&messages);
        let log_size = min_log_size(witness.total_blocks());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, claim) = generate_interaction_trace(&relations, &witness, log_size, false, false);
        assert_eq!(claim.total(), SecureField::zero());
    }

    #[test]
    fn keyed_digest_and_stream_tuples_balance_all_five_messages() {
        let messages: [&[u8]; 5] = [b"issuer", b"mso", b"revocation", b"item-0", b"item-1"];
        let witness = packed(&messages);
        let log_size = min_log_size(witness.total_blocks());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, claim) = generate_interaction_trace(&relations, &witness, log_size, true, true);
        assert_eq!(
            claim.total()
                + digest_consumer(&relations, &witness)
                + stream_consumer(&relations, &witness),
            SecureField::zero(),
        );
    }

    #[test]
    fn keyed_digest_slot_and_stream_index_tampering_do_not_balance() {
        let messages: [&[u8]; 5] = [b"issuer", b"mso", b"revocation", b"item-0", b"item-1"];
        let witness = packed(&messages);
        let log_size = min_log_size(witness.total_blocks());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, claim) = generate_interaction_trace(&relations, &witness, log_size, true, true);

        let mut wrong_digest = digest_consumer(&relations, &witness);
        let message = &witness.messages[0];
        let bytes = h_out_digest_bytes(&message.blocks.last().unwrap().h_out);
        let mut tuple = [BaseField::zero(); 1 + DIGEST_BYTES];
        tuple[0] = BaseField::from(1u32);
        for (index, byte) in bytes.iter().enumerate() {
            tuple[index + 1] = BaseField::from(*byte);
        }
        wrong_digest -= inverse(&relations.packed_digest, &tuple);
        tuple[0] = BaseField::from(0u32);
        wrong_digest += inverse(&relations.packed_digest, &tuple);
        assert_ne!(
            claim.total() + wrong_digest + stream_consumer(&relations, &witness),
            SecureField::zero(),
        );

        let mut wrong_stream = stream_consumer(&relations, &witness);
        let block = &witness.messages[0].blocks[0];
        let byte = word_be_bytes(block.schedule[0].lo, block.schedule[0].hi)[0];
        let honest = [
            BaseField::from(PACKED_SHA_STREAM_FIELD_BASE),
            BaseField::from(0u32),
            BaseField::from(byte),
        ];
        let wrong_index = [
            BaseField::from(PACKED_SHA_STREAM_FIELD_BASE),
            BaseField::from(1u32),
            BaseField::from(byte),
        ];
        wrong_stream -= inverse(&relations.field.field, &honest);
        wrong_stream += inverse(&relations.field.field, &wrong_index);
        assert_ne!(
            claim.total() + digest_consumer(&relations, &witness) + wrong_stream,
            SecureField::zero(),
        );
    }

    #[test]
    fn range8_multiplicity_and_digest_bytes_cover_every_packed_block() {
        let messages: [&[u8]; 4] = [b"a", &[0x42; 70], b"abc", &[0x11; 130]];
        let witness = packed(&messages);
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, producer_sum) = range_k_interaction(
            &relations,
            &witness,
            RangeKind::Range8,
            range_log_size(RangeKind::Range8),
            None,
        );
        let consumer_sum = witness
            .messages
            .iter()
            .flat_map(|message| message.blocks.iter())
            .flat_map(|block| h_out_digest_bytes(&block.h_out))
            .map(|byte| inverse(&relations.range.range_8, &[BaseField::from(byte)]))
            .sum::<SecureField>();
        assert_eq!(producer_sum + consumer_sum, SecureField::zero());
    }
}
