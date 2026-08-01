//! LogUp interaction-trace generator for every SHA-256 component.
//!
//! `Sha256Eval` and each range-table producer emit one interaction trace.
//! Digest exposure also yields the final digest on the `Sha256Digest` channel.
//! This yield gives the isolated SHA component a nonzero claimed sum.
//!
//! The consumer batches four fractions per interaction column. Each producer
//! batches two fractions per interaction column.
//!
//! The total claimed sum must be zero. Each consumer term must cancel a
//! producer term with the same key.
//!
//! Lookup order must match the `add_to_relation` order in each evaluator. A
//! different order produces different denominators and invalidates the proof.

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
use crate::constants::{DIGEST_BYTES, N_STATE_WORDS};
use crate::constraints::LOGUP_BATCH;
use crate::digest_bridge::{
    digest_bridge_lookups, DIGEST_BRIDGE_LOG_SIZE, DIGEST_BRIDGE_LOOKUPS_BASE,
};
use crate::field_exposure::{word_be_bytes, FieldExposure, FULL_PADDED_STREAM_SITES_PER_ROW};
use crate::multiplicities::range_k_multiplicities;
use crate::relations::Sha256Relations;
use crate::trace::{h_out_digest_bytes, Layout};
use crate::types::Sha256Witness;

/// Lookup sites the main `Sha256Eval` fires per **row**, **excluding** the
/// optional digest yield. Breakdown, matching the firing order in
/// [`write_round_row_lookups`] and `crate::constraints::Sha256Eval::evaluate`:
///
/// ```text
///   2 (schedule `Range_4` carry pair; t ≥ 16 rows)
/// +  8 (round carry range-checks; every round row)
/// + 16 (finalization carries, t = 63 rows)
/// +  1 (final-state limb bridge, final t = 63 row)
/// = 27
/// ```
///
/// A site that does not fire on a given row holds the neutral fraction `(0, 1)`.
pub const SHA_LOOKUPS_PER_ROW_BASE: usize = 27;

/// Return the lookup sites that `Sha256Eval` fires on each row.
///
/// The padded-stream provider adds four field sites.
#[inline]
pub fn sha_lookups_per_row(field_exposure: &FieldExposure) -> usize {
    SHA_LOOKUPS_PER_ROW_BASE + field_exposure.n_yields()
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
    pub digest_bridge: ComponentClaim,
    /// Claims for `Range_2`, `Range_4`, `Range_5`, and `Range_8`, in that
    /// order. A standalone proof must contain one claim per range table.
    pub range: Vec<ComponentClaim>,
}

impl InteractionClaim {
    /// Sum of all local component claims. A standalone verifier requires zero.
    /// A composed verifier balances this sum with cross-module claims.
    pub fn total(&self) -> SecureField {
        let mut s = self.sha256.claimed_sum;
        s += self.digest_bridge.claimed_sum;
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
        self.digest_bridge.mix_into(channel);
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

/// Class-D blinded producer fraction. It mirrors the single gated
/// `add_to_relation` entry `crate::components::emit_blind` fires per row —
/// numerator `-(1 − is_dummy)·mult` — over the doubled (blinded) domain.
/// Returns one `Vec<Frac>` of length `mults.len() = 2^(L+1)`: on a real row
/// (`idx < real_len`) the numerator is `-mult`, identical to the unblinded emit;
/// on a dummy row (`idx ≥ real_len`, `is_dummy = 1`) the numerator is `0`, so
/// the fresh random blind multiplicity committed there never enters the LogUp
/// sum. It stays in the committed multiplicity column as the mask. The caller
/// pushes one fraction per producer. `build_interaction_columns` pairs two
/// producer fractions in one interaction column.
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

// ---------------------------------------------------------------------------
// Producer-side per-table interaction columns
// ---------------------------------------------------------------------------

/// Build the interaction trace for one `Range_k` producer.
fn range_k_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    kind: RangeKind,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let log_size = range_log_size(kind);
    let mults = range_k_multiplicities(witness, kind);
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
    let has_padding = n_blocks * crate::trace::ROWS_PER_BLOCK < n_rows;
    let last_block_idx = n_blocks.saturating_sub(1);

    // One fraction vector per lookup site (`lookup_idx`), each of length
    // `n_rows`, default-filled with the neutral `(0, 1)`; real rows
    // overwrite the sites that fire on them. See
    // [`SHA_LOOKUPS_PER_ROW_BASE`] for the per-row site breakdown.
    let lookups_per_row = sha_lookups_per_row(field_exposure);
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
                is_last_block,
                field_exposure,
                block_idx,
            );
            debug_assert_eq!(cursor, lookups_per_row, "row lookup miscount");
        }
    }

    build_interaction_columns(log_size, LOGUP_BATCH, all_lookups)
}

fn digest_bridge_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    expose_digest: bool,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1usize << DIGEST_BRIDGE_LOG_SIZE;
    let mut lookups: Vec<Vec<Frac>> = (0..digest_bridge_lookups(expose_digest))
        .map(|_| vec![(SecureField::zero(), SecureField::one()); n_rows])
        .collect();
    let block = witness
        .blocks
        .last()
        .expect("SHA witness has a final block");
    let bytes = h_out_digest_bytes(&block.h_out);
    let mut cursor = 0;
    for byte in bytes {
        lookups[cursor][0] = (
            SecureField::one(),
            combine_range(relations, RangeKind::Range8, byte),
        );
        cursor += 1;
    }

    let limbs: [BaseField; 2 * N_STATE_WORDS] = std::array::from_fn(|index| {
        let word = index / 2;
        BaseField::from(if index.is_multiple_of(2) {
            block.h_out[word].lo
        } else {
            block.h_out[word].hi
        })
    });
    lookups[cursor][0] = (SecureField::one(), relations.digest.limbs.combine(&limbs));
    cursor += 1;

    if expose_digest {
        let values: [BaseField; DIGEST_BYTES] =
            std::array::from_fn(|index| BaseField::from(bytes[index]));
        lookups[cursor][0] = (
            -SecureField::one(),
            relations.digest.digest.combine(&values),
        );
        cursor += 1;
    }
    debug_assert_eq!(cursor, digest_bridge_lookups(expose_digest));
    debug_assert_eq!(DIGEST_BRIDGE_LOOKUPS_BASE, DIGEST_BYTES + 1);
    build_interaction_columns(DIGEST_BRIDGE_LOG_SIZE, LOGUP_BATCH, lookups)
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

    // ---- 2. Round carry range-checks (8 sites; every round row) ----
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

    // ---- 3. Finalization carries (t = 63 rows) ----
    if t == crate::constants::N_ROUNDS - 1 {
        for c in &block.finalization_carries {
            write_carry_range_pair(all, cursor, slot, relations, RangeKind::Range2, *c);
        }
    } else {
        *cursor += 16;
    }

    // ---- 4. Final-state limb bridge ----
    if t == crate::constants::N_ROUNDS - 1 && is_last_block {
        let values: [BaseField; 2 * N_STATE_WORDS] = std::array::from_fn(|index| {
            let word = index / 2;
            if index.is_multiple_of(2) {
                BaseField::from(block.h_out[word].lo)
            } else {
                BaseField::from(block.h_out[word].hi)
            }
        });
        let denom = relations.digest.limbs.combine(&values);
        let num = -SecureField::from(BaseField::from(u32::from(is_last_block)));
        all[*cursor][slot] = (num, denom);
    }
    *cursor += 1;

    // ---- 5. Four padded-stream bytes on each input-word row ----
    if !field_exposure.is_empty() {
        if t < crate::trace::WORDS_PER_BLOCK {
            let (field_id, _) = field_exposure
                .full_padded_stream()
                .expect("field lookups require an active padded-stream provider");
            write_field_row_lookups(
                all,
                cursor,
                slot,
                block.schedule[t],
                block_idx * crate::constants::BLOCK_BYTES + t * crate::constants::WORD_BYTES,
                field_id,
                &relations.field.field,
            );
        } else {
            *cursor += field_exposure.n_yields();
        }
    }
}

/// Write one input word's four padded-stream field yields.
fn write_field_row_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    word: crate::types::WordLimbs,
    byte_start: usize,
    field_id: u32,
    field_rel: &crate::relations::Sha256Field,
) {
    for byte_in_word in 0..FULL_PADDED_STREAM_SITES_PER_ROW {
        let value = word_be_bytes(word.lo, word.hi)[byte_in_word];
        let byte_index = byte_start + byte_in_word;
        let tuple = [
            BaseField::from(field_id),
            BaseField::from(byte_index as u32),
            BaseField::from(value),
        ];
        all[*cursor][slot] = (-SecureField::one(), field_rel.combine(&tuple));
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
    )
}

fn generate_interaction_trace_inner(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    sha256_log_size: u32,
    expose_digest: bool,
    field_exposure: &FieldExposure,
    include_table_providers: bool,
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    let mut combined = Vec::new();

    // Sha256Eval consumer first — its slot in the proof's component list.
    // `field_exposure` adds one credential-field yield per exposed byte.
    let (sha_trace, sha_sum) =
        sha256_interaction(relations, witness, sha256_log_size, field_exposure);
    combined.extend(sha_trace);
    let sha256 = ComponentClaim {
        claimed_sum: sha_sum,
    };

    let (bridge_trace, bridge_sum) = digest_bridge_interaction(relations, witness, expose_digest);
    combined.extend(bridge_trace);
    let digest_bridge = ComponentClaim {
        claimed_sum: bridge_sum,
    };

    // Range producers in the canonical `RANGE_TABLES` order.
    let mut range = Vec::with_capacity(RANGE_TABLES.len());
    if include_table_providers {
        for &kind in RANGE_TABLES {
            let (t, s) = range_k_interaction(relations, witness, kind);
            combined.extend(t);
            range.push(ComponentClaim { claimed_sum: s });
        }
    }

    let claim = InteractionClaim {
        sha256,
        digest_bridge,
        range,
    };
    (combined, claim)
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let (_, producer_sum) = range_k_interaction(&relations, &witness, RangeKind::Range8);
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

    #[test]
    fn full_padded_stream_balances_exact_bytes_indices_and_block_totality() {
        const STREAM_FIELD_ID: u32 = 77;
        let message: Vec<u8> = (0..130).map(|i| ((i * 37 + 11) % 251) as u8).collect();
        let witness = compute_sha256_witness(&message);
        assert_eq!(
            witness.padding.padded.len(),
            3 * crate::constants::BLOCK_BYTES
        );
        let exposure =
            FieldExposure::from_full_padded_stream(STREAM_FIELD_ID, witness.padding.padded.len());
        assert_eq!(
            exposure.n_yields(),
            FULL_PADDED_STREAM_SITES_PER_ROW,
            "interaction width stays at four sites regardless of block count",
        );

        let log_size = min_log_size(witness.blocks.len());
        let relations = Sha256Relations::draw(&mut Blake2sChannel::default());
        let (_, claim) =
            generate_interaction_trace(&relations, &witness, log_size, false, &exposure);
        let tuples: Vec<(u32, u32, u32)> = witness
            .padding
            .padded
            .iter()
            .enumerate()
            .map(|(index, &byte)| (STREAM_FIELD_ID, index as u32, byte as u32))
            .collect();
        assert_eq!(
            claim.total() + synthetic_field_consumer(&relations, &tuples),
            SecureField::zero(),
            "all padded bytes in canonical block/byte order must balance",
        );

        let truncated = &tuples[..2 * crate::constants::BLOCK_BYTES];
        assert_ne!(
            claim.total() + synthetic_field_consumer(&relations, truncated),
            SecureField::zero(),
            "a consumer omitting the final block must not balance",
        );

        let mut wrong_order = tuples.clone();
        let left = crate::constants::BLOCK_BYTES - 1;
        let right = crate::constants::BLOCK_BYTES;
        let left_byte = wrong_order[left].2;
        assert_ne!(
            left_byte, wrong_order[right].2,
            "test boundary bytes differ"
        );
        wrong_order[left].2 = wrong_order[right].2;
        wrong_order[right].2 = left_byte;
        assert_ne!(
            claim.total() + synthetic_field_consumer(&relations, &wrong_order),
            SecureField::zero(),
            "swapping bytes across a block boundary must not balance",
        );

        let mut wrong_index = tuples.clone();
        wrong_index[crate::constants::BLOCK_BYTES].1 += 1;
        assert_ne!(
            claim.total() + synthetic_field_consumer(&relations, &wrong_index),
            SecureField::zero(),
            "changing an absolute stream index must not balance",
        );
    }
}
