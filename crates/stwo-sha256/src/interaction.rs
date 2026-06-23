//! LogUp interaction-trace generator for every SHA-256 component.
//!
//! The main `Sha256Eval` (consumer) and the 22 producer table components
//! (8 σ/Σ decode + 1 packed Maj/Ch + 1 `xor_8` + 8 split-and-pack + 4
//! `Range_k`) each emit their own interaction trace. When the digest provider
//! is exposed, `Sha256Eval` *also* yields the final-block digest on the
//! `Sha256Digest` channel — the one provider-side term it contributes — which
//! is why its claimed sum is non-zero on its own in that mode. Each is built by
//! walking that component's fractions row-by-row through
//! [`stwo_constraint_framework::LogupTraceGenerator`] — pairs of
//! consecutive fractions share an interaction column (matching
//! `eval.finalize_logup_in_pairs()`).
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

use crate::components::{
    range_log_size, RangeKind, DECODE_TABLES, RANGE_TABLES, ROUND_SPLIT_TABLES, SIGMA_SPLIT_TABLES,
};
use crate::constants::DIGEST_BYTES;
use crate::field_exposure::{word_be_bytes, FieldExposure, BYTE_RANGE_CHECK_OFFSET};
use crate::multiplicities::{
    decode_multiplicities, maj_ch_multiplicities, range_k_multiplicities,
    round_split_pack_multiplicities, sigma_split_pack_multiplicities, xor_8_multiplicities,
    MajChMultiplicities,
};
use crate::partitions::{
    pack_round_groups, round_groups_half_indices, GROUPS_PER_ROUND_PARTITION, SIGMA0_GROUPS,
    SIGMA1_GROUPS,
};
use crate::relations::Sha256Relations;
use crate::tables::{
    build_decode_table, build_maj_ch_table, build_round_split_pack_table,
    build_sigma_split_pack_table, build_xor_8_table, Half, Half16, LowerSigmaPartition,
    RoundPartition,
};
use crate::trace::{h_out_digest_bytes, Layout};
use crate::types::Sha256Witness;

/// Consumer-side lookups the main `Sha256Eval` fires per block, **excluding**
/// the optional digest yield. Breakdown (W=6), matching the firing order in
/// [`write_block_lookups`] and `crate::constraints::Sha256Eval::evaluate`:
///   8 (h_in aux split-pack) + 48·18 (schedule entries) + 64·44 (rounds)
///   + 16 (finalization carries) + 16 (terminal `Range_16`) = 3720.
pub const SHA_LOOKUPS_PER_BLOCK_BASE: usize = 3720;

/// Total consumer-side lookups `Sha256Eval` fires per block. The digest
/// provider adds exactly one width-32 yield when `expose_digest` is set;
/// the credential-field provider adds, per exposed byte column, two
/// `Range16` byte range-checks (the `[0, 256)` pin) plus one width-3 yield per
/// exposed window byte — i.e. `2·n_columns + n_yields`. All are zero for the
/// standalone AIR. Both the interaction generator here and `crate::air`'s
/// interaction-column sizing read this so the two never drift.
#[inline]
pub fn sha_lookups_per_block(expose_digest: bool, field_exposure: &FieldExposure) -> usize {
    SHA_LOOKUPS_PER_BLOCK_BASE
        + usize::from(expose_digest)
        + 2 * field_exposure.n_columns()
        + field_exposure.n_yields()
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
    pub decode: Vec<ComponentClaim>, // 8
    pub maj_ch: ComponentClaim,
    pub xor_8: ComponentClaim,
    pub round_split_pack: Vec<ComponentClaim>, // 4
    pub sigma_split_pack: Vec<ComponentClaim>, // 4
    pub range: Vec<ComponentClaim>,            // 4: Range_2, Range_4, Range_5, Range_16
}

impl InteractionClaim {
    /// Sum of every component's claimed sum. The verifier checks this is
    /// zero — modulo cross-component LogUp wiring outside this crate
    /// (currently none). Used as the soundness backbone.
    pub fn total(&self) -> SecureField {
        let mut s = self.sha256.claimed_sum;
        for c in &self.decode {
            s += c.claimed_sum;
        }
        s += self.maj_ch.claimed_sum;
        s += self.xor_8.claimed_sum;
        for c in &self.round_split_pack {
            s += c.claimed_sum;
        }
        for c in &self.sigma_split_pack {
            s += c.claimed_sum;
        }
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
        for c in &self.decode {
            c.mix_into(channel);
        }
        self.maj_ch.mix_into(channel);
        self.xor_8.mix_into(channel);
        for c in &self.round_split_pack {
            c.mix_into(channel);
        }
        for c in &self.sigma_split_pack {
            c.mix_into(channel);
        }
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
type Frac = (SecureField, SecureField);

/// Build one interaction trace for a component from its list of
/// row-iterators. `lookups[k]` is the k-th lookup the component fires —
/// a `Vec<Frac>` of length `2^log_size` giving the row-by-row fraction.
///
/// Pairs of consecutive lookups share one interaction column, matching
/// `finalize_logup_in_pairs`. Odd counts get a final single-lookup column.
fn build_interaction_columns(
    log_size: u32,
    lookups: Vec<Vec<Frac>>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    debug_assert!(log_size >= LOG_N_LANES, "log_size < LOG_N_LANES");
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

    // Walk lookups in chunks of 2 — each chunk shares one interaction
    // column. An odd remainder (last lookup) gets its own column.
    let mut i = 0;
    while i + 2 <= lookups.len() {
        let lo0 = &lookups[i];
        let lo1 = &lookups[i + 1];
        let mut col = gen.new_col();
        for vec_row in 0..(n_rows / N_LANES) {
            let mut num_arr = [SecureField::zero(); N_LANES];
            let mut den_arr = [SecureField::one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (n0, d0) = lo0[row];
                let (n1, d1) = lo1[row];
                // n0/d0 + n1/d1 = (n0·d1 + n1·d0) / (d0·d1)
                num_arr[lane] = n0 * d1 + n1 * d0;
                den_arr[lane] = d0 * d1;
            }
            col.write_frac(
                vec_row,
                PackedSecureField::from_array(num_arr),
                PackedSecureField::from_array(den_arr),
            );
        }
        col.finalize_col();
        i += 2;
    }
    if i < lookups.len() {
        let single = &lookups[i];
        let mut col = gen.new_col();
        for vec_row in 0..(n_rows / N_LANES) {
            let mut num_arr = [SecureField::zero(); N_LANES];
            let mut den_arr = [SecureField::one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (n, d) = single[row];
                num_arr[lane] = n;
                den_arr[lane] = d;
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
fn producer_frac_column<R, const N: usize>(
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

// (Padding helper removed — every per-table producer column is sized
// exactly to its `log_size` by construction, and the consumer-side
// builder pre-allocates `n_rows` per lookup with the zero-fraction
// default.)

// ---------------------------------------------------------------------------
// Producer-side per-table interaction columns
// ---------------------------------------------------------------------------

/// Build the interaction trace for one decode table.
fn decode_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    f: crate::partitions::SigmaFn,
    half: Half,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mults = decode_multiplicities(witness, f, half);
    let rows = build_decode_table(f, half);
    let log_size = crate::preprocessed::LOG_SIZE_16;
    let frac_col: Vec<Frac> = match (f, half) {
        (crate::partitions::SigmaFn::Sigma0, Half::S) => producer_frac_column(
            &relations.sigma_decode.sigma0_s,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::Sigma0, Half::SComplement) => producer_frac_column(
            &relations.sigma_decode.sigma0_s_complement,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::Sigma1, Half::S) => producer_frac_column(
            &relations.sigma_decode.sigma1_s,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::Sigma1, Half::SComplement) => producer_frac_column(
            &relations.sigma_decode.sigma1_s_complement,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::LowerSigma0, Half::S) => producer_frac_column(
            &relations.sigma_decode.lower_sigma0_s,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::LowerSigma0, Half::SComplement) => producer_frac_column(
            &relations.sigma_decode.lower_sigma0_s_complement,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::LowerSigma1, Half::S) => producer_frac_column(
            &relations.sigma_decode.lower_sigma1_s,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
        (crate::partitions::SigmaFn::LowerSigma1, Half::SComplement) => producer_frac_column(
            &relations.sigma_decode.lower_sigma1_s_complement,
            &mults,
            rows.into_iter().map(decode_row_to_felts),
        ),
    };

    build_interaction_columns(log_size, vec![frac_col])
}

fn decode_row_to_felts(r: crate::tables::DecodeRow) -> [BaseField; 5] {
    [
        BaseField::from(r.key),
        BaseField::from(r.o_main_lo),
        BaseField::from(r.o_main_hi),
        BaseField::from(r.o2_partial_lo),
        BaseField::from(r.o2_partial_hi),
    ]
}

/// Build the interaction trace for the packed Maj/Ch table — 2 lookups
/// (Maj, Ch) batch into one interaction column.
fn maj_ch_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    group_width: u32,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let MajChMultiplicities { maj, ch } = maj_ch_multiplicities(witness, group_width);
    let rows = build_maj_ch_table(group_width);
    let log_size = crate::preprocessed::maj_ch_log_size(group_width);

    let maj_frac = producer_frac_column(
        &relations.maj,
        &maj,
        rows.iter().map(|r| {
            [
                BaseField::from(r.a),
                BaseField::from(r.b),
                BaseField::from(r.c),
                BaseField::from(r.maj_val),
            ]
        }),
    );
    let ch_frac = producer_frac_column(
        &relations.ch,
        &ch,
        rows.iter().map(|r| {
            [
                BaseField::from(r.a),
                BaseField::from(r.b),
                BaseField::from(r.c),
                BaseField::from(r.ch_val),
            ]
        }),
    );

    build_interaction_columns(log_size, vec![maj_frac, ch_frac])
}

fn xor_8_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mults = xor_8_multiplicities(witness);
    let rows = build_xor_8_table();
    let log_size = crate::preprocessed::LOG_SIZE_16;
    let frac = producer_frac_column(
        &relations.xor_8,
        &mults,
        rows.iter().map(|r| {
            [
                BaseField::from(r.x),
                BaseField::from(r.y),
                BaseField::from(r.z),
            ]
        }),
    );
    build_interaction_columns(log_size, vec![frac])
}

fn round_split_pack_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    p: RoundPartition,
    h: Half16,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mults = round_split_pack_multiplicities(witness, p, h);
    let groups = match p {
        RoundPartition::Sigma0AndMaj => SIGMA0_GROUPS,
        RoundPartition::Sigma1AndCh => SIGMA1_GROUPS,
    };
    let s_mask = p.s_mask();
    let rows = build_round_split_pack_table(&groups, s_mask, h);
    let log_size = crate::preprocessed::LOG_SIZE_16;
    // 5-cell row: (key, g0, g1, g2, g3) — the four W=6 sub-groups in this half.
    let row_iter = rows.iter().map(|r| {
        [
            BaseField::from(r.key),
            BaseField::from(r.groups[0]),
            BaseField::from(r.groups[1]),
            BaseField::from(r.groups[2]),
            BaseField::from(r.groups[3]),
        ]
    });
    let frac = match (p, h) {
        (RoundPartition::Sigma0AndMaj, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.sigma0_lo, &mults, row_iter)
        }
        (RoundPartition::Sigma0AndMaj, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.sigma0_hi, &mults, row_iter)
        }
        (RoundPartition::Sigma1AndCh, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.sigma1_lo, &mults, row_iter)
        }
        (RoundPartition::Sigma1AndCh, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.sigma1_hi, &mults, row_iter)
        }
    };
    build_interaction_columns(log_size, vec![frac])
}

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
        RangeKind::Range16 => producer_frac_column(&relations.range.range_16, &mults, row_iter),
    };
    build_interaction_columns(log_size, vec![frac])
}

fn sigma_split_pack_interaction(
    relations: &Sha256Relations,
    witness: &Sha256Witness,
    p: LowerSigmaPartition,
    h: Half16,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let mults = sigma_split_pack_multiplicities(witness, p, h);
    let rows = build_sigma_split_pack_table(p.parts(), h);
    let log_size = crate::preprocessed::LOG_SIZE_16;
    let row_iter = rows.iter().map(|r| {
        [
            BaseField::from(r.key),
            BaseField::from(r.groups[0]),
            BaseField::from(r.groups[1]),
        ]
    });
    let frac = match (p, h) {
        (LowerSigmaPartition::LowerSigma0, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.lower_sigma0_lo, &mults, row_iter)
        }
        (LowerSigmaPartition::LowerSigma0, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.lower_sigma0_hi, &mults, row_iter)
        }
        (LowerSigmaPartition::LowerSigma1, Half16::Lo) => {
            producer_frac_column(&relations.split_pack.lower_sigma1_lo, &mults, row_iter)
        }
        (LowerSigmaPartition::LowerSigma1, Half16::Hi) => {
            producer_frac_column(&relations.split_pack.lower_sigma1_hi, &mults, row_iter)
        }
    };
    build_interaction_columns(log_size, vec![frac])
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
    // `is_last_block` matches the AIR gate `enabler · (1 − enabler_next)`:
    // set on the final block only when a padding successor exists. See
    // `crate::trace::generate_trace`. The field provider gates on the symmetric
    // `is_first_block` (block 0), which needs no padding successor.
    let has_padding = n_blocks < n_rows;
    let last_block_idx = n_blocks.saturating_sub(1);

    // Pre-allocate per-lookup fraction vectors. Each filled with `(0, 1)`
    // for padding rows up front; real-block rows overwrite below.
    //
    // Count of lookups per block (matches `Sha256Eval::evaluate` exactly):
    //   - 4 round-side split-pack on h_in aux (1 per b_init/c_init/f_init/g_init, lo+hi each = 8 lookups)
    //   - per schedule entry (48):
    //       2 σ-decode (each = 2 decode lookups + 4 xor_8 lookups = 6 lookups per σ) ⇒ 12
    //       2 σ-input split-pack (lo+hi each = 4 lookups) ⇒ 4
    //       2 carry-range lookups on `(carry_lo, carry_hi)` against `Range_4` ⇒ 2
    //     ⇒ 18 per entry
    //   - per round (64):
    //       2 Σ-decode ⇒ 12
    //       8 Maj + 8 Ch ⇒ 16   (W=6: one lookup per group position, 8 groups)
    //       4 round-side split-pack (a, maj_out, e, ch_out — lo+hi each = 8) ⇒ 8
    //       4 carry-range lookups (2 × `Range_5` for T1; 2 × `Range_2` × 3 families) ⇒ 8
    //     ⇒ 44 per round
    //   - finalization: 8 mod-2³² adds × 2 carries × 1 `Range_2` lookup each ⇒ 16
    //   - terminal `Range_16` on `h_out`: 8 words × 2 limbs ⇒ 16
    //
    // Total per block = 8 + 48·18 + 64·44 + 16 + 16
    //                 = 8 + 864 + 2816 + 16 + 16 = 3720 (= SHA_LOOKUPS_PER_BLOCK_BASE).
    //
    // When `expose_digest` is set the digest provider appends exactly
    // one width-32 yield after the terminal `Range_16` block — the only
    // provider-side (negative-multiplicity) term the SHA module emits — so the
    // count becomes `sha_lookups_per_block(true) = 3721`. The yield's
    // numerator is `−is_last_block`, zero on every block but the final one, so
    // intermediate/padding blocks contribute `(0, denom)` and do not perturb
    // the sum; only the final block's `−1/combine(digest)` survives, leaving
    // the module's claimed sum non-zero until a consumer requires it.
    //
    // Note the split-pack *lookup count* is unchanged from W=7 (still one
    // lo+hi pair per operand); only each split-pack row's *width* grew
    // (4 → 5 cells). The +256 over the old 3464 is purely the 4 extra
    // Maj + 4 extra Ch lookups per round × 64 rounds.
    //
    // We allocate one Vec<Frac> per lookup index (`lookup_idx`) of length
    // `n_rows`, default-filled, then fill real-block rows below.
    let lookups_per_block = sha_lookups_per_block(expose_digest, field_exposure);
    let mut all_lookups: Vec<Vec<Frac>> = (0..lookups_per_block)
        .map(|_| vec![(SecureField::zero(), SecureField::one()); n_rows])
        .collect();

    for (block_idx, block) in witness.blocks.iter().enumerate() {
        let slot = Layout::block_slot(block_idx, log_size);
        let is_last_block = block_idx == last_block_idx && has_padding;
        let is_first_block = block_idx == 0;
        let mut cursor = 0usize;
        write_block_lookups(
            &mut all_lookups,
            &mut cursor,
            slot,
            block,
            relations,
            expose_digest,
            is_last_block,
            field_exposure,
            is_first_block,
        );
        debug_assert_eq!(cursor, lookups_per_block, "block lookup miscount");
    }

    build_interaction_columns(log_size, all_lookups)
}

/// Write every lookup for one block at its trace slot, in **exactly** the
/// `Sha256Eval::evaluate` firing order. Bumps `cursor` past each lookup
/// so the same lookup index always lands at the same column across
/// blocks.
#[allow(clippy::too_many_arguments)]
fn write_block_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    block: &crate::types::BlockWitness,
    relations: &Sha256Relations,
    expose_digest: bool,
    is_last_block: bool,
    field_exposure: &FieldExposure,
    is_first_block: bool,
) {
    // Per-partition lo/hi half projections (length 4 each, W=6) — the same
    // `round_groups_half_indices` projection the constraint side keys on.
    let (sigma0_lo_idx, sigma0_hi_idx) = round_groups_half_indices(&SIGMA0_GROUPS);
    let (sigma1_lo_idx, sigma1_hi_idx) = round_groups_half_indices(&SIGMA1_GROUPS);

    // ---- 1. h_in aux split-pack lookups (4 operands × 2 halves = 8) ----
    //
    // Order in Sha256Eval::evaluate: b_init, c_init, f_init, g_init —
    // each fires wire_round_split_pack(word, grp, rel_lo, rel_hi).
    // Each wire_round_split_pack emits 2 lookups (lo then hi).
    for op_idx in 0..4 {
        let (word, lo_rel_tag, hi_rel_tag) = match op_idx {
            0 => (block.h_in[1].to_u32(), RelTag::Sigma0Lo, RelTag::Sigma0Hi),
            1 => (block.h_in[2].to_u32(), RelTag::Sigma0Lo, RelTag::Sigma0Hi),
            2 => (block.h_in[5].to_u32(), RelTag::Sigma1Lo, RelTag::Sigma1Hi),
            3 => (block.h_in[6].to_u32(), RelTag::Sigma1Lo, RelTag::Sigma1Hi),
            _ => unreachable!(),
        };
        // op_idx 0,1 are the Σ0 partition; 2,3 the Σ1 partition.
        let (lo_idx, hi_idx): (&[usize], &[usize]) = if op_idx < 2 {
            (&sigma0_lo_idx, &sigma0_hi_idx)
        } else {
            (&sigma1_lo_idx, &sigma1_hi_idx)
        };
        write_round_split_pack_pair(
            all,
            cursor,
            slot,
            word,
            relations,
            lo_rel_tag,
            hi_rel_tag,
            // 8-element packed-group values come from the aux witness.
            match op_idx {
                0 => block.aux_split_pack.b_init.vals,
                1 => block.aux_split_pack.c_init.vals,
                2 => block.aux_split_pack.f_init.vals,
                3 => block.aux_split_pack.g_init.vals,
                _ => unreachable!(),
            },
            lo_idx,
            hi_idx,
        );
    }

    // ---- 2. Schedule entries (48 × 16 lookups) ----
    for entry in &block.schedule_entries {
        // σ0(W[t-15]) decode wiring fires:
        //   - S-side lookup (5 cells)
        //   - S′-side lookup (5 cells)
        //   - 4 chunk-wise xor_8 lookups
        // = 6 lookups
        let dec_sigma0 = &entry.lower_sigma0_decode;
        write_sigma_decode_lookups(
            all,
            cursor,
            slot,
            dec_sigma0,
            RelTag::LowerSigma0DecodeS,
            RelTag::LowerSigma0DecodeSPrime,
            relations,
        );
        let dec_sigma1 = &entry.lower_sigma1_decode;
        write_sigma_decode_lookups(
            all,
            cursor,
            slot,
            dec_sigma1,
            RelTag::LowerSigma1DecodeS,
            RelTag::LowerSigma1DecodeSPrime,
            relations,
        );

        // σ-input split-and-pack: 4 lookups (lo+hi for σ0, lo+hi for σ1).
        write_sigma_input_split_lookups(
            all,
            cursor,
            slot,
            entry.w_t_minus_15.to_u32(),
            &entry.lower_sigma0_input_split,
            relations,
            RelTag::LowerSigma0SplitLo,
            RelTag::LowerSigma0SplitHi,
        );
        write_sigma_input_split_lookups(
            all,
            cursor,
            slot,
            entry.w_t_minus_2.to_u32(),
            &entry.lower_sigma1_input_split,
            relations,
            RelTag::LowerSigma1SplitLo,
            RelTag::LowerSigma1SplitHi,
        );

        // Schedule-recurrence carry range-check (4-addend add → `Range_4`).
        // Matches `emit_mod_2_32_add_linear` in `Sha256Eval` for the
        // `W[t] = σ1 + W[t-7] + σ0 + W[t-16]` recurrence.
        write_carry_range_pair(
            all,
            cursor,
            slot,
            relations,
            RangeKind::Range4,
            entry.carries,
        );
    }

    // ---- 3. Rounds (64 × 32 lookups) ----
    //
    // Mirror Sha256Eval::evaluate: §8.1 reuse-chain across rounds.
    let mut b_grp = block.aux_split_pack.b_init.vals;
    let mut c_grp = block.aux_split_pack.c_init.vals;
    let mut f_grp = block.aux_split_pack.f_init.vals;
    let mut g_grp = block.aux_split_pack.g_init.vals;

    for round in &block.rounds {
        // 2 Σ-decode wirings (Σ0(a) and Σ1(e)) — 6 lookups each ⇒ 12.
        write_sigma_decode_lookups(
            all,
            cursor,
            slot,
            &round.sigma0_decode,
            RelTag::Sigma0DecodeS,
            RelTag::Sigma0DecodeSPrime,
            relations,
        );
        write_sigma_decode_lookups(
            all,
            cursor,
            slot,
            &round.sigma1_decode,
            RelTag::Sigma1DecodeS,
            RelTag::Sigma1DecodeSPrime,
            relations,
        );

        // 8 Maj + 8 Ch.
        let a_grp = round.maj_ch.a_grp.vals;
        let maj_grp = round.maj_ch.maj_grp.vals;
        let e_grp = round.maj_ch.e_grp.vals;
        let ch_grp = round.maj_ch.ch_grp.vals;
        for i in 0..GROUPS_PER_ROUND_PARTITION {
            let denom = relations.maj.combine(&[
                BaseField::from(a_grp[i]),
                BaseField::from(b_grp[i]),
                BaseField::from(c_grp[i]),
                BaseField::from(maj_grp[i]),
            ]);
            all[*cursor][slot] = (SecureField::one(), denom);
            *cursor += 1;
        }
        for i in 0..GROUPS_PER_ROUND_PARTITION {
            let denom = relations.ch.combine(&[
                BaseField::from(e_grp[i]),
                BaseField::from(f_grp[i]),
                BaseField::from(g_grp[i]),
                BaseField::from(ch_grp[i]),
            ]);
            all[*cursor][slot] = (SecureField::one(), denom);
            *cursor += 1;
        }

        // 4 round-side split-pack: a, maj_out (Σ0 partition), e, ch_out (Σ1 partition).
        // Each emits 2 lookups (lo + hi).
        let a_word = round.state_in[0].to_u32(); // a
        write_round_split_pack_pair(
            all,
            cursor,
            slot,
            a_word,
            relations,
            RelTag::Sigma0Lo,
            RelTag::Sigma0Hi,
            a_grp,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
        );
        let maj_word = round.maj.to_u32();
        let maj_packed = pack_round_groups(maj_word, &SIGMA0_GROUPS);
        write_round_split_pack_pair(
            all,
            cursor,
            slot,
            maj_word,
            relations,
            RelTag::Sigma0Lo,
            RelTag::Sigma0Hi,
            maj_packed,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
        );
        let e_word = round.state_in[4].to_u32(); // e
        write_round_split_pack_pair(
            all,
            cursor,
            slot,
            e_word,
            relations,
            RelTag::Sigma1Lo,
            RelTag::Sigma1Hi,
            e_grp,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
        );
        let ch_word = round.ch.to_u32();
        let ch_packed = pack_round_groups(ch_word, &SIGMA1_GROUPS);
        write_round_split_pack_pair(
            all,
            cursor,
            slot,
            ch_word,
            relations,
            RelTag::Sigma1Lo,
            RelTag::Sigma1Hi,
            ch_packed,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
        );

        // Carry range-checks for the four mod-2³² adds of this round.
        // Order matches `Sha256Eval::evaluate`'s `emit_mod_2_32_add_linear`
        // sequence: T1 (5-addend, `Range_5`), T2/e_new/a_new (2-addend each,
        // `Range_2`).
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

        // §8.1 chain advance: b ← a, c ← b, f ← e, g ← f.
        let prev_b = b_grp;
        b_grp = a_grp;
        c_grp = prev_b;
        let prev_f = f_grp;
        f_grp = e_grp;
        g_grp = prev_f;
    }

    // ---- 4. Finalization carry range-checks (8 × Range_2 pairs) ----
    for c in &block.finalization_carries {
        write_carry_range_pair(all, cursor, slot, relations, RangeKind::Range2, *c);
    }

    // ---- 5. Terminal `Range_16` on every `h_out` limb (8 × 2) ----
    for h in &block.h_out {
        write_range_check(all, cursor, slot, relations, RangeKind::Range16, h.lo);
        write_range_check(all, cursor, slot, relations, RangeKind::Range16, h.hi);
    }

    // ---- 6. Digest yield (provider side, final block only) ----
    //
    // Mirrors the `if self.expose_digest { add_to_relation(...) }` tail of
    // `Sha256Eval::evaluate`: a single width-32 yield on the `Sha256Digest`
    // channel with multiplicity `−is_last_block`. The 32 cells are this
    // block's `h_out` bytes in `h_out_digest_bytes` order — identical to the
    // byte columns the constraint reads — so producer and consumer combine the
    // same tuple. On non-final blocks the numerator is `0` (the frac is
    // `(0, denom)`), so only the final block contributes `−1/combine(digest)`.
    if expose_digest {
        let bytes = h_out_digest_bytes(&block.h_out);
        let values: [BaseField; DIGEST_BYTES] = std::array::from_fn(|i| BaseField::from(bytes[i]));
        let denom = relations.digest.digest.combine(&values);
        let num = -SecureField::from(BaseField::from(u32::from(is_last_block)));
        all[*cursor][slot] = (num, denom);
        *cursor += 1;
    }

    // ---- 7. Credential-field range-checks + yields (provider side, first block) ----
    //
    // Mirrors the field tail of `Sha256Eval::evaluate`, in the same order:
    //   7a. two `Range16` byte range-checks per exposed byte column (the
    //       `[0, 256)` pin, multiplicity `is_first_block`), then
    //   7b. one width-3 `(field_id, byte_index, value)` yield per exposed window
    //       byte on the `Sha256Field` channel (multiplicity `−is_first_block`).
    // Every byte value is read from this block's covered message word in
    // `word_be_bytes` order — identical to the columns the constraint reads — so
    // producer and consumer combine the same tuple. On non-first blocks the
    // numerator is `0`, so only block 0 contributes; the matching `Range16`
    // producer increments are in `range_k_multiplicities`.
    if !field_exposure.is_empty() {
        // Cache each covered word's big-endian bytes once, keyed by decomposed
        // word slot (same order the constraint/trace use).
        let word_bytes: Vec<[u32; crate::constants::WORD_BYTES]> = field_exposure
            .decomposed_words()
            .iter()
            .map(|&w| {
                let limb = block.schedule[w];
                word_be_bytes(limb.lo, limb.hi)
            })
            .collect();
        let is_first_sf = SecureField::from(BaseField::from(u32::from(is_first_block)));

        // 7a. Range-check every exposed byte to `[0, 256)` — word-slot major,
        // byte minor (the `field_bytes` order on the constraint side).
        for bytes in &word_bytes {
            for &b in bytes {
                all[*cursor][slot] = (is_first_sf, combine_range(relations, RangeKind::Range16, b));
                *cursor += 1;
                all[*cursor][slot] = (
                    is_first_sf,
                    combine_range(relations, RangeKind::Range16, b + BYTE_RANGE_CHECK_OFFSET),
                );
                *cursor += 1;
            }
        }

        // 7b. Yield each window byte (`−is_first_block`).
        for y in field_exposure.yields() {
            let slot_idx = field_exposure.yield_column_slot(y);
            let word_slot = slot_idx / crate::constants::WORD_BYTES;
            let byte_in_word = slot_idx % crate::constants::WORD_BYTES;
            let value = word_bytes[word_slot][byte_in_word];
            let tuple = [
                BaseField::from(y.field_id),
                BaseField::from(y.byte_index),
                BaseField::from(value),
            ];
            let denom = relations.field.field.combine(&tuple);
            all[*cursor][slot] = (-is_first_sf, denom);
            *cursor += 1;
        }
    }
}

/// Internal tag for which split-pack relation a write targets.
#[derive(Copy, Clone)]
enum RelTag {
    Sigma0DecodeS,
    Sigma0DecodeSPrime,
    Sigma1DecodeS,
    Sigma1DecodeSPrime,
    LowerSigma0DecodeS,
    LowerSigma0DecodeSPrime,
    LowerSigma1DecodeS,
    LowerSigma1DecodeSPrime,
    Sigma0Lo,
    Sigma0Hi,
    Sigma1Lo,
    Sigma1Hi,
    LowerSigma0SplitLo,
    LowerSigma0SplitHi,
    LowerSigma1SplitLo,
    LowerSigma1SplitHi,
}

fn combine_with_tag(relations: &Sha256Relations, tag: RelTag, values: &[BaseField]) -> SecureField {
    match tag {
        RelTag::Sigma0DecodeS => relations.sigma_decode.sigma0_s.combine(values),
        RelTag::Sigma0DecodeSPrime => relations.sigma_decode.sigma0_s_complement.combine(values),
        RelTag::Sigma1DecodeS => relations.sigma_decode.sigma1_s.combine(values),
        RelTag::Sigma1DecodeSPrime => relations.sigma_decode.sigma1_s_complement.combine(values),
        RelTag::LowerSigma0DecodeS => relations.sigma_decode.lower_sigma0_s.combine(values),
        RelTag::LowerSigma0DecodeSPrime => relations
            .sigma_decode
            .lower_sigma0_s_complement
            .combine(values),
        RelTag::LowerSigma1DecodeS => relations.sigma_decode.lower_sigma1_s.combine(values),
        RelTag::LowerSigma1DecodeSPrime => relations
            .sigma_decode
            .lower_sigma1_s_complement
            .combine(values),
        RelTag::Sigma0Lo => relations.split_pack.sigma0_lo.combine(values),
        RelTag::Sigma0Hi => relations.split_pack.sigma0_hi.combine(values),
        RelTag::Sigma1Lo => relations.split_pack.sigma1_lo.combine(values),
        RelTag::Sigma1Hi => relations.split_pack.sigma1_hi.combine(values),
        RelTag::LowerSigma0SplitLo => relations.split_pack.lower_sigma0_lo.combine(values),
        RelTag::LowerSigma0SplitHi => relations.split_pack.lower_sigma0_hi.combine(values),
        RelTag::LowerSigma1SplitLo => relations.split_pack.lower_sigma1_lo.combine(values),
        RelTag::LowerSigma1SplitHi => relations.split_pack.lower_sigma1_hi.combine(values),
    }
}

/// Combine a single-value lookup against the `Range_k` channel for `kind`.
fn combine_range(relations: &Sha256Relations, kind: RangeKind, value: u32) -> SecureField {
    let v = [BaseField::from(value)];
    match kind {
        RangeKind::Range2 => relations.range.range_2.combine(&v),
        RangeKind::Range4 => relations.range.range_4.combine(&v),
        RangeKind::Range5 => relations.range.range_5.combine(&v),
        RangeKind::Range16 => relations.range.range_16.combine(&v),
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

fn write_sigma_decode_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    dec: &crate::types::SigmaDecodeWitness,
    s_tag: RelTag,
    sp_tag: RelTag,
    relations: &Sha256Relations,
) {
    // (1) S-side decode lookup (5 cells).
    let s_vals = [
        BaseField::from(dec.key_s),
        BaseField::from(dec.o_main_s.lo),
        BaseField::from(dec.o_main_s.hi),
        BaseField::from(dec.o2_partial_s.lo),
        BaseField::from(dec.o2_partial_s.hi),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, s_tag, &s_vals),
    );
    *cursor += 1;

    // (2) S′-side decode lookup.
    let sp_vals = [
        BaseField::from(dec.key_s_complement),
        BaseField::from(dec.o_main_s_complement.lo),
        BaseField::from(dec.o_main_s_complement.hi),
        BaseField::from(dec.o2_partial_s_complement.lo),
        BaseField::from(dec.o2_partial_s_complement.hi),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, sp_tag, &sp_vals),
    );
    *cursor += 1;

    // (3) 4 chunk-wise xor_8 lookups: (chunks_s[i], chunks_s'[i], chunks_combined[i])
    // for i in (lo.b0, lo.b1, hi.b0, hi.b1).
    let chunks_s = [
        dec.o2_chunks_s.lo.b0,
        dec.o2_chunks_s.lo.b1,
        dec.o2_chunks_s.hi.b0,
        dec.o2_chunks_s.hi.b1,
    ];
    let chunks_sp = [
        dec.o2_chunks_s_complement.lo.b0,
        dec.o2_chunks_s_complement.lo.b1,
        dec.o2_chunks_s_complement.hi.b0,
        dec.o2_chunks_s_complement.hi.b1,
    ];
    let chunks_combined = [
        dec.o2_chunks_combined.lo.b0,
        dec.o2_chunks_combined.lo.b1,
        dec.o2_chunks_combined.hi.b0,
        dec.o2_chunks_combined.hi.b1,
    ];
    for i in 0..4 {
        let denom = relations.xor_8.combine(&[
            BaseField::from(chunks_s[i]),
            BaseField::from(chunks_sp[i]),
            BaseField::from(chunks_combined[i]),
        ]);
        all[*cursor][slot] = (SecureField::one(), denom);
        *cursor += 1;
    }
}

#[allow(clippy::too_many_arguments)]
fn write_sigma_input_split_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    word: u32,
    split: &crate::types::SigmaInputSplitPackWitness,
    relations: &Sha256Relations,
    lo_tag: RelTag,
    hi_tag: RelTag,
) {
    let word_lo = word & 0xFFFF;
    let word_hi = (word >> 16) & 0xFFFF;
    let lo_vals = [
        BaseField::from(word_lo),
        BaseField::from(split.packed_s_lo),
        BaseField::from(split.packed_s_complement_lo),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, lo_tag, &lo_vals),
    );
    *cursor += 1;
    let hi_vals = [
        BaseField::from(word_hi),
        BaseField::from(split.packed_s_hi),
        BaseField::from(split.packed_s_complement_hi),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, hi_tag, &hi_vals),
    );
    *cursor += 1;
}

#[allow(clippy::too_many_arguments)]
fn write_round_split_pack_pair(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    word: u32,
    relations: &Sha256Relations,
    lo_tag: RelTag,
    hi_tag: RelTag,
    grp: [u32; GROUPS_PER_ROUND_PARTITION],
    lo_idx: &[usize],
    hi_idx: &[usize],
) {
    // Mirror `constraints::wire_round_split_pack` exactly: the lo-half tuple
    // is `(word.lo, grp[lo_idx[0..4]])`, the hi-half `(word.hi,
    // grp[hi_idx[0..4]])`. Any divergence here breaks the LogUp balance.
    debug_assert_eq!(lo_idx.len(), 4);
    debug_assert_eq!(hi_idx.len(), 4);
    let word_lo = word & 0xFFFF;
    let word_hi = (word >> 16) & 0xFFFF;
    let lo_vals = [
        BaseField::from(word_lo),
        BaseField::from(grp[lo_idx[0]]),
        BaseField::from(grp[lo_idx[1]]),
        BaseField::from(grp[lo_idx[2]]),
        BaseField::from(grp[lo_idx[3]]),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, lo_tag, &lo_vals),
    );
    *cursor += 1;
    let hi_vals = [
        BaseField::from(word_hi),
        BaseField::from(grp[hi_idx[0]]),
        BaseField::from(grp[hi_idx[1]]),
        BaseField::from(grp[hi_idx[2]]),
        BaseField::from(grp[hi_idx[3]]),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, hi_tag, &hi_vals),
    );
    *cursor += 1;
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

    // 8 decode producers.
    let mut decode = Vec::with_capacity(8);
    for &(f, h) in DECODE_TABLES {
        let (t, s) = decode_interaction(relations, witness, f, h);
        combined.extend(t);
        decode.push(ComponentClaim { claimed_sum: s });
    }
    // 1 Maj/Ch.
    let (mc_trace, mc_sum) = maj_ch_interaction(relations, witness, group_width);
    combined.extend(mc_trace);
    let maj_ch = ComponentClaim {
        claimed_sum: mc_sum,
    };
    // 1 xor_8.
    let (xor_trace, xor_sum) = xor_8_interaction(relations, witness);
    combined.extend(xor_trace);
    let xor_8 = ComponentClaim {
        claimed_sum: xor_sum,
    };
    // 4 round-side split-pack.
    let mut round_split_pack = Vec::with_capacity(4);
    for &(p, h) in ROUND_SPLIT_TABLES {
        let (t, s) = round_split_pack_interaction(relations, witness, p, h);
        combined.extend(t);
        round_split_pack.push(ComponentClaim { claimed_sum: s });
    }
    // 4 σ-side split-pack.
    let mut sigma_split_pack = Vec::with_capacity(4);
    for &(p, h) in SIGMA_SPLIT_TABLES {
        let (t, s) = sigma_split_pack_interaction(relations, witness, p, h);
        combined.extend(t);
        sigma_split_pack.push(ComponentClaim { claimed_sum: s });
    }
    // 4 range producers (Range_2, Range_4, Range_5, Range_16).
    let mut range = Vec::with_capacity(4);
    for &kind in RANGE_TABLES {
        let (t, s) = range_k_interaction(relations, witness, kind, field_exposure);
        combined.extend(t);
        range.push(ComponentClaim { claimed_sum: s });
    }

    let claim = InteractionClaim {
        sha256,
        decode,
        maj_ch,
        xor_8,
        round_split_pack,
        sigma_split_pack,
        range,
    };
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
