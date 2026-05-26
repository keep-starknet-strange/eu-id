//! LogUp interaction-trace generator for every SHA-256 component.
//!
//! The main `Sha256Eval` (consumer) and the 22 producer table components
//! (8 σ/Σ decode + 1 packed Maj/Ch + 1 `xor_8` + 8 split-and-pack + 4
//! `Range_k`) each emit their own interaction trace. Each is built by
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
use crate::multiplicities::{
    decode_multiplicities, maj_ch_multiplicities, range_k_multiplicities,
    round_split_pack_multiplicities, sigma_split_pack_multiplicities, xor_8_multiplicities,
    MajChMultiplicities,
};
use crate::partitions::{
    pack_round_groups, GROUPS_PER_ROUND_PARTITION, SIGMA0_GROUPS, SIGMA1_GROUPS,
};
use crate::relations::Sha256Relations;
use crate::tables::{
    build_decode_table, build_maj_ch_table, build_round_split_pack_table,
    build_sigma_split_pack_table, build_xor_8_table, Half, Half16, LowerSigmaPartition,
    RoundPartition,
};
use crate::trace::Layout;
use crate::types::Sha256Witness;

// ---------------------------------------------------------------------------
// Per-component claim
// ---------------------------------------------------------------------------

/// One component's slot in the aggregate interaction claim. `claimed_sum`
/// is what the verifier checks each component's interaction column
/// cumulatively reaches; the total over every component must be zero.
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
    // 4-cell row: (key, g0, g1, g2).
    let row_iter = rows.iter().map(|r| {
        [
            BaseField::from(r.key),
            BaseField::from(r.groups[0]),
            BaseField::from(r.groups[1]),
            BaseField::from(r.groups[2]),
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
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let n_rows = 1usize << log_size;

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
    //       6 Maj + 6 Ch ⇒ 12
    //       4 round-side split-pack (a, maj_out, e, ch_out — lo+hi each = 8) ⇒ 8
    //       4 carry-range lookups (2 × `Range_5` for T1; 2 × `Range_2` × 3 families) ⇒ 8
    //     ⇒ 40 per round
    //   - finalization: 8 mod-2³² adds × 2 carries × 1 `Range_2` lookup each ⇒ 16
    //   - terminal `Range_16` on `h_out`: 8 words × 2 limbs ⇒ 16
    //
    // Total per block = 8 + 48·18 + 64·40 + 16 + 16
    //                 = 8 + 864 + 2560 + 16 + 16 = 3464.
    //
    // We allocate one Vec<Frac> per lookup index (`lookup_idx`) of length
    // `n_rows`, default-filled, then fill real-block rows below.
    let lookups_per_block = 3464usize;
    let mut all_lookups: Vec<Vec<Frac>> = (0..lookups_per_block)
        .map(|_| vec![(SecureField::zero(), SecureField::one()); n_rows])
        .collect();

    for (block_idx, block) in witness.blocks.iter().enumerate() {
        let slot = Layout::block_slot(block_idx, log_size);
        let mut cursor = 0usize;
        write_block_lookups(&mut all_lookups, &mut cursor, slot, block, relations);
        debug_assert_eq!(cursor, lookups_per_block, "block lookup miscount");
    }

    build_interaction_columns(log_size, all_lookups)
}

/// Write every lookup for one block at its trace slot, in **exactly** the
/// `Sha256Eval::evaluate` firing order. Bumps `cursor` past each lookup
/// so the same lookup index always lands at the same column across
/// blocks.
fn write_block_lookups(
    all: &mut [Vec<Frac>],
    cursor: &mut usize,
    slot: usize,
    block: &crate::types::BlockWitness,
    relations: &Sha256Relations,
) {
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
        write_round_split_pack_pair(
            all,
            cursor,
            slot,
            word,
            relations,
            lo_rel_tag,
            hi_rel_tag,
            // 6-element packed-group values come from the aux witness.
            match op_idx {
                0 => block.aux_split_pack.b_init.vals,
                1 => block.aux_split_pack.c_init.vals,
                2 => block.aux_split_pack.f_init.vals,
                3 => block.aux_split_pack.g_init.vals,
                _ => unreachable!(),
            },
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

        // 6 Maj + 6 Ch.
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
) {
    let word_lo = word & 0xFFFF;
    let word_hi = (word >> 16) & 0xFFFF;
    // wire_round_split_pack lo: (word.lo, grp[0], grp[3], grp[4])
    let lo_vals = [
        BaseField::from(word_lo),
        BaseField::from(grp[0]),
        BaseField::from(grp[3]),
        BaseField::from(grp[4]),
    ];
    all[*cursor][slot] = (
        SecureField::one(),
        combine_with_tag(relations, lo_tag, &lo_vals),
    );
    *cursor += 1;
    // wire_round_split_pack hi: (word.hi, grp[1], grp[2], grp[5])
    let hi_vals = [
        BaseField::from(word_hi),
        BaseField::from(grp[1]),
        BaseField::from(grp[2]),
        BaseField::from(grp[5]),
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
) -> (
    Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim,
) {
    let mut combined = Vec::new();

    // Sha256Eval consumer first — its slot in the proof's component list.
    let (sha_trace, sha_sum) = sha256_interaction(relations, witness, sha256_log_size);
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
        let (t, s) = range_k_interaction(relations, witness, kind);
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
