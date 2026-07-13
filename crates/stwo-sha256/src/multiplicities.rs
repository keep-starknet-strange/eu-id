//! Per-key (per-row) multiplicity counting for every preprocessed lookup
//! table the SHA-256 component consumes.
//!
//! For each table produced in [`crate::tables`], this module walks a
//! [`Sha256Witness`] and returns a `Vec<u32>` of length equal to the table's
//! row count — the i-th entry holds the number of times the AIR fires a
//! `add_to_relation(rel, +1, …)` keyed on table row `i`.
//!
//! Why this lives in its own module:
//!
//! - [`crate::witness`] already exposes *totals* per relation
//!   (`DecodeLookupMultiplicities`, `MajChXorMultiplicities`) — those are the
//!   sanity-check view. For the
//!   LogUp interaction trace the prover needs the **per-row vector**
//!   instead: it is what gets committed as the multiplicity column the
//!   producer-side `Sha256Eval`-cousin reads via `next_trace_mask`.
//! - The mapping from "a witness value" to "the table row it keys" is
//!   table-specific (e.g. the σ-decode keys come from `pack_half_key` on
//!   the input word at the partition's `S` mask; the Maj/Ch row index is
//!   `(a · 2^W + b) · 2^W + c` from the packed groups; …). Concentrating
//!   that mapping here keeps the trace generator, the witness emitter and
//!   the AIR consumer-side wiring decoupled from one another.
//!
//! Every counter starts at 0; the witness walk increments by 1 per
//! `add_to_relation` site documented in `crate::constraints`. The total
//! over each vector matches the corresponding `witness::*_multiplicities_*`
//! helper exactly — `total_sanity_*` tests in this module check that.

use crate::components::{range_log_size, RangeKind};
use crate::constants::{N_ROUNDS, N_STATE_WORDS};
use crate::field_exposure::{word_be_bytes, FieldExposure, BYTE_RANGE_CHECK_OFFSET};
use crate::partitions::SigmaFn;
use crate::tables::{pack_half_key, Half};
use crate::types::Sha256Witness;

/// Number of rows in every 2¹⁶-row table (decode and xor_8).
pub const ROWS_16: usize = 1 << 16;

/// Build the per-row multiplicity vector for one σ/Σ decode table.
///
/// `f` chooses the function (`Σ0`/`Σ1`/`σ0`/`σ1`) and `half` picks the
/// S-side or S′-side table. The table is keyed on the 16-bit
/// `pack_half_key(input_word, side_mask)`.
///
/// **AIR firing rule (from `crate::constraints::wire_sigma_decode`):**
/// - Round-side: every round `t` fires `Σ0(a[t])` and `Σ1(e[t])` — two
///   decode S-side + two decode S′-side lookups per round. The input
///   word is `a[t]` for `Σ0`, `e[t]` for `Σ1`.
/// - Schedule-side: every schedule entry `j ∈ [0, 48)` fires
///   `σ0(W[t-15])` and `σ1(W[t-2])` (where `t = j + 16`) — two decode
///   S-side + two decode S′-side lookups per entry. The input word is
///   `W[t-15]` for `σ0`, `W[t-2]` for `σ1`.
pub fn decode_multiplicities(witness: &Sha256Witness, f: SigmaFn, half: Half) -> Vec<u32> {
    let mut mults = vec![0u32; ROWS_16];
    let s_mask = f.s_mask();
    let side_mask = match half {
        Half::S => s_mask,
        Half::SComplement => !s_mask,
    };

    for block in &witness.blocks {
        // Round-side fires Σ0 / Σ1 only.
        if matches!(f, SigmaFn::Sigma0 | SigmaFn::Sigma1) {
            for round in &block.rounds {
                let input_word = match f {
                    SigmaFn::Sigma0 => round.state_in[0].to_u32(), // a
                    SigmaFn::Sigma1 => round.state_in[4].to_u32(), // e
                    _ => unreachable!(),
                };
                let key = pack_half_key(input_word, side_mask);
                mults[key as usize] += 1;
            }
        }
        // Schedule-side fires σ0 / σ1 only.
        if matches!(f, SigmaFn::LowerSigma0 | SigmaFn::LowerSigma1) {
            for entry in &block.schedule_entries {
                let input_word = match f {
                    SigmaFn::LowerSigma0 => entry.w_t_minus_15.to_u32(),
                    SigmaFn::LowerSigma1 => entry.w_t_minus_2.to_u32(),
                    _ => unreachable!(),
                };
                let key = pack_half_key(input_word, side_mask);
                mults[key as usize] += 1;
            }
        }
    }
    mults
}

pub fn sum_multiplicity_vectors(vectors: impl IntoIterator<Item = Vec<u32>>) -> Vec<u32> {
    let mut iter = vectors.into_iter();
    let mut acc = iter.next().unwrap_or_default();
    for v in iter {
        assert_eq!(
            acc.len(),
            v.len(),
            "cannot sum multiplicity vectors of different lengths"
        );
        for (a, b) in acc.iter_mut().zip(v) {
            *a += b;
        }
    }
    acc
}

/// Build the per-row multiplicity vector for the generic `xor_8` table.
///
/// The table has 2¹⁶ rows indexed by `(y, x) → y · 256 + x` (matching
/// `crate::tables::build_xor_8_table`). The AIR keys it on `(x, y, z)` with
/// `z = x ⊕ y`; the row index depends on `(x, y)` only.
///
/// Firing rule: every σ-application — `Σ0`/`Σ1` per round and `σ0`/`σ1`
/// per schedule entry — fires four chunk-wise `xor_8` lookups (the four
/// O2-partial byte chunks: `(lo.b0, lo.b1, hi.b0, hi.b1)`). The chunks
/// of the S-side and S′-side partials are the keys.
pub fn xor_8_multiplicities(witness: &Sha256Witness) -> Vec<u32> {
    let mut mults = vec![0u32; ROWS_16];
    let bump = |m: &mut [u32], x: u32, y: u32| {
        let key = (y as usize) * 256 + (x as usize);
        m[key] += 1;
    };

    for block in &witness.blocks {
        for entry in &block.schedule_entries {
            for d in [&entry.lower_sigma0_decode, &entry.lower_sigma1_decode] {
                bump(
                    &mut mults,
                    d.o2_chunks_s.lo.b0,
                    d.o2_chunks_s_complement.lo.b0,
                );
                bump(
                    &mut mults,
                    d.o2_chunks_s.lo.b1,
                    d.o2_chunks_s_complement.lo.b1,
                );
                bump(
                    &mut mults,
                    d.o2_chunks_s.hi.b0,
                    d.o2_chunks_s_complement.hi.b0,
                );
                bump(
                    &mut mults,
                    d.o2_chunks_s.hi.b1,
                    d.o2_chunks_s_complement.hi.b1,
                );
            }
        }
        for round in &block.rounds {
            for d in [&round.sigma0_decode, &round.sigma1_decode] {
                bump(
                    &mut mults,
                    d.o2_chunks_s.lo.b0,
                    d.o2_chunks_s_complement.lo.b0,
                );
                bump(
                    &mut mults,
                    d.o2_chunks_s.lo.b1,
                    d.o2_chunks_s_complement.lo.b1,
                );
                bump(
                    &mut mults,
                    d.o2_chunks_s.hi.b0,
                    d.o2_chunks_s_complement.hi.b0,
                );
                bump(
                    &mut mults,
                    d.o2_chunks_s.hi.b1,
                    d.o2_chunks_s_complement.hi.b1,
                );
            }
        }
    }
    mults
}

/// Build the per-row multiplicity vector for one `Range_k` table.
///
/// The vector's length is `2^range_log_size(kind)`. For `k < 2^LOG_N_LANES`
/// the producer is padded with leading zero-valued rows; consumer-side
/// lookups on carry values `c ∈ [0, k)` increment the row indexed by `c`.
///
/// Firing rule (mirrors `crate::constraints::emit_mod_2_32_add_linear` and
/// the terminal `Range_16` wiring in `Sha256Eval::evaluate`):
///   - One `Range_4` increment per schedule-recurrence carry-limb pair (2
///     limbs × 48 entries per block).
///   - One `Range_5` increment per `T1` carry-limb pair (2 limbs × 64
///     rounds per block).
///   - One `Range_2` increment per `T2`/`e_new`/`a_new` carry-limb pair (2
///     limbs × 3 families × 64 rounds per block) plus per finalization
///     carry-limb pair (2 limbs × 8 words per block).
///   - One `Range_16` increment per terminal `h_out` limb (2 limbs × 8
///     words per block), plus — when `field_exposure` is non-empty — two
///     increments per exposed field byte column in each target block (the byte
///     and the byte + [`BYTE_RANGE_CHECK_OFFSET`] of the `[0, 256)`
///     range-check).
///
/// `field_exposure` affects only `Range16`; every other kind ignores it.
pub fn range_k_multiplicities(
    witness: &Sha256Witness,
    kind: RangeKind,
    field_exposure: &FieldExposure,
) -> Vec<u32> {
    let log_size = range_log_size(kind);
    let mut mults = vec![0u32; 1usize << log_size];
    let bump = |m: &mut [u32], value: u32| {
        m[value as usize] += 1;
    };

    for block in &witness.blocks {
        match kind {
            RangeKind::Range4 => {
                for entry in &block.schedule_entries {
                    bump(&mut mults, entry.carries.lo);
                    bump(&mut mults, entry.carries.hi);
                }
            }
            RangeKind::Range5 => {
                for round in &block.rounds {
                    bump(&mut mults, round.t1_carries.lo);
                    bump(&mut mults, round.t1_carries.hi);
                }
            }
            RangeKind::Range2 => {
                for round in &block.rounds {
                    bump(&mut mults, round.t2_carries.lo);
                    bump(&mut mults, round.t2_carries.hi);
                    bump(&mut mults, round.e_new_carries.lo);
                    bump(&mut mults, round.e_new_carries.hi);
                    bump(&mut mults, round.a_new_carries.lo);
                    bump(&mut mults, round.a_new_carries.hi);
                }
                for c in &block.finalization_carries {
                    bump(&mut mults, c.lo);
                    bump(&mut mults, c.hi);
                }
            }
            RangeKind::Range16 => {
                for j in 0..N_STATE_WORDS {
                    bump(&mut mults, block.h_out[j].lo);
                    bump(&mut mults, block.h_out[j].hi);
                }
            }
        }
    }

    // Field-byte range-checks: each exposed byte column `b` is pinned to
    // `[0, 256)` by two consumer-side `Range16` lookups (on `b` and on
    // `b + BYTE_RANGE_CHECK_OFFSET`). Block-0 legacy exposure fires once on
    // block 0. Multi-block exposure fires once per target-block selector,
    // matching `Sha256Eval::evaluate` and section 7 of
    // `interaction::write_round_row_lookups`. Count them here so the `Range16`
    // producer absorbs them.
    if matches!(kind, RangeKind::Range16) {
        if field_exposure.needs_block_witness() {
            for block_idx in field_exposure.target_blocks() {
                let Some(block) = witness.blocks.get(*block_idx) else {
                    continue;
                };
                for &word_idx in field_exposure.decomposed_words() {
                    let limb = block.schedule[word_idx];
                    for b in word_be_bytes(limb.lo, limb.hi) {
                        bump(&mut mults, b);
                        bump(&mut mults, b + BYTE_RANGE_CHECK_OFFSET);
                    }
                }
            }
        } else if !field_exposure.is_empty() {
            if let Some(block0) = witness.blocks.first() {
                for &word_idx in field_exposure.decomposed_words() {
                    let limb = block0.schedule[word_idx];
                    for b in word_be_bytes(limb.lo, limb.hi) {
                        bump(&mut mults, b);
                        bump(&mut mults, b + BYTE_RANGE_CHECK_OFFSET);
                    }
                }
            }
        }
    }

    mults
}

// Compile-time sanity: no callers should accidentally use deprecated APIs.
#[allow(dead_code)]
const _: () = {
    assert!(N_ROUNDS == 64);
    assert!(N_STATE_WORDS == 8);
};

// Re-export so call sites can name partitions/half without re-importing.
pub use crate::tables::Half as DecodeHalf;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::{
        compute_sha256_witness, decode_multiplicities_for_witness,
        maj_ch_xor_multiplicities_for_witness,
    };

    /// Per-key vectors sum to the per-witness totals reported by the
    /// existing `witness::*_multiplicities_*` helpers. Any drift caught
    /// closed.
    #[test]
    fn decode_per_row_totals_match_witness_totals() {
        let w = compute_sha256_witness(b"abc");
        let totals = decode_multiplicities_for_witness(&w);
        let m = |f, h| decode_multiplicities(&w, f, h).iter().sum::<u32>();

        assert_eq!(m(SigmaFn::Sigma0, Half::S), totals.sigma0_s);
        assert_eq!(
            m(SigmaFn::Sigma0, Half::SComplement),
            totals.sigma0_s_complement
        );
        assert_eq!(m(SigmaFn::Sigma1, Half::S), totals.sigma1_s);
        assert_eq!(
            m(SigmaFn::Sigma1, Half::SComplement),
            totals.sigma1_s_complement
        );
        assert_eq!(m(SigmaFn::LowerSigma0, Half::S), totals.lower_sigma0_s);
        assert_eq!(
            m(SigmaFn::LowerSigma0, Half::SComplement),
            totals.lower_sigma0_s_complement
        );
        assert_eq!(m(SigmaFn::LowerSigma1, Half::S), totals.lower_sigma1_s);
        assert_eq!(
            m(SigmaFn::LowerSigma1, Half::SComplement),
            totals.lower_sigma1_s_complement
        );
    }

    #[test]
    fn xor_8_per_row_totals_match_witness_totals() {
        let w = compute_sha256_witness(b"abc");
        let totals = maj_ch_xor_multiplicities_for_witness(&w);
        let v = xor_8_multiplicities(&w);
        assert_eq!(v.iter().sum::<u32>(), totals.xor_8);
    }

    /// Per-block totals for each `Range_k` multiplicity vector match the
    /// structural per-block lookup counts the AIR's `Sha256Eval` fires.
    /// Drift between this and the consumer-side wiring is the same kind
    /// of soundness-relevant gap the existing `*_per_row_totals_*` tests
    /// guard against — kept here so a future edit to either side fails
    /// closed at unit-test time, not at integration-test time.
    #[test]
    fn range_k_per_block_totals_match_structural_counts() {
        use crate::components::RangeKind;
        let w = compute_sha256_witness(b"abc");
        let n_entries = (N_ROUNDS - 16) as u32; // 48 schedule entries
        let n_rounds = N_ROUNDS as u32;
        let n_words = N_STATE_WORDS as u32;

        // Range_4: schedule-recurrence carries — 2 limbs × 48 entries.
        let total = range_k_multiplicities(&w, RangeKind::Range4, &FieldExposure::empty())
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * n_entries);

        // Range_5: T1 carries — 2 limbs × 64 rounds.
        let total = range_k_multiplicities(&w, RangeKind::Range5, &FieldExposure::empty())
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * n_rounds);

        // Range_2: T2 + e_new + a_new (3 × 64) round carries + 8
        // finalization carries, ×2 limbs each.
        let total = range_k_multiplicities(&w, RangeKind::Range2, &FieldExposure::empty())
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * (3 * n_rounds + n_words));

        // Range_16: 2 limbs × 8 terminal h_out words.
        let total = range_k_multiplicities(&w, RangeKind::Range16, &FieldExposure::empty())
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * n_words);
    }

    /// With a credential exposure, the `Range16` producer gains exactly two
    /// increments per exposed first-block field byte — the `[0, 256)`
    /// credential-field byte range-check (one on `b`, one on
    /// `b + BYTE_RANGE_CHECK_OFFSET`).
    /// This is the producer side of the byte range-check that closes the
    /// sub-word forge; the consumer side lives in `constraints`/`interaction`.
    #[test]
    fn range_16_counts_field_byte_checks() {
        use crate::components::RangeKind;
        use air_core::relations::field_id;

        // "EUID" | ver | 2007-03-15 | DE(276): DOB c[5..9], nationality c[9..11].
        let credential: [u8; 11] = [b'E', b'U', b'I', b'D', 1, 0x07, 0xD7, 3, 15, 0x01, 0x14];
        let w = compute_sha256_witness(&credential);
        let exposure = FieldExposure::from_preimage_windows(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, 9, 2),
        ]);

        let empty = range_k_multiplicities(&w, RangeKind::Range16, &FieldExposure::empty());
        let with = range_k_multiplicities(&w, RangeKind::Range16, &exposure);

        // Two added lookups per exposed byte column in the one target block.
        let added = with.iter().sum::<u32>() - empty.iter().sum::<u32>();
        assert_eq!(added, 2 * exposure.n_byte_columns() as u32);

        // Each first-block field byte `b` bumps row `b` and row `b + OFFSET`.
        let block0 = &w.blocks[0];
        for &word_idx in exposure.decomposed_words() {
            let limb = block0.schedule[word_idx];
            for b in word_be_bytes(limb.lo, limb.hi) {
                assert!(
                    with[b as usize] > empty[b as usize],
                    "row {b} must be bumped"
                );
                let hi = (b + BYTE_RANGE_CHECK_OFFSET) as usize;
                assert!(with[hi] > empty[hi], "row b+OFFSET={hi} must be bumped");
            }
        }
    }

    /// The multi-block producer bumps `Range16` twice per exposed byte column
    /// for **each** target block — matching the per-target-block selector loop
    /// on the consumer side.
    #[test]
    fn range_16_counts_multi_block_field_byte_checks() {
        use crate::components::RangeKind;
        use air_core::relations::field_id;

        let msg: Vec<u8> = (0..150).map(|i| (i % 251) as u8).collect();
        let w = compute_sha256_witness(&msg);
        assert_eq!(w.blocks.len(), 3, "test message must span 3 blocks");
        let exposure = FieldExposure::from_preimage_windows_multi(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, 64 + 9, 2),
            (99, 128 + 12, 3),
        ]);

        let empty = range_k_multiplicities(&w, RangeKind::Range16, &FieldExposure::empty());
        let with = range_k_multiplicities(&w, RangeKind::Range16, &exposure);

        let added = with.iter().sum::<u32>() - empty.iter().sum::<u32>();
        assert_eq!(
            added,
            2 * exposure.n_byte_columns() as u32 * exposure.target_blocks().len() as u32,
            "two Range16 lookups per exposed byte column for each target block selector",
        );

        for &block_idx in exposure.target_blocks() {
            let block = &w.blocks[block_idx];
            for &word_idx in exposure.decomposed_words() {
                let limb = block.schedule[word_idx];
                for b in word_be_bytes(limb.lo, limb.hi) {
                    assert!(
                        with[b as usize] > empty[b as usize],
                        "block {block_idx} row {b} must be bumped",
                    );
                    let hi = (b + BYTE_RANGE_CHECK_OFFSET) as usize;
                    assert!(
                        with[hi] > empty[hi],
                        "block {block_idx} row b+OFFSET={hi} must be bumped",
                    );
                }
            }
        }
    }

    /// Honest `Range_k` carry counts never fall outside `[0, k)` — the
    /// witness layer's `add_words_with_carries` already guarantees this,
    /// and the multiplicity helper bumps `mults[value]`, so an
    /// out-of-bound carry would either panic (index out of bounds) or
    /// silently land in a padding slot. This test pins the property at
    /// the multiplicity layer.
    #[test]
    fn range_k_honest_counts_live_within_table_bounds() {
        use crate::components::RangeKind;
        let w = compute_sha256_witness(&[0x42u8; 200]); // multi-block, mixed bytes
        for kind in [
            RangeKind::Range2,
            RangeKind::Range4,
            RangeKind::Range5,
            RangeKind::Range16,
        ] {
            let mults = range_k_multiplicities(&w, kind, &FieldExposure::empty());
            let k = kind.bound() as usize;
            // Any multiplicity past row k-1 means an out-of-range carry
            // got counted — the witness is malformed.
            for (i, &m) in mults.iter().enumerate() {
                if i >= k {
                    assert_eq!(m, 0, "{kind:?}: row {i} > k-1 = {} has m = {m}", k - 1);
                }
            }
        }
    }

    /// Negative complement of [`range_k_honest_counts_live_within_table_bounds`]
    /// — pins the `Range_k` LogUp soundness gate from the multiplicity side
    /// without paying for a real proof.
    ///
    /// The end-to-end equivalent is
    /// `tests/prove_verify_round_trip.rs::rejects_out_of_range_carry_witness_mutation`,
    /// but that test is `#[ignore]`d (release-only) because a real proof
    /// dominates wall time. This debug-mode test exercises the same
    /// soundness invariant by checking the *necessary condition* the
    /// LogUp argument enforces: a witness carry outside `[0, k)` shows
    /// up as a consumer-side multiplicity bump at an index the producer
    /// `Range_k` table has no row for, so the consumer/producer claimed
    /// sums cannot balance. Together with the producer-side parity
    /// invariants further up this module, this closes audit lesson L4
    /// (docs/research/sha256-air-design.md §11) on the LogUp side at debug
    /// cadence.
    #[test]
    fn out_of_range_carry_mutation_shifts_multiplicity_outside_table() {
        use crate::components::RangeKind;
        let mut w = compute_sha256_witness(b"abc");

        let baseline = range_k_multiplicities(&w, RangeKind::Range2, &FieldExposure::empty());
        let k = RangeKind::Range2.bound() as usize;

        // Mirror the witness mutation that
        // `rejects_out_of_range_carry_witness_mutation` runs end-to-end:
        // bump finalization carry word 7 lo from its honest `< 2` value
        // to `5` — outside the `Range_2` producer table.
        let last = w.blocks.last_mut().expect("at least one block");
        let original = last.finalization_carries[7].lo;
        assert!(
            (original as usize) < k,
            "honest carry must live within [0, k); got {original}",
        );
        last.finalization_carries[7].lo = 5;

        let mutated = range_k_multiplicities(&w, RangeKind::Range2, &FieldExposure::empty());

        // Bucket 5 is outside `[0, k = 2)`, so the producer Range_2 table
        // has no row for it. The mutation moves exactly one count from
        // `mults[original]` to `mults[5]`; every other bucket is unchanged.
        assert_eq!(
            mutated[5],
            baseline[5] + 1,
            "out-of-range carry value 5 must bump the multiplicity at bucket 5",
        );
        assert_eq!(
            mutated[original as usize] + 1,
            baseline[original as usize],
            "original honest bucket should lose one count",
        );
        for i in 0..mutated.len() {
            if i != 5 && i != original as usize {
                assert_eq!(
                    mutated[i], baseline[i],
                    "bucket {i} should be unchanged by a single-cell carry mutation",
                );
            }
        }

        // The LogUp soundness condition the gate enforces: the consumer's
        // claimed sum cannot balance the producer's if any multiplicity
        // outside `[0, k)` is non-zero.
        assert!(
            mutated[k..].iter().any(|m| *m > 0),
            "mutation must place at least one multiplicity outside the producer range",
        );
    }

    #[test]
    fn shared_table_multiplicities_sum_per_consumer_vectors() {
        use crate::components::RANGE_TABLES;
        let first = compute_sha256_witness(b"abc");
        let second = compute_sha256_witness(&[0x42u8; 200]);
        let consumers = [
            (&first, FieldExposure::empty()),
            (&second, FieldExposure::empty()),
        ];

        let shared = crate::shared_tables::ShaTableMultiplicities::from_consumers(&consumers);

        // Class D: the stored vectors are blinded (2× length, random dummy upper
        // half). Only the REAL lower half is the deterministic union sum; the
        // upper half is fresh per-proof mask and is asserted equal to neither
        // witness. We compare the lower half against the union sum here.
        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            let expected: Vec<u32> = range_k_multiplicities(&first, kind, &FieldExposure::empty())
                .into_iter()
                .zip(range_k_multiplicities(
                    &second,
                    kind,
                    &FieldExposure::empty(),
                ))
                .map(|(a, b)| a + b)
                .collect();
            assert_eq!(&shared.range[i][..expected.len()], &expected[..]);
            assert_eq!(shared.range[i].len(), 2 * expected.len());
        }
    }
}
