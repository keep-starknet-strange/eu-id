//! Per-key multiplicity counting for the active SHA-256 range lookup tables.
//!
//! For each `Range_k` table produced in [`crate::components`], this module
//! walks a [`Sha256Witness`] and returns a `Vec<u32>` of length equal to the
//! table's committed row count. The i-th entry holds the number of times the
//! AIR fires a `Range_k` lookup keyed on row `i`.
//!
//! Why this lives in its own module:
//!
//! The mapping from "a witness value" to "the table row it keys" is
//! table-specific. Concentrating the active range mapping here keeps the trace
//! generator, witness emitter, and AIR consumer-side wiring decoupled from one
//! another.
//!
//! Every counter starts at 0; the witness walk increments by 1 per
//! `add_to_relation` site documented in `crate::constraints`. The total
//! over each vector matches the corresponding `witness::*_multiplicities_*`
//! helper exactly — `total_sanity_*` tests in this module check that.

use crate::components::{range_log_size, RangeKind};
use crate::constants::{N_ROUNDS, N_STATE_WORDS};
use crate::field_exposure::{word_be_bytes, FieldExposure};
use crate::types::Sha256Witness;

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

/// Build the per-row multiplicity vector for one `Range_k` table.
///
/// The vector's length is `2^range_log_size(kind)`. For `k < 2^LOG_N_LANES`
/// the producer is padded with leading zero-valued rows; consumer-side
/// lookups on carry values `c ∈ [0, k)` increment the row indexed by `c`.
///
/// Firing rule (mirrors `crate::constraints::emit_mod_2_32_add_linear` and
/// the terminal `Range_8` wiring in `Sha256Eval::evaluate`):
///   - One `Range_4` increment per schedule-recurrence carry-limb pair (2
///     limbs × 48 entries per block).
///   - One `Range_5` increment per `T1` carry-limb pair (2 limbs × 64
///     rounds per block).
///   - One `Range_2` increment per `T2`/`e_new`/`a_new` carry-limb pair (2
///     limbs × 3 families × 64 rounds per block) plus per finalization
///     carry-limb pair (2 limbs × 8 words per block).
///   - One `Range_8` increment per terminal `h_out` byte (4 bytes × 8
///     words per block), plus — when `field_exposure` is non-empty — one
///     increment per exposed field byte column in each target block.
///
/// `field_exposure` affects only `Range8`; every other kind ignores it.
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
            RangeKind::Range8 => {
                for j in 0..N_STATE_WORDS {
                    for b in word_be_bytes(block.h_out[j].lo, block.h_out[j].hi) {
                        bump(&mut mults, b);
                    }
                }
            }
        }
    }

    // Field-byte range-checks: each exposed byte column `b` is pinned to
    // `[0, 256)` by one consumer-side `Range8` lookup. Block-0 legacy exposure
    // fires once on block 0. Multi-block exposure fires once per target-block selector,
    // matching `Sha256Eval::evaluate` and section 7 of
    // `interaction::write_round_row_lookups`. Count them here so the `Range8`
    // producer absorbs them.
    if matches!(kind, RangeKind::Range8) {
        if field_exposure.full_padded_stream().is_some() {
            // Stream bytes are linear combinations of already
            // boolean-constrained W bits, so this mode deliberately adds no
            // duplicate Range8 sites.
        } else if field_exposure.needs_block_witness() {
            for block_idx in field_exposure.target_blocks() {
                let Some(block) = witness.blocks.get(*block_idx) else {
                    continue;
                };
                for &word_idx in field_exposure.decomposed_words() {
                    let limb = block.schedule[word_idx];
                    for b in word_be_bytes(limb.lo, limb.hi) {
                        bump(&mut mults, b);
                    }
                }
            }
        } else if !field_exposure.is_empty() {
            if let Some(block0) = witness.blocks.first() {
                for &word_idx in field_exposure.decomposed_words() {
                    let limb = block0.schedule[word_idx];
                    for b in word_be_bytes(limb.lo, limb.hi) {
                        bump(&mut mults, b);
                    }
                }
            }
        }
    }

    mults
}

// Compile-time sanity for the structural constants this module assumes.
const _: () = {
    assert!(N_ROUNDS == 64);
    assert!(N_STATE_WORDS == 8);
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::compute_sha256_witness;

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

        // Range_8: 4 bytes × 8 terminal h_out words.
        let total = range_k_multiplicities(&w, RangeKind::Range8, &FieldExposure::empty())
            .iter()
            .sum::<u32>();
        assert_eq!(total, 4 * n_words);
    }

    /// With a credential exposure, the `Range8` producer gains exactly one
    /// increment per exposed first-block field byte.
    /// This is the producer side of the byte range-check that closes the
    /// sub-word forge; the consumer side lives in `constraints`/`interaction`.
    #[test]
    fn range_8_counts_field_byte_checks() {
        use crate::components::RangeKind;
        use air_core::relations::field_id;

        // "EUID" | ver | 2007-03-15 | DE(276): DOB c[5..9], nationality c[9..11].
        let credential: [u8; 11] = [b'E', b'U', b'I', b'D', 1, 0x07, 0xD7, 3, 15, 0x01, 0x14];
        let w = compute_sha256_witness(&credential);
        let exposure = FieldExposure::from_preimage_windows(&[
            (field_id::DOB, 5, 4),
            (field_id::NATIONALITY, 9, 2),
        ]);

        let empty = range_k_multiplicities(&w, RangeKind::Range8, &FieldExposure::empty());
        let with = range_k_multiplicities(&w, RangeKind::Range8, &exposure);

        // One added lookup per exposed byte column in the one target block.
        let added = with.iter().sum::<u32>() - empty.iter().sum::<u32>();
        assert_eq!(added, exposure.n_byte_columns() as u32);

        // Each first-block field byte `b` bumps row `b`.
        let block0 = &w.blocks[0];
        for &word_idx in exposure.decomposed_words() {
            let limb = block0.schedule[word_idx];
            for b in word_be_bytes(limb.lo, limb.hi) {
                assert!(
                    with[b as usize] > empty[b as usize],
                    "row {b} must be bumped"
                );
            }
        }
    }

    /// The multi-block producer bumps `Range8` once per exposed byte column
    /// for **each** target block — matching the per-target-block selector loop
    /// on the consumer side.
    #[test]
    fn range_8_counts_multi_block_field_byte_checks() {
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

        let empty = range_k_multiplicities(&w, RangeKind::Range8, &FieldExposure::empty());
        let with = range_k_multiplicities(&w, RangeKind::Range8, &exposure);

        let added = with.iter().sum::<u32>() - empty.iter().sum::<u32>();
        assert_eq!(
            added,
            exposure.n_byte_columns() as u32 * exposure.target_blocks().len() as u32,
            "one Range8 lookup per exposed byte column for each target block selector",
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
                }
            }
        }
    }

    #[test]
    fn full_padded_stream_adds_no_duplicate_range_8_checks() {
        use crate::components::RangeKind;

        let w = compute_sha256_witness(&[0x42u8; 150]);
        let exposure = FieldExposure::from_full_padded_stream(77, w.padding.padded.len());
        assert_eq!(
            range_k_multiplicities(&w, RangeKind::Range8, &exposure),
            range_k_multiplicities(&w, RangeKind::Range8, &FieldExposure::empty()),
            "stream bytes come from boolean W bits and need no Range8 duplication",
        );
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
            RangeKind::Range8,
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
