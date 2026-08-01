//! Per-key multiplicity counting for the active SHA-256 range lookup tables.
//!
//! Each result vector has one entry for each committed table row. Entry `i`
//! counts lookups with the key from row `i`.
//!
//! The count must match the `add_to_relation` sites in
//! [`crate::constraints`].

use crate::components::{range_log_size, RangeKind};
use crate::constants::{N_ROUNDS, N_STATE_WORDS};
use crate::field_exposure::word_be_bytes;
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
/// the producer is padded with trailing zero-valued rows; consumer-side
/// lookups on carry values `c ∈ [0, k)` increment the row indexed by `c`.
///
/// Firing rule (mirrors `crate::constraints::emit_mod_2_32_add_linear` and
/// the final digest-byte wiring in `crate::digest_bridge`):
///   - One `Range_4` increment per schedule-recurrence carry-limb pair (2
///     limbs × 48 entries per block).
///   - One `Range_5` increment per `T1` carry-limb pair (2 limbs × 64
///     rounds per block).
///   - One `Range_2` increment per `T2`/`e_new`/`a_new` carry-limb pair (2
///     limbs × 3 families × 64 rounds per block) plus per finalization
///     carry-limb pair (2 limbs × 8 words per block).
///   - One `Range_8` increment per final digest byte (32 total).
pub fn range_k_multiplicities(witness: &Sha256Witness, kind: RangeKind) -> Vec<u32> {
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
            RangeKind::Range8 => {}
        }
    }

    if kind == RangeKind::Range8 {
        let final_block = witness
            .blocks
            .last()
            .expect("SHA witness has a final block");
        for word in &final_block.h_out {
            for byte in word_be_bytes(word.lo, word.hi) {
                bump(&mut mults, byte);
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
    /// This test fails if the multiplicity calculation and consumer wiring
    /// use different totals.
    #[test]
    fn range_k_per_block_totals_match_structural_counts() {
        use crate::components::RangeKind;
        let w = compute_sha256_witness(b"abc");
        let n_entries = (N_ROUNDS - 16) as u32; // 48 schedule entries
        let n_rounds = N_ROUNDS as u32;
        let n_words = N_STATE_WORDS as u32;

        // Range_4: schedule-recurrence carries — 2 limbs × 48 entries.
        let total = range_k_multiplicities(&w, RangeKind::Range4)
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * n_entries);

        // Range_5: T1 carries — 2 limbs × 64 rounds.
        let total = range_k_multiplicities(&w, RangeKind::Range5)
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * n_rounds);

        // Range_2: T2 + e_new + a_new (3 × 64) round carries + 8
        // finalization carries, ×2 limbs each.
        let total = range_k_multiplicities(&w, RangeKind::Range2)
            .iter()
            .sum::<u32>();
        assert_eq!(total, 2 * (3 * n_rounds + n_words));

        // Range_8: 4 bytes × 8 terminal h_out words.
        let total = range_k_multiplicities(&w, RangeKind::Range8)
            .iter()
            .sum::<u32>();
        assert_eq!(total, 4 * n_words);
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
            let mults = range_k_multiplicities(&w, kind);
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
    /// but that test is ignored because a real proof dominates wall time.
    /// This unit test checks the same necessary condition that the
    /// LogUp argument enforces: a witness carry outside `[0, k)` shows
    /// up as a consumer-side multiplicity bump at an index the producer
    /// `Range_k` table has no row for, so the consumer/producer claimed
    /// sums cannot balance.
    #[test]
    fn out_of_range_carry_mutation_shifts_multiplicity_outside_table() {
        use crate::components::RangeKind;
        let mut w = compute_sha256_witness(b"abc");

        let baseline = range_k_multiplicities(&w, RangeKind::Range2);
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

        let mutated = range_k_multiplicities(&w, RangeKind::Range2);

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
        let consumers = [&first, &second];

        let shared = crate::shared_tables::ShaTableMultiplicities::from_consumers(&consumers);

        // Class D: the stored vectors are blinded (2× length, random dummy upper
        // half). Only the REAL lower half is the deterministic union sum; the
        // upper half is fresh per-proof mask and is asserted equal to neither
        // witness. We compare the lower half against the union sum here.
        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            let expected: Vec<u32> = range_k_multiplicities(&first, kind)
                .into_iter()
                .zip(range_k_multiplicities(&second, kind))
                .map(|(a, b)| a + b)
                .collect();
            assert_eq!(&shared.range[i][..expected.len()], &expected[..]);
            assert_eq!(shared.range[i].len(), 2 * expected.len());
        }
    }
}
