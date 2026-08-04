//! Per-key multiplicity counting for the range tables consumed by SHA-256.
//!
//! This module counts lookup uses from a packed SHA witness.
//! It returns one `Vec<u32>` for each active range table.
//! The vector length equals the table row count.
//! Entry `i` counts relation uses for table row `i`.
//!
//! Keeping the witness-to-table-row mapping here keeps trace generation,
//! witness emission, and AIR wiring separate.

use crate::components::{range_log_size, RangeKind};
use crate::constants::{N_ROUNDS, N_STATE_WORDS};
use crate::types::PackedSha256Witness;

/// Build the per-row multiplicity vector for one `Range_k` table.
///
/// The vector's length is `2^range_log_size(kind)`. Extra rows after the first
/// `k` rows have value zero and multiplicity zero. A consumer lookup for
/// `c ∈ [0, k)` increments row `c`.
///
/// The count rules mirror the AIR relation uses:
///   - One `Range_4` increment per schedule-recurrence carry-limb pair (2
///     limbs × 48 entries per block).
///   - One `Range_5` increment per `T1` carry-limb pair (2 limbs × 64
///     rounds per block).
///   - One `Range_2` increment for each `T2`, `e_new`, and `a_new` carry limb.
///     Each block has two limbs in three families for 64 rounds. It also has
///     two finalization carry limbs for each of eight words.
///   - One `Range_8` increment per terminal `h_out` byte (4 bytes × 8
///     words per block).
pub(crate) fn range_k_multiplicities(witness: &PackedSha256Witness, kind: RangeKind) -> Vec<u32> {
    let log_size = range_log_size(kind);
    let mut mults = vec![0u32; 1usize << log_size];
    let bump = |m: &mut [u32], value: u32| {
        m[value as usize] += 1;
    };

    for message in &witness.messages {
        for block in &message.blocks {
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
                    for byte in crate::trace::h_out_digest_bytes(&block.h_out) {
                        bump(&mut mults, byte);
                    }
                }
            }
        }
    }

    mults
}

// Compile-time checks for the fixed SHA dimensions.
#[allow(dead_code)]
const _: () = {
    assert!(N_ROUNDS == 64);
    assert!(N_STATE_WORDS == 8);
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::compute_packed_sha256_witness;

    /// Confirm that each `Range_k` total matches the AIR lookup count.
    ///
    /// This unit test detects drift between multiplicities and consumer wiring.
    #[test]
    fn range_k_per_block_totals_match_structural_counts() {
        use crate::components::RangeKind;
        let w = compute_packed_sha256_witness(&[&b"abc"[..]]).unwrap();
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

    /// Confirm that honest `Range_k` counts stay in `[0, k)`.
    ///
    /// The witness addition helper creates an in-range carry.
    /// The multiplicity helper increments `mults[value]`.
    /// All later padding slots must remain zero.
    #[test]
    fn range_k_honest_counts_live_within_table_bounds() {
        use crate::components::RangeKind;
        let w = compute_packed_sha256_witness(&[&[0x42u8; 200][..]]).unwrap();
        for kind in [
            RangeKind::Range2,
            RangeKind::Range4,
            RangeKind::Range5,
            RangeKind::Range8,
        ] {
            let mults = range_k_multiplicities(&w, kind);
            let k = kind.bound() as usize;
            // A nonzero multiplicity after row k-1 identifies an invalid
            // carry in the witness.
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
    /// The release test proves the equivalent end-to-end property.
    /// This debug test checks the LogUp count condition.
    /// An out-of-range carry increments a row absent from the producer table.
    /// The consumer and producer claim sums then cannot balance.
    #[test]
    fn out_of_range_carry_mutation_shifts_multiplicity_outside_table() {
        use crate::components::RangeKind;
        let mut w = compute_packed_sha256_witness(&[&b"abc"[..]]).unwrap();

        let baseline = range_k_multiplicities(&w, RangeKind::Range2);
        let k = RangeKind::Range2.bound() as usize;

        // Match the mutation in the end-to-end release test.
        // Change finalization word seven from an honest carry to five.
        // Five is outside the `Range_2` producer table.
        let last = w.messages[0].blocks.last_mut().expect("at least one block");
        let original = last.finalization_carries[7].lo;
        assert!(
            (original as usize) < k,
            "honest carry must live within [0, k); got {original}",
        );
        last.finalization_carries[7].lo = 5;

        let mutated = range_k_multiplicities(&w, RangeKind::Range2);

        // Bucket 5 is outside `[0, k = 2)`, so the producer Range_2 table
        // has no row for it. The mutation moves exactly one count from
        // `mults[original]` to `mults[5]`. All other buckets stay unchanged.
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
        let packed = compute_packed_sha256_witness(&[&b"abc"[..], &[0x42u8; 200][..]]).unwrap();
        let shared = crate::shared_tables::ShaTableMultiplicities::from_packed(&packed);

        // Class D doubles each vector and fills the dummy upper half with a
        // random mask. Only the real lower half contains the deterministic
        // union sum. Compare that lower half with the union here.
        for (i, &kind) in RANGE_TABLES.iter().enumerate() {
            let expected = range_k_multiplicities(&packed, kind);
            assert_eq!(&shared.range[i][..expected.len()], &expected[..]);
            let producer = crate::components::SharedProducer::Range(kind);
            let real_len = 1usize << (producer.blind_log_size() - 1);
            assert_eq!(shared.range[i].len(), 2 * real_len);
            assert!(
                shared.range[i][expected.len()..real_len]
                    .iter()
                    .all(|&multiplicity| multiplicity == 0),
                "extra real rows must have zero multiplicity"
            );
        }
    }
}
