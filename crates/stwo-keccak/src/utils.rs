//! State representation and the native Keccak-f[1600] reference used to fill
//! and validate traces.
//!
//! The state is `[PackedM31; 200]`: 25 lanes of 8 little-endian byte limbs.
//! Byte `idx = lane*8 + byte_idx`. The `N_LANES` SIMD lanes of each `PackedM31`
//! carry independent permutation instances. One column set proves `N_LANES`
//! permutations at once. This is the unit for cells-per-permutation accounting.

use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::prover::backend::simd::m31::{PackedM31, N_LANES};

use crate::constants::{N_BYTES_IN_STATE, N_BYTES_IN_U64, N_LANES_KECCAK, N_ROUNDS};

// ───────────────────────────── Spread encoding ─────────────────────────────
//
// Stride-2 "spread" form: a byte `b = Σ bᵢ·2ⁱ` maps to `spread(b) = Σ bᵢ·4ⁱ`
// (a 16-bit value whose 8 base-4 digits are exactly `b`'s bits). Sums of ≤3
// spread values stay carry-free in M31 (each base-4 slot sums to ≤3), so XOR of
// up to three bytes is a single dense `sum → spread(xor)` table lookup. AndNot
// retargets onto the same table: `spread(b'⊕b'') = 2·spread(¬b'∧b'') +
// spread(b') − spread(b'')` lets a `spread(b')+spread(b'')` xor3 lookup certify
// the committed `spread(¬b'∧b'')` output. The Keccak state is carried in
// spread form across all rounds and through the `KeccakStateRelation`. Byte
// form appears only at the HashIo boundary, where the `conv` table converts
// it.

/// Largest spread value: `spread(0xFF) = Σ 4ⁱ = (4⁸−1)/3 = 21845`.
pub const SPREAD_MAX: u32 = spread_u32(0xFF);

/// `spread(byte)`: interleave each of the byte's 8 bits into base-4 slots.
pub const fn spread_u32(byte: u32) -> u32 {
    let mut out = 0u32;
    let mut i = 0;
    while i < 8 {
        out |= ((byte >> i) & 1) << (2 * i);
        i += 1;
    }
    out
}

/// Inverse of [`spread_u32`] for a *valid* spread value (each base-4 digit 0/1).
pub const fn unspread_u32(spread: u32) -> u32 {
    let mut out = 0u32;
    let mut i = 0;
    while i < 8 {
        out |= ((spread >> (2 * i)) & 1) << i;
        i += 1;
    }
    out
}

/// A monotone activity mask: the first `padding_offset` rows are active (1),
/// the rest are padding (0). Used to gate real vs. padded permutation rows.
#[derive(Debug, Clone)]
pub struct Enabler {
    pub padding_offset: usize,
}

impl Enabler {
    /// Create an enabler active on the first `padding_offset` rows.
    pub const fn new(padding_offset: usize) -> Self {
        Self { padding_offset }
    }

    /// The packed mask for vector row `vec_row`.
    pub fn packed_at(&self, vec_row: usize) -> PackedM31 {
        let row_offset = vec_row * N_LANES;
        if row_offset >= self.padding_offset {
            return PackedM31::zero();
        }
        if row_offset + N_LANES <= self.padding_offset {
            return PackedM31::one();
        }
        let mut res = [M31::zero(); N_LANES];
        let enabled = self.padding_offset - row_offset;
        res[..enabled].fill(M31::one());
        PackedM31::from_array(res)
    }
}

// ───────────────────── Column ordering for row-offset masks ─────────────────

/// A base-field column evaluation over the circle domain (bit-reversed order).
pub type ColEval = stwo::prover::poly::circle::CircleEvaluation<
    stwo::prover::backend::simd::SimdBackend,
    M31,
    stwo::prover::poly::BitReversedOrder,
>;

/// Wrap a coset-ordered value vector (length `2^log_size`) into a circle-domain
/// `CircleEvaluation`, applying the coset→circle-domain permutation the
/// `[-1, 0]` masks expect (mirror of `stwo-mldsa`'s `air_util::col_eval`).
pub fn col_eval(log_size: u32, values: Vec<M31>) -> ColEval {
    use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
    assert_eq!(
        values.len(),
        1usize << log_size,
        "column length must be 2^log_size"
    );
    let mut ordered = vec![M31::zero(); values.len()];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ColEval::new(
        stwo::core::poly::circle::CanonicCoset::new(log_size).circle_domain(),
        stwo::prover::backend::simd::column::BaseColumn::from_iter(ordered),
    )
}

/// Map circle-domain (bit-reversed) row → coset index, for packing interaction
/// columns whose logical order is coset order.
pub fn circle_row_to_coset(log_size: u32) -> Vec<usize> {
    use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
    let rows = 1usize << log_size;
    let mut lookup = vec![0usize; rows];
    for coset in 0..rows {
        let domain_row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset, log_size),
            log_size,
        );
        lookup[domain_row] = coset;
    }
    lookup
}

// ───────────────────────────── Keccak-f[1600] ──────────────────────────────

const KECCAK_RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];
const KECCAK_PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];
const KECCAK_RC: [u64; N_ROUNDS] = crate::constants::iota_rc_rounds();

/// A single Keccak-f[1600] round over all SIMD lanes, in place.
pub fn keccak_f1600_round(state: &mut [PackedM31; N_BYTES_IN_STATE], round: usize) {
    debug_assert!(round < N_ROUNDS);
    for lane in 0..N_LANES {
        let mut words = load_lane_words(state, lane);
        keccak_f1600_round_words(&mut words, round);
        store_lane_words(state, lane, &words);
    }
}

fn keccak_f1600_round_words(state: &mut [u64; N_LANES_KECCAK], round: usize) {
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
    }
    let mut d = [0u64; 5];
    for x in 0..5 {
        d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
    }
    for y in 0..5 {
        for x in 0..5 {
            state[x + 5 * y] ^= d[x];
        }
    }
    let mut current = state[1];
    for i in 0..24 {
        let idx = KECCAK_PI[i];
        let tmp = state[idx];
        state[idx] = current.rotate_left(KECCAK_RHO[i]);
        current = tmp;
    }
    for y in 0..5 {
        let base = 5 * y;
        let row = [
            state[base],
            state[base + 1],
            state[base + 2],
            state[base + 3],
            state[base + 4],
        ];
        for x in 0..5 {
            state[base + x] = row[x] ^ ((!row[(x + 1) % 5]) & row[(x + 2) % 5]);
        }
    }
    state[0] ^= KECCAK_RC[round];
}

fn load_lane_words(state: &[PackedM31; N_BYTES_IN_STATE], lane: usize) -> [u64; N_LANES_KECCAK] {
    let mut words = [0u64; N_LANES_KECCAK];
    for (w, word) in words.iter_mut().enumerate() {
        let mut value = 0u64;
        for byte_idx in 0..N_BYTES_IN_U64 {
            let idx = w * N_BYTES_IN_U64 + byte_idx;
            let byte = state[idx].to_array()[lane].0 as u64;
            value |= byte << (8 * byte_idx);
        }
        *word = value;
    }
    words
}

fn store_lane_words(
    state: &mut [PackedM31; N_BYTES_IN_STATE],
    lane: usize,
    words: &[u64; N_LANES_KECCAK],
) {
    for (w, &value) in words.iter().enumerate() {
        for byte_idx in 0..N_BYTES_IN_U64 {
            let idx = w * N_BYTES_IN_U64 + byte_idx;
            let mut lanes = state[idx].to_array();
            lanes[lane] = M31::from(((value >> (8 * byte_idx)) & 0xFF) as u32);
            state[idx] = PackedM31::from_array(lanes);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spread_round_trips_and_is_carry_free() {
        for b in 0u32..256 {
            let s = spread_u32(b);
            assert_eq!(unspread_u32(s), b, "round trip byte {b:#x}");
            // Every base-4 digit of a spread value is 0 or 1.
            for i in 0..8 {
                assert!((s >> (2 * i)) & 0b11 <= 1, "digit {i} of spread({b:#x})");
            }
        }
        assert_eq!(SPREAD_MAX, spread_u32(0xFF));
        // Sum of three spread bytes stays carry-free: each slot ≤ 3.
        let s = spread_u32(0xFF) + spread_u32(0xFF) + spread_u32(0xFF);
        for i in 0..8 {
            assert_eq!((s >> (2 * i)) & 0b11, 3, "triple-sum slot {i} == 3");
        }
        assert_eq!(s, (1 << 16) - 1, "3·spread(0xFF) fills the dense key space");
    }
}
