//! Binds the SHA-256 digest to the P256 ECDSA message hash.
//!
//! P256 stores `z` as 20 little-endian 13-bit limbs.
//! SHA-256 yields the digest as 32 big-endian bytes.
//!
//! ## Why a bridge is needed
//!
//! The combined proof must show that `z` equals `SHA-256(C)`.
//! The 8-bit and 13-bit boundaries do not align.
//! Thus, this module converts the P256 limbs to bytes.
//! It consumes these bytes on the shared `Sha256Digest` LogUp relation.
//! The SHA module provides the same relation.
//! The global balance cancels only when both byte strings are equal.
//!
//! ## The recomposition (this file)
//!
//! Treat `z` as a 256-bit integer.
//! Each byte boundary has one unsigned carry.
//! The bytes, limbs, and carries satisfy this base-256 identity:
//!
//! ```text
//! c[k] + limb_term_k = lb[k] + 256·c[k+1],   k = 0..32,   c[0] = c[32] = 0
//! ```
//!
//! Here, `limb_term_k = z_limb[i] · 2^shift` for the limb that starts in byte `k`.
//! Twelve byte positions have no starting limb.
//! The value `13·i / 8` does not repeat a byte.
//! Thus, at most one limb feeds each byte.
//! Each `limb_term_k` is less than `2^20`.
//! Each carry is less than `2^13`.
//!
//! The AIR range-checks each byte to `[0, 256)`.
//! It also range-checks each carry to `[0, 2^13)`.
//! With zero end carries, these checks make the base-256 decomposition unique.
//! The consumer supplies the byte range checks required by `DigestRelation`.
//!
//! [`air`] holds the constraints + LogUp wiring. [`witness`] generates the
//! trace and interaction columns. This `mod.rs` holds the prover-independent
//! recomposition math and its reference tests.

pub mod air;
pub mod module;
pub mod witness;

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::{relation, Relation};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::field::limbs::P256M31BigInt;
use crate::public_inputs::PublicEcdsaInstance;

// P256 provides the `(sig_id, z[20])` relation analytically.
// This bridge consumes the relation.
// A separate relation instance prevents overlap with other P256 channels.
// Thus, the relation binds the bridge limbs to the proven ECDSA value.
relation!(ScalarZRelation, SCALAR_Z_RELATION_ARITY);

/// Shared handle for the `ScalarZRelation`: P256 draws it and `set`s it (the
/// provider half lives in P256's `lookup_sum`, see [`scalar_z_provider_claimed_sum`]).
/// The bridge module reads it back and consumes it.
pub type SharedScalarZRelation = air_core::relations::SharedRelation<ScalarZRelation>;

/// Returns the values for a `ScalarZRelation` lookup.
///
/// The order is `sig_id` followed by 20 little-endian `z` limbs.
pub fn scalar_z_relation_values(
    instance: &PublicEcdsaInstance<M31>,
) -> [M31; SCALAR_Z_RELATION_ARITY] {
    let mut values = [M31::from_u32_unchecked(0); SCALAR_Z_RELATION_ARITY];
    values[0] = instance.sig_id;
    values[1..].copy_from_slice(instance.z.limbs());
    values
}

/// Returns the analytic P256 provider sum for the `z` binding.
///
/// The key is `(sig_id, z[20])`.
/// The sum contains `−1/combine(sig_id, z)` for each public instance.
/// The bridge consumes the opposite term for its committed value.
/// The terms cancel only when the bridge and public values match.
/// The public-input binding already binds the public value to the ECDSA proof.
pub fn scalar_z_provider_claimed_sum(
    instances: &[PublicEcdsaInstance<M31>],
    relation: &ScalarZRelation,
) -> SecureField {
    instances
        .iter()
        .map(|instance| {
            let values = scalar_z_relation_values(instance);
            let denominator: SecureField = relation.combine(&values);
            -SecureField::from(M31::from_u32_unchecked(1)) / denominator
        })
        .sum()
}

// --- Trace column layout (committed in this order, read sequentially by the
// eval, written in the same order by the trace generator) ---

/// Per-signature id, shared with the `(sig_id, z)` binding relation.
pub const COL_SIG_ID: usize = 0;
/// First of the 20 `z` limbs (13-bit, little-endian).
pub const COL_Z_START: usize = COL_SIG_ID + 1;
/// First of the 32 big-endian digest bytes.
pub const COL_BYTES_START: usize = COL_Z_START + N_LIMBS;
/// First of the 31 base-256 carries `c[1..=31]`.
pub const COL_CARRIES_START: usize = COL_BYTES_START + DIGEST_BYTES;
/// Total committed columns of the bridge's main trace.
pub const TOTAL_COLS: usize = COL_CARRIES_START + N_CARRIES;

/// Number of digest bytes carried by the cross-module relation.
///
/// This value equals
/// `stwo_sha256::constants::DIGEST_BYTES`. The 32 bytes are the big-endian
/// serialization of `z` (`U256` order, byte 0 = most-significant), identical to
/// the SHA provider's `h_out_digest_bytes` layout.
pub const DIGEST_BYTES: usize = 32;

/// Committed base-256 carry columns of the recomposition. There is one boundary
/// carry between each adjacent pair of the 32 little-endian byte positions. The
/// two outermost (`c[0]` before byte 0 and `c[32]` after byte 31) are the
/// constant zero, leaving `DIGEST_BYTES − 1` committed carries `c[1..=31]`.
pub const N_CARRIES: usize = DIGEST_BYTES - 1;

/// Arity of the internal `(sig_id, z[20])` binding relation.
///
/// P256 provides the relation, and this bridge consumes it.
pub const SCALAR_Z_RELATION_ARITY: usize = 1 + N_LIMBS;

/// Preprocessed active selector id prefix for digest bridge rows. The concrete
/// id includes log size and active row count because the column contents depend
/// on both public shape parameters.
pub const ACTIVE_PREPROCESSED_ID_PREFIX: &str = "digest_bind_active";

/// Returns the limb and bit shift that start at little-endian byte `k`.
///
/// Byte zero is the least-significant byte of `z`.
/// No two limbs start in the same byte because `gcd(8, 13) = 1`.
/// The function returns `None` for the 12 carry-only positions.
///
/// ```text
/// byte_pos(i) = (LIMB_BITS · i) / 8
/// shift(i) = (LIMB_BITS · i) % 8
/// ```
pub fn limb_feeding_byte(k: usize) -> Option<(usize, u32)> {
    (0..N_LIMBS).find_map(|i| {
        let start = LIMB_BITS * i;
        (start / 8 == k).then_some((i, (start % 8) as u32))
    })
}

/// Computes the byte-bridge witness for `z`.
///
/// The witness contains 32 big-endian digest bytes and 31 unsigned base-256 carries.
///
/// The first returned byte is the most significant byte.
/// This order matches the `Sha256Digest` relation.
pub fn z_digest_byte_witness(z: &P256M31BigInt) -> ([u8; DIGEST_BYTES], [u32; N_CARRIES]) {
    let limbs = z.limbs();
    let mut le_bytes = [0u8; DIGEST_BYTES];
    let mut carries = [0u32; N_CARRIES];
    let mut carry = 0u32;
    for k in 0..DIGEST_BYTES {
        let limb_term = limb_feeding_byte(k).map_or(0, |(i, shift)| limbs[i].0 << shift);
        let acc = carry + limb_term;
        le_bytes[k] = (acc & 0xFF) as u8;
        carry = acc >> 8;
        if k < N_CARRIES {
            carries[k] = carry; // c[k+1]
        }
    }
    debug_assert_eq!(carry, 0, "final base-256 carry must vanish for a 256-bit z");

    // Big-endian (U256 / SHA digest) order: big-endian byte j == little-endian
    // byte 31−j.
    let mut be_bytes = [0u8; DIGEST_BYTES];
    for (j, slot) in be_bytes.iter_mut().enumerate() {
        *slot = le_bytes[DIGEST_BYTES - 1 - j];
    }
    (be_bytes, carries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::U256;

    /// At most one limb starts in any byte, and exactly 20 byte positions are
    /// fed (one per limb). The other 12 are pure carry pass-through.
    #[test]
    fn each_byte_is_fed_by_at_most_one_limb() {
        let mut fed = 0usize;
        let mut seen_limbs = [false; N_LIMBS];
        for k in 0..DIGEST_BYTES {
            if let Some((i, shift)) = limb_feeding_byte(k) {
                fed += 1;
                assert!(!seen_limbs[i], "limb {i} fed two bytes");
                seen_limbs[i] = true;
                assert!(shift < 8);
                assert_eq!(LIMB_BITS * i / 8, k);
            }
        }
        assert_eq!(fed, N_LIMBS, "every limb must feed exactly one byte");
        assert!(seen_limbs.iter().all(|&s| s));
    }

    /// The witnessed bytes are exactly `z`'s big-endian `U256` bytes — the same
    /// order the SHA provider emits — for a spread of values.
    #[test]
    fn bytes_match_u256_big_endian() {
        let cases = [
            U256::ZERO,
            U256::from_le_u64s(&[1, 0, 0, 0]),
            U256::from_le_u64s(&[
                0xDEAD_BEEF_CAFE_BABE,
                0x1234_5678_9ABC_DEF0,
                0xFFFF_FFFF_0000_0001,
                0x0000_0001_FFFF_FFFE,
            ]),
            U256::from_le_u64s(&[u64::MAX, u64::MAX, u64::MAX, u64::MAX]),
        ];
        for val in cases {
            let z = P256M31BigInt::from_u256(&val);
            let (bytes, _carries) = z_digest_byte_witness(&z);
            assert_eq!(
                bytes, val.0,
                "bridge bytes must equal U256 big-endian bytes"
            );
        }
    }

    /// Every carry stays within the `[0, 2^13)` window the AIR range-checks.
    #[test]
    fn carries_fit_range13() {
        let val = U256::from_le_u64s(&[u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
        let z = P256M31BigInt::from_u256(&val);
        let (_bytes, carries) = z_digest_byte_witness(&z);
        for (m, &c) in carries.iter().enumerate() {
            assert!(
                c < (1 << LIMB_BITS),
                "carry c[{}] = {c} exceeds 2^13",
                m + 1
            );
        }
    }

    /// The base-256 recurrence the AIR enforces holds for the witnessed
    /// (bytes, carries) — a direct check of the relation the constraints encode.
    #[test]
    fn recurrence_holds() {
        let val = U256::from_le_u64s(&[
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0xA5A5_5A5A_F0F0_0F0F,
            0x0000_DEAD_BEEF_0000,
        ]);
        let z = P256M31BigInt::from_u256(&val);
        let (be_bytes, carries) = z_digest_byte_witness(&z);
        let limbs = z.limbs();
        for k in 0..DIGEST_BYTES {
            let c_in = if k == 0 { 0 } else { carries[k - 1] };
            let c_out = if k == DIGEST_BYTES - 1 { 0 } else { carries[k] };
            let limb_term = limb_feeding_byte(k).map_or(0, |(i, shift)| limbs[i].0 << shift);
            // lb[k] = big-endian byte 31−k.
            let lb = u32::from(be_bytes[DIGEST_BYTES - 1 - k]);
            assert_eq!(
                c_in + limb_term,
                lb + 256 * c_out,
                "recurrence broken at little-endian byte {k}",
            );
        }
    }
}
