//! Range-check LogUp components for the P-256 AIR.
//!
//! ## Soundness
//!
//! Every range table shares one [`RangeCheckRelation`] type, but each
//! table draws an independent instance from the Fiat-Shamir channel. The
//! independent LogUp randomness keeps tables disjoint: a use against a
//! Range7 instance can only be balanced by a provide against the same
//! instance.
//!
//! Pair each relation instance with **exactly one** provider component.
//! The LogUp sum is balanced across every use and every provide of the
//! same relation: a missing provider leaves the proof unbalanced, and a
//! duplicated provider lets the prover over-account multiplicities.
//!
//! ## Phases
//!
//! - [`component`] — constraints emitted by each provider.
//! - [`trace`]     — preprocessed and multiplicity columns.
//! - [`interaction`] — LogUp interaction column and the provider's piece
//!   of the global LogUp identity.

pub mod component;
pub mod interaction;
pub mod trace;

pub use component::{
    RangeCheckComponent, RangeCheckEval, SignedCarryRangeComponent, SignedCarryRangeEval,
};
pub use interaction::{
    batching_with_solo, consecutive_batching, write_batched_logup_columns,
    write_logup_columns_with_batching, RangeCheckInteractionClaim,
};
pub use trace::{ColumnEval, RangeCheckClaim, SignedCarryRangeClaim};

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{relation, EvalAtRow, RelationEntry};

pub const RANGE13_BITS: u32 = 13;
pub const RANGE16_BITS: u32 = 16;
pub const RANGE11_BITS: u32 = 11;
pub const RANGE9_BITS: u32 = 9;
pub const RANGE7_BITS: u32 = 7;

/// Mersenne-31 modulus `2^31 − 1`.
const M31_MODULUS_I64: i64 = (1i64 << 31) - 1;

/// Largest absolute carry that round-trips through [`encode_signed_carry`]:
/// `M31_MODULUS / 2 = 1_073_741_823`. Outside `[−M31_HALF, M31_HALF]` the
/// encoding wraps modulo `M31_MODULUS` and [`decode_signed_carry`] returns
/// the centered representative, not the original input.
pub const M31_HALF: i64 = M31_MODULUS_I64 / 2;

/// Largest representable trace `log_size`. `log_size = 31` would require a
/// preprocessed value `2^31 − 1`, which is outside M31's representable
/// range.
const MAX_LOG_SIZE: u32 = 30;

relation!(RangeCheckRelation, 1);

pub fn range_check_value_column_id(log_size: u32) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_range{log_size}_value"),
    }
}

pub fn signed_carry_value_column_id(equation_name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_signed_carry_{equation_name}_value"),
    }
}

pub fn signed_carry_active_column_id(equation_name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("p256_signed_carry_{equation_name}_active"),
    }
}

/// Centered M31 encoding of a signed carry. Inputs must satisfy
/// `|carry| ≤ M31_HALF`; outside that range the encoding wraps modulo
/// `M31_MODULUS` and the round-trip with [`decode_signed_carry`] no longer
/// holds.
/// Sum of `1 / denominator_i` with one Montgomery batch inversion
/// (`FieldExpOps::batch_inverse`) instead of one field inversion per term.
/// Callers gate which denominators they collect (numerators are 0/1 booleans),
/// so the result is bit-identical to the naive per-term division.
pub fn batched_inverse_sum(
    denominators: &[stwo::core::fields::qm31::SecureField],
) -> stwo::core::fields::qm31::SecureField {
    use stwo::core::fields::FieldExpOps;
    stwo::core::fields::qm31::SecureField::batch_inverse(denominators)
        .into_iter()
        .sum()
}

pub fn encode_signed_carry(carry: i64) -> M31 {
    assert!(
        (-M31_HALF..=M31_HALF).contains(&carry),
        "carry {carry} outside centered range [-{M31_HALF}, {M31_HALF}]",
    );
    let encoded = if carry >= 0 {
        carry as u32
    } else {
        (M31_MODULUS_I64 + carry) as u32
    };
    M31::from_u32_unchecked(encoded)
}

/// Inverse of [`encode_signed_carry`]: M31 values in the upper half wrap
/// back to their negative carry representative.
pub fn decode_signed_carry(value: M31) -> i64 {
    let v = value.0 as i64;
    if v * 2 <= M31_MODULUS_I64 {
        v
    } else {
        v - M31_MODULUS_I64
    }
}

/// Add a single use of a range check at `value`, weighted by `gate`.
///
/// The LogUp sum on this relation balances iff `value` appears in the
/// table provided by the [`RangeCheckEval`] (or [`SignedCarryRangeEval`])
/// that shares this relation instance. Pass `E::F::one()` as `gate` for an
/// unconditional check.
pub fn add_range_check<E: EvalAtRow>(
    eval: &mut E,
    relation: &RangeCheckRelation,
    gate: E::F,
    value: E::F,
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), &[value]));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinct_log_sizes_get_distinct_preprocessed_column_ids() {
        let widths = [
            RANGE16_BITS,
            RANGE13_BITS,
            RANGE11_BITS,
            RANGE9_BITS,
            RANGE7_BITS,
        ];
        let ids = widths.map(range_check_value_column_id);
        for i in 0..ids.len() {
            for j in (i + 1)..ids.len() {
                assert_ne!(ids[i].id, ids[j].id);
            }
        }
    }

    #[test]
    fn signed_carry_column_ids_namespace_by_equation_and_role() {
        assert_ne!(
            signed_carry_value_column_id("ec_double").id,
            signed_carry_value_column_id("ec_add").id,
        );
        assert_ne!(
            signed_carry_value_column_id("eq").id,
            signed_carry_active_column_id("eq").id,
        );
    }

    #[test]
    fn encode_signed_carry_round_trips() {
        for carry in [-M31_HALF, -1000, -1, 0, 1, 1000, M31_HALF] {
            assert_eq!(decode_signed_carry(encode_signed_carry(carry)), carry);
        }
    }

    #[test]
    fn encode_signed_carry_uses_centered_representation() {
        assert_eq!(encode_signed_carry(0).0, 0);
        assert_eq!(encode_signed_carry(7).0, 7);
        assert_eq!(encode_signed_carry(-1).0, (M31_MODULUS_I64 - 1) as u32);
        assert_eq!(encode_signed_carry(-7).0, (M31_MODULUS_I64 - 7) as u32);
    }

    #[test]
    #[should_panic(expected = "outside centered range")]
    fn encode_signed_carry_panics_above_half() {
        let _ = encode_signed_carry(M31_HALF + 1);
    }
}
