//! Prover-side trace generation for the range-check providers.

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use stwo::{
    core::{
        channel::Channel,
        fields::m31::M31,
        poly::circle::CanonicCoset,
        utils::{bit_reverse_index, coset_index_to_circle_domain_index},
    },
    prover::{
        backend::simd::{column::BaseColumn, SimdBackend},
        poly::{circle::CircleEvaluation, BitReversedOrder},
    },
};

use super::{encode_signed_carry, M31_HALF, MAX_LOG_SIZE};

pub type ColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

/// Wrap an iterator of `2^log_size` M31 values in a bit-reversed
/// CircleEvaluation. Centralizing this call keeps the caller out of the
/// `CanonicCoset`/`BaseColumn` boilerplate and rules out domain/order
/// drift between providers.
fn column_eval(log_size: u32, values: impl IntoIterator<Item = M31>) -> ColumnEval {
    let values = coset_order_to_circle_domain_order(log_size, values);
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(values),
    )
}

fn coset_order_to_circle_domain_order(
    log_size: u32,
    values: impl IntoIterator<Item = M31>,
) -> Vec<M31> {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

/// Prover-side claim for a [`super::RangeCheckEval`] provider.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeCheckClaim {
    pub log_size: u32,
}

impl RangeCheckClaim {
    pub fn new(log_size: u32) -> Self {
        assert!(
            log_size <= MAX_LOG_SIZE,
            "log_size {log_size} exceeds maximum {MAX_LOG_SIZE}",
        );
        Self { log_size }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    /// Preprocessed column `[0, 1, …, 2^log_size − 1]`.
    pub fn gen_preprocessed_column(&self) -> ColumnEval {
        let size = 1u32 << self.log_size;
        column_eval(self.log_size, (0..size).map(M31::from_u32_unchecked))
    }

    /// Multiplicity column: row `v` holds the number of times `v` appears
    /// in `uses`. Panics if any use is outside `[0, 2^log_size)`.
    pub fn gen_multiplicity_trace(&self, uses: impl IntoIterator<Item = M31>) -> ColumnEval {
        let size = 1usize << self.log_size;
        let mut multiplicity = vec![M31::zero(); size];
        for value in uses {
            let idx = value.0 as usize;
            assert!(
                idx < size,
                "range-check use {} exceeds table size 2^{}",
                value.0,
                self.log_size,
            );
            multiplicity[idx] += M31::one();
        }
        column_eval(self.log_size, multiplicity)
    }

    // ---- Class D multiplicity blinding (Q-015 §4b / p4c Class D) ----
    //
    // The committed multiplicity column leaks: each row's count is a function
    // of the private witness bytes, and every proof-side opening of the column
    // is a linear functional over the full domain. Class D extends the table
    // one log larger and fills the new upper half with fresh random
    // multiplicities over RESERVED dummy keys. Per the masking note Case 1,
    // >= 2^log_size uniform blind cells (with the full-rank circle-code opening
    // submatrix) make every opening of the column uniform, masking the real
    // lower-half counts. The dummy keys `[2^log_size, 2^(log_size+1))` are
    // UNREACHABLE by honest consumers, which only ever emit values proven
    // `< 2^log_size`, so soundness is unaffected; balance is preserved by the
    // intra-component cancelling `+is_dummy*mult` emit in the eval.

    /// `log_size + 1`: the committed row count of the Class-D blinded table.
    pub fn blind_log_size(&self) -> u32 {
        self.log_size + 1
    }

    /// Class-D preprocessed value column `[0, 1, ..., 2^(log_size+1) - 1]`. The
    /// lower half is the real range `[0, 2^log_size)`; the upper half is the
    /// reserved dummy keys `[2^log_size, 2^(log_size+1))`.
    pub fn gen_blind_preprocessed_column(&self) -> ColumnEval {
        let size = 1u32 << self.blind_log_size();
        column_eval(
            self.blind_log_size(),
            (0..size).map(M31::from_u32_unchecked),
        )
    }

    /// Class-D preprocessed `is_dummy` selector: `0` over the real lower half,
    /// `1` over the dummy upper half.
    pub fn gen_blind_dummy_column(&self) -> ColumnEval {
        let real = 1usize << self.log_size;
        let size = 1usize << self.blind_log_size();
        column_eval(
            self.blind_log_size(),
            (0..size).map(|i| if i < real { M31::zero() } else { M31::one() }),
        )
    }

    /// Class-D multiplicity column: real counts over the lower half, fresh
    /// random blind cells over the dummy upper half. The dummy cells are the
    /// mask; the eval's `+is_dummy*mult` term makes any value there balance.
    pub fn gen_blind_multiplicity_trace(
        &self,
        uses: impl IntoIterator<Item = M31>,
        mut rng: impl FnMut() -> M31,
    ) -> ColumnEval {
        let real = 1usize << self.log_size;
        let size = 1usize << self.blind_log_size();
        let mut multiplicity = vec![M31::zero(); size];
        for value in uses {
            let idx = value.0 as usize;
            assert!(
                idx < real,
                "range-check use {} exceeds table size 2^{}",
                value.0,
                self.log_size,
            );
            multiplicity[idx] += M31::one();
        }
        for slot in multiplicity.iter_mut().take(size).skip(real) {
            *slot = rng();
        }
        column_eval(self.blind_log_size(), multiplicity)
    }
}

/// Prover-side claim for a [`super::SignedCarryRangeEval`] provider.
#[derive(Clone, Debug)]
pub struct SignedCarryRangeClaim {
    pub log_size: u32,
    pub bound: i64,
    pub equation_name: String,
}

impl SignedCarryRangeClaim {
    /// `new` enforces `0 < bound ≤ M31_HALF` and `2·bound + 1 ≤ 2^log_size`.
    pub fn new(log_size: u32, bound: i64, equation_name: impl Into<String>) -> Self {
        assert!(
            log_size <= MAX_LOG_SIZE,
            "log_size {log_size} exceeds maximum {MAX_LOG_SIZE}",
        );
        assert!(
            (1..=M31_HALF).contains(&bound),
            "bound {bound} must be in (0, M31_HALF]",
        );
        let real_entries = 2u64 * bound as u64 + 1;
        let capacity = 1u64 << log_size;
        assert!(
            real_entries <= capacity,
            "{real_entries} encoded entries exceed table capacity 2^{log_size}",
        );
        Self {
            log_size,
            bound,
            equation_name: equation_name.into(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
        channel.mix_u64(self.bound as u64);
    }

    fn real_entries(&self) -> usize {
        (2 * self.bound + 1) as usize
    }

    /// Preprocessed `value` column: centered M31 encoding of
    /// `[−bound, …, bound]` followed by zeros.
    pub fn gen_value_column(&self) -> ColumnEval {
        let size = 1usize << self.log_size;
        let real = self.real_entries();
        column_eval(
            self.log_size,
            (0..size).map(|i| {
                if i < real {
                    encode_signed_carry(i as i64 - self.bound)
                } else {
                    M31::zero()
                }
            }),
        )
    }

    /// Preprocessed `active` column: `1` over the real rows, `0` over the
    /// padding.
    pub fn gen_active_column(&self) -> ColumnEval {
        let size = 1usize << self.log_size;
        let real = self.real_entries();
        column_eval(
            self.log_size,
            (0..size).map(|i| if i < real { M31::one() } else { M31::zero() }),
        )
    }

    /// Multiplicity column: row `c + bound` holds the count of times the
    /// carry `c` is used. Padding rows stay zero — constraint 2 of
    /// [`super::SignedCarryRangeEval`] requires it. Panics if any use is
    /// outside `[−bound, bound]`.
    pub fn gen_multiplicity_trace(&self, uses: impl IntoIterator<Item = i64>) -> ColumnEval {
        let size = 1usize << self.log_size;
        let mut multiplicity = vec![M31::zero(); size];
        for carry in uses {
            assert!(
                (-self.bound..=self.bound).contains(&carry),
                "use carry {carry} outside [-{}, {}]",
                self.bound,
                self.bound,
            );
            let row = (carry + self.bound) as usize;
            multiplicity[row] += M31::one();
        }
        column_eval(self.log_size, multiplicity)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_check_preprocessed_column_has_2_pow_log_size_rows() {
        let column = RangeCheckClaim::new(5).gen_preprocessed_column();
        assert_eq!(column.domain.log_size(), 5);
        assert_eq!(column.domain.size(), 1 << 5);
    }

    #[test]
    fn range_check_multiplicity_trace_has_2_pow_log_size_rows() {
        let trace =
            RangeCheckClaim::new(4).gen_multiplicity_trace((0..3).map(M31::from_u32_unchecked));
        assert_eq!(trace.domain.size(), 1 << 4);
    }

    #[test]
    #[should_panic(expected = "exceeds table size")]
    fn range_check_multiplicity_panics_on_out_of_range_use() {
        let _ = RangeCheckClaim::new(3).gen_multiplicity_trace([M31::from_u32_unchecked(8)]);
    }

    #[test]
    #[should_panic(expected = "exceeds maximum")]
    fn range_check_claim_panics_on_log_size_above_max() {
        let _ = RangeCheckClaim::new(MAX_LOG_SIZE + 1);
    }

    #[test]
    #[should_panic(expected = "exceed table capacity")]
    fn signed_carry_claim_rejects_overflow() {
        let _ = SignedCarryRangeClaim::new(2, 5, "test");
    }

    #[test]
    #[should_panic(expected = "outside")]
    fn signed_carry_multiplicity_panics_outside_bound() {
        let _ = SignedCarryRangeClaim::new(4, 3, "eq").gen_multiplicity_trace([4i64]);
    }

    #[test]
    fn signed_carry_value_column_pads_to_power_of_two() {
        assert_eq!(
            SignedCarryRangeClaim::new(4, 3, "eq")
                .gen_value_column()
                .domain
                .size(),
            16,
        );
    }

    #[test]
    fn signed_carry_active_column_pads_to_power_of_two() {
        assert_eq!(
            SignedCarryRangeClaim::new(4, 3, "eq")
                .gen_active_column()
                .domain
                .size(),
            16,
        );
    }
}
