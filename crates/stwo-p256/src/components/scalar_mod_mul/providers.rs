use crate::range_checks::{RangeCheckClaim, SignedCarryRangeClaim, RANGE13_BITS};

use super::columns::M31ColumnEval;
use super::layout::ScalarModMulLookupUses;
use super::SCALAR_MOD_MUL_SPLIT_CARRY_BOUND;

pub(crate) const SIGNED_CARRY_EQUATION: &str = "scalar_mod_mul_reduction";

#[derive(Clone, Debug)]
pub(crate) struct LookupProviderClaims {
    pub(crate) range13: RangeCheckClaim,
    pub(crate) signed_carry: SignedCarryRangeClaim,
}

impl LookupProviderClaims {
    pub(crate) fn scalar_mod_mul() -> Self {
        Self {
            range13: RangeCheckClaim::new(RANGE13_BITS),
            signed_carry: SignedCarryRangeClaim::new(
                signed_carry_log_size(SCALAR_MOD_MUL_SPLIT_CARRY_BOUND),
                SCALAR_MOD_MUL_SPLIT_CARRY_BOUND,
                SIGNED_CARRY_EQUATION,
            ),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct LookupProviderTraces {
    pub(crate) range13_multiplicity: M31ColumnEval,
    pub(crate) signed_carry_multiplicity: M31ColumnEval,
    pub(crate) range13_value: M31ColumnEval,
    pub(crate) signed_carry_value: M31ColumnEval,
    pub(crate) signed_carry_active: M31ColumnEval,
}

impl LookupProviderTraces {
    pub(crate) fn from_uses(claims: &LookupProviderClaims, uses: ScalarModMulLookupUses) -> Self {
        Self {
            range13_multiplicity: claims.range13.gen_multiplicity_trace(uses.range13),
            signed_carry_multiplicity: claims
                .signed_carry
                .gen_multiplicity_trace(uses.signed_carry),
            range13_value: claims.range13.gen_preprocessed_column(),
            signed_carry_value: claims.signed_carry.gen_value_column(),
            signed_carry_active: claims.signed_carry.gen_active_column(),
        }
    }
}

fn signed_carry_log_size(bound: i64) -> u32 {
    (2 * bound as u64 + 1).next_power_of_two().ilog2()
}
