use num_traits::Zero;
use stwo::core::{
    channel::Channel,
    fields::qm31::{SecureField, QM31},
};

use crate::range_checks::RangeCheckInteractionClaim;

#[derive(Clone, Debug)]
pub struct ScalarModMulInteractionClaim {
    pub canonical_scalars: SecureField,
    pub ab_chunks: SecureField,
    pub qn_chunks: SecureField,
    pub accumulators: SecureField,
    pub reduction_digits: SecureField,
}

impl ScalarModMulInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.canonical_scalars,
            self.ab_chunks,
            self.qn_chunks,
            self.accumulators,
            self.reduction_digits,
        ]);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarModMulProofSliceInteractionClaim {
    pub scalar_mod_mul: ScalarModMulInteractionClaim,
    pub range13: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
}

impl ScalarModMulProofSliceInteractionClaim {
    pub(crate) fn claimed_sum(&self) -> SecureField {
        self.scalar_mod_mul.canonical_scalars
            + self.scalar_mod_mul.ab_chunks
            + self.scalar_mod_mul.qn_chunks
            + self.scalar_mod_mul.accumulators
            + self.scalar_mod_mul.reduction_digits
            + self.range13.claimed_sum
            + self.signed_carry.claimed_sum
    }
}

pub(crate) fn zero_interaction_claim() -> ScalarModMulProofSliceInteractionClaim {
    let zero = QM31::zero();
    ScalarModMulProofSliceInteractionClaim {
        scalar_mod_mul: ScalarModMulInteractionClaim {
            canonical_scalars: zero,
            ab_chunks: zero,
            qn_chunks: zero,
            accumulators: zero,
            reduction_digits: zero,
        },
        range13: RangeCheckInteractionClaim { claimed_sum: zero },
        signed_carry: RangeCheckInteractionClaim { claimed_sum: zero },
    }
}
