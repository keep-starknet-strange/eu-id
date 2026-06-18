pub mod digest_bind;
pub mod fake_glv;
pub mod final_add;
pub mod final_check;
pub mod gamma_digest;
pub mod hinted_mul;
pub mod projective_rcb_mul;
pub mod public_inputs;
pub mod public_key_curve;
pub mod scalar_mod_mul;
pub mod scalar_setup;

use serde::{Deserialize, Serialize};
use stwo::core::{channel::Channel, fields::m31::M31, fields::qm31::SecureField};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComponentInteractionClaim {
    pub claimed_sum: SecureField,
}

impl ComponentInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: SecureField::from(M31::from_u32_unchecked(0)),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}
