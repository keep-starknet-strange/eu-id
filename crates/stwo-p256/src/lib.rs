#![feature(portable_simd)]

pub mod components;
pub mod constants;
pub mod curve;
#[cfg(test)]
pub mod debug;
pub mod ecdsa {
    pub use crate::reference::ecdsa::*;
}
pub mod field;
pub mod gadgets;
pub mod projective_air {
    pub use crate::components::projective_rcb_mul::*;
}
pub mod proof;
pub mod public_inputs {
    pub use crate::components::public_inputs::*;
}
pub mod public_key_check {
    pub use crate::components::public_key_curve::native::*;
}
pub mod public_key_curve_air {
    pub use crate::components::public_key_curve::air::*;
}
pub mod range_checks;
pub mod reference;
pub mod scalar;
pub mod types;

pub mod limbs {
    pub use crate::field::limbs::*;
}

pub mod field_ops {
    pub use crate::field::ops::*;
}

pub mod fp_solinas {
    pub use crate::field::solinas::native::*;
}

pub mod fp_solinas_air {
    pub use crate::field::solinas::air::*;
}

pub mod projective {
    pub use crate::curve::projective::*;
}

pub mod fake_glv_chain {
    pub use crate::scalar::fake_glv_chain::*;
}

pub mod fake_glv_chain_continuity {
    pub use crate::scalar::fake_glv_chain_continuity::*;
}

pub mod fake_glv_chain_expansion {
    pub use crate::scalar::fake_glv_chain_expansion::*;
}

pub mod fake_glv_chain_schedule {
    pub use crate::scalar::fake_glv_chain_schedule::*;
}

pub mod fake_glv_direct_prepared_operand {
    pub use crate::scalar::fake_glv_direct_prepared_operand::*;
}

pub mod fake_glv_ec_source {
    pub use crate::scalar::fake_glv_ec_source::*;
}

pub mod fake_glv_lsb_correction_operand {
    pub use crate::scalar::fake_glv_lsb_correction_operand::*;
}

pub mod fake_glv_prepared_point_source {
    pub use crate::scalar::fake_glv_prepared_point_source::*;
}

pub mod final_add_air {
    pub use crate::components::final_add::*;
}
pub mod final_check {
    pub use crate::components::final_check::native::*;
}
pub mod final_check_air {
    pub use crate::components::final_check::air::*;
}
pub mod prepared_point {
    pub use crate::scalar::prepared_point::*;
}

pub mod prepared_table {
    pub use crate::scalar::prepared_table::*;
}
