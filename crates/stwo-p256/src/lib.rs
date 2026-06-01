#![feature(portable_simd)]

pub mod constants;
pub mod curve;
pub mod debug;
pub mod ecdsa;
pub mod field_ops;
pub mod fp_solinas;
pub mod fp_solinas_air;
pub mod limbs;
pub mod projective;
pub mod projective_air;
pub mod proof;
pub mod public_inputs;
pub mod public_key_check;
pub mod range_checks;
pub mod scalar;
pub mod types;

pub mod canonical_lt {
    pub use crate::scalar::canonical_lt::*;
}

pub mod cert_bind {
    pub use crate::scalar::cert_bind::*;
}

pub mod fake_glv_chain {
    pub use crate::scalar::fake_glv_chain::*;
}

pub mod fake_glv_chain_expansion {
    pub use crate::scalar::fake_glv_chain_expansion::*;
}

pub mod fake_glv_ec_source {
    pub use crate::scalar::fake_glv_ec_source::*;
}

pub mod final_check;
pub mod fake_glv_scalar {
    pub use crate::scalar::fake_glv_scalar::*;
}

pub mod fake_glv_selector {
    pub use crate::scalar::fake_glv_selector::*;
}

pub mod fake_glv_selector_lookup {
    pub use crate::scalar::fake_glv_selector_lookup::*;
}

pub mod prepared_point {
    pub use crate::scalar::prepared_point::*;
}

pub mod prepared_table {
    pub use crate::scalar::prepared_table::*;
}

pub mod scalar_setup_air {
    pub use crate::scalar::setup_air::*;
}

pub mod scalar_setup_witness {
    pub use crate::scalar::setup_witness::*;
}
