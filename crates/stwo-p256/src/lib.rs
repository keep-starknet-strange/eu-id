#![feature(portable_simd)]

pub mod constants;
pub mod curve;
pub mod debug;
pub mod ecdsa;
pub mod field_ops;
pub mod limbs;
pub mod public_inputs;
pub mod range_checks;
pub mod scalar;
pub mod types;

pub mod canonical_lt {
    pub use crate::scalar::canonical_lt::*;
}

pub mod cert_bind {
    pub use crate::scalar::cert_bind::*;
}

pub mod fake_glv_scalar {
    pub use crate::scalar::fake_glv_scalar::*;
}

pub mod fake_glv_selector {
    pub use crate::scalar::fake_glv_selector::*;
}

pub mod scalar_setup_air {
    pub use crate::scalar::setup_air::*;
}

pub mod scalar_setup_witness {
    pub use crate::scalar::setup_witness::*;
}
