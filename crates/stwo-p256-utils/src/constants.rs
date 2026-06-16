//! Limb-width constants shared between the AIR and the Solinas reduction.

/// Width of one big-integer limb in bits. With `N_LIMBS = 20`, a single limb
/// product `(2^13 − 1)^2` summed over 20 convolution terms equals
/// `20 · (2^13 − 1)^2 < 2^31`, fitting M31.
pub const LIMB_BITS: usize = 13;

/// Number of limbs per 256-bit value. `20 · 13 = 260 ≥ 256`.
pub const N_LIMBS: usize = 20;
