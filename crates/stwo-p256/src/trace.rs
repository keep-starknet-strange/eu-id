use stwo::core::fields::m31::BaseField;

use stwo_p256_utils::constants::N_LIMBS;

use crate::ecdsa::EcdsaVerifyWitness;

/// Number of columns for a single modular multiplication witness in the trace.
/// Layout: a (N_LIMBS) + b (N_LIMBS) + result (N_LIMBS) + quotient (N_LIMBS) + carries (2*N_LIMBS)
pub const MUL_MOD_COLS: usize = 6 * N_LIMBS;

/// Number of columns for a single modular add/sub witness.
/// Layout: a (N_LIMBS) + b (N_LIMBS) + result (N_LIMBS) + flag (1) + carries (N_LIMBS + 1)
pub const ADD_SUB_MOD_COLS: usize = 3 * N_LIMBS + 1 + N_LIMBS + 1;

/// Placeholder: will generate a full Stwo execution trace from an ECDSA verification witness.
///
/// The trace encodes every intermediate value of the computation as M31 columns
/// so that the AIR constraints can enforce correctness.
///
/// This is the next major implementation target.
pub fn generate_ecdsa_trace(
    _witness: &EcdsaVerifyWitness,
    _log_n_rows: u32,
) -> Vec<Vec<BaseField>> {
    todo!("Trace generation from ECDSA witness - next implementation step")
}
