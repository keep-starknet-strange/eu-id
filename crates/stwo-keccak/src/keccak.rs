//! Keccak-f[1600] permutation boundary witness generation.
//!
//! The carrier uses one input boundary and one output boundary for each of the
//! 24 rounds. This module computes those 25 boundary states. It does not
//! define an AIR component.

use num_traits::Zero;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use stwo::core::fields::m31::M31;
use stwo::prover::backend::simd::m31::PackedM31;

use crate::constants::{N_BYTES_IN_STATE, N_ROUNDS};
use crate::utils::{spread_u32, unspread_u32};

const BOUNDARIES_PER_PERMUTATION: usize = N_ROUNDS + 1;

/// One spread-form permutation boundary.
pub struct BoundaryRow {
    pub perm_id: M31,
    pub state: [M31; N_BYTES_IN_STATE],
}

/// The boundary rows for all requested permutations.
pub struct BoundaryWitness {
    pub n_perms: usize,
    pub rows: Vec<BoundaryRow>,
}

/// Generate the 25 scalar boundary rows for each permutation.
///
/// Each input is `[spread_state(200) | permutation_id]`. Lane zero contains
/// the scalar witness value.
pub fn generate_boundary_witness(
    perm_inputs: &[[PackedM31; N_BYTES_IN_STATE + 1]],
) -> BoundaryWitness {
    let n_perms = perm_inputs.len();
    let per_permutation_rows: Vec<Vec<BoundaryRow>> = perm_inputs
        .par_iter()
        .map(|input| {
            let perm_id = input[N_BYTES_IN_STATE].to_array()[0];
            let mut bytes = [0u8; N_BYTES_IN_STATE];
            let mut spread = [M31::zero(); N_BYTES_IN_STATE];
            for byte in 0..N_BYTES_IN_STATE {
                spread[byte] = input[byte].to_array()[0];
                bytes[byte] = unspread_u32(spread[byte].0) as u8;
            }

            let mut rows = Vec::with_capacity(BOUNDARIES_PER_PERMUTATION);
            rows.push(BoundaryRow {
                perm_id,
                state: spread,
            });
            for round in 0..N_ROUNDS {
                apply_round(&mut bytes, round);
                let state = std::array::from_fn(|byte| M31::from(spread_u32(bytes[byte] as u32)));
                rows.push(BoundaryRow { perm_id, state });
            }
            rows
        })
        .collect();

    let rows: Vec<BoundaryRow> = per_permutation_rows.into_iter().flatten().collect();
    debug_assert_eq!(rows.len(), n_perms * BOUNDARIES_PER_PERMUTATION);
    BoundaryWitness { n_perms, rows }
}

fn apply_round(state: &mut [u8; N_BYTES_IN_STATE], round: usize) {
    let mut packed: [PackedM31; N_BYTES_IN_STATE] =
        std::array::from_fn(|byte| PackedM31::from(M31::from(state[byte] as u32)));
    crate::utils::keccak_f1600_round(&mut packed, round);
    for byte in 0..N_BYTES_IN_STATE {
        state[byte] = packed[byte].to_array()[0].0 as u8;
    }
}
