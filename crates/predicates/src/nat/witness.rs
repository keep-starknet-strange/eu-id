use crate::nat::table::gen_blind_multiplicity_column;
use crate::nat::types::{PublicInput, Witness};
use crate::types::Trace;
use crate::utils::random_m31_cell;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

/// Class-C rewrite (Q-015 / p4c): the nationality component is a single-active-
/// row trace with a preprocessed selector. Row 0 holds the real witness; every
/// constraint and lookup use in [`super::eval`] is gated by the preprocessed
/// `active` selector, so the remaining rows are free blind rows filled with
/// fresh random field cells. `LOG_SIZE = 9` gives `511 ≥ 256` blind rows.
const LOG_SIZE: u32 = 9;
const ACTIVE_ROW: usize = 0;

pub struct WitnessData {
    pub witness_trace: Trace,
    pub table_mult_trace: Trace,
    pub nationality: u32,
    /// The two credential nationality byte values `[code_hi, code_lo]`
    /// (big-endian) when the credential binding is wired (`Some`) — the require
    /// tuples the interaction trace emits against the shared `Sha256Field`
    /// channel. `None` for a standalone nationality proof, where
    /// [`witness_trace`](Self::witness_trace) holds only the single base
    /// `nationality` column.
    pub nat_bytes: Option<[u32; 2]>,
}

impl WitnessData {
    pub fn new(witness: &Witness, public: &PublicInput, bind_nat: bool) -> Self {
        // Base + optional binding column values on the active row, in eval-read
        // order. The single-row require selector is now the preprocessed `active`
        // column, so binding no longer contributes a `bind_active` column.
        let mut active_values = vec![witness.nationality];
        if bind_nat {
            active_values.push(witness.nationality >> 8);
            active_values.push(witness.nationality & 0xFF);
        }
        let nat_bytes = bind_nat.then_some([witness.nationality >> 8, witness.nationality & 0xFF]);

        let witness_trace = active_values.into_iter().map(active_column).collect();

        // Class-D blinded accepted-set multiplicity: real count (1) on the used
        // code's row, fresh random on the reserved dummy upper half.
        let table_mult_trace = vec![gen_blind_multiplicity_column(public, witness.nat_index)];

        Self {
            witness_trace,
            table_mult_trace,
            nationality: witness.nationality,
            nat_bytes,
        }
    }

    pub fn log_size() -> u32 {
        LOG_SIZE
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.witness_trace.clone());
        tb.extend_evals(self.table_mult_trace.clone());
    }
}

/// A column that holds `active_value` on [`ACTIVE_ROW`] and a fresh uniform
/// random field cell on every other row. The random inactive cells are the
/// Class-C blind rows: the eval gates every witness-touching constraint off the
/// preprocessed `active` selector, so those rows are unconstrained and mask the
/// column's proof-side openings.
fn active_column(
    active_value: u32,
) -> CircleEvaluation<SimdBackend, M31, stwo::prover::poly::BitReversedOrder> {
    let domain = CanonicCoset::new(LOG_SIZE).circle_domain();
    let mut data: Vec<M31> = (0..1usize << LOG_SIZE).map(|_| random_m31_cell()).collect();
    data[ACTIVE_ROW] = M31::from_u32_unchecked(active_value);
    CircleEvaluation::new(domain, BaseColumn::from_iter(data))
}

#[cfg(test)]
mod class_c_tests {
    use super::*;
    use stwo::prover::backend::simd::m31::N_LANES;

    fn test_public() -> PublicInput {
        PublicInput::new(vec![276, 250, 300])
    }

    fn test_witness() -> Witness {
        // DE=276 is the second entry in the sorted set [250, 276, 300].
        Witness {
            public: test_public(),
            nationality: 276,
            nat_index: 1,
        }
    }

    fn trace_fingerprint(trace: &Trace) -> Vec<[M31; N_LANES]> {
        trace
            .iter()
            .flat_map(|column| column.values.data.iter().map(|packed| packed.to_array()))
            .collect()
    }

    /// Class-C: `LOG_SIZE = 9` leaves `511 ≥ 256` blind rows past the single
    /// active row (the Q-015 blind budget).
    #[test]
    fn nat_class_c_has_at_least_256_blind_rows() {
        let blind_rows = (1usize << WitnessData::log_size()) - 1;
        assert!(
            blind_rows >= 256,
            "nat Class-C needs ≥256 blind rows, got {blind_rows}"
        );
    }

    /// Class-C: the inactive (blind) rows carry fresh randomness — non-zero and
    /// different across two witness generations of the same witness.
    #[test]
    fn nat_class_c_inactive_cells_are_fresh_per_trace() {
        let witness = test_witness();
        let public = test_public();
        let first = trace_fingerprint(&WitnessData::new(&witness, &public, false).witness_trace);
        let second = trace_fingerprint(&WitnessData::new(&witness, &public, false).witness_trace);
        let zero = [M31::from_u32_unchecked(0); N_LANES];

        assert!(
            first.iter().any(|value| *value != zero),
            "nat blind rows are still all zero"
        );
        assert_ne!(
            first, second,
            "nat inactive cells must be fresh per trace (differ across two generations)"
        );
    }
}
