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

/// Class-C nationality trace. The complete signed array occupies a
/// transcript-bound active prefix of at most 256 rows. Every remaining cell is
/// freshly randomized, so the fixed log-9 domain always leaves at least 256
/// blind rows.
const LOG_SIZE: u32 = 9;

pub struct WitnessData {
    pub witness_trace: Trace,
    pub table_mult_trace: Trace,
    pub nationalities: Vec<u32>,
    pub accepted: Vec<bool>,
    /// All credential nationality bytes `[code_hi, code_lo]` (big-endian) when
    /// the semantic credential binding is wired.
    pub nat_bytes: Option<Vec<[u32; 2]>>,
}

impl WitnessData {
    pub fn new(witness: &Witness, public: &PublicInput, bind_nat: bool) -> Self {
        assert_eq!(witness.nationalities.len(), witness.accepted.len());
        assert_eq!(witness.nationalities.len(), witness.accepted_rows.len());

        let accepted: Vec<u32> = witness
            .accepted
            .iter()
            .map(|value| u32::from(*value))
            .collect();
        let mut seen_before = Vec::with_capacity(accepted.len());
        let mut seen_after = Vec::with_capacity(accepted.len());
        let mut seen = 0u32;
        for &is_accepted in &accepted {
            seen_before.push(seen);
            seen |= is_accepted;
            seen_after.push(seen);
        }

        // Trace-column order mirrors `NationalityEval`: value, accepted bit,
        // prefix-OR before/after, then optional bound bytes.
        let mut witness_trace = vec![
            active_prefix_column(&witness.nationalities),
            active_prefix_column(&accepted),
            active_prefix_column(&seen_before),
            active_prefix_column(&seen_after),
        ];
        let nat_bytes = bind_nat.then(|| {
            witness
                .nationalities
                .iter()
                .map(|nationality| [nationality >> 8, nationality & 0xFF])
                .collect::<Vec<_>>()
        });
        if let Some(bytes) = &nat_bytes {
            let high: Vec<u32> = bytes.iter().map(|value| value[0]).collect();
            let low: Vec<u32> = bytes.iter().map(|value| value[1]).collect();
            witness_trace.push(active_prefix_column(&high));
            witness_trace.push(active_prefix_column(&low));
        }

        // Class-D table multiplicity counts every accepted signed entry.
        let accepted_rows: Vec<usize> = witness.accepted_rows.iter().flatten().copied().collect();
        let table_mult_trace = vec![gen_blind_multiplicity_column(public, &accepted_rows)];

        Self {
            witness_trace,
            table_mult_trace,
            nationalities: witness.nationalities.clone(),
            accepted: witness.accepted.clone(),
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

/// A column containing the complete active prefix and fresh randomness on all
/// remaining rows. At most 256 entries are active, so at least 256 independent
/// blind rows remain in the fixed log-9 domain.
fn active_prefix_column(
    active_values: &[u32],
) -> CircleEvaluation<SimdBackend, M31, stwo::prover::poly::BitReversedOrder> {
    let domain = CanonicCoset::new(LOG_SIZE).circle_domain();
    let mut data: Vec<M31> = (0..1usize << LOG_SIZE).map(|_| random_m31_cell()).collect();
    for (row, &value) in active_values.iter().enumerate() {
        data[row] = M31::from_u32_unchecked(value);
    }
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
            nationalities: vec![276],
            accepted: vec![true],
            accepted_rows: vec![Some(1)],
        }
    }

    fn trace_fingerprint(trace: &Trace) -> Vec<[M31; N_LANES]> {
        trace
            .iter()
            .flat_map(|column| column.values.data.iter().map(|packed| packed.to_array()))
            .collect()
    }

    /// Class-C: even a maximal 256-entry signed array leaves 256 blind rows.
    #[test]
    fn nat_class_c_has_at_least_256_blind_rows() {
        let blind_rows =
            (1usize << WitnessData::log_size()) - crate::nat::types::MAX_PRESENTED_NATIONALITIES;
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
