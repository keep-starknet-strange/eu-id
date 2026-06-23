use crate::nat::types::{PublicInput, Witness};
use crate::types::Trace;
use crate::utils::push_repeated_column;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

pub struct WitnessData {
    pub witness_trace: Trace,
    pub table_mult_trace: Trace,
    pub nationality: u32,
    #[allow(dead_code)]
    pub nat_index: usize,
    /// The two credential nationality byte values `[code_hi, code_lo]` (big-endian)
    /// when the credential binding is wired (`Some`) — the require tuples the
    /// interaction trace emits against the shared `Sha256Field` channel. `None`
    /// for a standalone nationality proof, where
    /// [`witness_trace`](Self::witness_trace) holds only the single base
    /// `nationality` column.
    pub nat_bytes: Option<[u32; 2]>,
}

/// Trace column index of the single-row binding selector `bind_active` (the
/// second column, right after the base `nationality` column). Only present when
/// the binding is wired; the interaction trace reads it as the require numerator.
pub const BIND_ACTIVE_COL: usize = 1;

impl WitnessData {
    pub fn new(witness: &Witness, public: &PublicInput, bind_nat: bool) -> Self {
        let acceptable_nats_log_size = public.log_size();

        let mut witness_trace = Vec::new();
        push_repeated_column(&mut witness_trace, witness.nationality, LOG_N_LANES);

        // The credential-field binding columns (slots 1..4). `bind_active`
        // selects the single row whose nationality-byte requires fire;
        // `code_hi`/`code_lo` are the big-endian nationality bytes the
        // reconciliation constraint ties to the packed `nationality`. Repeated so
        // the always-on reconciliation holds on every row; the global LogUp
        // balance forces the selected row's bytes to the credential's signed
        // bytes. Big-endian recomposition matches `Credential::encode` (the u16
        // nationality is `code_hi · 256 + code_lo`) — the same two bytes SHA
        // yields for the nationality window (`docs/credential-format.md`).
        if bind_nat {
            push_single_active(&mut witness_trace, LOG_N_LANES);
            push_repeated_column(&mut witness_trace, witness.nationality >> 8, LOG_N_LANES);
            push_repeated_column(&mut witness_trace, witness.nationality & 0xFF, LOG_N_LANES);
        }
        let nat_bytes = bind_nat.then_some([witness.nationality >> 8, witness.nationality & 0xFF]);

        let mut mult_data = vec![M31::zero(); 1 << acceptable_nats_log_size];
        mult_data[witness.nat_index] = M31::from_u32_unchecked(1 << LOG_N_LANES);
        let table_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(acceptable_nats_log_size).circle_domain(),
            BaseColumn::from_iter(mult_data),
        )];

        Self {
            witness_trace,
            table_mult_trace,
            nationality: witness.nationality,
            nat_index: witness.nat_index,
            nat_bytes,
        }
    }

    pub fn log_size() -> u32 {
        LOG_N_LANES
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.witness_trace.clone());
        tb.extend_evals(self.table_mult_trace.clone());
    }
}

/// A column that is `1` on exactly one row and `0` on the rest — the
/// credential-field binding single-row require selector. Any single fixed row
/// works: the nat witness repeats its columns across all rows, and the boolean
/// constraint plus the cross-module balance force this column to fire once with
/// the credential's bytes.
fn push_single_active(
    columns: &mut Vec<CircleEvaluation<SimdBackend, M31, stwo::prover::poly::BitReversedOrder>>,
    log_size: u32,
) {
    let domain = CanonicCoset::new(log_size).circle_domain();
    let mut data = vec![M31::zero(); 1 << log_size];
    data[0] = M31::from_u32_unchecked(1);
    columns.push(CircleEvaluation::new(domain, BaseColumn::from_iter(data)));
}
