//! `msglink` produces the public message bytes for a composed statement.
//!
//! The µ chain absorbs `tr ‖ 0x00 ‖ 0x00 ‖ M`. This component yields one
//! [`MsgLinkRelation`] tuple `(field_id, byte_index, byte)` for each byte in
//! `M`. The verifier builds the evaluation from the public message. Thus, the
//! tuples are fixed public constants and do not need a byte range check.
//!
//! ## Hosted message source
//!
//! The public-message path uses [`MsgLinkRelation`]. The hosted path uses a
//! `FieldBytesRelation`. Both relations contain
//! `(field_id, byte_index, byte)`, so the µ bridge can consume either source.
//!
//! The layout uses one packed row (`LOG_N_LANES`) and enables lane 0. One relation
//! entry per message byte. Every constraint degree ≤ 2 (enabler boolean +
//! degree-0 constant tuples), bound = log_size + 1.

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES, N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::air_util::{col_eval, m31, ColEval};
use crate::binding::MsgLinkRelation;

/// Field identifier for the public message bytes.
pub const MSG_FIELD_ID: u32 = 0;

/// The component's fixed log-size: one packed row, lane 0 active.
pub const MSGLINK_LOG_SIZE: u32 = LOG_N_LANES;

/// Base columns: the lane-0 enabler only.
pub const N_BASE_COLS: usize = 1;

/// Interaction columns: one paired fraction column (QM31 = 4 M31 cols) per two
/// message bytes (`finalize_logup_in_pairs`).
pub fn n_interaction_cols(msg_len: usize) -> usize {
    msg_len.div_ceil(2) * SECURE_EXTENSION_DEGREE
}

/// Lane-0 enabler (1 on lane 0, 0 elsewhere) — a single logical instance.
fn lane0_enabler() -> PackedM31 {
    let mut lanes = [M31::from_u32_unchecked(0); N_LANES];
    lanes[0] = M31::from_u32_unchecked(1);
    PackedM31::from_array(lanes)
}

/// Base trace: the lane-0 enabler column.
pub fn gen_msglink_base_trace() -> Vec<ColEval> {
    let rows = 1usize << MSGLINK_LOG_SIZE;
    let mut enabler = vec![m31(0); rows];
    enabler[0] = m31(1);
    vec![col_eval(MSGLINK_LOG_SIZE, enabler)]
}

/// AIR evaluator for the public-message byte producer.
#[derive(Clone)]
pub struct MsgLinkEval {
    /// The public message bytes that both sides construct from the public input.
    pub message: Vec<u8>,
    /// The message-byte relation this component yields into.
    pub msglink: MsgLinkRelation,
}

impl FrameworkEval for MsgLinkEval {
    fn log_size(&self) -> u32 {
        MSGLINK_LOG_SIZE
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        MSGLINK_LOG_SIZE + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = eval.next_trace_mask();
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_constraint(enabler.clone() * (one - enabler.clone()));
        let en = E::EF::from(enabler);
        // Yield (+en) each public message byte: (MSG_FIELD_ID, i, M[i]).
        for (i, &b) in self.message.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.msglink,
                en.clone(),
                &[
                    E::F::from(m31(MSG_FIELD_ID)),
                    E::F::from(m31(i as u32)),
                    E::F::from(m31(b as u32)),
                ],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Interaction trace with one positive fraction per byte and two fractions per
/// column.
pub fn gen_msglink_interaction(
    message: &[u8],
    msglink: &MsgLinkRelation,
) -> (Vec<ColEval>, SecureField) {
    let mut gen = LogupTraceGenerator::new(MSGLINK_LOG_SIZE);
    let en = PackedQM31::from(lane0_enabler());
    let fracs: Vec<(PackedQM31, PackedQM31)> = message
        .iter()
        .enumerate()
        .map(|(i, &b)| {
            let tuple = [
                PackedM31::from(m31(MSG_FIELD_ID)),
                PackedM31::from(m31(i as u32)),
                PackedM31::from(m31(b as u32)),
            ];
            (en, msglink.combine(&tuple))
        })
        .collect();
    let mut i = 0;
    while i + 2 <= fracs.len() {
        let mut col = gen.new_col();
        let (n0, d0) = fracs[i];
        let (n1, d1) = fracs[i + 1];
        col.write_frac(0, n0 * d1 + n1 * d0, d0 * d1);
        col.finalize_col();
        i += 2;
    }
    if i < fracs.len() {
        let mut col = gen.new_col();
        let (n, d) = fracs[i];
        col.write_frac(0, n, d);
        col.finalize_col();
    }
    gen.finalize_last()
}
