//! `msglink` — the message-byte producer for `M`'s bytes (M6 composed statement).
//!
//! The µ chain absorbs `tr ‖ 0x00 ‖ 0x00 ‖ M`. This component is the LogUp
//! *producer* of `M`'s bytes: it yields one [`MsgLinkRelation`]
//! `(field_id, byte_index, byte)` per message byte. The bytes are PUBLIC Eval
//! constants (the verifier constructs this Eval from the public message, exactly
//! like `stwo_keccak::sponge::io_provider` pins its message), so the yielded
//! tuples are pinned to the real `M` — no committed byte cell to forge and no
//! range check needed (a constant `u8` is a byte by construction).
//!
//! ## Hosted SHA producer compatibility
//!
//! stwo-sha256's `FieldExposure` producer already yields arbitrary multi-block
//! `(field_id, byte_index, byte)` windows of the SHA-256 preimage, per-byte
//! range-checked in-AIR (see `crates/stwo-sha256/src/field_exposure.rs`).
//! [`MsgLinkRelation`] deliberately mirrors that exact tuple shape so hosted
//! proofs can use the SHA-side producer as the yield source with no relation or
//! consumer change; the µ-absorb bridge (the consumer) stays the same.
//!
//! Layout: a single packed row (`LOG_N_LANES`), lane-0 enabler; one relation
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

/// The single `field_id` tag M's bytes are yielded under. M is one contiguous
/// window; hosted SHA producers use their own field ids and are mapped by the bridge.
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

#[derive(Clone)]
pub struct MsgLinkEval {
    /// The PUBLIC message bytes (both sides construct from the public input).
    pub message: Vec<u8>,
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

/// Interaction trace: one `+enabler / combine(tuple)` fraction per byte, paired
/// two-per-column (mirrors `io_provider::generate_interaction_trace`).
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
