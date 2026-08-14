//! Constraint side of the digest-bind bridge.
//!
//! [`DigestBindEval`] recomposes message hash `z` from 32 big-endian bytes.
//! It range-checks each byte and carry.
//! The combined proof consumes the bytes on the shared `Sha256Digest` channel.
//! The SHA provider supplies the opposite relation term.

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};
use stwo_p256_utils::constants::N_LIMBS;

use air_core::relations::DigestBytesRelation;

use crate::range_checks::{add_range_check, RangeCheckRelation};

use super::{
    limb_feeding_byte, ScalarZRelation, ACTIVE_PREPROCESSED_ID_PREFIX, DIGEST_BYTES, N_CARRIES,
    SCALAR_Z_RELATION_ARITY,
};

/// The four LogUp channels the bridge consumes, plus the cross-module digest
/// gate. The two range channels are balanced inside this bridge module (their
/// provider components live here). The `(sig_id, z)` channel is balanced by
/// P256's analytic provider term ([`super::scalar_z_provider_claimed_sum`]).
/// Only the `digest` channel is truly cross-module — its provider is the SHA
/// module.
#[derive(Clone, Debug)]
pub struct DigestBindEval {
    pub log_size: u32,
    pub active_rows: usize,
    /// `[0, 256)` table — pins every digest byte.
    pub range8: RangeCheckRelation,
    /// `[0, 2^13)` table — pins every base-256 carry.
    pub range13: RangeCheckRelation,
    /// `(sig_id, z[20])` — consumed here, balanced by P256's analytic provider
    /// term ([`super::scalar_z_provider_claimed_sum`]).
    pub scalar_z: ScalarZRelation,
    /// The shared cross-module digest channel. Must be combined over the SAME
    /// `LookupElements` the SHA provider yields with (injected via the shared
    /// handle). Only *used* when `expose_digest` is set.
    pub digest: DigestBytesRelation,
    /// Whether to emit the cross-module digest require (combined path). Off for
    /// a standalone P256 proof, so the bridge stays internally balanced.
    pub expose_digest: bool,
}

pub(super) fn active_col_id(log_size: u32, active_rows: usize) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("{ACTIVE_PREPROCESSED_ID_PREFIX}_{log_size}_{active_rows}"),
    }
}

impl FrameworkEval for DigestBindEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Recomposition is degree 2. Pair-batched LogUp columns multiply two
        // linear denominators, so their constraints stay within the standard
        // `log_size + 1` budget.
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let zero = E::F::from(M31::from_u32_unchecked(0));
        let two_pow_8 = E::F::from(M31::from_u32_unchecked(1 << 8));

        let active = eval.get_preprocessed_column(active_col_id(self.log_size, self.active_rows));
        // Columns, in committed order (see `super::COL_*`).
        let sig_id = eval.next_trace_mask();
        let z: [E::F; N_LIMBS] = core::array::from_fn(|_| eval.next_trace_mask());
        let bytes: [E::F; DIGEST_BYTES] = core::array::from_fn(|_| eval.next_trace_mask());
        let carries: [E::F; N_CARRIES] = core::array::from_fn(|_| eval.next_trace_mask());

        // Base-256 recomposition, one constraint per little-endian byte `k`:
        //   c[k] + limb_term_k − lb[k] − 256·c[k+1] = 0     (gated by `active`)
        // with c[0] = c[32] = 0, lb[k] = big-endian byte 31−k, and limb_term_k
        // the (single) limb whose 13-bit window starts in byte `k`, shifted.
        for k in 0..DIGEST_BYTES {
            let c_in = if k == 0 {
                zero.clone()
            } else {
                carries[k - 1].clone()
            };
            let c_out = if k == DIGEST_BYTES - 1 {
                zero.clone()
            } else {
                carries[k].clone()
            };
            let limb_term = match limb_feeding_byte(k) {
                Some((i, shift)) => {
                    z[i].clone() * E::F::from(M31::from_u32_unchecked(1u32 << shift))
                }
                None => zero.clone(),
            };
            let lb = bytes[DIGEST_BYTES - 1 - k].clone();
            let recurrence = c_in + limb_term - lb - two_pow_8.clone() * c_out;
            eval.add_constraint(active.clone() * recurrence);
        }

        // --- LogUp consumes, in the canonical order the interaction trace
        // replays (range8 bytes, range13 carries, scalar_z, then the optional
        // digest). The digest is emitted last so toggling `expose_digest` only
        // affects the final batched column. ---

        // Range-check every byte to [0, 256) and every carry to [0, 2^13). Gated
        // by `active` so padding rows contribute no use.
        for byte in &bytes {
            add_range_check(&mut eval, &self.range8, active.clone(), byte.clone());
        }
        for carry in &carries {
            add_range_check(&mut eval, &self.range13, active.clone(), carry.clone());
        }

        // Consume `(sig_id, z[20])` (+active). P256 provides the matching
        // −active term analytically in its claimed sum, binding the bridge's
        // `z` limbs to the proven, public-input-bound `z`.
        let mut scalar_z_values = Vec::with_capacity(SCALAR_Z_RELATION_ARITY);
        scalar_z_values.push(sig_id);
        scalar_z_values.extend(z.iter().cloned());
        eval.add_to_relation(RelationEntry::base(
            &self.scalar_z,
            active.clone(),
            &scalar_z_values,
        ));

        // Cross-module digest require: consume the 32 bytes (+active), the exact
        // counterpart of the SHA provider's −is_last_block yield over the same
        // relation. It cancels if and only if the byte strings match.
        // Thus, `z = SHA-256(C)`.
        if self.expose_digest {
            eval.add_to_relation(RelationEntry::base(&self.digest, active, &bytes));
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type DigestBindComponent = FrameworkComponent<DigestBindEval>;

/// Returns the number of bridge LogUp lookups for one evaluation.
///
/// The count includes byte checks, carry checks, scalar binding, and an optional digest binding.
pub const fn digest_bind_lookups(expose_digest: bool) -> usize {
    DIGEST_BYTES + N_CARRIES + 1 + if expose_digest { 1 } else { 0 }
}
