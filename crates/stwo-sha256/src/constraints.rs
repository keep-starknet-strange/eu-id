//! AIR evaluator for the SHA-256 component.
//!
//! Implements [`FrameworkEval`] for the one-row-per-block layout defined in
//! [`crate::trace`]. The **linear** constraints — IV binding on the first
//! block, every mod-2³² limb-add identity (schedule recurrence, round adds,
//! finalization), and the state-chain that ties round outputs back to the
//! next round's inputs — are emitted here. The **lookup** relations for
//! `Σ`/`σ`/`Maj`/`Ch`/`xor_8` are stubbed with comments pointing at the
//! shared range-check / LogUp foundation that lives upstream of this stream
//! (see §9.4 of the validated design). Once that foundation lands, this
//! module imports its `RelationEntry` helpers and inserts the
//! `add_to_relation` calls in the sites marked below.
//!
//! Read-order invariant: every `next_trace_mask` call here happens in the
//! same order as the writes in [`crate::trace::write_block_row`]. Layout
//! offsets are not used directly here — they are documented in
//! [`crate::trace::Layout`] for cross-checking.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval};

use crate::constants::{IV, K, N_ROUNDS, N_STATE_WORDS};
use crate::types::LIMB_BITS;

/// AIR evaluator over the wide one-row-per-block layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (i.e. the smallest power-of-two ≥ block count).
    pub log_size: u32,
}

impl FrameworkEval for Sha256Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Every constraint here is degree ≤ 2 (most are linear; the binary
        // checks `x · (1 − x) = 0` are degree 2). The `+1` is the standard
        // FRI commitment headroom.
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // ---- header ----
        let enabler = eval.next_trace_mask();
        eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));

        let is_first_block = eval.next_trace_mask();
        eval.add_constraint(is_first_block.clone() * (E::F::one() - is_first_block.clone()));

        // ---- h_in: 8 words × (lo, hi) ----
        let h_in: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // IV binding: on the first block row, `h_in == IV`. We multiply by
        // `is_first_block` so the constraint is vacuous on every other row.
        for ((lo, hi), &iv_word) in h_in.iter().zip(IV.iter()) {
            let iv_lo = E::F::from(M31::from(iv_word & 0xFFFF));
            let iv_hi = E::F::from(M31::from(iv_word >> LIMB_BITS));
            eval.add_constraint(is_first_block.clone() * (lo.clone() - iv_lo));
            eval.add_constraint(is_first_block.clone() * (hi.clone() - iv_hi));
        }

        // ---- W[0..63]: 64 words × (lo, hi) ----
        let w: [(E::F, E::F); N_ROUNDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // ---- schedule entries: 48 × (σ0, σ1, carries) ----
        //
        // The σ-output values are not free — they are the *result* of a
        // lookup keyed on `W[t-15]` (for σ0) and `W[t-2]` (for σ1). Each
        // such lookup is two decode-table reads plus an `xor_8` chunk-wise
        // combination of the two `O2` partials (§9 of the design). The
        // LogUp `add_to_relation` calls hook in at the marker below; for
        // now we read the σ outputs as columns and emit the *linear* add
        // identity that ties them to `W[t]`.
        for j in 0..(N_ROUNDS - 16) {
            let t = j + 16;
            let s0 = (eval.next_trace_mask(), eval.next_trace_mask());
            let s1 = (eval.next_trace_mask(), eval.next_trace_mask());
            let carry_lo = eval.next_trace_mask();
            let carry_hi = eval.next_trace_mask();

            // TODO(shared-foundation): lookup constraints
            //   σ1(W[t-2]) -> s1   via Σ/σ decode + xor_8 combine
            //   σ0(W[t-15]) -> s0  via Σ/σ decode + xor_8 combine
            //   carry_lo, carry_hi ∈ [0, 4)   via range-check table
            //   s0.lo, s0.hi, s1.lo, s1.hi ∈ [0, 2¹⁶)  (implicit via lookup).

            // W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]  (mod 2³²)
            //
            // Limb-add identity, 4 addends:
            //   lo: s1.lo + W[t-7].lo + s0.lo + W[t-16].lo
            //         = W[t].lo + 2¹⁶ · carry_lo
            //   hi: s1.hi + W[t-7].hi + s0.hi + W[t-16].hi + carry_lo
            //         = W[t].hi + 2¹⁶ · carry_hi
            let w_t = w[t].clone();
            let w_t_minus_2 = w[t - 2].clone();
            let w_t_minus_7 = w[t - 7].clone();
            let w_t_minus_15 = w[t - 15].clone();
            let w_t_minus_16 = w[t - 16].clone();
            let _ = (w_t_minus_2, w_t_minus_15); // these are inputs to the σ lookups, used by the
                                                 // (currently stubbed) LogUp constraints above; in the linear add identity below the
                                                 // σ outputs already represent their contribution.

            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[s1.clone(), w_t_minus_7, s0.clone(), w_t_minus_16],
                &w_t,
                &carry_lo,
                &carry_hi,
            );
        }

        // ---- 64 rounds ----
        //
        // Track `(a, b, c, d, e, f, g, h)` symbolically across rounds.
        let mut state: [(E::F, E::F); N_STATE_WORDS] = h_in.clone();

        for (t, &k_t) in K.iter().enumerate().take(N_ROUNDS) {
            let [ref a, ref b, ref c, ref d, ref e, ref f, ref g, ref h_state] = state;

            // Round outputs, in the trace's column order:
            // σ0, σ1, ch, maj, t1, t2, a_new, e_new (each lo, hi),
            // then 4 carry pairs: t1, t2, e_new, a_new.
            let sigma0 = (eval.next_trace_mask(), eval.next_trace_mask());
            let sigma1 = (eval.next_trace_mask(), eval.next_trace_mask());
            let ch = (eval.next_trace_mask(), eval.next_trace_mask());
            let maj = (eval.next_trace_mask(), eval.next_trace_mask());
            let t1 = (eval.next_trace_mask(), eval.next_trace_mask());
            let t2 = (eval.next_trace_mask(), eval.next_trace_mask());
            let a_new = (eval.next_trace_mask(), eval.next_trace_mask());
            let e_new = (eval.next_trace_mask(), eval.next_trace_mask());

            let t1_carry = (eval.next_trace_mask(), eval.next_trace_mask());
            let t2_carry = (eval.next_trace_mask(), eval.next_trace_mask());
            let e_new_carry = (eval.next_trace_mask(), eval.next_trace_mask());
            let a_new_carry = (eval.next_trace_mask(), eval.next_trace_mask());

            // TODO(shared-foundation): lookup constraints
            //   σ0(a)  -> sigma0   via Σ/σ decode + xor_8
            //   σ1(e)  -> sigma1   via Σ/σ decode + xor_8
            //   Maj(a,b,c) -> maj  via packed Maj/Ch table at width W
            //   Ch(e,f,g)  -> ch   via packed Maj/Ch table
            //   carry_*.lo, carry_*.hi ∈ [0, k)  via range-check table
            //   every limb output ∈ [0, 2¹⁶)    (implicit via lookup).

            // K[t] is a circuit constant, never a free column.
            let k_lo = E::F::from(M31::from(k_t & 0xFFFF));
            let k_hi = E::F::from(M31::from(k_t >> LIMB_BITS));
            let k_t = (k_lo, k_hi);

            // T1 = h + Σ1 + Ch + K[t] + W[t]  (5-addend mod-2³² add).
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[
                    h_state.clone(),
                    sigma1.clone(),
                    ch.clone(),
                    k_t.clone(),
                    w[t].clone(),
                ],
                &t1,
                &t1_carry.0,
                &t1_carry.1,
            );

            // T2 = Σ0 + Maj  (2-addend add).
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[sigma0.clone(), maj.clone()],
                &t2,
                &t2_carry.0,
                &t2_carry.1,
            );

            // e_new = d + T1.
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[d.clone(), t1.clone()],
                &e_new,
                &e_new_carry.0,
                &e_new_carry.1,
            );

            // a_new = T1 + T2.
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[t1.clone(), t2.clone()],
                &a_new,
                &a_new_carry.0,
                &a_new_carry.1,
            );

            // State rotation for the next round:
            //   (a, b, c, d, e, f, g, h) ← (a_new, a, b, c, e_new, e, f, g)
            state = [
                a_new,
                a.clone(),
                b.clone(),
                c.clone(),
                e_new,
                e.clone(),
                f.clone(),
                g.clone(),
            ];
        }

        // ---- finalization carries: 8 × (lo, hi) ----
        let final_carries: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // ---- h_out: 8 words × (lo, hi) ----
        let h_out: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // Finalization: h_out[j] = h_in[j] + working_var[j]  (mod 2³²).
        for (j, working) in state.iter().enumerate().take(N_STATE_WORDS) {
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[h_in[j].clone(), working.clone()],
                &h_out[j],
                &final_carries[j].0,
                &final_carries[j].1,
            );
        }

        // TODO(integration): digest binding. Expose `h_out` to the integration
        // layer via two LogUp relations (interface contract item 1):
        //   - `valueDigests` membership uses the IssuerSignedItem hash output;
        //   - ECDSA `z` consumes the COSE Sig_structure hash output.
        // The relation tag names (interface contract item 2) get agreed with
        // the mdoc and integration stream owners before wiring.

        // TODO(shared-foundation): block-chain copy constraint.
        //   For every row r > 0 (a non-first block row), h_in[r] == h_out[r-1]
        //   limb-by-limb. Implementing this requires `EvalAtRow`'s cross-row
        //   mask helpers (`next_trace_mask_at_offset` or similar), which are
        //   part of the shared foundation work.

        // TODO(shared-foundation): `eval.finalize_logup_in_pairs()` once the
        // lookup relations above are populated.

        eval
    }
}

/// Emit the two linear constraints of one limb-grouped mod-2³² add.
///
/// For `addends = [a, b, c, …]` (each `(lo, hi)`) and result `r = (lo, hi)`,
/// constrains:
///
/// `Σ aᵢ.lo = r.lo + 2¹⁶ · carry_lo`
/// `Σ aᵢ.hi + carry_lo = r.hi + 2¹⁶ · carry_hi`
///
/// `carry_hi` is the discarded mod-2³² wraparound; the AIR range-checks both
/// carries via a lookup (stubbed, see TODO markers in callers).
///
/// The constraint is multiplied by `enabler` so padding rows (`enabler = 0`)
/// remain unconstrained.
fn emit_mod_2_32_add_linear<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    addends: &[(E::F, E::F)],
    result: &(E::F, E::F),
    carry_lo: &E::F,
    carry_hi: &E::F,
) {
    let two_pow_16 = E::F::from(M31::from(1u32 << LIMB_BITS));

    let mut sum_lo = E::F::from(M31::from(0u32));
    let mut sum_hi = E::F::from(M31::from(0u32));
    for (lo, hi) in addends {
        sum_lo += lo.clone();
        sum_hi += hi.clone();
    }

    // sum_lo - result.lo - 2¹⁶·carry_lo == 0
    eval.add_constraint(
        enabler.clone() * (sum_lo - result.0.clone() - two_pow_16.clone() * carry_lo.clone()),
    );
    // sum_hi + carry_lo - result.hi - 2¹⁶·carry_hi == 0
    eval.add_constraint(
        enabler * (sum_hi + carry_lo.clone() - result.1.clone() - two_pow_16 * carry_hi.clone()),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::{generate_trace, min_log_size, Layout};
    use crate::witness::compute_sha256_witness;

    /// Sanity: a fully-populated trace from a real message satisfies the
    /// **linear** add identities this module emits, end-to-end. Lookup
    /// relations are stubbed, so this only checks limb-add consistency
    /// (and IV binding, finalization, the state chain) — but a failure here
    /// indicates the witness or the constraint algebra is off, not just a
    /// missing lookup.
    fn check_linear_constraints_on_message(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for row in 0..witness.blocks.len() {
            check_add_identities_in_row(&trace, row);
            check_iv_binding_first_row(&trace, row);
            check_h_out_finalization(&trace, row, &witness);
        }
    }

    /// For every limb-add `c = Σ aᵢ`, verify
    /// `Σ aᵢ.lo = c.lo + 2¹⁶·carry_lo` and
    /// `Σ aᵢ.hi + carry_lo = c.hi + 2¹⁶·carry_hi`.
    fn check_add_identities_in_row(trace: &[Vec<stwo::core::fields::m31::BaseField>], row: usize) {
        let v = |col: usize| trace[col][row].0;
        let two16 = 1u64 << 16;

        // Schedule entries.
        for j in 0..(N_ROUNDS - 16) {
            let t = j + 16;
            let entry_cols = Layout::schedule_entry(j);
            let s0 = (v(entry_cols[0]) as u64, v(entry_cols[1]) as u64);
            let s1 = (v(entry_cols[2]) as u64, v(entry_cols[3]) as u64);
            let c_lo = v(entry_cols[4]) as u64;
            let c_hi = v(entry_cols[5]) as u64;

            let w_t = limb_pair(trace, row, Layout::schedule_word(t));
            let w_t_minus_7 = limb_pair(trace, row, Layout::schedule_word(t - 7));
            let w_t_minus_16 = limb_pair(trace, row, Layout::schedule_word(t - 16));

            let lhs_lo = s1.0 + w_t_minus_7.0 + s0.0 + w_t_minus_16.0;
            let rhs_lo = w_t.0 + two16 * c_lo;
            assert_eq!(lhs_lo, rhs_lo, "schedule t={t}: low limb identity");

            let lhs_hi = s1.1 + w_t_minus_7.1 + s0.1 + w_t_minus_16.1 + c_lo;
            let rhs_hi = w_t.1 + two16 * c_hi;
            assert_eq!(lhs_hi, rhs_hi, "schedule t={t}: high limb identity");
        }

        // Rounds.
        let mut state: [(u64, u64); 8] = std::array::from_fn(|j| {
            let (lo, hi) = Layout::h_in_word(j);
            (v(lo) as u64, v(hi) as u64)
        });
        for (t, &k_t) in K.iter().enumerate().take(N_ROUNDS) {
            let cols = Layout::round_col(t);
            let sigma0 = (v(cols[0]) as u64, v(cols[1]) as u64);
            let sigma1 = (v(cols[2]) as u64, v(cols[3]) as u64);
            let ch = (v(cols[4]) as u64, v(cols[5]) as u64);
            let maj = (v(cols[6]) as u64, v(cols[7]) as u64);
            let t1 = (v(cols[8]) as u64, v(cols[9]) as u64);
            let t2 = (v(cols[10]) as u64, v(cols[11]) as u64);
            let a_new = (v(cols[12]) as u64, v(cols[13]) as u64);
            let e_new = (v(cols[14]) as u64, v(cols[15]) as u64);
            let t1_carry = (v(cols[16]) as u64, v(cols[17]) as u64);
            let t2_carry = (v(cols[18]) as u64, v(cols[19]) as u64);
            let e_new_carry = (v(cols[20]) as u64, v(cols[21]) as u64);
            let a_new_carry = (v(cols[22]) as u64, v(cols[23]) as u64);

            let w_t = limb_pair(trace, row, Layout::schedule_word(t));
            let k_lo = (k_t & 0xFFFF) as u64;
            let k_hi = (k_t >> 16) as u64;
            let [a, b, c, d, e, _f, _g, h] = state;
            let _ = b;
            let _ = c;

            // T1 add.
            assert_eq!(
                h.0 + sigma1.0 + ch.0 + k_lo + w_t.0,
                t1.0 + two16 * t1_carry.0,
                "t={t}: T1.lo"
            );
            assert_eq!(
                h.1 + sigma1.1 + ch.1 + k_hi + w_t.1 + t1_carry.0,
                t1.1 + two16 * t1_carry.1,
                "t={t}: T1.hi"
            );
            // T2 add.
            assert_eq!(sigma0.0 + maj.0, t2.0 + two16 * t2_carry.0, "t={t}: T2.lo");
            assert_eq!(
                sigma0.1 + maj.1 + t2_carry.0,
                t2.1 + two16 * t2_carry.1,
                "t={t}: T2.hi"
            );
            // e_new add.
            assert_eq!(
                d.0 + t1.0,
                e_new.0 + two16 * e_new_carry.0,
                "t={t}: e_new.lo"
            );
            assert_eq!(
                d.1 + t1.1 + e_new_carry.0,
                e_new.1 + two16 * e_new_carry.1,
                "t={t}: e_new.hi"
            );
            // a_new add.
            assert_eq!(
                t1.0 + t2.0,
                a_new.0 + two16 * a_new_carry.0,
                "t={t}: a_new.lo"
            );
            assert_eq!(
                t1.1 + t2.1 + a_new_carry.0,
                a_new.1 + two16 * a_new_carry.1,
                "t={t}: a_new.hi"
            );

            // State rotation.
            state = [a_new, a, state[1], state[2], e_new, e, state[5], state[6]];
        }

        // Finalization adds.
        for (j, working) in state.iter().enumerate().take(N_STATE_WORDS) {
            let (h_in_lo, h_in_hi) = Layout::h_in_word(j);
            let (h_out_lo, h_out_hi) = Layout::h_out_word(j);
            let (c_lo, c_hi) = Layout::final_carry(j);
            let h_in_v = (v(h_in_lo) as u64, v(h_in_hi) as u64);
            let h_out_v = (v(h_out_lo) as u64, v(h_out_hi) as u64);
            let carry = (v(c_lo) as u64, v(c_hi) as u64);
            assert_eq!(
                h_in_v.0 + working.0,
                h_out_v.0 + two16 * carry.0,
                "final[{j}].lo"
            );
            assert_eq!(
                h_in_v.1 + working.1 + carry.0,
                h_out_v.1 + two16 * carry.1,
                "final[{j}].hi"
            );
        }
    }

    fn check_iv_binding_first_row(trace: &[Vec<stwo::core::fields::m31::BaseField>], row: usize) {
        if row != 0 {
            return;
        }
        for (j, &iv_j) in IV.iter().enumerate().take(N_STATE_WORDS) {
            let (lo, hi) = Layout::h_in_word(j);
            let word = trace[lo][row].0 | (trace[hi][row].0 << 16);
            assert_eq!(word, iv_j, "h_in[{j}] not bound to IV on row 0");
        }
    }

    fn check_h_out_finalization(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        row: usize,
        witness: &crate::types::Sha256Witness,
    ) {
        for j in 0..N_STATE_WORDS {
            let (lo, hi) = Layout::h_out_word(j);
            let word = trace[lo][row].0 | (trace[hi][row].0 << 16);
            assert_eq!(word, witness.blocks[row].h_out[j].to_u32());
        }
    }

    fn limb_pair(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        row: usize,
        cols: (usize, usize),
    ) -> (u64, u64) {
        (trace[cols.0][row].0 as u64, trace[cols.1][row].0 as u64)
    }

    #[test]
    fn linear_identities_hold_for_empty() {
        check_linear_constraints_on_message(b"");
    }

    #[test]
    fn linear_identities_hold_for_abc() {
        check_linear_constraints_on_message(b"abc");
    }

    #[test]
    fn linear_identities_hold_for_multi_block() {
        check_linear_constraints_on_message(&[0xABu8; 200]);
    }
}
