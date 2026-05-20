//! AIR evaluator for the SHA-256 component.
//!
//! Implements [`FrameworkEval`] for the one-row-per-block layout defined in
//! [`crate::trace`]. The **linear** constraints — IV binding on the first
//! block, every mod-2³² limb-add identity (schedule recurrence, round adds,
//! finalization), and the state-chain that ties round outputs back to the
//! next round's inputs — are emitted here. The **`Σ`/`σ` decode-table LogUp
//! lookups** (§9.3 of the validated design) and the matching σ-output
//! reassembly + `O2` chunk-bind constraints are wired below; the chunk-wise
//! `xor_8` lookups that close `o2_combined = o2_partial_s ⊕ o2_partial_s'`,
//! the `Maj`/`Ch` lookups, the split-and-pack key pin, and the carry
//! range-checks land in the follow-on lookup-wiring work.
//!
//! Read-order invariant: every `next_trace_mask` call here happens in the
//! same order as the writes in [`crate::trace::write_block_row`]. Layout
//! offsets are not used directly here — they are documented in
//! [`crate::trace::Layout`] for cross-checking.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::constants::{IV, K, N_ROUNDS, N_STATE_WORDS};
use crate::relations::SigmaDecodeRelations;
use crate::types::LIMB_BITS;

/// AIR evaluator over the wide one-row-per-block layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (i.e. the smallest power-of-two ≥ block count).
    pub log_size: u32,
    /// LogUp channels for the eight `Σ`/`σ` decode tables.
    pub relations: SigmaDecodeRelations,
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

        // ---- schedule entries: 48 × (σ0, σ1 limbs + carries + decode blocks) ----
        //
        // The σ-output values are not free — each is enforced via two
        // decode-table lookups (one per `S`/`S′` half) on the input word's
        // 16-bit packed halves, plus a chunk-wise `xor_8` combine of the two
        // `O2` partials (§9.3). This loop emits the decode-side
        // `add_to_relation` calls and the σ-output reassembly identity that
        // ties the decoded intermediates to the σ-output limbs; the
        // chunk-wise XOR lookups land in the follow-on wiring task.
        for j in 0..(N_ROUNDS - 16) {
            let t = j + 16;
            let s0 = (eval.next_trace_mask(), eval.next_trace_mask());
            let s1 = (eval.next_trace_mask(), eval.next_trace_mask());
            let carry_lo = eval.next_trace_mask();
            let carry_hi = eval.next_trace_mask();

            // σ-decode blocks (read in the order written by
            // `trace::write_sigma_decode_block`).
            let sigma0_decode = read_sigma_decode::<E>(&mut eval);
            let sigma1_decode = read_sigma_decode::<E>(&mut eval);

            // σ0(W[t-15]) → s0 — emit S-side and S′-side decode lookups,
            // the linear reassembly identity, and the O2 chunk-bind.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma0_decode,
                &s0,
                &self.relations.lower_sigma0_s,
                &self.relations.lower_sigma0_s_complement,
            );
            // σ1(W[t-2]) → s1.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma1_decode,
                &s1,
                &self.relations.lower_sigma1_s,
                &self.relations.lower_sigma1_s_complement,
            );

            // W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]  (mod 2³²)
            //
            // Limb-add identity, 4 addends:
            //   lo: s1.lo + W[t-7].lo + s0.lo + W[t-16].lo
            //         = W[t].lo + 2¹⁶ · carry_lo
            //   hi: s1.hi + W[t-7].hi + s0.hi + W[t-16].hi + carry_lo
            //         = W[t].hi + 2¹⁶ · carry_hi
            let w_t = w[t].clone();
            let w_t_minus_7 = w[t - 7].clone();
            let w_t_minus_16 = w[t - 16].clone();
            // `W[t-2]` and `W[t-15]` are the inputs to σ1 and σ0; the
            // decode-table key-pin (split-and-pack lookup, §9.3) lands in a
            // follow-on task, at which point `key_s + key_s_complement` is
            // tied back to `W[t-2]` / `W[t-15]`.

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

            // σ-decode blocks for Σ0(a) and Σ1(e), in the order written by
            // `trace::write_block_row`.
            let sigma0_decode = read_sigma_decode::<E>(&mut eval);
            let sigma1_decode = read_sigma_decode::<E>(&mut eval);

            // Σ0(a) → sigma0 — S/S′ decode lookups, σ-output reassembly,
            // and `O2` chunk-bind constraints (chunk-wise `xor_8` lookups
            // land in the follow-on task).
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma0_decode,
                &sigma0,
                &self.relations.sigma0_s,
                &self.relations.sigma0_s_complement,
            );
            // Σ1(e) → sigma1.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma1_decode,
                &sigma1,
                &self.relations.sigma1_s,
                &self.relations.sigma1_s_complement,
            );

            // Lookups still to be wired by follow-on tasks:
            //   Maj(a,b,c) -> maj  via packed Maj/Ch table at width W
            //   Ch(e,f,g)  -> ch   via packed Maj/Ch table
            //   o2_combined.* via chunk-wise xor_8 on the matched triple
            //   carry_*.lo, carry_*.hi ∈ [0, k)  via range-check tables
            //   key_s / key_s_complement pinned to the input word via
            //     split-and-pack lookup.

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

        // `eval.finalize_logup_in_pairs()` is deferred until *all* LogUp
        // channels are populated — the `Σ`/`σ` decode lookups above account
        // for ~half the entries; the chunk-wise `xor_8`, the `Maj`/`Ch`
        // lookups, the split-and-pack key pin, and the carry range checks
        // join in follow-on tasks. Calling `finalize_*` before then would
        // emit a cumulative-sum constraint inconsistent with the (yet-to-
        // land) remaining `add_to_relation` calls.

        eval
    }
}

/// One σ-application's worth of decoded intermediates, read from the trace
/// in the column order written by [`crate::trace::write_sigma_decode_block`].
/// `s_values` and `s_complement_values` are kept as 5-element arrays so they
/// can be passed straight to `add_to_relation` (matching the decode-table row
/// shape `(key, o_main_lo, o_main_hi, o2_partial_lo, o2_partial_hi)`).
struct SigmaDecodeMasks<F: Clone> {
    /// `[key_s, o_main_s.lo, o_main_s.hi, o2_partial_s.lo, o2_partial_s.hi]`.
    s_values: [F; 5],
    /// `[key_s_complement, o_main_s_complement.lo, o_main_s_complement.hi,
    /// o2_partial_s_complement.lo, o2_partial_s_complement.hi]`.
    s_complement_values: [F; 5],
    /// `(o2_combined.lo, o2_combined.hi)` — the field sum the σ-output
    /// reassembly identity reads.
    o2_combined: (F, F),
    /// Byte chunks of `o2_partial_s` — `(lo.b0, lo.b1, hi.b0, hi.b1)`.
    o2_chunks_s: [F; 4],
    /// Byte chunks of `o2_partial_s_complement`.
    o2_chunks_s_complement: [F; 4],
    /// Byte chunks of `o2_combined`.
    o2_chunks_combined: [F; 4],
}

/// Pull one σ-decode block off the `EvalAtRow` mask iterator. The reads
/// happen in trace-write order — keeping `wire_sigma_decode` independent of
/// the actual column layout.
fn read_sigma_decode<E: EvalAtRow>(eval: &mut E) -> SigmaDecodeMasks<E::F> {
    let s_values = std::array::from_fn::<E::F, 5, _>(|_| eval.next_trace_mask());
    let s_complement_values = std::array::from_fn::<E::F, 5, _>(|_| eval.next_trace_mask());
    let o2_combined = (eval.next_trace_mask(), eval.next_trace_mask());
    let o2_chunks_s = std::array::from_fn::<E::F, 4, _>(|_| eval.next_trace_mask());
    let o2_chunks_s_complement = std::array::from_fn::<E::F, 4, _>(|_| eval.next_trace_mask());
    let o2_chunks_combined = std::array::from_fn::<E::F, 4, _>(|_| eval.next_trace_mask());
    SigmaDecodeMasks {
        s_values,
        s_complement_values,
        o2_combined,
        o2_chunks_s,
        o2_chunks_s_complement,
        o2_chunks_combined,
    }
}

/// Emit all the constraints + LogUp lookups one σ-application contributes:
///
/// 1. **`S`-side decode lookup** — `(key_s, o_main_s.lo, o_main_s.hi,
///    o2_partial_s.lo, o2_partial_s.hi) ∈ table(rel_s)`.
/// 2. **`S′`-side decode lookup** — analogous, against `rel_s_complement`.
/// 3. **σ-output reassembly identity** — `σ.lo = o_main_s.lo +
///    o_main_s_complement.lo + o2_combined.lo` (`.hi` analogous). Field
///    addition matches XOR because the spread `O0`/`O1`/`O2` bits are
///    disjoint.
/// 4. **`O2` chunk-bind identities** — `o2_partial_s.lo = b0 + 256·b1`
///    (and the `.hi` and `s_complement` and `combined` analogues). These
///    are what the follow-on chunk-wise `xor_8` lookups will key on.
///
/// The chunks themselves are *not* range-checked here — the `xor_8` lookup
/// pins them to `[0, 256)`; the chunk-bind constraint above then pins each
/// 16-bit limb to `[0, 2¹⁶)` (one of the design's §11 L1 lookup ⇒ implicit
/// range checks). Until that lookup lands, the prover is trusted on the
/// chunks; this is the soundness gap the follow-on task closes.
fn wire_sigma_decode<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    decode: &SigmaDecodeMasks<E::F>,
    sigma_out: &(E::F, E::F),
    rel_s: &impl stwo_constraint_framework::Relation<E::F, E::EF>,
    rel_s_complement: &impl stwo_constraint_framework::Relation<E::F, E::EF>,
) {
    // (1) S-side decode-table lookup — "use" the row at multiplicity +1.
    eval.add_to_relation(RelationEntry::new(rel_s, E::EF::one(), &decode.s_values));
    // (2) S′-side decode-table lookup.
    eval.add_to_relation(RelationEntry::new(
        rel_s_complement,
        E::EF::one(),
        &decode.s_complement_values,
    ));

    // (3) σ-output reassembly: σ = o_main_s + o_main_s_complement + o2_combined,
    // limb by limb, gated by `enabler`.
    let o_main_s_lo = decode.s_values[1].clone();
    let o_main_s_hi = decode.s_values[2].clone();
    let o_main_s_complement_lo = decode.s_complement_values[1].clone();
    let o_main_s_complement_hi = decode.s_complement_values[2].clone();
    let o2_combined_lo = decode.o2_combined.0.clone();
    let o2_combined_hi = decode.o2_combined.1.clone();

    eval.add_constraint(
        enabler.clone()
            * (sigma_out.0.clone() - o_main_s_lo - o_main_s_complement_lo - o2_combined_lo),
    );
    eval.add_constraint(
        enabler.clone()
            * (sigma_out.1.clone() - o_main_s_hi - o_main_s_complement_hi - o2_combined_hi),
    );

    // (4) O2 chunk-bind: each 16-bit limb equals `b0 + 256·b1`. We do this
    // for the S-side partial, the S′-side partial, and the combined value —
    // three matched chunk sets that the chunk-wise `xor_8` lookup will tie
    // together as `chunks_combined[i] = chunks_s[i] ⊕ chunks_s_complement[i]`.
    let o2_partial_s_lo = decode.s_values[3].clone();
    let o2_partial_s_hi = decode.s_values[4].clone();
    let o2_partial_s_complement_lo = decode.s_complement_values[3].clone();
    let o2_partial_s_complement_hi = decode.s_complement_values[4].clone();
    emit_chunk_bind::<E>(
        eval,
        enabler.clone(),
        o2_partial_s_lo,
        o2_partial_s_hi,
        &decode.o2_chunks_s,
    );
    emit_chunk_bind::<E>(
        eval,
        enabler.clone(),
        o2_partial_s_complement_lo,
        o2_partial_s_complement_hi,
        &decode.o2_chunks_s_complement,
    );
    emit_chunk_bind::<E>(
        eval,
        enabler,
        decode.o2_combined.0.clone(),
        decode.o2_combined.1.clone(),
        &decode.o2_chunks_combined,
    );
}

/// Emit the two linear chunk-bind constraints: `limb_lo = b0_lo + 256·b1_lo`
/// and `limb_hi = b0_hi + 256·b1_hi`, gated by `enabler`. `chunks` is in the
/// trace order `(lo.b0, lo.b1, hi.b0, hi.b1)` matching
/// [`crate::trace::write_chunk_quad`].
fn emit_chunk_bind<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    limb_lo: E::F,
    limb_hi: E::F,
    chunks: &[E::F; 4],
) {
    let byte_base = E::F::from(M31::from(1u32 << 8));
    eval.add_constraint(
        enabler.clone() * (limb_lo - chunks[0].clone() - byte_base.clone() * chunks[1].clone()),
    );
    eval.add_constraint(enabler * (limb_hi - chunks[2].clone() - byte_base * chunks[3].clone()));
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
/// carries via a `Range_k` lookup (one of `Range_2`/`4`/`5` per add family,
/// see [`crate::headroom`]) — that wiring lands with the shared-foundation
/// roll-out.
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

    /// Each σ-application's decoded intermediates round-trip the σ-output
    /// reassembly identity and the `O2` chunk-bind that the AIR emits in
    /// [`wire_sigma_decode`]. A failure here means the witness or the
    /// reassembly algebra is off — not just a missing lookup.
    fn check_decode_reassembly_in_row(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        row: usize,
    ) {
        let v = |col: usize| trace[col][row].0;
        let two_pow_8 = 1u32 << 8;

        let check_block = |base: usize, label: &str| -> (u32, u32) {
            // Layout per `crate::trace::SIGMA_DECODE_COLS`:
            //   0..5   S-side tuple   (key, o_main.lo, .hi, o2_partial.lo, .hi)
            //   5..10  S′-side tuple
            //   10,11  o2_combined.lo, .hi
            //   12..16 o2_chunks_s             (lo.b0, lo.b1, hi.b0, hi.b1)
            //   16..20 o2_chunks_s_complement
            //   20..24 o2_chunks_combined
            // Chunk-bind: `limb == b0 + 256·b1` for each of the six limbs.
            assert_eq!(
                v(base + 3),
                v(base + 12) + two_pow_8 * v(base + 13),
                "{label}: chunk-bind o2_partial_s.lo"
            );
            assert_eq!(
                v(base + 4),
                v(base + 14) + two_pow_8 * v(base + 15),
                "{label}: chunk-bind o2_partial_s.hi"
            );
            assert_eq!(
                v(base + 8),
                v(base + 16) + two_pow_8 * v(base + 17),
                "{label}: chunk-bind o2_partial_s_complement.lo"
            );
            assert_eq!(
                v(base + 9),
                v(base + 18) + two_pow_8 * v(base + 19),
                "{label}: chunk-bind o2_partial_s_complement.hi"
            );
            assert_eq!(
                v(base + 10),
                v(base + 20) + two_pow_8 * v(base + 21),
                "{label}: chunk-bind o2_combined.lo"
            );
            assert_eq!(
                v(base + 11),
                v(base + 22) + two_pow_8 * v(base + 23),
                "{label}: chunk-bind o2_combined.hi"
            );
            // Reassembly: σ = o_main_s + o_main_s_complement + o2_combined
            // — limb by limb. Returned so the caller compares against the
            // σ-output limbs committed elsewhere in the row.
            (
                v(base + 1) + v(base + 6) + v(base + 10),
                v(base + 2) + v(base + 7) + v(base + 11),
            )
        };

        for j in 0..(N_ROUNDS - 16) {
            let [s0_lo, s0_hi, s1_lo, s1_hi, _, _] = Layout::schedule_entry(j);
            let s0 = (v(s0_lo), v(s0_hi));
            let s1 = (v(s1_lo), v(s1_hi));
            let sigma0_sum = check_block(Layout::schedule_entry_decode(j, 0), "schedule σ0");
            assert_eq!(s0, sigma0_sum, "schedule[{j}]: σ0 reassembly");
            let sigma1_sum = check_block(Layout::schedule_entry_decode(j, 1), "schedule σ1");
            assert_eq!(s1, sigma1_sum, "schedule[{j}]: σ1 reassembly");
        }

        for t in 0..N_ROUNDS {
            let cols = Layout::round_col(t);
            let sigma0 = (v(cols[0]), v(cols[1]));
            let sigma1 = (v(cols[2]), v(cols[3]));
            let sigma0_sum = check_block(Layout::round_decode(t, 0), "round Σ0");
            assert_eq!(sigma0, sigma0_sum, "round[{t}]: Σ0 reassembly");
            let sigma1_sum = check_block(Layout::round_decode(t, 1), "round Σ1");
            assert_eq!(sigma1, sigma1_sum, "round[{t}]: Σ1 reassembly");
        }
    }

    #[test]
    fn decode_reassembly_holds_for_abc() {
        let witness = compute_sha256_witness(b"abc");
        let trace = generate_trace(&witness, min_log_size(witness.blocks.len()));
        for row in 0..witness.blocks.len() {
            check_decode_reassembly_in_row(&trace, row);
        }
    }

    #[test]
    fn decode_reassembly_holds_for_multi_block() {
        let witness = compute_sha256_witness(&[0xABu8; 200]);
        let trace = generate_trace(&witness, min_log_size(witness.blocks.len()));
        for row in 0..witness.blocks.len() {
            check_decode_reassembly_in_row(&trace, row);
        }
    }

    /// Per-block decode-lookup multiplicities equal the static per-block
    /// counts dictated by the trace shape — 64 round σ-applications (per
    /// side per function), 48 schedule σ-applications likewise. Sanity:
    /// the wiring fires the expected number of times.
    #[test]
    fn decode_lookup_multiplicities_match_per_block_totals() {
        use crate::witness::{decode_multiplicities_for_block, decode_multiplicities_for_witness};

        // Single block (`b"abc"` is one padded block).
        let witness = compute_sha256_witness(b"abc");
        assert_eq!(witness.blocks.len(), 1);
        let m = decode_multiplicities_for_block(&witness.blocks[0]);
        assert_eq!(m.sigma0_s, N_ROUNDS as u32);
        assert_eq!(m.sigma0_s_complement, N_ROUNDS as u32);
        assert_eq!(m.sigma1_s, N_ROUNDS as u32);
        assert_eq!(m.sigma1_s_complement, N_ROUNDS as u32);
        assert_eq!(m.lower_sigma0_s, (N_ROUNDS - 16) as u32);
        assert_eq!(m.lower_sigma0_s_complement, (N_ROUNDS - 16) as u32);
        assert_eq!(m.lower_sigma1_s, (N_ROUNDS - 16) as u32);
        assert_eq!(m.lower_sigma1_s_complement, (N_ROUNDS - 16) as u32);
        // Total = 4·64 (rounds) + 4·48 (schedule) = 448 decode lookups per block.
        assert_eq!(
            m.total(),
            4 * (N_ROUNDS as u32) + 4 * ((N_ROUNDS - 16) as u32)
        );
        assert_eq!(m.total(), 448);

        // Multi-block scaling is exactly linear in `n_blocks`.
        let multi = compute_sha256_witness(&[0xABu8; 200]);
        let n = multi.blocks.len() as u32;
        assert!(n >= 2, "expected the multi-block case to exceed one block");
        let agg = decode_multiplicities_for_witness(&multi);
        assert_eq!(agg.total(), n * 448);
        assert_eq!(agg.sigma0_s, n * N_ROUNDS as u32);
        assert_eq!(agg.lower_sigma1_s_complement, n * (N_ROUNDS - 16) as u32);
    }
}
