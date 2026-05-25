//! AIR evaluator for the SHA-256 component.
//!
//! Implements [`FrameworkEval`] for the one-row-per-block layout defined in
//! [`crate::trace`]. The **linear** constraints — IV binding on the first
//! block, every mod-2³² limb-add identity (schedule recurrence, round adds,
//! finalization), the within-row state-chain that ties round outputs back
//! to the next round's inputs, and the §10.3 **cross-row block-chain copy
//! constraint** that pins block `b+1`'s `h_in` to block `b`'s `h_out` via a
//! `[0, -1]` interaction mask — are emitted here. The **`Σ`/`σ` decode-table
//! LogUp lookups** (§9.3 of the validated design), the matching σ-output
//! reassembly + `O2` chunk-bind constraints, the chunk-wise `xor_8`
//! lookups that close `o2_combined = o2_partial_s ⊕ o2_partial_s'`, the
//! **packed `Maj`/`Ch` lookups** keyed on the per-round packed-group
//! decompositions, and the **split-and-pack lookups** (3.9.5) that pin
//! every packed-group / decode-key column back to a `(lo, hi)` word
//! limb — all wired below. The §8.1 reuse chain lets `b`/`c`/`f`/`g` of
//! the Maj/Ch lookups alias prior rounds' `a`/`e` columns (and the
//! per-block `h_in[1]`/`h_in[2]`/`h_in[5]`/`h_in[6]` aux splits for the
//! chain's first two rounds), so the trace commits each value's split
//! once. The mod-2³² limb-add carries are range-checked through
//! `Range_{2,4,5}` lookups (one family per add per
//! [`emit_mod_2_32_add_linear`] call) and the final-block `h_out` digest
//! limbs through `Range_16` (per design §10.2 / §11 L1).
//!
//! Beyond the compression-loop constraints, the §10.4 **padding-role**
//! block — appended after `h_out` per [`crate::trace::PADDING_ROW_COLS`]
//! — emits the constraints that pin the FIPS 180-4 §5.1.1 padding
//! structure: the `0x80` marker sits at the right byte (one-hot word /
//! byte selectors → byte-decomposition of the marker word), the bytes
//! after the marker are zero (cumulative-selector gates), the words after
//! the marker word are zero (with the length-block exception), and the
//! length block's `W[14]`/`W[15]` carry the bit-length limbs. Block-
//! alignment (`padded.len() % 64 == 0`) is structural — one trace row
//! IS one 64-byte block — and so no per-row constraint expresses it. The
//! cross-component binding of the bit-length and the marker position to
//! the mdoc-parser stream lands with roadmap 2.4.
//!
//! Read-order invariant: every `next_trace_mask` call here happens in the
//! same order as the writes in [`crate::trace::write_block_row`]. Layout
//! offsets are not used directly here — they are documented in
//! [`crate::trace::Layout`] for cross-checking.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, Relation, RelationEntry, ORIGINAL_TRACE_IDX,
};

use crate::constants::{IV, K, N_ROUNDS, N_STATE_WORDS};
use crate::partitions::{
    lower_sigma_key_hi_coeff_s, lower_sigma_key_hi_coeff_s_complement, round_key_coeffs,
    GROUPS_PER_ROUND_PARTITION, LOWER_SIGMA0_PARTS, LOWER_SIGMA1_PARTS, SIGMA0_GROUPS,
    SIGMA1_GROUPS,
};
use crate::relations::Sha256Relations;
use crate::trace::ROUND_MAJ_CH_OPERANDS;
use crate::types::{BYTES_PER_WORD, LIMB_BITS, WORDS_PER_BLOCK};

/// AIR evaluator over the wide one-row-per-block layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (i.e. the smallest power-of-two ≥ block count).
    pub log_size: u32,
    /// LogUp channels: `Σ`/`σ` decode tables (8), packed Maj/Ch (2),
    /// chunk-wise `xor_8` (1).
    pub relations: Sha256Relations,
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

        // ---- §8.1 reuse chain initial splits ----
        //
        // 4 operands × 6 groups, in the fixed `[b_init, c_init, f_init,
        // g_init]` order matching [`crate::trace::write_h_in_aux_grp`].
        // Each operand is the a-side / e-side split-and-pack of a specific
        // `h_in[j]` and gets pinned to that limb pair by the corresponding
        // split-and-pack lookup below.
        let b_init: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let c_init: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let f_init: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let g_init: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());

        // a-side split-and-pack lookups for `h_in[1]` (→ `b_init`) and
        // `h_in[2]` (→ `c_init`); e-side for `h_in[5]` / `h_in[6]`.
        // Pins each limb to `[0, 2¹⁶)` implicitly via the lookup input.
        wire_round_split_pack::<E>(
            &mut eval,
            enabler.clone(),
            &h_in[1],
            &b_init,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            enabler.clone(),
            &h_in[2],
            &c_init,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            enabler.clone(),
            &h_in[5],
            &f_init,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            enabler.clone(),
            &h_in[6],
            &g_init,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );

        // ---- W[0..63]: 64 words × (lo, hi) ----
        let w: [(E::F, E::F); N_ROUNDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // ---- schedule entries: 48 × (σ0, σ1 limbs + carries + decode blocks) ----
        //
        // The σ-output values are not free — each is enforced via two
        // decode-table lookups (one per `S`/`S′` half) on the input word's
        // 16-bit packed halves, plus a chunk-wise `xor_8` combine of the
        // two `O2` partials (§9.3). This loop emits the decode-side
        // `add_to_relation` calls, the σ-output reassembly identity that
        // ties the decoded intermediates to the σ-output limbs, and the
        // chunk-wise `xor_8` lookups that bind the `O2` combine.
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

            // σ-input split-and-pack blocks (read in the order written by
            // `trace::write_sigma_input_split_block`). One per σ-application.
            let sigma0_input_split = read_sigma_input_split::<E>(&mut eval);
            let sigma1_input_split = read_sigma_input_split::<E>(&mut eval);

            // σ0(W[t-15]) → s0 — emit S-side and S′-side decode lookups,
            // the linear reassembly identity, the O2 chunk-bind, and the
            // chunk-wise `xor_8` lookup that closes
            // `o2_combined = o2_partial_s ⊕ o2_partial_s'`.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma0_decode,
                &s0,
                &self.relations.sigma_decode.lower_sigma0_s,
                &self.relations.sigma_decode.lower_sigma0_s_complement,
                &self.relations.xor_8,
            );
            // σ1(W[t-2]) → s1.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma1_decode,
                &s1,
                &self.relations.sigma_decode.lower_sigma1_s,
                &self.relations.sigma_decode.lower_sigma1_s_complement,
                &self.relations.xor_8,
            );

            // σ-input split-and-pack lookups — one per half. Pin
            // `W[t-15].(lo, hi)` to the `σ0` partition's split-and-pack
            // tables, and `W[t-2].(lo, hi)` to the `σ1` partition's. As
            // with the round side, this implicitly range-checks each
            // input limb to `[0, 2¹⁶)`.
            let w_t_minus_15 = w[t - 15].clone();
            let w_t_minus_2 = w[t - 2].clone();
            wire_sigma_input_split::<E>(
                &mut eval,
                enabler.clone(),
                &w_t_minus_15,
                &sigma0_input_split,
                &self.relations.split_pack.lower_sigma0_lo,
                &self.relations.split_pack.lower_sigma0_hi,
            );
            wire_sigma_input_split::<E>(
                &mut eval,
                enabler.clone(),
                &w_t_minus_2,
                &sigma1_input_split,
                &self.relations.split_pack.lower_sigma1_lo,
                &self.relations.split_pack.lower_sigma1_hi,
            );

            // Tie each σ-decode block's `key_s` / `key_s_complement` to
            // the σ-input split-and-pack outputs by linear assembly
            // (§9.3 / partitions::lower_sigma_key_hi_coeff_s). Without
            // this pin, a prover supplies arbitrary `key_s` to the
            // decode-table lookup; with the pin, the decode key must
            // come from the bits of `W[t-15]` / `W[t-2]`.
            emit_sigma_input_decode_key_reassembly::<E>(
                &mut eval,
                enabler.clone(),
                &sigma0_decode,
                &sigma0_input_split,
                lower_sigma_key_hi_coeff_s(&LOWER_SIGMA0_PARTS),
                lower_sigma_key_hi_coeff_s_complement(&LOWER_SIGMA0_PARTS),
            );
            emit_sigma_input_decode_key_reassembly::<E>(
                &mut eval,
                enabler.clone(),
                &sigma1_decode,
                &sigma1_input_split,
                lower_sigma_key_hi_coeff_s(&LOWER_SIGMA1_PARTS),
                lower_sigma_key_hi_coeff_s_complement(&LOWER_SIGMA1_PARTS),
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

            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[s1.clone(), w_t_minus_7, s0.clone(), w_t_minus_16],
                &w_t,
                &carry_lo,
                &carry_hi,
                crate::components::RangeKind::Range4,
                &self.relations,
            );
        }

        // ---- 64 rounds ----
        //
        // Track `(a, b, c, d, e, f, g, h)` symbolically across rounds, plus
        // the §8.1 reuse chain for the a-side and e-side packed-group
        // splits: `b_grp[t] = a_grp[t-1]`, `c_grp[t] = a_grp[t-2]`, with
        // the first two rounds seeded from the per-block aux splits
        // (`b_init = h_in[1]`, `c_init = h_in[2]`, `f_init = h_in[5]`,
        // `g_init = h_in[6]`).
        let mut state: [(E::F, E::F); N_STATE_WORDS] = h_in.clone();
        let mut b_grp = b_init.clone();
        let mut c_grp = c_init.clone();
        let mut f_grp = f_init.clone();
        let mut g_grp = g_init.clone();

        let sigma0_coeffs = round_key_coeffs(&SIGMA0_GROUPS);
        let sigma1_coeffs = round_key_coeffs(&SIGMA1_GROUPS);

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
            // `O2` chunk-bind constraints, and the chunk-wise `xor_8`
            // lookup that combines the two `O2` partials.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma0_decode,
                &sigma0,
                &self.relations.sigma_decode.sigma0_s,
                &self.relations.sigma_decode.sigma0_s_complement,
                &self.relations.xor_8,
            );
            // Σ1(e) → sigma1.
            wire_sigma_decode::<E>(
                &mut eval,
                enabler.clone(),
                &sigma1_decode,
                &sigma1,
                &self.relations.sigma_decode.sigma1_s,
                &self.relations.sigma_decode.sigma1_s_complement,
                &self.relations.xor_8,
            );

            // Maj/Ch packed-group block — 24 cells (post §8.1 reuse).
            // Operand order is fixed: `[a, maj_out]` (a-side / Σ0
            // partition) followed by `[e, ch_out]` (e-side / Σ1). The
            // `b`/`c`/`f`/`g` lookup keys come from the §8.1 chain
            // (`b_grp`, `c_grp`, `f_grp`, `g_grp` updated at end of loop).
            let packed_groups: [[E::F; GROUPS_PER_ROUND_PARTITION]; ROUND_MAJ_CH_OPERANDS] =
                std::array::from_fn(|_| {
                    std::array::from_fn::<E::F, GROUPS_PER_ROUND_PARTITION, _>(|_| {
                        eval.next_trace_mask()
                    })
                });
            let [a_grp, maj_grp, e_grp, ch_grp] = packed_groups;

            // 6 Maj lookups — one per a-side group position. The row
            // shape is `(a_grp[i], b_grp[i], c_grp[i], maj_grp[i])`,
            // matching `MajRelation` (size 4). With the split-and-pack
            // lookups below in place, `a_grp` is pinned to `a.(lo, hi)`,
            // `b_grp` (= `a_grp[t-1]` or aux `b_init`) is pinned to its
            // originating limb, and similarly for `c_grp` and `maj_grp`.
            //
            // Multiplicity is `enabler` (1 on real-block rows, 0 on
            // padding) so padding rows — every cell zero — don't pollute
            // the producer's LogUp balance with all-zero keys.
            let maj_ch_mult = E::EF::from(enabler.clone());
            for i in 0..GROUPS_PER_ROUND_PARTITION {
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.maj,
                    maj_ch_mult.clone(),
                    &[
                        a_grp[i].clone(),
                        b_grp[i].clone(),
                        c_grp[i].clone(),
                        maj_grp[i].clone(),
                    ],
                ));
            }
            // 6 Ch lookups — one per e-side group position. Same shape,
            // against `ChRelation` (size 4).
            for i in 0..GROUPS_PER_ROUND_PARTITION {
                eval.add_to_relation(RelationEntry::new(
                    &self.relations.ch,
                    maj_ch_mult.clone(),
                    &[
                        e_grp[i].clone(),
                        f_grp[i].clone(),
                        g_grp[i].clone(),
                        ch_grp[i].clone(),
                    ],
                ));
            }

            // Round-side split-and-pack lookups — one per half per fresh
            // operand (a-side: `a`, `maj`; e-side: `e`, `ch`). Each
            // lookup pins three packed-group columns to the table row
            // determined by the input limb, and implicitly range-checks
            // the limb to `[0, 2¹⁶)` (design §11 L1).
            wire_round_split_pack::<E>(
                &mut eval,
                enabler.clone(),
                a,
                &a_grp,
                &self.relations.split_pack.sigma0_lo,
                &self.relations.split_pack.sigma0_hi,
            );
            wire_round_split_pack::<E>(
                &mut eval,
                enabler.clone(),
                &maj,
                &maj_grp,
                &self.relations.split_pack.sigma0_lo,
                &self.relations.split_pack.sigma0_hi,
            );
            wire_round_split_pack::<E>(
                &mut eval,
                enabler.clone(),
                e,
                &e_grp,
                &self.relations.split_pack.sigma1_lo,
                &self.relations.split_pack.sigma1_hi,
            );
            wire_round_split_pack::<E>(
                &mut eval,
                enabler.clone(),
                &ch,
                &ch_grp,
                &self.relations.split_pack.sigma1_lo,
                &self.relations.split_pack.sigma1_hi,
            );

            // Tie each round σ-decode block's `key_s` / `key_s_complement`
            // to the just-pinned `a_grp` / `e_grp` packed values via
            // linear assembly (partitions::round_key_coeffs). This is
            // what closes the Σ0/Σ1 decode lookups against the actual
            // input word's bits — without it, a prover supplies arbitrary
            // `key_s` to the decode lookup.
            emit_round_decode_key_reassembly::<E>(
                &mut eval,
                enabler.clone(),
                &sigma0_decode,
                &a_grp,
                sigma0_coeffs,
            );
            emit_round_decode_key_reassembly::<E>(
                &mut eval,
                enabler.clone(),
                &sigma1_decode,
                &e_grp,
                sigma1_coeffs,
            );

            // Carry range-checks fire inside each `emit_mod_2_32_add_linear`
            // call below (`Range_5` for `T1`, `Range_2` for `T2`/`e_new`/
            // `a_new` per the headroom audit).

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
                crate::components::RangeKind::Range5,
                &self.relations,
            );

            // T2 = Σ0 + Maj  (2-addend add).
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[sigma0.clone(), maj.clone()],
                &t2,
                &t2_carry.0,
                &t2_carry.1,
                crate::components::RangeKind::Range2,
                &self.relations,
            );

            // e_new = d + T1.
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[d.clone(), t1.clone()],
                &e_new,
                &e_new_carry.0,
                &e_new_carry.1,
                crate::components::RangeKind::Range2,
                &self.relations,
            );

            // a_new = T1 + T2.
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[t1.clone(), t2.clone()],
                &a_new,
                &a_new_carry.0,
                &a_new_carry.1,
                crate::components::RangeKind::Range2,
                &self.relations,
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

            // §8.1 reuse-chain advance, mirroring the working-state
            // rotation on the packed-group side. After round `t` we
            // have:
            //   b_grp_next = a_grp[t]   (because b[t+1] = a[t])
            //   c_grp_next = b_grp[t]   (because c[t+1] = b[t])
            //   f_grp_next = e_grp[t]
            //   g_grp_next = f_grp[t]
            // Compute the *next* values before overwriting `b_grp` /
            // `f_grp` so the chain stays consistent.
            let prev_b_grp = b_grp.clone();
            b_grp = a_grp.clone();
            c_grp = prev_b_grp;
            let prev_f_grp = f_grp.clone();
            f_grp = e_grp.clone();
            g_grp = prev_f_grp;
        }

        // ---- finalization carries: 8 × (lo, hi) ----
        let final_carries: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // ---- h_out: 8 words × (lo, hi), each read at offsets [0, -1] ----
        //
        // The cross-row offset gives us this row's `h_out` *and* the
        // previous (coset-predecessor) row's `h_out` in one mask call. The
        // previous row's values feed the §10.3 block-chain constraint
        // below; this row's values feed the finalization adds.
        //
        // `Layout::block_slot` ensures block `b` lives at coset index `b`,
        // so offset `-1` resolves to block `b − 1`'s row (with cyclic
        // wraparound on row 0 / first block — which is shielded by the
        // chain gate below).
        let mut h_out: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (E::F::from(M31::from(0u32)), E::F::from(M31::from(0u32))));
        let mut h_out_prev: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (E::F::from(M31::from(0u32)), E::F::from(M31::from(0u32))));
        for j in 0..N_STATE_WORDS {
            let [lo_cur, lo_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
            let [hi_cur, hi_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
            h_out[j] = (lo_cur, hi_cur);
            h_out_prev[j] = (lo_prev, hi_prev);
        }

        // Finalization: h_out[j] = h_in[j] + working_var[j]  (mod 2³²).
        for (j, working) in state.iter().enumerate().take(N_STATE_WORDS) {
            emit_mod_2_32_add_linear(
                &mut eval,
                enabler.clone(),
                &[h_in[j].clone(), working.clone()],
                &h_out[j],
                &final_carries[j].0,
                &final_carries[j].1,
                crate::components::RangeKind::Range2,
                &self.relations,
            );
        }

        // Terminal `Range_16` on every real-block `h_out` limb. Most
        // intermediate limbs are transitively pinned to `[0, 2¹⁶)` via the
        // next block's split-and-pack lookups, but the final block's
        // `h_out` (the digest output) has no downstream consumer in this
        // standalone component — without these lookups a prover could
        // present out-of-range M31 values that still satisfy the linear
        // finalization identity (research/sha256-air-design.md §10.2 / §11
        // L1). Firing on every real block costs 16 lookups per row and
        // simplifies the gating (just `enabler`) without changing
        // soundness for intermediate blocks.
        for h_out_word in h_out.iter().take(N_STATE_WORDS) {
            wire_carry_range_check::<E>(
                &mut eval,
                enabler.clone(),
                h_out_word.0.clone(),
                crate::components::RangeKind::Range16,
                &self.relations,
            );
            wire_carry_range_check::<E>(
                &mut eval,
                enabler.clone(),
                h_out_word.1.clone(),
                crate::components::RangeKind::Range16,
                &self.relations,
            );
        }

        // §10.3 multi-block chain: on every *continuation* row (a real
        // block other than the first), `h_in[j] == h_out_prev[j]` for both
        // limbs. The roadmap calls for the constraint to be vacuous on
        // first-block rows (constrained to IV instead) and on padding rows
        // (kept untouched by `enabler = 0`).
        //
        // Per design-lesson L5 ("keep all constraints degree ≤ 2") we
        // combine the two gates into a single linear factor
        // `(enabler − is_first_block)` rather than multiplying both:
        //   - first-block real row (enabler=1, is_first_block=1): factor 0
        //   - continuation real row  (enabler=1, is_first_block=0): factor 1
        //   - padding row            (enabler=0, is_first_block=0): factor 0
        // The product with the limb-difference stays degree 2, so the
        // existing `max_constraint_log_degree_bound = log_size + 1`
        // headroom is preserved.
        let chain_gate = enabler.clone() - is_first_block.clone();
        for j in 0..N_STATE_WORDS {
            eval.add_constraint(chain_gate.clone() * (h_in[j].0.clone() - h_out_prev[j].0.clone()));
            eval.add_constraint(chain_gate.clone() * (h_in[j].1.clone() - h_out_prev[j].1.clone()));
        }

        // TODO(integration): digest binding. Expose `h_out` to the integration
        // layer via two LogUp relations (interface contract item 1):
        //   - `valueDigests` membership uses the IssuerSignedItem hash output;
        //   - ECDSA `z` consumes the COSE Sig_structure hash output.
        // The relation tag names (interface contract item 2) get agreed with
        // the mdoc and integration stream owners before wiring.

        // ---- §10.4 padding-role constraints (roadmap 3.9.7) ----
        //
        // Read order mirrors `crate::trace::write_padding_row`; offsets
        // are documented on `Layout::COL_PADDING_*`.
        let is_marker_block = eval.next_trace_mask();
        let is_length_block = eval.next_trace_mask();
        let is_length_only_block = eval.next_trace_mask();
        let is_marker_only_block = eval.next_trace_mask();
        let is_marker_word: [E::F; WORDS_PER_BLOCK] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let marker_byte_sel: [E::F; BYTES_PER_WORD] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let marker_word_byte: [E::F; BYTES_PER_WORD] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let marker_word_post_strict_15 = eval.next_trace_mask();
        let bit_length_w14_lo = eval.next_trace_mask();
        let bit_length_w14_hi = eval.next_trace_mask();
        let bit_length_w15_lo = eval.next_trace_mask();
        let bit_length_w15_hi = eval.next_trace_mask();

        // (P.A) Binary checks. Every padding-role flag and one-hot bit
        // satisfies `x · (1 − x) = 0`. Not gated by `enabler`: on padding
        // rows every cell is 0 and the identity holds trivially.
        for flag in [
            &is_marker_block,
            &is_length_block,
            &is_length_only_block,
            &is_marker_only_block,
            &marker_word_post_strict_15,
        ] {
            eval.add_constraint(flag.clone() * (E::F::one() - flag.clone()));
        }
        for bit in is_marker_word.iter() {
            eval.add_constraint(bit.clone() * (E::F::one() - bit.clone()));
        }
        for bit in marker_byte_sel.iter() {
            eval.add_constraint(bit.clone() * (E::F::one() - bit.clone()));
        }

        // (P.B) One-hot sums match the block role. Marker-word selectors
        // sum to `is_marker_block` (1 on a marker block, 0 elsewhere);
        // marker-byte selectors do the same. Degree 1.
        let sum_is_marker_word: E::F = is_marker_word
            .iter()
            .cloned()
            .fold(E::F::from(M31::from(0u32)), |acc, b| acc + b);
        eval.add_constraint(sum_is_marker_word - is_marker_block.clone());
        let sum_marker_byte_sel: E::F = marker_byte_sel
            .iter()
            .cloned()
            .fold(E::F::from(M31::from(0u32)), |acc, b| acc + b);
        eval.add_constraint(sum_marker_byte_sel - is_marker_block.clone());

        // (P.C) Aux-flag definitions. Each is the product of two role
        // flags — committed as standalone columns so downstream
        // constraints stay degree ≤ 2 instead of degree 3. Constraint
        // form `aux − product = 0` is degree 2.
        eval.add_constraint(
            is_length_only_block.clone()
                - (E::F::one() - is_marker_block.clone()) * is_length_block.clone(),
        );
        eval.add_constraint(
            is_marker_only_block.clone()
                - is_marker_block.clone() * (E::F::one() - is_length_block.clone()),
        );

        // Cumulative one-hot sums: `cumulative_marker_word_sel[j] =
        // Σ_{j' < j} is_marker_word[j']`. With `is_marker_word` one-hot,
        // this is `0` for `j ≤ marker_word_idx` and `1` for
        // `j > marker_word_idx` (i.e., "strictly after marker"). Built
        // up in-place by accumulating each prefix.
        let mut cum_marker_word: [E::F; WORDS_PER_BLOCK] =
            std::array::from_fn(|_| E::F::from(M31::from(0u32)));
        for j in 1..WORDS_PER_BLOCK {
            cum_marker_word[j] = cum_marker_word[j - 1].clone() + is_marker_word[j - 1].clone();
        }
        let cum_marker_word_at_end = cum_marker_word[WORDS_PER_BLOCK - 1].clone()
            + is_marker_word[WORDS_PER_BLOCK - 1].clone();
        // Sanity: the total marker-word cumulative equals is_marker_block
        // (drops out of (P.B), restated here for the constraint loop's
        // self-documentation; not a separate identity).
        let _ = cum_marker_word_at_end;

        // (P.C') marker-word post-strict aux for the `W[15]` slot.
        // `marker_word_post_strict_15 = cum_marker_word[15] · (1 −
        // is_length_block)`. On a marker-only block (Case B's penult,
        // marker at `W[14]` or `W[15]`) this fires only when the marker
        // is at `W[14]` (cum[15] = 1) — forcing `W[15]` to zero. On
        // length-bearing blocks the `(1 − is_length_block) = 0` factor
        // zeros it. The symmetric `_14` aux would be identically zero
        // (no valid trace places the marker strictly before `W[14]`) and
        // is omitted; see `crate::types::PaddingRowWitness`.
        eval.add_constraint(
            marker_word_post_strict_15.clone()
                - cum_marker_word[15].clone() * (E::F::one() - is_length_block.clone()),
        );

        // (P.D) Marker-word byte assembly. The marker word `W[k]` (where
        // `k = marker_word_idx`) selected via the one-hot vector matches
        // the BE byte decomposition `(byte_0, byte_1, byte_2, byte_3)`.
        // Reads of the schedule words happen at offsets fixed by
        // `Layout::schedule_word(j)`; we already pulled those into the
        // local `w: [(E::F, E::F); N_ROUNDS]` array at the top of
        // `evaluate`, so they're in scope here.
        //
        // `W[k].hi = byte_0 · 256 + byte_1`, `W[k].lo = byte_2 · 256 + byte_3`.
        // On non-marker rows every is_marker_word[j] = 0 and the bytes
        // are 0 too (default trace fill), so both identities hold
        // vacuously. Degree 2 — sum-of-products of two degree-1 cells.
        let byte_base = E::F::from(M31::from(1u32 << 8));
        let mut sum_w_hi = E::F::from(M31::from(0u32));
        let mut sum_w_lo = E::F::from(M31::from(0u32));
        for j in 0..WORDS_PER_BLOCK {
            sum_w_hi += is_marker_word[j].clone() * w[j].1.clone();
            sum_w_lo += is_marker_word[j].clone() * w[j].0.clone();
        }
        eval.add_constraint(
            sum_w_hi
                - byte_base.clone() * marker_word_byte[0].clone()
                - marker_word_byte[1].clone(),
        );
        eval.add_constraint(
            sum_w_lo
                - byte_base.clone() * marker_word_byte[2].clone()
                - marker_word_byte[3].clone(),
        );

        // (P.E) The marker byte is `0x80`. Per byte position `b`, the
        // one-hot selector pins `byte[b] = 0x80` exactly when this is
        // the marker byte. On non-marker rows every selector is 0 and
        // the constraint is vacuous. Degree 2.
        let marker_value = E::F::from(M31::from(0x80u32));
        for b in 0..BYTES_PER_WORD {
            eval.add_constraint(
                marker_byte_sel[b].clone() * (marker_word_byte[b].clone() - marker_value.clone()),
            );
        }

        // (P.F) Bytes strictly after the marker byte (within the marker
        // word) are zero. `cumulative_byte_sel_before[b] = Σ_{b' < b}
        // marker_byte_sel[b']` selects "the marker is at some earlier
        // byte position than `b`". For `b = 0` it's identically 0
        // (constraint vacuous); for `b = 1, 2, 3` it's the cumulative
        // sum. Degree 2.
        let mut cum_byte_sel = E::F::from(M31::from(0u32));
        for b in 0..BYTES_PER_WORD {
            // Constraint uses the cumulative *before* b, so emit before
            // accumulating b's own selector.
            eval.add_constraint(cum_byte_sel.clone() * marker_word_byte[b].clone());
            cum_byte_sel += marker_byte_sel[b].clone();
        }

        // (P.G) Words strictly after the marker word are zero — with the
        // length-field exception. The "must be zero" indicator for each
        // word index `j ∈ [0, 14)` is the sum of two mutually exclusive
        // sources:
        //   - `cum_marker_word[j]`: marker block with marker before j.
        //   - `is_length_only_block`: pure length block (W[0..14] all zero).
        // For `W[15]` only the marker-only-block contribution applies
        // (in length-bearing blocks `W[14]`/`W[15]` are the length
        // field); we use the pre-committed `marker_word_post_strict_15`
        // aux to express it without a degree-3 product. `W[14]` gets no
        // (P.G) constraint: the only way it would need one is a marker
        // block with marker strictly before `W[14]`, which never happens
        // (in Case A `is_length_block = 1` zeros the gate; in Case B
        // penult the marker is always at `W[14]` or `W[15]`, and when
        // it's at `W[14]` the byte-level (P.D)/(P.E)/(P.F) already pin
        // `W[14]` to `0x80000000`).
        for j in 0..14 {
            let gate = cum_marker_word[j].clone() + is_length_only_block.clone();
            eval.add_constraint(gate.clone() * w[j].0.clone());
            eval.add_constraint(gate * w[j].1.clone());
        }
        eval.add_constraint(marker_word_post_strict_15.clone() * w[15].0.clone());
        eval.add_constraint(marker_word_post_strict_15.clone() * w[15].1.clone());

        // (P.H) Length-field encoding. On a length-bearing block,
        // `W[14]` and `W[15]` equal the committed bit-length limbs. The
        // 64-bit bit-length stored as four 16-bit limbs:
        //   bit_length_w14_hi : bits 48..63 (W[14].hi)
        //   bit_length_w14_lo : bits 32..47 (W[14].lo)
        //   bit_length_w15_hi : bits 16..31 (W[15].hi)
        //   bit_length_w15_lo : bits  0..15 (W[15].lo)
        // The cross-component LogUp binding to the mdoc parser (post 2.4)
        // exposes these four limbs uniformly — that's why we keep the
        // limb commitment separate from `W[14]`/`W[15]` themselves
        // rather than relying on the schedule cells alone. Degree 2.
        eval.add_constraint(
            is_length_block.clone() * (w[14].0.clone() - bit_length_w14_lo.clone()),
        );
        eval.add_constraint(
            is_length_block.clone() * (w[14].1.clone() - bit_length_w14_hi.clone()),
        );
        eval.add_constraint(
            is_length_block.clone() * (w[15].0.clone() - bit_length_w15_lo.clone()),
        );
        eval.add_constraint(
            is_length_block.clone() * (w[15].1.clone() - bit_length_w15_hi.clone()),
        );

        // Note: block-alignment (padded.len() % 64 == 0) is structural —
        // one trace row IS one 64-byte block — and the AIR cannot
        // represent a partial block. So no per-row constraint is needed
        // for that requirement (roadmap 3.9.7's "total padded length is a
        // multiple of BLOCK_BYTES").
        //
        // Note: cross-component binding of bit_length and marker position
        // to the mdoc/COSE-parser stream lands with roadmap 2.4 and is
        // explicitly out of scope here (per 3.9.7's implementation note).

        // Close the LogUp loop over every SHA-256-specific channel: the
        // eight `Σ`/`σ` decode lookups, the packed `Maj`/`Ch` pair, the
        // chunk-wise `xor_8`, the eight split-and-pack channels, and the
        // four `Range_k` channels (`Range_2`/`4`/`5` for mod-2³² carries
        // per family; `Range_16` for terminal `h_out` limbs). Each pair of
        // fractions batches into one interaction column (pairs share a
        // denominator) for proof-size economy.
        eval.finalize_logup_in_pairs();

        eval
    }
}

/// One σ-input's split-and-pack outputs, in the column order written by
/// [`crate::trace::write_sigma_input_split_block`]:
/// `(packed_s_lo, packed_s_complement_lo, packed_s_hi, packed_s_complement_hi)`.
/// The two `_lo` cells feed the σ-partition lo-half split-and-pack lookup
/// `(word.lo, packed_s_lo, packed_s_complement_lo)`; the two `_hi` cells feed
/// the hi-half twin. Linear assembly of the four cells, weighted by
/// `lower_sigma_key_hi_coeff_s` (and the `_s_complement` twin), equals the
/// σ-decode block's `(key_s, key_s_complement)`.
struct SigmaInputSplitMasks<F: Clone> {
    packed_s_lo: F,
    packed_s_complement_lo: F,
    packed_s_hi: F,
    packed_s_complement_hi: F,
}

/// Pull one σ-input split-and-pack block off the `EvalAtRow` mask iterator.
fn read_sigma_input_split<E: EvalAtRow>(eval: &mut E) -> SigmaInputSplitMasks<E::F> {
    SigmaInputSplitMasks {
        packed_s_lo: eval.next_trace_mask(),
        packed_s_complement_lo: eval.next_trace_mask(),
        packed_s_hi: eval.next_trace_mask(),
        packed_s_complement_hi: eval.next_trace_mask(),
    }
}

/// Fire a pair of round-side split-and-pack lookups (lo half, hi half) on
/// `word` against its partition's tables.
///
/// `grp` is the 6-element packed-group commitment in `groups_in_order`
/// ordering — `[L0, H0, H1, L1, L2, H2]` for the Σ0/Maj partition (or the
/// analogous Σ1/Ch e-side ordering). The lo-half table content carries
/// the three groups that live in the lo limb (`L0`, `L1`, `L2` for Σ0)
/// in `s` order then `s_complement` order, which projects to trace cells
/// `grp[0]`, `grp[3]`, `grp[4]`. The hi half analogously projects to
/// `grp[1]`, `grp[2]`, `grp[5]`. Each lookup row matches the
/// `(key, packed_group_0, packed_group_1, packed_group_2)` shape of
/// [`crate::relations::ROUND_SPLIT_PACK_REL_SIZE`].
///
/// Firing the lookup pins the three packed-group cells to the table row
/// determined by `word.lo` (resp. `word.hi`) and implicitly range-checks
/// the limb to `[0, 2¹⁶)` (design §11 L1).
fn wire_round_split_pack<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    word: &(E::F, E::F),
    grp: &[E::F; GROUPS_PER_ROUND_PARTITION],
    rel_lo: &impl Relation<E::F, E::EF>,
    rel_hi: &impl Relation<E::F, E::EF>,
) {
    // Gate by `enabler` so padding rows (every cell zero, so denominator
    // collapses to `-z` for every lookup) contribute a zero fraction
    // instead of `+1/(-z)`. Without this, every padding row would emit
    // 130-or-so consumer lookups all keyed on the all-zero row of the
    // table — which the producer's multiplicity column doesn't account
    // for, breaking the LogUp sum-to-zero balance.
    let mult = E::EF::from(enabler);
    eval.add_to_relation(RelationEntry::new(
        rel_lo,
        mult.clone(),
        &[
            word.0.clone(),
            grp[0].clone(),
            grp[3].clone(),
            grp[4].clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        rel_hi,
        mult,
        &[
            word.1.clone(),
            grp[1].clone(),
            grp[2].clone(),
            grp[5].clone(),
        ],
    ));
}

/// Fire a pair of σ-side split-and-pack lookups (lo half, hi half) on
/// `word` against its `σ` partition's tables.
///
/// Each row matches `(key, packed_s, packed_s_complement)`, the width-3
/// shape of [`crate::relations::SIGMA_SPLIT_PACK_REL_SIZE`]. The lookup
/// pins the two packed values to the table row determined by the
/// half-limb and implicitly range-checks the limb to `[0, 2¹⁶)`.
fn wire_sigma_input_split<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    word: &(E::F, E::F),
    split: &SigmaInputSplitMasks<E::F>,
    rel_lo: &impl Relation<E::F, E::EF>,
    rel_hi: &impl Relation<E::F, E::EF>,
) {
    let mult = E::EF::from(enabler);
    eval.add_to_relation(RelationEntry::new(
        rel_lo,
        mult.clone(),
        &[
            word.0.clone(),
            split.packed_s_lo.clone(),
            split.packed_s_complement_lo.clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::new(
        rel_hi,
        mult,
        &[
            word.1.clone(),
            split.packed_s_hi.clone(),
            split.packed_s_complement_hi.clone(),
        ],
    ));
}

/// Tie a round σ-decode block's `key_s` and `key_s_complement` to the
/// packed-group cells of the corresponding operand (`a` for Σ0, `e` for
/// Σ1) via linear assembly with the partition-specific coefficients
/// (`partitions::round_key_coeffs`).
///
///   `key_s            = c[0]·g[0] + c[1]·g[1] + c[2]·g[2]`
///   `key_s_complement = c[3]·g[3] + c[4]·g[4] + c[5]·g[5]`
///
/// where `g[i] = grp[i]` (the i-th packed group of the operand) and
/// `c[i]` is the i-th coefficient. This closes the soundness loop on the
/// Σ-decode lookups: the lookup's `key_s` must come from the bits of the
/// operand committed elsewhere in the row. Gated by `enabler` so the
/// constraint is vacuous on padding rows.
fn emit_round_decode_key_reassembly<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    decode: &SigmaDecodeMasks<E::F>,
    grp: &[E::F; GROUPS_PER_ROUND_PARTITION],
    coeffs: [u32; GROUPS_PER_ROUND_PARTITION],
) {
    let c = coeffs.map(|v| E::F::from(M31::from(v)));
    eval.add_constraint(
        enabler.clone()
            * (decode.s_values[0].clone()
                - c[0].clone() * grp[0].clone()
                - c[1].clone() * grp[1].clone()
                - c[2].clone() * grp[2].clone()),
    );
    eval.add_constraint(
        enabler
            * (decode.s_complement_values[0].clone()
                - c[3].clone() * grp[3].clone()
                - c[4].clone() * grp[4].clone()
                - c[5].clone() * grp[5].clone()),
    );
}

/// Tie a σ-input decode block's `key_s` and `key_s_complement` to the
/// σ-input split-and-pack outputs by linear assembly with the partition's
/// hi-coefficient constants
/// (`partitions::lower_sigma_key_hi_coeff_s` / `..._s_complement`).
///
///   `key_s            = packed_s_lo + hi_coeff_s · packed_s_hi`
///   `key_s_complement = packed_s_complement_lo
///                        + hi_coeff_s_complement · packed_s_complement_hi`
///
/// Closes the soundness loop on the `σ0`/`σ1` decode lookups against the
/// schedule-word input. Gated by `enabler`.
fn emit_sigma_input_decode_key_reassembly<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    decode: &SigmaDecodeMasks<E::F>,
    split: &SigmaInputSplitMasks<E::F>,
    hi_coeff_s: u32,
    hi_coeff_s_complement: u32,
) {
    let c_hi_s = E::F::from(M31::from(hi_coeff_s));
    let c_hi_s_complement = E::F::from(M31::from(hi_coeff_s_complement));
    eval.add_constraint(
        enabler.clone()
            * (decode.s_values[0].clone()
                - split.packed_s_lo.clone()
                - c_hi_s * split.packed_s_hi.clone()),
    );
    eval.add_constraint(
        enabler
            * (decode.s_complement_values[0].clone()
                - split.packed_s_complement_lo.clone()
                - c_hi_s_complement * split.packed_s_complement_hi.clone()),
    );
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
///    are what the chunk-wise `xor_8` lookup in step 5 keys on.
/// 5. **Chunk-wise `xor_8` lookups** — four firings of
///    `(chunks_s[i], chunks_s_complement[i], chunks_combined[i]) ∈ xor_8`,
///    one per chunk position `i ∈ {lo.b0, lo.b1, hi.b0, hi.b1}`. Together
///    with the chunk-bind identities this closes
///    `o2_combined = o2_partial_s ⊕ o2_partial_s'` and implicitly
///    range-checks every chunk to `[0, 256)` and every `O2` limb to
///    `[0, 2¹⁶)` (design §9.3 / §11 L1).
fn wire_sigma_decode<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    decode: &SigmaDecodeMasks<E::F>,
    sigma_out: &(E::F, E::F),
    rel_s: &impl Relation<E::F, E::EF>,
    rel_s_complement: &impl Relation<E::F, E::EF>,
    rel_xor_8: &impl Relation<E::F, E::EF>,
) {
    // (1) S-side decode-table lookup — "use" the row at multiplicity
    // `enabler` (1 on real rows, 0 on padding so the all-zero key on a
    // padding row doesn't pollute the producer's LogUp balance).
    let lookup_mult = E::EF::from(enabler.clone());
    eval.add_to_relation(RelationEntry::new(
        rel_s,
        lookup_mult.clone(),
        &decode.s_values,
    ));
    // (2) S′-side decode-table lookup.
    eval.add_to_relation(RelationEntry::new(
        rel_s_complement,
        lookup_mult.clone(),
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
    // three matched chunk sets the chunk-wise `xor_8` lookup ties together
    // as `chunks_combined[i] = chunks_s[i] ⊕ chunks_s_complement[i]`.
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

    // (5) Chunk-wise `xor_8` lookups — one per chunk index. The chunks
    // live at the same offsets in `o2_chunks_s` / `o2_chunks_s_complement`
    // / `o2_chunks_combined` (the trace writer keeps them in the
    // `(lo.b0, lo.b1, hi.b0, hi.b1)` order documented on
    // [`crate::trace::SIGMA_DECODE_COLS`]).
    for i in 0..4 {
        eval.add_to_relation(RelationEntry::new(
            rel_xor_8,
            lookup_mult.clone(),
            &[
                decode.o2_chunks_s[i].clone(),
                decode.o2_chunks_s_complement[i].clone(),
                decode.o2_chunks_combined[i].clone(),
            ],
        ));
    }
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
/// `carry_hi` is the discarded mod-2³² wraparound. Both carry limbs are
/// pinned to `[0, k)` by an `add_to_relation` lookup against the family's
/// `Range_k` channel — `Range_2` for 2-addend adds, `Range_4` for the
/// 4-addend schedule recurrence, `Range_5` for the 5-addend `T1`. See
/// [`crate::headroom`] for the audited family bounds.
///
/// The linear constraints are multiplied by `enabler` so padding rows
/// (`enabler = 0`) remain unconstrained. The carry lookups are also gated
/// by `enabler` (passed as the multiplicity) so the producer-side
/// LogUp balance is not perturbed by zero-valued padding-row carries.
#[allow(clippy::too_many_arguments)]
fn emit_mod_2_32_add_linear<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    addends: &[(E::F, E::F)],
    result: &(E::F, E::F),
    carry_lo: &E::F,
    carry_hi: &E::F,
    range_kind: crate::components::RangeKind,
    relations: &Sha256Relations,
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
        enabler.clone()
            * (sum_hi + carry_lo.clone() - result.1.clone() - two_pow_16 * carry_hi.clone()),
    );

    // Carry range-checks via the family's `Range_k` channel. Multiplicity
    // is `enabler` so padding rows (every cell zero) don't bump the row-0
    // producer count.
    wire_carry_range_check::<E>(
        eval,
        enabler.clone(),
        carry_lo.clone(),
        range_kind,
        relations,
    );
    wire_carry_range_check::<E>(eval, enabler, carry_hi.clone(), range_kind, relations);
}

/// Fire one `add_to_relation(rel, +enabler, &[value])` against the chosen
/// `Range_k` channel. Inlined helper so call sites stay short.
fn wire_carry_range_check<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    value: E::F,
    kind: crate::components::RangeKind,
    relations: &Sha256Relations,
) {
    use crate::components::RangeKind;
    let mult = E::EF::from(enabler);
    match kind {
        RangeKind::Range2 => {
            eval.add_to_relation(RelationEntry::new(&relations.range.range_2, mult, &[value]))
        }
        RangeKind::Range4 => {
            eval.add_to_relation(RelationEntry::new(&relations.range.range_4, mult, &[value]))
        }
        RangeKind::Range5 => {
            eval.add_to_relation(RelationEntry::new(&relations.range.range_5, mult, &[value]))
        }
        RangeKind::Range16 => eval.add_to_relation(RelationEntry::new(
            &relations.range.range_16,
            mult,
            &[value],
        )),
    }
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
        for block_idx in 0..witness.blocks.len() {
            let slot = Layout::block_slot(block_idx, log_size);
            check_add_identities_in_row(&trace, slot);
            if block_idx == 0 {
                check_iv_binding_first_row(&trace, slot);
            }
            check_h_out_finalization(&trace, slot, &witness, block_idx);
        }
        // §10.3 chain constraint: block `b+1`'s `h_in` equals block `b`'s
        // `h_out`. Verified row-by-row in the witness via `block_slot`.
        for block_idx in 1..witness.blocks.len() {
            let cur = Layout::block_slot(block_idx, log_size);
            let prev = Layout::block_slot(block_idx - 1, log_size);
            check_block_chain_link(&trace, cur, prev);
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
        for (j, &iv_j) in IV.iter().enumerate().take(N_STATE_WORDS) {
            let (lo, hi) = Layout::h_in_word(j);
            let word = trace[lo][row].0 | (trace[hi][row].0 << 16);
            assert_eq!(word, iv_j, "h_in[{j}] not bound to IV on first-block row");
        }
    }

    fn check_h_out_finalization(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        row: usize,
        witness: &crate::types::Sha256Witness,
        block_idx: usize,
    ) {
        for j in 0..N_STATE_WORDS {
            let (lo, hi) = Layout::h_out_word(j);
            let word = trace[lo][row].0 | (trace[hi][row].0 << 16);
            assert_eq!(word, witness.blocks[block_idx].h_out[j].to_u32());
        }
    }

    /// §10.3 chain check on the trace: every limb of `h_in` at row `cur`
    /// equals the corresponding limb of `h_out` at row `prev`. Mirrors the
    /// AIR's cross-row copy constraint (3.9.6) at the trace level.
    fn check_block_chain_link(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        cur: usize,
        prev: usize,
    ) {
        for j in 0..N_STATE_WORDS {
            let (h_in_lo, h_in_hi) = Layout::h_in_word(j);
            let (h_out_lo, h_out_hi) = Layout::h_out_word(j);
            assert_eq!(
                trace[h_in_lo][cur].0, trace[h_out_lo][prev].0,
                "chain mismatch: h_in[{j}].lo @ {cur} != h_out[{j}].lo @ {prev}"
            );
            assert_eq!(
                trace[h_in_hi][cur].0, trace[h_out_hi][prev].0,
                "chain mismatch: h_in[{j}].hi @ {cur} != h_out[{j}].hi @ {prev}"
            );
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
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for block_idx in 0..witness.blocks.len() {
            check_decode_reassembly_in_row(&trace, Layout::block_slot(block_idx, log_size));
        }
    }

    #[test]
    fn decode_reassembly_holds_for_multi_block() {
        let witness = compute_sha256_witness(&[0xABu8; 200]);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for block_idx in 0..witness.blocks.len() {
            check_decode_reassembly_in_row(&trace, Layout::block_slot(block_idx, log_size));
        }
    }

    /// Maj/Ch/`xor_8` multiplicities per block equal the static counts
    /// the trace shape dictates — 6 Maj + 6 Ch lookups per round, and 4
    /// chunk-wise `xor_8` lookups per σ-application (with 2 σ-applications
    /// per round and 2 per schedule entry). A regression here means the
    /// witness-side counter (which the LogUp table-side multiplicity
    /// column must reproduce) has drifted from the constraint-side wiring.
    #[test]
    fn maj_ch_xor_multiplicities_match_per_block_totals() {
        use crate::partitions::GROUPS_PER_ROUND_PARTITION;
        use crate::witness::{
            maj_ch_xor_multiplicities_for_block, maj_ch_xor_multiplicities_for_witness,
        };

        let witness = crate::witness::compute_sha256_witness(b"abc");
        assert_eq!(witness.blocks.len(), 1);
        let m = maj_ch_xor_multiplicities_for_block(&witness.blocks[0]);
        let groups = GROUPS_PER_ROUND_PARTITION as u32;
        // 6 packed-group lookups per round per function.
        assert_eq!(m.maj, (N_ROUNDS as u32) * groups);
        assert_eq!(m.ch, (N_ROUNDS as u32) * groups);
        assert_eq!(m.maj, 64 * 6);
        // 4 xor_8 per σ-application; (2·64 + 2·48) σ-applications/block.
        let sigma_apps_per_block = 2 * (N_ROUNDS as u32) + 2 * ((N_ROUNDS - 16) as u32);
        assert_eq!(m.xor_8, 4 * sigma_apps_per_block);
        assert_eq!(m.xor_8, 4 * (128 + 96));
        assert_eq!(m.total(), m.maj + m.ch + m.xor_8);

        // Multi-block scaling is exactly linear in `n_blocks`.
        let multi = crate::witness::compute_sha256_witness(&[0xABu8; 200]);
        let n = multi.blocks.len() as u32;
        assert!(n >= 2);
        let agg = maj_ch_xor_multiplicities_for_witness(&multi);
        assert_eq!(agg.maj, n * m.maj);
        assert_eq!(agg.ch, n * m.ch);
        assert_eq!(agg.xor_8, n * m.xor_8);
    }

    /// Drives [`Sha256Eval::evaluate`] through Stwo's `InfoEvaluator` and
    /// asserts every observable count lines up:
    ///
    ///   - The number of `next_trace_mask` calls equals `Layout::TOTAL_COLS`
    ///     — a drift here silently shifts every constraint and lookup
    ///     against the column it reads.
    ///   - Per-relation lookup firings (one entry per `relation!` tag)
    ///     equal the per-block static counts from
    ///     `crate::witness::*_multiplicities_for_block`. This covers
    ///     decode (3.9.3), Maj/Ch + xor_8 (3.9.4), and the eight
    ///     split-and-pack channels (3.9.5).
    ///   - The total lookup count equals the sum across all per-channel
    ///     witness-side totals.
    #[test]
    fn evaluate_mask_and_lookup_counts_agree_with_witness() {
        use stwo_constraint_framework::ORIGINAL_TRACE_IDX;

        let log_size = 4;
        let eval = Sha256Eval {
            log_size,
            relations: Sha256Relations::dummy(),
        };
        let info = run_evaluate_with_finalized_info(&eval, log_size);

        // The AIR fires one row's worth of lookups (i.e. per-block totals
        // — every row of the trace runs one block's evaluator pass).
        let witness = compute_sha256_witness(b"abc");
        let decode = crate::witness::decode_multiplicities_for_block(&witness.blocks[0]);
        let maj_ch_xor = crate::witness::maj_ch_xor_multiplicities_for_block(&witness.blocks[0]);
        let split_pack = crate::witness::split_pack_multiplicities_for_block(&witness.blocks[0]);

        // The `relation!` macro derives the relation tag's name as the
        // struct name string. These must agree with what
        // `crate::relations` declares.
        let get = |name: &str| -> u32 {
            info.logup_counts
                .iter()
                .find_map(|(k, v)| if k == name { Some(*v as u32) } else { None })
                .unwrap_or(0)
        };

        // Decode (3.9.3).
        assert_eq!(get("Sigma0DecodeS"), decode.sigma0_s);
        assert_eq!(get("Sigma0DecodeSPrime"), decode.sigma0_s_complement);
        assert_eq!(get("Sigma1DecodeS"), decode.sigma1_s);
        assert_eq!(get("Sigma1DecodeSPrime"), decode.sigma1_s_complement);
        assert_eq!(get("LowerSigma0DecodeS"), decode.lower_sigma0_s);
        assert_eq!(
            get("LowerSigma0DecodeSPrime"),
            decode.lower_sigma0_s_complement
        );
        assert_eq!(get("LowerSigma1DecodeS"), decode.lower_sigma1_s);
        assert_eq!(
            get("LowerSigma1DecodeSPrime"),
            decode.lower_sigma1_s_complement
        );

        // Maj/Ch/xor_8 (3.9.4).
        assert_eq!(get("MajRelation"), maj_ch_xor.maj);
        assert_eq!(get("ChRelation"), maj_ch_xor.ch);
        assert_eq!(get("Xor8Relation"), maj_ch_xor.xor_8);

        // Split-and-pack (3.9.5).
        assert_eq!(get("Sigma0SplitPackLo"), split_pack.sigma0_lo);
        assert_eq!(get("Sigma0SplitPackHi"), split_pack.sigma0_hi);
        assert_eq!(get("Sigma1SplitPackLo"), split_pack.sigma1_lo);
        assert_eq!(get("Sigma1SplitPackHi"), split_pack.sigma1_hi);
        assert_eq!(get("LowerSigma0SplitPackLo"), split_pack.lower_sigma0_lo);
        assert_eq!(get("LowerSigma0SplitPackHi"), split_pack.lower_sigma0_hi);
        assert_eq!(get("LowerSigma1SplitPackLo"), split_pack.lower_sigma1_lo);
        assert_eq!(get("LowerSigma1SplitPackHi"), split_pack.lower_sigma1_hi);

        // Range_k carry / terminal lookups (3.9.2 wiring of the
        // shared-foundation `Range_*` channels). Per block, structurally:
        //   Range_4  : 2 carries × 48 schedule entries        = 96
        //   Range_5  : 2 carries × 64 rounds (T1 only)        = 128
        //   Range_2  : 2 carries × (3 round-side adds × 64
        //                          + 8 finalization adds)     = 400
        //   Range_16 : 2 limbs × 8 h_out words                = 16
        let n_entries = (N_ROUNDS as u32) - 16; // schedule entries per block
        let range_4_per_block: u32 = 2 * n_entries;
        let range_5_per_block: u32 = 2 * (N_ROUNDS as u32);
        let range_2_per_block: u32 = 2 * (3 * (N_ROUNDS as u32) + (N_STATE_WORDS as u32));
        let range_16_per_block: u32 = 2 * (N_STATE_WORDS as u32);
        assert_eq!(get("Range2Relation"), range_2_per_block);
        assert_eq!(get("Range4Relation"), range_4_per_block);
        assert_eq!(get("Range5Relation"), range_5_per_block);
        assert_eq!(get("Range16Relation"), range_16_per_block);

        // Mask count — `info.mask_offsets[ORIGINAL_TRACE_IDX]` is the
        // main trace (the list pushed by every `next_trace_mask` call).
        assert_eq!(
            info.mask_offsets[ORIGINAL_TRACE_IDX].len(),
            Layout::TOTAL_COLS,
            "AIR's `next_trace_mask` count diverged from `Layout::TOTAL_COLS`",
        );

        // Verify the witness-side total firings = sum across channels.
        let total_lookups: u32 = info.logup_counts.iter().map(|(_, &v)| v as u32).sum();
        let range_total =
            range_2_per_block + range_4_per_block + range_5_per_block + range_16_per_block;
        let expected_total = decode.total() + maj_ch_xor.total() + split_pack.total() + range_total;
        assert_eq!(total_lookups, expected_total);
    }

    /// Drive one `InfoEvaluator` pass through `Sha256Eval::evaluate`.
    /// `evaluate` ends with `finalize_logup_in_pairs()` (so the
    /// `LogupAtRow` Drop guard passes) — this helper just exposes the
    /// captured info to the test assertions.
    fn run_evaluate_with_finalized_info(
        eval: &Sha256Eval,
        log_size: u32,
    ) -> stwo_constraint_framework::InfoEvaluator {
        use stwo::core::fields::qm31::SecureField;
        use stwo_constraint_framework::{FrameworkEval, InfoEvaluator};
        eval.evaluate(InfoEvaluator::new(log_size, vec![], SecureField::default()))
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

    // ------------------------------------------------------------------
    // §10.3 cross-row block-chain copy constraint (roadmap 3.9.6)
    //
    // The constraint is `(enabler − is_first_block) · (h_in − h_out_prev) = 0`.
    // We evaluate it directly on the trace data (the same style as
    // `linear_identities_hold_for_*` above) rather than driving Stwo's
    // `AssertEvaluator` — the latter would require a finalized
    // interaction trace, which depends on 3.9.2's shared-foundation
    // carry range-checks. The roadmap-mandated mutation case (an `h_in`
    // mutation on a non-first block row triggering rejection) is exactly
    // what this formula catches, so the test is structurally faithful to
    // the AIR even though it doesn't route through `Sha256Eval::evaluate`.
    // 3.9.8 wires the AssertEvaluator-based suite once the interaction
    // trace is available.
    // ------------------------------------------------------------------

    /// Coset-order predecessor of `slot` in a bit-reversed circle-domain
    /// trace of size `2^log_size`. Mirrors `AssertEvaluator`'s `off = -1`
    /// path so a trace-level residual computation lines up with the
    /// constraint values the AIR would emit on the same data.
    fn coset_predecessor_slot(slot: usize, log_size: u32) -> usize {
        use stwo::core::utils::{
            bit_reverse_index, circle_domain_index_to_coset_index,
            coset_index_to_circle_domain_index,
        };
        let domain_size = 1isize << log_size;
        let coset_index =
            circle_domain_index_to_coset_index(bit_reverse_index(slot, log_size), log_size)
                as isize;
        let prev_coset = (coset_index - 1).rem_euclid(domain_size) as usize;
        bit_reverse_index(
            coset_index_to_circle_domain_index(prev_coset, log_size),
            log_size,
        )
    }

    /// For one row `slot` of `trace`, compute every block-chain limb
    /// residual the AIR emits at that point:
    ///
    /// ```text
    /// resid[j].lo = (enabler[slot] − is_first_block[slot])
    ///                 · (h_in[j].lo[slot] − h_out[j].lo[slot − 1 coset])
    /// resid[j].hi = …  (analogous)
    /// ```
    ///
    /// Returns a `Vec<(i64, i64)>` of length `N_STATE_WORDS` so callers
    /// can either assert all-zero (honest) or assert at least one
    /// non-zero (mutated).
    fn block_chain_residuals(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        slot: usize,
        log_size: u32,
    ) -> Vec<(i64, i64)> {
        let prev_slot = coset_predecessor_slot(slot, log_size);
        let enabler = trace[Layout::COL_ENABLER][slot].0 as i64;
        let is_first = trace[Layout::COL_IS_FIRST_BLOCK][slot].0 as i64;
        let gate = enabler - is_first;
        (0..N_STATE_WORDS)
            .map(|j| {
                let (h_in_lo, h_in_hi) = Layout::h_in_word(j);
                let (h_out_lo, h_out_hi) = Layout::h_out_word(j);
                let lo_diff = trace[h_in_lo][slot].0 as i64 - trace[h_out_lo][prev_slot].0 as i64;
                let hi_diff = trace[h_in_hi][slot].0 as i64 - trace[h_out_hi][prev_slot].0 as i64;
                (gate * lo_diff, gate * hi_diff)
            })
            .collect()
    }

    /// Honest multi-block trace: every slot — first-block, continuation,
    /// padding — yields all-zero chain residuals. Covers the gating
    /// truth-table the constraint relies on (first-block vacuous via
    /// `is_first_block`, padding vacuous via `enabler`, chain active
    /// in-between).
    #[test]
    fn chain_constraint_is_zero_on_honest_multi_block_trace() {
        let witness = compute_sha256_witness(&[0xABu8; 200]);
        assert!(witness.blocks.len() >= 2, "need ≥2 blocks for the chain");
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let n_rows = 1usize << log_size;
        for slot in 0..n_rows {
            let residuals = block_chain_residuals(&trace, slot, log_size);
            for (j, (lo, hi)) in residuals.iter().enumerate() {
                assert_eq!(
                    *lo, 0,
                    "chain residual nonzero on honest trace: slot {slot}, h[{j}].lo"
                );
                assert_eq!(
                    *hi, 0,
                    "chain residual nonzero on honest trace: slot {slot}, h[{j}].hi"
                );
            }
        }
    }

    /// Mutating block 1's `h_in[0].lo` must break the chain constraint
    /// at block 1's row (and only there — block 0's row stays vacuous
    /// because `is_first_block = 1`). This is the roadmap-mandated 3.9.6
    /// negative case and the seed for 3.9.8's broader mutation suite.
    #[test]
    fn chain_constraint_rejects_h_in_mutation_on_block_1() {
        let witness = compute_sha256_witness(&[0xABu8; 200]);
        assert!(witness.blocks.len() >= 2, "need multi-block message");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);

        // Mutate `h_in[0].lo` of block 1 to a value that cannot equal
        // block 0's `h_out[0].lo`. Block 0's h_out is a SHA-256
        // compression from `IV` over an all-`0xAB` block — not `0xFFFF`,
        // so the assert_ne below is defensive but expected to hold.
        let block_1_slot = Layout::block_slot(1, log_size);
        let block_0_slot = Layout::block_slot(0, log_size);
        let (h_in_lo, _) = Layout::h_in_word(0);
        let (h_out_lo, _) = Layout::h_out_word(0);
        assert_ne!(
            trace[h_in_lo][block_1_slot].0, 0xFFFFu32,
            "mutation target must change the cell",
        );
        trace[h_in_lo][block_1_slot] = stwo::core::fields::m31::BaseField::from(0xFFFFu32);

        // Block 1's chain residual is now non-zero: the gate is
        // `enabler(1) − is_first_block(0) = 1` and the limb difference
        // is `0xFFFF − h_out[0].lo @ block_0_slot ≠ 0`.
        let residuals = block_chain_residuals(&trace, block_1_slot, log_size);
        let expected_diff = 0xFFFFi64 - trace[h_out_lo][block_0_slot].0 as i64;
        assert_eq!(
            residuals[0].0, expected_diff,
            "chain residual at block 1, H[0].lo should reflect the mutation",
        );
        assert_ne!(
            residuals[0].0, 0,
            "AIR rejects the mutated trace via the chain constraint"
        );

        // Block 0's chain residual stays zero — the `is_first_block` gate
        // makes the constraint vacuous on the first-block row, so the
        // mutation at block 1 does not falsely poison block 0.
        let block_0_residuals = block_chain_residuals(&trace, block_0_slot, log_size);
        for (lo, hi) in block_0_residuals {
            assert_eq!(lo, 0, "first-block row must remain vacuous after mutation");
            assert_eq!(hi, 0, "first-block row must remain vacuous after mutation");
        }
    }

    // ------------------------------------------------------------------
    // §10.4 padding-role constraints (roadmap 3.9.7)
    //
    // Each constraint is evaluated directly on the trace data, mirroring
    // the algebraic expression `Sha256Eval::evaluate` emits. The format
    // matches the §10.3 chain tests above: a positive case (honest trace
    // ⇒ every residual is zero) plus per-class mutation cases (one
    // constraint goes non-zero per mutation). 3.9.8 wires the same suite
    // through `AssertEvaluator` once the interaction trace is available.
    // ------------------------------------------------------------------

    /// Read trace cell `(col, row)` as `i64`. M31 values are non-negative
    /// integers `< 2³¹`, well inside `i64`.
    fn cell(trace: &[Vec<stwo::core::fields::m31::BaseField>], col: usize, row: usize) -> i64 {
        trace[col][row].0 as i64
    }

    /// All padding-row residuals for one slot. The AIR emits these as
    /// individual constraints; the test asserts each one is zero on an
    /// honest trace. A negative-test mutation flips at least one entry
    /// to non-zero.
    ///
    /// Order matches the constraint emission order in
    /// `Sha256Eval::evaluate` so a residual index here can be traced back
    /// to a specific algebraic identity.
    fn padding_residuals(
        trace: &[Vec<stwo::core::fields::m31::BaseField>],
        slot: usize,
    ) -> Vec<i64> {
        let v = |col: usize| cell(trace, col, slot);
        let is_marker_block = v(Layout::COL_IS_MARKER_BLOCK);
        let is_length_block = v(Layout::COL_IS_LENGTH_BLOCK);
        let is_length_only_block = v(Layout::COL_IS_LENGTH_ONLY_BLOCK);
        let is_marker_only_block = v(Layout::COL_IS_MARKER_ONLY_BLOCK);
        let is_marker_word: [i64; 16] = std::array::from_fn(|j| v(Layout::is_marker_word(j)));
        let marker_byte_sel: [i64; 4] = std::array::from_fn(|b| v(Layout::marker_byte_sel(b)));
        let marker_word_byte: [i64; 4] = std::array::from_fn(|b| v(Layout::marker_word_byte(b)));
        let marker_word_post_strict_15 = v(Layout::COL_MARKER_WORD_POST_STRICT_15);
        let bit_length_w14_lo = v(Layout::COL_BIT_LENGTH_W14_LO);
        let bit_length_w14_hi = v(Layout::COL_BIT_LENGTH_W14_HI);
        let bit_length_w15_lo = v(Layout::COL_BIT_LENGTH_W15_LO);
        let bit_length_w15_hi = v(Layout::COL_BIT_LENGTH_W15_HI);

        let w_lo = |j: usize| v(Layout::schedule_word(j).0);
        let w_hi = |j: usize| v(Layout::schedule_word(j).1);

        let mut out = Vec::new();

        // (P.A) binary flags
        for &x in &[
            is_marker_block,
            is_length_block,
            is_length_only_block,
            is_marker_only_block,
            marker_word_post_strict_15,
        ] {
            out.push(x * (1 - x));
        }
        for &x in is_marker_word.iter() {
            out.push(x * (1 - x));
        }
        for &x in marker_byte_sel.iter() {
            out.push(x * (1 - x));
        }

        // (P.B) one-hot sums
        let sum_imw: i64 = is_marker_word.iter().sum();
        out.push(sum_imw - is_marker_block);
        let sum_mbs: i64 = marker_byte_sel.iter().sum();
        out.push(sum_mbs - is_marker_block);

        // (P.C) aux flag definitions
        out.push(is_length_only_block - (1 - is_marker_block) * is_length_block);
        out.push(is_marker_only_block - is_marker_block * (1 - is_length_block));

        // Cumulative marker-word selector (strictly-before-j).
        let mut cum = [0i64; 16];
        for j in 1..16 {
            cum[j] = cum[j - 1] + is_marker_word[j - 1];
        }

        // (P.C') post-strict aux for j = 15. (The symmetric `_14` aux
        // was dropped — see the constraint-emit site for the rationale.)
        out.push(marker_word_post_strict_15 - cum[15] * (1 - is_length_block));

        // (P.D) marker-word byte assembly.
        let sum_w_hi: i64 = (0..16).map(|j| is_marker_word[j] * w_hi(j)).sum();
        let sum_w_lo: i64 = (0..16).map(|j| is_marker_word[j] * w_lo(j)).sum();
        out.push(sum_w_hi - 256 * marker_word_byte[0] - marker_word_byte[1]);
        out.push(sum_w_lo - 256 * marker_word_byte[2] - marker_word_byte[3]);

        // (P.E) marker byte = 0x80.
        for b in 0..4 {
            out.push(marker_byte_sel[b] * (marker_word_byte[b] - 0x80));
        }

        // (P.F) bytes after marker = 0.
        let mut cum_bs = 0i64;
        for b in 0..4 {
            out.push(cum_bs * marker_word_byte[b]);
            cum_bs += marker_byte_sel[b];
        }

        // (P.G) words after marker = 0 (with length-block exception).
        // Range loop mirrors the AIR's constraint emission order; the
        // body calls `w_lo(j)`/`w_hi(j)` closures, so an iterator form
        // over `cum` would read worse than the index loop.
        #[allow(clippy::needless_range_loop)]
        for j in 0..14 {
            let gate = cum[j] + is_length_only_block;
            out.push(gate * w_lo(j));
            out.push(gate * w_hi(j));
        }
        out.push(marker_word_post_strict_15 * w_lo(15));
        out.push(marker_word_post_strict_15 * w_hi(15));

        // (P.H) length-field encoding.
        out.push(is_length_block * (w_lo(14) - bit_length_w14_lo));
        out.push(is_length_block * (w_hi(14) - bit_length_w14_hi));
        out.push(is_length_block * (w_lo(15) - bit_length_w15_lo));
        out.push(is_length_block * (w_hi(15) - bit_length_w15_hi));

        out
    }

    /// Assert every padding residual at every real-block slot is zero.
    /// Padding rows (`enabler = 0`) are *not* exempt because the padding
    /// constraints are emitted without an explicit `enabler` factor —
    /// they instead rely on every padding-region cell being 0 by default
    /// trace fill, which makes each algebraic identity trivially satisfied
    /// there. This test covers both invariants in one pass.
    fn assert_padding_holds_for_message(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let n_rows = 1usize << log_size;
        for slot in 0..n_rows {
            for (i, &r) in padding_residuals(&trace, slot).iter().enumerate() {
                assert_eq!(
                    r,
                    0,
                    "padding residual #{i} non-zero on honest trace at slot {slot} (msg.len()={})",
                    msg.len(),
                );
            }
        }
    }

    /// Case A (single trailing block, msg.len() % 64 ∈ [0, 56)):
    /// the empty message ⇒ one block with marker at byte 0 and length
    /// at bytes [56, 64). Smallest possible padded trace.
    #[test]
    fn padding_constraints_hold_for_empty_message() {
        assert_padding_holds_for_message(b"");
    }

    /// Case A, marker in middle of a word: "abc" puts the marker at
    /// byte 3 of `W[0]` (the LSB byte), with bytes 0..3 carrying the
    /// message tail. Exercises every (P.D)/(P.E)/(P.F) byte-position
    /// branch on a marker word with non-zero pre-marker bytes.
    #[test]
    fn padding_constraints_hold_for_abc() {
        assert_padding_holds_for_message(b"abc");
    }

    /// Case B (overflow, marker in penultimate block): `msg.len() = 56`
    /// pushes the length into a second padding-only block. Exercises the
    /// `is_marker_only_block` and `is_length_only_block` aux flags and
    /// the (P.G) "all of W[0..14] is zero in the length-only block" path.
    #[test]
    fn padding_constraints_hold_for_56_byte_message() {
        let msg: Vec<u8> = (0..56u8).collect();
        assert_padding_holds_for_message(&msg);
    }

    /// Larger multi-block example to triple-check `is_marker_block = 0`
    /// pure-message blocks emit no constraint violation. 200 bytes ⇒
    /// 4 blocks: blocks 0–2 are pure message, block 3 is the marker
    /// and length block (Case A).
    #[test]
    fn padding_constraints_hold_for_multi_block_message() {
        assert_padding_holds_for_message(&[0xABu8; 200]);
    }

    /// Marker-offset mutation: shift the `marker_byte_sel` one-hot so
    /// the AIR thinks the marker is at a different byte position than
    /// the actual `0x80` in `W[k]`. Covers roadmap 3.9.7's "wrong marker
    /// offset" negative case (and is the marker-byte direct analogue of
    /// 3.9.8's marker-position-shift mutation class).
    #[test]
    fn padding_rejects_marker_byte_sel_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::block_slot(0, log_size);

        // Honest: marker at byte 3 of W[0]; marker_byte_sel[3] == 1,
        // others 0.
        assert_eq!(cell(&trace, Layout::marker_byte_sel(3), slot), 1);
        // Move the selector to byte 0 — claiming the 0x80 is the MSB.
        trace[Layout::marker_byte_sel(3)][slot] = stwo::core::fields::m31::BaseField::from(0u32);
        trace[Layout::marker_byte_sel(0)][slot] = stwo::core::fields::m31::BaseField::from(1u32);

        let residuals = padding_residuals(&trace, slot);
        assert!(
            residuals.iter().any(|&r| r != 0),
            "AIR must reject a marker_byte_sel mutation"
        );
    }

    /// Length-field mutation: bump `W[15]` of the length block while
    /// leaving `bit_length_w15_*` untouched. The (P.H) identity goes
    /// non-zero.
    #[test]
    fn padding_rejects_length_field_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::block_slot(0, log_size);
        assert_eq!(cell(&trace, Layout::COL_IS_LENGTH_BLOCK, slot), 1);

        // Honest: W[15] = bit length 24 (0x18) ⇒ W[15].lo = 0x18.
        let (w15_lo, _) = Layout::schedule_word(15);
        assert_eq!(cell(&trace, w15_lo, slot), 0x18);
        trace[w15_lo][slot] = stwo::core::fields::m31::BaseField::from(0x99u32);

        let residuals = padding_residuals(&trace, slot);
        assert!(
            residuals.iter().any(|&r| r != 0),
            "AIR must reject a length-field mutation"
        );
    }

    /// Non-zero fill-byte mutation: a real "abc" trace has `W[1..14]`
    /// all zero (the zero-fill between the marker and the length).
    /// Setting `W[5]` to a non-zero value violates the (P.G) "words
    /// after marker are zero" identity.
    #[test]
    fn padding_rejects_non_zero_fill_word_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::block_slot(0, log_size);

        // Honest: W[5] is in the zero-fill region.
        let (w5_lo, _) = Layout::schedule_word(5);
        assert_eq!(cell(&trace, w5_lo, slot), 0);
        trace[w5_lo][slot] = stwo::core::fields::m31::BaseField::from(0x42u32);

        let residuals = padding_residuals(&trace, slot);
        assert!(
            residuals.iter().any(|&r| r != 0),
            "AIR must reject a non-zero fill word mutation"
        );
    }

    /// Marker-word-index mutation: shift the `is_marker_word` one-hot
    /// to a different word. The (P.D) byte-assembly identity goes
    /// non-zero — the bytes committed for the marker word are still the
    /// real `W[0]`'s bytes, but the AIR now reads `W[j]` for the
    /// new `j`.
    #[test]
    fn padding_rejects_marker_word_index_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::block_slot(0, log_size);

        // Honest: marker at W[0].
        assert_eq!(cell(&trace, Layout::is_marker_word(0), slot), 1);
        trace[Layout::is_marker_word(0)][slot] = stwo::core::fields::m31::BaseField::from(0u32);
        trace[Layout::is_marker_word(5)][slot] = stwo::core::fields::m31::BaseField::from(1u32);

        let residuals = padding_residuals(&trace, slot);
        assert!(
            residuals.iter().any(|&r| r != 0),
            "AIR must reject a marker-word-index mutation"
        );
    }

    /// Bit-length-limb mutation: the prover claims a different
    /// `bit_length_w15_lo` than what `W[15]` actually holds. (P.H)
    /// catches this. This is the direct analogue of the "wrong message
    /// length claim" attack the post-2.4 cross-component binding closes;
    /// today it surfaces as the on-row inconsistency the AIR rejects.
    #[test]
    fn padding_rejects_bit_length_limb_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::block_slot(0, log_size);

        // Honest: bit_length_w15_lo = 0x18 (bit length for "abc" is 24).
        assert_eq!(cell(&trace, Layout::COL_BIT_LENGTH_W15_LO, slot), 0x18);
        trace[Layout::COL_BIT_LENGTH_W15_LO][slot] =
            stwo::core::fields::m31::BaseField::from(0x42u32);

        let residuals = padding_residuals(&trace, slot);
        assert!(
            residuals.iter().any(|&r| r != 0),
            "AIR must reject a bit-length limb mutation"
        );
    }

    /// Block-alignment (`padded.len() % 64 == 0`) is structural — one
    /// trace row IS one 64-byte block — so the AIR cannot represent a
    /// partial block. No per-row constraint expresses this requirement;
    /// the trace shape itself does. This test documents that invariant
    /// at the structural level by asserting every honest message yields
    /// `padded.len() % BLOCK_BYTES == 0`, exercising the natural
    /// `n_blocks · BLOCK_BYTES = padded.len()` identity FIPS §5.1.1
    /// implies and which the witness layer assumes.
    #[test]
    fn padded_length_is_always_block_aligned() {
        use crate::constants::BLOCK_BYTES;
        for n in [0usize, 1, 3, 55, 56, 57, 63, 64, 65, 127, 128, 200, 511] {
            let witness = compute_sha256_witness(&vec![0xABu8; n]);
            assert_eq!(
                witness.padding.padded.len() % BLOCK_BYTES,
                0,
                "padded length not block-aligned for msg.len()={n}",
            );
            assert_eq!(
                witness.padding.padded.len(),
                witness.padding.n_blocks * BLOCK_BYTES,
                "n_blocks · BLOCK_BYTES != padded.len() for msg.len()={n}",
            );
        }
    }
}
