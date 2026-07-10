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
//! decompositions, and the **split-and-pack lookups** that pin
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
//! the mdoc-parser stream lands with the integration layer (mdoc/COSE
//! structure analysis).
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

use crate::components::{is_first_row_column_id, round_cyclic_column_ids};
use crate::constants::{DIGEST_BYTES, IV, N_STATE_WORDS};
use crate::field_exposure::FieldExposure;
use crate::partitions::{
    round_groups_half_indices, RoundGroups, GROUPS_PER_ROUND_PARTITION, SIGMA0_GROUPS,
    SIGMA1_GROUPS,
};
use crate::relations::Sha256Relations;
use crate::trace::WORD_BIT_COLS;
use crate::types::{BYTES_PER_WORD, LIMB_BITS, WORDS_PER_BLOCK};

/// AIR evaluator over the rotated one-row-per-round layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (the smallest power of two **strictly**
    /// greater than `64 · block count`, per [`crate::trace::min_log_size`]).
    pub log_size: u32,
    /// LogUp channels: `Σ`/`σ` decode tables (8), packed Maj/Ch (2),
    /// chunk-wise `xor_8` (1), the four `Range_k` channels, and the
    /// cross-component `Sha256Digest` channel.
    pub relations: Sha256Relations,
    /// When set, the AIR *yields* the final-block digest bytes on the
    /// `Sha256Digest` channel (the producer half of the `SHA_DIGEST ↔ ECDSA_Z`
    /// binding). Off for the standalone SHA proof — the digest has no
    /// in-module consumer, so yielding it would leave the module's claimed
    /// sum non-zero and the standalone proof would not self-balance. The
    /// combined prover sets it once a consumer (P256 `z`) is composed in. The
    /// `is_last_block` flag, the digest byte columns, and their decomposition
    /// constraints are present and enforced regardless — only the
    /// cross-module *yield* is gated.
    pub expose_digest: bool,
    /// Credential-field byte exposure. When non-empty, the AIR commits a
    /// byte-decomposition of each covered message word as a dynamic column tail
    /// (live on `t = 15` rows) and *yields* the configured byte windows on the
    /// **first block** over the `Sha256Field` channel, so predicate consumers
    /// can require the exact bytes of the field they bind. Empty for a
    /// standalone SHA proof and for the combined proof before the predicate
    /// consumers are wired (yields with no consumer would leave the module's
    /// claimed sum non-zero). The byte columns and their decomposition
    /// constraints exist iff the exposure is non-empty; the cross-module yield
    /// is what binds.
    pub field_exposure: FieldExposure,
}

impl FrameworkEval for Sha256Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Constraints here are degree ≤ 3: a degree-2 boundary gate
        // (`enabler · is_round_k`, with the indicator preprocessed) times a
        // linear identity, or `enabler` times a degree-2 boundary-select
        // expression. `log_size + 1` covers D ≤ 3 — the same budget the
        // P256 components in the composed proof already use. The `+1` is
        // the standard FRI headroom.
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // ---- preprocessed round-cyclic columns ----
        //
        // All functions of `t = natural_row mod 64` alone, committed once
        // per circuit (see `crate::preprocessed`): the round constant
        // `K[t]`'s limbs, the boundary indicators, and the schedule gate.
        let cyclic = round_cyclic_column_ids();
        let k_lo = eval.get_preprocessed_column(cyclic[0].clone());
        let k_hi = eval.get_preprocessed_column(cyclic[1].clone());
        let r0 = eval.get_preprocessed_column(cyclic[2].clone());
        let r1 = eval.get_preprocessed_column(cyclic[3].clone());
        let r2 = eval.get_preprocessed_column(cyclic[4].clone());
        let r3 = eval.get_preprocessed_column(cyclic[5].clone());
        let r15 = eval.get_preprocessed_column(cyclic[6].clone());
        let r63 = eval.get_preprocessed_column(cyclic[7].clone());
        let is_sched = eval.get_preprocessed_column(cyclic[8].clone());
        // `is_first_row` pins exactly one anchor row (natural row 0 = block
        // 0, round 0) for IV binding.
        let is_first_row = eval.get_preprocessed_column(is_first_row_column_id());

        // ---- header ----
        //
        // `enabler` is read with a `[0, -1, 1]` cross-row mask so the
        // contiguity constraint can pin `enabler_prev` (first-real-row
        // marker `enabler_step`) and the digest gate can pin `enabler_next`
        // (last-real-row marker `is_last_block`).
        let [enabler, enabler_prev, enabler_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, 1]);
        eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));

        // The row-family gates. Each is `enabler · indicator` — degree 2,
        // used both as constraint gates and as LogUp multiplicities.
        let gate_r0 = enabler.clone() * r0.clone();
        let gate_r15 = enabler.clone() * r15.clone();
        let gate_r63 = enabler.clone() * r63.clone();
        let gate_sched = enabler.clone() * is_sched.clone();

        // ---- W: the row's schedule word, read at every offset any family
        // needs. `w[k]` is `W[t−k]`: the schedule recurrence reads k ∈
        // {2, 7, 15, 16}; the `t = 15` padding/field families read the
        // block's message words `W[j] = w[15−j]`, j ∈ [0, 16).
        let w_lo = eval.next_interaction_mask(
            ORIGINAL_TRACE_IDX,
            [
                0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14, -15, -16,
            ],
        );
        let w_hi = eval.next_interaction_mask(
            ORIGINAL_TRACE_IDX,
            [
                0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14, -15, -16,
            ],
        );
        let w: [(E::F, E::F); 17] = std::array::from_fn(|k| (w_lo[k].clone(), w_hi[k].clone()));
        let w_bits_m: [[E::F; 3]; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -2, -15]));
        let w_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bits_m[i][0].clone());

        // ---- round family: outputs, carries, Σ-decodes, packed groups ----
        //
        // Column order matches `trace::write_round_row`: σ0, σ1, ch, maj,
        // t1, t2 read at offset 0; a_new / e_new additionally at offsets
        // −1..−4 (they carry the working state across rows).
        let sigma0 = (eval.next_trace_mask(), eval.next_trace_mask());
        let sigma1 = (eval.next_trace_mask(), eval.next_trace_mask());
        let ch = (eval.next_trace_mask(), eval.next_trace_mask());
        let maj = (eval.next_trace_mask(), eval.next_trace_mask());
        let t1 = (eval.next_trace_mask(), eval.next_trace_mask());
        let t2 = (eval.next_trace_mask(), eval.next_trace_mask());
        let a_new_lo = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -4]);
        let a_new_hi = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -4]);
        let e_new_lo = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -4]);
        let e_new_hi = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -4]);
        let a_new = (a_new_lo[0].clone(), a_new_hi[0].clone());
        let e_new = (e_new_lo[0].clone(), e_new_hi[0].clone());

        let t1_carry = (eval.next_trace_mask(), eval.next_trace_mask());
        let t2_carry = (eval.next_trace_mask(), eval.next_trace_mask());
        let e_new_carry = (eval.next_trace_mask(), eval.next_trace_mask());
        let a_new_carry = (eval.next_trace_mask(), eval.next_trace_mask());

        let a_bits_m: [[E::F; 3]; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2]));
        let b_bits_m: [[E::F; 2]; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]));
        let c_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|_| eval.next_trace_mask());
        let e_bits_m: [[E::F; 3]; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2]));
        let f_bits_m: [[E::F; 2]; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]));
        let g_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|_| eval.next_trace_mask());
        let a_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| a_bits_m[i][0].clone());
        let b_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| b_bits_m[i][0].clone());
        let e_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| e_bits_m[i][0].clone());
        let f_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| f_bits_m[i][0].clone());

        // Packed output groups retained only for the surviving round
        // split-pack lookups. Their values are constrained below from
        // virtual Maj/Ch bit expressions.
        let maj_grp: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let ch_grp: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let a_grp: [E::F; GROUPS_PER_ROUND_PARTITION] =
            pack_round_group_exprs::<E>(&a_bits, &SIGMA0_GROUPS);
        let e_grp: [E::F; GROUPS_PER_ROUND_PARTITION] =
            pack_round_group_exprs::<E>(&e_bits, &SIGMA1_GROUPS);

        // ---- schedule family (live t ≥ 16) ----
        let s0 = (eval.next_trace_mask(), eval.next_trace_mask());
        let s1 = (eval.next_trace_mask(), eval.next_trace_mask());
        let sched_carry_lo = eval.next_trace_mask();
        let sched_carry_hi = eval.next_trace_mask();
        let sched_sigma0_bits: [E::F; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let sched_sigma1_bits: [E::F; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let sched_sigma0_split = read_sigma_input_split::<E>(&mut eval);
        let sched_sigma1_split = read_sigma_input_split::<E>(&mut eval);

        // ---- t = 0 family ----
        //
        // `is_first_block` is also read at offset −15: the field-exposure
        // family on the `t = 15` row gates its range checks and yields by
        // "is this block 0", which lives 15 rows up.
        let [is_first_block, is_first_block_m15] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -15]);
        // C1 anchors: pin `is_first_block ≡ is_first_row` and force the
        // anchor row to be committed as a real row.
        eval.add_constraint(is_first_block.clone() - is_first_row.clone());
        eval.add_constraint(is_first_row.clone() * (E::F::one() - enabler.clone()));

        // `h_in`: this block's input state (t = 0 row), laid out (lo, hi)
        // per word — reads interleave accordingly. Offsets −1..−3 feed the
        // working-state boundary selects on rows t ∈ {1, 2, 3}; offset −63
        // feeds the finalization adds on the t = 63 row of the same block.
        let mut h_in_lo: [[E::F; 5]; N_STATE_WORDS] =
            std::array::from_fn(|_| std::array::from_fn(|_| E::F::from(M31::from(0u32))));
        let mut h_in_hi: [[E::F; 5]; N_STATE_WORDS] =
            std::array::from_fn(|_| std::array::from_fn(|_| E::F::from(M31::from(0u32))));
        for j in 0..N_STATE_WORDS {
            h_in_lo[j] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -63]);
            h_in_hi[j] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -63]);
        }

        // IV binding on the anchor row.
        for (j, &iv_word) in IV.iter().enumerate() {
            let iv_lo = E::F::from(M31::from(iv_word & 0xFFFF));
            let iv_hi = E::F::from(M31::from(iv_word >> LIMB_BITS));
            eval.add_constraint(is_first_block.clone() * (h_in_lo[j][0].clone() - iv_lo));
            eval.add_constraint(is_first_block.clone() * (h_in_hi[j][0].clone() - iv_hi));
        }

        // §8.1 reuse-chain initial splits (t = 0 row): b/c/f/g_init, each
        // read at offsets [0, −1] (row t = 1 seeds its `c`/`g` duplicates
        // from the previous row's aux cells).
        let b_init: [[E::F; 2]; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]));
        let c_init: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let f_init: [[E::F; 2]; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]));
        let g_init: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|_| eval.next_trace_mask());

        let (sigma0_lo_idx, sigma0_hi_idx) = round_groups_half_indices(&SIGMA0_GROUPS);
        let (sigma1_lo_idx, sigma1_hi_idx) = round_groups_half_indices(&SIGMA1_GROUPS);

        // Aux split-and-pack lookups (8 sites), gated to t = 0 rows.
        let b_init_now: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|i| b_init[i][0].clone());
        let f_init_now: [E::F; GROUPS_PER_ROUND_PARTITION] =
            std::array::from_fn(|i| f_init[i][0].clone());
        let h_in_word =
            |j: usize| -> (E::F, E::F) { (h_in_lo[j][0].clone(), h_in_hi[j][0].clone()) };
        let h_in_0 = h_in_word(0);
        let h_in_1 = h_in_word(1);
        let h_in_2 = h_in_word(2);
        let h_in_4 = h_in_word(4);
        let h_in_5 = h_in_word(5);
        let h_in_6 = h_in_word(6);
        wire_round_split_pack::<E>(
            &mut eval,
            gate_r0.clone(),
            &h_in_1,
            &b_init_now,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            gate_r0.clone(),
            &h_in_2,
            &c_init,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            gate_r0.clone(),
            &h_in_5,
            &f_init_now,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            gate_r0.clone(),
            &h_in_6,
            &g_init,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );

        // ---- schedule constraints (gate: enabler · is_schedule) ----
        //
        // W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16] (mod 2³²).
        // The lower-σ bit formulas are deliberately ungated so their degree-3
        // xor expressions are not multiplied by `gate_sched`; only the linear
        // recomposition into the live schedule limbs is gated.
        let w_m15_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bits_m[i][2].clone());
        let w_m2_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bits_m[i][1].clone());
        let lower_sigma0_bits = lower_sigma0_expr_bits::<E>(&w_m15_bits);
        let lower_sigma1_bits = lower_sigma1_expr_bits::<E>(&w_m2_bits);
        constrain_bits_equal::<E>(&mut eval, &sched_sigma0_bits, &lower_sigma0_bits);
        constrain_bits_equal::<E>(&mut eval, &sched_sigma1_bits, &lower_sigma1_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_sched.clone(), &s0, &sched_sigma0_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_sched.clone(), &s1, &sched_sigma1_bits);
        wire_sigma_input_split::<E>(
            &mut eval,
            gate_sched.clone(),
            &w[15],
            &sched_sigma0_split,
            &self.relations.split_pack.lower_sigma0_lo,
            &self.relations.split_pack.lower_sigma0_hi,
        );
        wire_sigma_input_split::<E>(
            &mut eval,
            gate_sched.clone(),
            &w[2],
            &sched_sigma1_split,
            &self.relations.split_pack.lower_sigma1_lo,
            &self.relations.split_pack.lower_sigma1_hi,
        );
        emit_mod_2_32_add_linear(
            &mut eval,
            gate_sched.clone(),
            &[s1.clone(), w[7].clone(), s0.clone(), w[16].clone()],
            &w[0],
            &sched_carry_lo,
            &sched_carry_hi,
            crate::components::RangeKind::Range4,
            &self.relations,
        );

        // ---- working-state boundary selects ----
        //
        // The state entering round `t` is, per slot, either an earlier
        // row's `a_new`/`e_new` or (for t ∈ {0..3}) an `h_in` word of the
        // t = 0 row, selected by the preprocessed round indicators. Each
        // select is a degree-2 expression; it only ever appears inside
        // `enabler`-gated linear identities (degree ≤ 3 total).
        let not_r0 = E::F::one() - r0.clone();
        let not_r01 = E::F::one() - r0.clone() - r1.clone();
        let not_r012 = E::F::one() - r0.clone() - r1.clone() - r2.clone();
        let not_r0123 = E::F::one() - r0.clone() - r1.clone() - r2.clone() - r3.clone();
        let boundary_select = |h_word: [usize; 4],
                               new_lo: &[E::F; 5],
                               new_hi: &[E::F; 5],
                               slot: usize|
         -> (E::F, E::F) {
            // slot 0 → a/e (uses h_in[h_word[0]]@0, new@−1),
            // slot 1 → b/f, slot 2 → c/g, slot 3 → d/h.
            match slot {
                0 => (
                    r0.clone() * h_in_lo[h_word[0]][0].clone() + not_r0.clone() * new_lo[1].clone(),
                    r0.clone() * h_in_hi[h_word[0]][0].clone() + not_r0.clone() * new_hi[1].clone(),
                ),
                1 => (
                    r0.clone() * h_in_lo[h_word[1]][0].clone()
                        + r1.clone() * h_in_lo[h_word[0]][1].clone()
                        + not_r01.clone() * new_lo[2].clone(),
                    r0.clone() * h_in_hi[h_word[1]][0].clone()
                        + r1.clone() * h_in_hi[h_word[0]][1].clone()
                        + not_r01.clone() * new_hi[2].clone(),
                ),
                2 => (
                    r0.clone() * h_in_lo[h_word[2]][0].clone()
                        + r1.clone() * h_in_lo[h_word[1]][1].clone()
                        + r2.clone() * h_in_lo[h_word[0]][2].clone()
                        + not_r012.clone() * new_lo[3].clone(),
                    r0.clone() * h_in_hi[h_word[2]][0].clone()
                        + r1.clone() * h_in_hi[h_word[1]][1].clone()
                        + r2.clone() * h_in_hi[h_word[0]][2].clone()
                        + not_r012.clone() * new_hi[3].clone(),
                ),
                3 => (
                    r0.clone() * h_in_lo[h_word[3]][0].clone()
                        + r1.clone() * h_in_lo[h_word[2]][1].clone()
                        + r2.clone() * h_in_lo[h_word[1]][2].clone()
                        + r3.clone() * h_in_lo[h_word[0]][3].clone()
                        + not_r0123.clone() * new_lo[4].clone(),
                    r0.clone() * h_in_hi[h_word[3]][0].clone()
                        + r1.clone() * h_in_hi[h_word[2]][1].clone()
                        + r2.clone() * h_in_hi[h_word[1]][2].clone()
                        + r3.clone() * h_in_hi[h_word[0]][3].clone()
                        + not_r0123.clone() * new_hi[4].clone(),
                ),
                _ => unreachable!(),
            }
        };
        // Only `d` and `h` enter the round adds as words; `a`/`e` enter via
        // their packed-group splits (case-split split-pack lookups below),
        // and `b`/`c`/`f`/`g` only via the committed group duplicates.
        let a_in = boundary_select([0, 1, 2, 3], &a_new_lo, &a_new_hi, 0);
        let e_in = boundary_select([4, 5, 6, 7], &e_new_lo, &e_new_hi, 0);
        let d_in = boundary_select([0, 1, 2, 3], &a_new_lo, &a_new_hi, 3);
        let h_in_state = boundary_select([4, 5, 6, 7], &e_new_lo, &e_new_hi, 3);

        // ---- round constraints ----
        constrain_boolean_bits::<E>(&mut eval, &w_bits);
        constrain_boolean_bits::<E>(&mut eval, &a_bits);
        constrain_boolean_bits::<E>(&mut eval, &b_bits);
        constrain_boolean_bits::<E>(&mut eval, &c_bits);
        constrain_boolean_bits::<E>(&mut eval, &e_bits);
        constrain_boolean_bits::<E>(&mut eval, &f_bits);
        constrain_boolean_bits::<E>(&mut eval, &g_bits);
        constrain_boolean_bits::<E>(&mut eval, &sched_sigma0_bits);
        constrain_boolean_bits::<E>(&mut eval, &sched_sigma1_bits);

        constrain_word_recomposition::<E>(&mut eval, enabler.clone(), &w[0], &w_bits);
        constrain_word_recomposition::<E>(&mut eval, enabler.clone(), &a_in, &a_bits);
        constrain_word_recomposition::<E>(&mut eval, enabler.clone(), &e_in, &e_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_r0.clone(), &h_in_1, &b_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_r0.clone(), &h_in_2, &c_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_r0.clone(), &h_in_5, &f_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_r0.clone(), &h_in_6, &g_bits);

        let gate_r1 = enabler.clone() * r1.clone();
        let gate_not_r0 = enabler.clone() * not_r0.clone();
        let gate_not_r01 = enabler.clone() * not_r01.clone();
        for i in 0..WORD_BIT_COLS {
            eval.add_constraint(gate_not_r0.clone() * (b_bits[i].clone() - a_bits_m[i][1].clone()));
            eval.add_constraint(gate_r1.clone() * (c_bits[i].clone() - b_bits_m[i][1].clone()));
            eval.add_constraint(
                gate_not_r01.clone() * (c_bits[i].clone() - a_bits_m[i][2].clone()),
            );
            eval.add_constraint(gate_not_r0.clone() * (f_bits[i].clone() - e_bits_m[i][1].clone()));
            eval.add_constraint(gate_r1.clone() * (g_bits[i].clone() - f_bits_m[i][1].clone()));
            eval.add_constraint(
                gate_not_r01.clone() * (g_bits[i].clone() - e_bits_m[i][2].clone()),
            );
        }

        let sigma0_bits = big_sigma0_expr_bits::<E>(&a_bits);
        let sigma1_bits = big_sigma1_expr_bits::<E>(&e_bits);
        let maj_bits = maj_expr_bits::<E>(&a_bits, &b_bits, &c_bits);
        let ch_bits = ch_expr_bits::<E>(&e_bits, &f_bits, &g_bits);
        constrain_word_recomposition_ungated::<E>(&mut eval, &sigma0, &sigma0_bits);
        constrain_word_recomposition_ungated::<E>(&mut eval, &sigma1, &sigma1_bits);
        constrain_word_recomposition_ungated::<E>(&mut eval, &maj, &maj_bits);
        constrain_word_recomposition_ungated::<E>(&mut eval, &ch, &ch_bits);
        let maj_grp_expr = pack_round_group_exprs::<E>(&maj_bits, &SIGMA0_GROUPS);
        let ch_grp_expr = pack_round_group_exprs::<E>(&ch_bits, &SIGMA1_GROUPS);
        for i in 0..GROUPS_PER_ROUND_PARTITION {
            eval.add_constraint(maj_grp[i].clone() - maj_grp_expr[i].clone());
            eval.add_constraint(ch_grp[i].clone() - ch_grp_expr[i].clone());
        }

        // Round-side split-and-pack lookups. `maj`/`ch` are fresh outputs
        // committed on this row — a single enabler-gated lookup each. The
        // `a`/`e` operand groups split against the *input* word, which is
        // `a_new@−1` on t ≥ 1 rows and `h_in[0]`/`h_in[4]` on the t = 0
        // row — two complementary-gated lookups per half so every tuple
        // element stays a committed cell.
        let a_prev = (a_new_lo[1].clone(), a_new_hi[1].clone());
        let e_prev = (e_new_lo[1].clone(), e_new_hi[1].clone());
        wire_round_split_pack::<E>(
            &mut eval,
            gate_not_r0.clone(),
            &a_prev,
            &a_grp,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            gate_r0.clone(),
            &h_in_0,
            &a_grp,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            enabler.clone(),
            &maj,
            &maj_grp,
            &sigma0_lo_idx,
            &sigma0_hi_idx,
            &self.relations.split_pack.sigma0_lo,
            &self.relations.split_pack.sigma0_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            gate_not_r0.clone(),
            &e_prev,
            &e_grp,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            gate_r0.clone(),
            &h_in_4,
            &e_grp,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );
        wire_round_split_pack::<E>(
            &mut eval,
            enabler.clone(),
            &ch,
            &ch_grp,
            &sigma1_lo_idx,
            &sigma1_hi_idx,
            &self.relations.split_pack.sigma1_lo,
            &self.relations.split_pack.sigma1_hi,
        );

        // The four mod-2³² adds of the round. K[t] comes from the
        // preprocessed cyclic columns; `h`/`d` are boundary selects.
        let k_t = (k_lo.clone(), k_hi.clone());
        emit_mod_2_32_add_linear(
            &mut eval,
            enabler.clone(),
            &[
                h_in_state.clone(),
                sigma1.clone(),
                ch.clone(),
                k_t,
                w[0].clone(),
            ],
            &t1,
            &t1_carry.0,
            &t1_carry.1,
            crate::components::RangeKind::Range5,
            &self.relations,
        );
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
        emit_mod_2_32_add_linear(
            &mut eval,
            enabler.clone(),
            &[d_in.clone(), t1.clone()],
            &e_new,
            &e_new_carry.0,
            &e_new_carry.1,
            crate::components::RangeKind::Range2,
            &self.relations,
        );
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

        // ---- t = 63 family: finalization, digest, chain ----
        let final_carries: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));

        // h_out, each limb read at [0, −1]: offset 0 feeds the finalization
        // on the t = 63 row; offset −1 feeds the block-chain constraint on
        // the next block's t = 0 row (its coset predecessor is this t = 63
        // row).
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

        // Finalization: h_out[j] = h_in[j] + working[j] (mod 2³²), on the
        // t = 63 row. `h_in[j]` is the same block's t = 0 row (offset −63);
        // `working[j]` is the state after round 63 — `a_new`/`e_new` of
        // this row and the three before it. All addends are committed
        // cells, so the degree-2 gate keeps every constraint ≤ 3.
        let working = |j: usize| -> (E::F, E::F) {
            match j {
                0..=3 => (a_new_lo[j].clone(), a_new_hi[j].clone()),
                4..=7 => (e_new_lo[j - 4].clone(), e_new_hi[j - 4].clone()),
                _ => unreachable!(),
            }
        };
        for j in 0..N_STATE_WORDS {
            let h_in_final = (h_in_lo[j][4].clone(), h_in_hi[j][4].clone());
            emit_mod_2_32_add_linear(
                &mut eval,
                gate_r63.clone(),
                &[h_in_final, working(j)],
                &h_out[j],
                &final_carries[j].0,
                &final_carries[j].1,
                crate::components::RangeKind::Range2,
                &self.relations,
            );
        }

        // Terminal `Range_16` on the block's `h_out` limbs (t = 63 rows).
        for h_out_word in h_out.iter().take(N_STATE_WORDS) {
            wire_range_check::<E>(
                &mut eval,
                gate_r63.clone(),
                h_out_word.0.clone(),
                crate::components::RangeKind::Range16,
                &self.relations,
            );
            wire_range_check::<E>(
                &mut eval,
                gate_r63.clone(),
                h_out_word.1.clone(),
                crate::components::RangeKind::Range16,
                &self.relations,
            );
        }

        // §10.3 multi-block chain, on continuation blocks' t = 0 rows: this
        // block's `h_in` equals the previous block's `h_out` (offset −1 =
        // the predecessor's t = 63 row). The gate `enabler·is_round_0 −
        // is_first_block` is 1 exactly on real continuation t = 0 rows, 0 on
        // the anchor row (IV binding takes over), on rows t ≠ 0 (both sides
        // of the difference are dead-family zeros there), and on padding.
        let chain_gate = gate_r0.clone() - is_first_block.clone();
        for j in 0..N_STATE_WORDS {
            eval.add_constraint(
                chain_gate.clone() * (h_in_lo[j][0].clone() - h_out_prev[j].0.clone()),
            );
            eval.add_constraint(
                chain_gate.clone() * (h_in_hi[j][0].clone() - h_out_prev[j].1.clone()),
            );
        }

        // ---- digest provider: is_last_block gate, byte view, yield ----
        //
        // `is_last_block = enabler · is_round_63 · (1 − enabler_next)`: 1
        // only at the last real row (the final block's t = 63 row, whose
        // successor is padding — guaranteed by `min_log_size`).
        let is_last_block = eval.next_trace_mask();
        eval.add_constraint(
            is_last_block.clone() - gate_r63.clone() * (E::F::one() - enabler_next.clone()),
        );

        // Digest byte view (t = 63 rows): per state word `j` the cells are
        // `[hi.b1, hi.b0, lo.b1, lo.b0]`; each limb recomposes as
        // `limb = 256·b1 + b0`. Limbs are `Range_16`-pinned above; byte
        // range checks are the consumer's responsibility (interface-contract
        // item 4).
        let digest_bytes: [E::F; DIGEST_BYTES] = std::array::from_fn(|_| eval.next_trace_mask());
        let two_pow_8 = E::F::from(M31::from(1u32 << 8));
        for (j, h_out_word) in h_out.iter().enumerate().take(N_STATE_WORDS) {
            eval.add_constraint(
                gate_r63.clone()
                    * (h_out_word.1.clone()
                        - two_pow_8.clone() * digest_bytes[4 * j].clone()
                        - digest_bytes[4 * j + 1].clone()),
            );
            eval.add_constraint(
                gate_r63.clone()
                    * (h_out_word.0.clone()
                        - two_pow_8.clone() * digest_bytes[4 * j + 2].clone()
                        - digest_bytes[4 * j + 3].clone()),
            );
        }
        if self.expose_digest {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.digest.digest,
                -is_last_block.clone(),
                &digest_bytes,
            ));
        }

        // ---- §10.4 padding-role constraints (t = 15 rows) ----
        //
        // Identical algebra to the wide layout; the block's message words
        // `W[j]` are the `W` columns of rows `t = j`, i.e. `w[15 − j]` from
        // here. On every row outside a real t = 15 row all padding cells
        // are zero, so each identity holds vacuously.
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

        // The block's message word `W[j]`, from the t = 15 row's viewpoint.
        let w_msg = |j: usize| -> &(E::F, E::F) { &w[15 - j] };

        // (P.A) Binary checks (ungated — all cells are 0 off-family).
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

        // (P.A') Mn1: pin the padding-role flags to 0 on disabled rows.
        let one_minus_enabler = E::F::one() - enabler.clone();
        for flag in [
            &is_marker_block,
            &is_length_block,
            &is_length_only_block,
            &is_marker_only_block,
        ] {
            eval.add_constraint(one_minus_enabler.clone() * flag.clone());
        }

        // (P.B) One-hot sums match the block role.
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

        // (P.C) Aux-flag definitions.
        eval.add_constraint(
            is_length_only_block.clone()
                - (E::F::one() - is_marker_block.clone()) * is_length_block.clone(),
        );
        eval.add_constraint(
            is_marker_only_block.clone()
                - is_marker_block.clone() * (E::F::one() - is_length_block.clone()),
        );

        // Cumulative one-hot marker-word prefix sums.
        let mut cum_marker_word: [E::F; WORDS_PER_BLOCK] =
            std::array::from_fn(|_| E::F::from(M31::from(0u32)));
        for j in 1..WORDS_PER_BLOCK {
            cum_marker_word[j] = cum_marker_word[j - 1].clone() + is_marker_word[j - 1].clone();
        }

        // (P.C') marker-word post-strict aux for the `W[15]` slot.
        eval.add_constraint(
            marker_word_post_strict_15.clone()
                - cum_marker_word[15].clone() * (E::F::one() - is_length_block.clone()),
        );

        // (P.D) Marker-word byte assembly.
        let byte_base = E::F::from(M31::from(1u32 << 8));
        let mut sum_w_hi = E::F::from(M31::from(0u32));
        let mut sum_w_lo = E::F::from(M31::from(0u32));
        for (j, is_marker) in is_marker_word.iter().enumerate().take(WORDS_PER_BLOCK) {
            sum_w_hi += is_marker.clone() * w_msg(j).1.clone();
            sum_w_lo += is_marker.clone() * w_msg(j).0.clone();
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

        // (P.E) The marker byte is `0x80`.
        let marker_value = E::F::from(M31::from(0x80u32));
        for b in 0..BYTES_PER_WORD {
            eval.add_constraint(
                marker_byte_sel[b].clone() * (marker_word_byte[b].clone() - marker_value.clone()),
            );
        }

        // (P.F) Bytes strictly after the marker byte are zero.
        let mut cum_byte_sel = E::F::from(M31::from(0u32));
        for b in 0..BYTES_PER_WORD {
            eval.add_constraint(cum_byte_sel.clone() * marker_word_byte[b].clone());
            cum_byte_sel += marker_byte_sel[b].clone();
        }

        // (P.G) Words strictly after the marker word are zero (length-field
        // exception; see the wide-layout derivation for the W[14]/W[15]
        // case analysis).
        for (j, cum_marker) in cum_marker_word.iter().enumerate().take(14) {
            let gate = cum_marker.clone() + is_length_only_block.clone();
            eval.add_constraint(gate.clone() * w_msg(j).0.clone());
            eval.add_constraint(gate * w_msg(j).1.clone());
        }
        eval.add_constraint(marker_word_post_strict_15.clone() * w_msg(15).0.clone());
        eval.add_constraint(marker_word_post_strict_15.clone() * w_msg(15).1.clone());

        // (P.H) Length-field encoding.
        eval.add_constraint(
            is_length_block.clone() * (w_msg(14).0.clone() - bit_length_w14_lo.clone()),
        );
        eval.add_constraint(
            is_length_block.clone() * (w_msg(14).1.clone() - bit_length_w14_hi.clone()),
        );
        eval.add_constraint(
            is_length_block.clone() * (w_msg(15).0.clone() - bit_length_w15_lo.clone()),
        );
        eval.add_constraint(
            is_length_block.clone() * (w_msg(15).1.clone() - bit_length_w15_hi.clone()),
        );

        // ---- C1 contiguity (aux column `enabler_step`) ----
        let enabler_step = eval.next_trace_mask();
        eval.add_constraint(
            enabler_step.clone() - enabler.clone() * (E::F::one() - enabler_prev.clone()),
        );
        eval.add_constraint((E::F::one() - is_first_row.clone()) * enabler_step.clone());

        // ---- field provider (target block t = 15 rows) ----
        //
        // The exposed message words are read through the same `W` offsets
        // the padding family uses. Legacy block-0 exposure is gated by the
        // existing first-block flag. Multi-block exposure appends a witness
        // block counter plus one selector per yielded byte; preprocessing stays
        // independent of message length and offsets.
        if !self.field_exposure.is_empty() {
            let field_bytes: Vec<E::F> = (0..self.field_exposure.n_byte_columns())
                .map(|_| eval.next_trace_mask())
                .collect();
            // Block counter: read at [0, -1] to pin its step behaviour. It is a
            // base/witness column carrying `block_idx` on every row.
            let block_counter = if self.field_exposure.needs_block_witness() {
                let [b, b_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
                // Base: 0 on block 0's anchor row.
                eval.add_constraint(is_first_block.clone() * b.clone());
                // Flat within a block (every real non-`t=0` row).
                eval.add_constraint(
                    enabler.clone() * (E::F::one() - r0.clone()) * (b.clone() - b_prev.clone()),
                );
                // +1 at each real continuation boundary (`chain_gate`, defined
                // in the h-chaining section above).
                eval.add_constraint(chain_gate.clone() * (b.clone() - b_prev - E::F::one()));
                Some(b)
            } else {
                None
            };
            // One selector per yielded byte (multi-block only), pinned below.
            let selectors: Vec<E::F> = if self.field_exposure.needs_block_witness() {
                (0..self.field_exposure.n_yields())
                    .map(|_| eval.next_trace_mask())
                    .collect()
            } else {
                Vec::new()
            };
            for (word_slot, &word_idx) in self.field_exposure.decomposed_words().iter().enumerate()
            {
                let (w_lo_v, w_hi_v) = w_msg(word_idx).clone();
                let base = word_slot * BYTES_PER_WORD;
                eval.add_constraint(
                    gate_r15.clone()
                        * (w_hi_v
                            - two_pow_8.clone() * field_bytes[base].clone()
                            - field_bytes[base + 1].clone()),
                );
                eval.add_constraint(
                    gate_r15.clone()
                        * (w_lo_v
                            - two_pow_8.clone() * field_bytes[base + 2].clone()
                            - field_bytes[base + 3].clone()),
                );
            }

            let byte_range_offset =
                E::F::from(M31::from(crate::field_exposure::BYTE_RANGE_CHECK_OFFSET));
            let legacy_block0_selector = is_first_block_m15;
            if !self.field_exposure.needs_block_witness() {
                // Legacy block-0 path: every byte range-checked once, gated by
                // the block-0 flag.
                for b in &field_bytes {
                    wire_range_check::<E>(
                        &mut eval,
                        legacy_block0_selector.clone(),
                        b.clone(),
                        crate::components::RangeKind::Range16,
                        &self.relations,
                    );
                    wire_range_check::<E>(
                        &mut eval,
                        legacy_block0_selector.clone(),
                        b.clone() + byte_range_offset.clone(),
                        crate::components::RangeKind::Range16,
                        &self.relations,
                    );
                }
            } else {
                let b = block_counter
                    .as_ref()
                    .expect("multi-block field exposure has a block counter");
                // Pin each selector: boolean, live only on `t = 15`, and hot
                // only when the counter equals this yield's target block.
                for (yield_idx, y) in self.field_exposure.yields().iter().enumerate() {
                    let selector = selectors[yield_idx].clone();
                    eval.add_constraint(selector.clone() * (selector.clone() - E::F::one()));
                    eval.add_constraint(selector.clone() * (E::F::one() - r15.clone()));
                    eval.add_constraint(
                        selector.clone() * (b.clone() - E::F::from(M31::from(y.block_idx as u32))),
                    );
                }
                // Each byte range-checked once per distinct target block, gated
                // by that block's representative selector.
                for target_block in self.field_exposure.target_blocks() {
                    let selector = self
                        .field_exposure
                        .yields()
                        .iter()
                        .position(|y| y.block_idx == *target_block)
                        .map(|yield_idx| selectors[yield_idx].clone())
                        .expect("target block has at least one selector");
                    for byte in &field_bytes {
                        wire_range_check::<E>(
                            &mut eval,
                            selector.clone(),
                            byte.clone(),
                            crate::components::RangeKind::Range16,
                            &self.relations,
                        );
                        wire_range_check::<E>(
                            &mut eval,
                            selector.clone(),
                            byte.clone() + byte_range_offset.clone(),
                            crate::components::RangeKind::Range16,
                            &self.relations,
                        );
                    }
                }
            }

            for (yield_idx, y) in self.field_exposure.yields().iter().enumerate() {
                let slot = self.field_exposure.yield_column_slot(y);
                let selector = if self.field_exposure.needs_block_witness() {
                    selectors[yield_idx].clone()
                } else {
                    legacy_block0_selector.clone()
                };
                let tuple = [
                    E::F::from(M31::from(y.field_id)),
                    E::F::from(M31::from(y.byte_index)),
                    field_bytes[slot].clone(),
                ];
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.field.field,
                    -selector.clone(),
                    &tuple,
                ));
            }
        }

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
/// `grp` is the 8-element packed-group commitment in `groups_in_order`
/// ordering (the four `S`-side groups then the four `S'`-side groups of the
/// W=6 partition). `lo_idx` / `hi_idx` are the per-partition projections
/// from [`crate::partitions::round_groups_half_indices`]: the positions
/// within `grp` whose bits live in the lo / hi 16-bit half (length 4 each).
/// The lo-half table row carries `grp[lo_idx[0..4]]`, the hi-half row
/// `grp[hi_idx[0..4]]`, in that order — matching
/// [`crate::tables::build_round_split_pack_table`] (which lists each half's
/// groups in `groups_in_order` index order). Each lookup row matches the
/// `(key, g0, g1, g2, g3)` shape of
/// [`crate::relations::ROUND_SPLIT_PACK_REL_SIZE`].
///
/// Firing the lookup pins the four packed-group cells to the table row
/// determined by `word.lo` (resp. `word.hi`) and implicitly range-checks
/// the limb to `[0, 2¹⁶)` (design §11 L1).
#[allow(clippy::too_many_arguments)]
fn wire_round_split_pack<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    word: &(E::F, E::F),
    grp: &[E::F; GROUPS_PER_ROUND_PARTITION],
    lo_idx: &[usize],
    hi_idx: &[usize],
    rel_lo: &impl Relation<E::F, E::EF>,
    rel_hi: &impl Relation<E::F, E::EF>,
) {
    // Each 16-bit half holds exactly 4 sub-groups under the W=6 partition,
    // so the relation tuple is `key + 4` packed groups (= ROUND_SPLIT_PACK_REL_SIZE).
    debug_assert_eq!(lo_idx.len(), 4);
    debug_assert_eq!(hi_idx.len(), 4);
    // Gate by `enabler` so padding rows (every cell zero, so denominator
    // collapses to `-z` for every lookup) contribute a zero fraction
    // instead of `+1/(-z)`. Without this, every padding row would emit
    // 130-or-so consumer lookups all keyed on the all-zero row of the
    // table — which the producer's multiplicity column doesn't account
    // for, breaking the LogUp sum-to-zero balance.
    let mult = enabler;
    eval.add_to_relation(RelationEntry::base(
        rel_lo,
        mult.clone(),
        &[
            word.0.clone(),
            grp[lo_idx[0]].clone(),
            grp[lo_idx[1]].clone(),
            grp[lo_idx[2]].clone(),
            grp[lo_idx[3]].clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::base(
        rel_hi,
        mult,
        &[
            word.1.clone(),
            grp[hi_idx[0]].clone(),
            grp[hi_idx[1]].clone(),
            grp[hi_idx[2]].clone(),
            grp[hi_idx[3]].clone(),
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
    let mult = enabler;
    eval.add_to_relation(RelationEntry::base(
        rel_lo,
        mult.clone(),
        &[
            word.0.clone(),
            split.packed_s_lo.clone(),
            split.packed_s_complement_lo.clone(),
        ],
    ));
    eval.add_to_relation(RelationEntry::base(
        rel_hi,
        mult,
        &[
            word.1.clone(),
            split.packed_s_hi.clone(),
            split.packed_s_complement_hi.clone(),
        ],
    ));
}

fn f_zero<E: EvalAtRow>() -> E::F {
    E::F::from(M31::from(0u32))
}

fn f_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from(value))
}

fn xor3<E: EvalAtRow>(x: E::F, y: E::F, z: E::F) -> E::F {
    let two = f_const::<E>(2);
    let four = f_const::<E>(4);
    x.clone() + y.clone() + z.clone()
        - two.clone() * (x.clone() * y.clone() + y.clone() * z.clone() + x.clone() * z.clone())
        + four * x * y * z
}

fn rotr_bit<F: Clone>(bits: &[F; WORD_BIT_COLS], out_bit: usize, rot: usize) -> F {
    bits[(out_bit + rot) % WORD_BIT_COLS].clone()
}

fn shr_bit<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS], out_bit: usize, shift: usize) -> E::F {
    bits.get(out_bit + shift)
        .cloned()
        .unwrap_or_else(f_zero::<E>)
}

fn big_sigma0_expr_bits<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS]) -> [E::F; WORD_BIT_COLS] {
    std::array::from_fn(|i| {
        xor3::<E>(
            rotr_bit(bits, i, 2),
            rotr_bit(bits, i, 13),
            rotr_bit(bits, i, 22),
        )
    })
}

fn big_sigma1_expr_bits<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS]) -> [E::F; WORD_BIT_COLS] {
    std::array::from_fn(|i| {
        xor3::<E>(
            rotr_bit(bits, i, 6),
            rotr_bit(bits, i, 11),
            rotr_bit(bits, i, 25),
        )
    })
}

fn lower_sigma0_expr_bits<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS]) -> [E::F; WORD_BIT_COLS] {
    std::array::from_fn(|i| {
        xor3::<E>(
            rotr_bit(bits, i, 7),
            rotr_bit(bits, i, 18),
            shr_bit::<E>(bits, i, 3),
        )
    })
}

fn lower_sigma1_expr_bits<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS]) -> [E::F; WORD_BIT_COLS] {
    std::array::from_fn(|i| {
        xor3::<E>(
            rotr_bit(bits, i, 17),
            rotr_bit(bits, i, 19),
            shr_bit::<E>(bits, i, 10),
        )
    })
}

fn maj_expr_bits<E: EvalAtRow>(
    a: &[E::F; WORD_BIT_COLS],
    b: &[E::F; WORD_BIT_COLS],
    c: &[E::F; WORD_BIT_COLS],
) -> [E::F; WORD_BIT_COLS] {
    let two = f_const::<E>(2);
    std::array::from_fn(|i| {
        a[i].clone() * b[i].clone() + a[i].clone() * c[i].clone() + b[i].clone() * c[i].clone()
            - two.clone() * a[i].clone() * b[i].clone() * c[i].clone()
    })
}

fn ch_expr_bits<E: EvalAtRow>(
    e: &[E::F; WORD_BIT_COLS],
    f: &[E::F; WORD_BIT_COLS],
    g: &[E::F; WORD_BIT_COLS],
) -> [E::F; WORD_BIT_COLS] {
    std::array::from_fn(|i| g[i].clone() + e[i].clone() * (f[i].clone() - g[i].clone()))
}

fn limb_sum<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS], start: usize) -> E::F {
    let mut acc = f_zero::<E>();
    for i in 0..LIMB_BITS as usize {
        acc += f_const::<E>(1u32 << i) * bits[start + i].clone();
    }
    acc
}

fn constrain_word_recomposition<E: EvalAtRow>(
    eval: &mut E,
    gate: E::F,
    word: &(E::F, E::F),
    bits: &[E::F; WORD_BIT_COLS],
) {
    eval.add_constraint(gate.clone() * (word.0.clone() - limb_sum::<E>(bits, 0)));
    eval.add_constraint(gate * (word.1.clone() - limb_sum::<E>(bits, LIMB_BITS as usize)));
}

fn constrain_word_recomposition_ungated<E: EvalAtRow>(
    eval: &mut E,
    word: &(E::F, E::F),
    bits: &[E::F; WORD_BIT_COLS],
) {
    eval.add_constraint(word.0.clone() - limb_sum::<E>(bits, 0));
    eval.add_constraint(word.1.clone() - limb_sum::<E>(bits, LIMB_BITS as usize));
}

fn constrain_boolean_bits<E: EvalAtRow>(eval: &mut E, bits: &[E::F; WORD_BIT_COLS]) {
    for bit in bits {
        eval.add_constraint(bit.clone() * (bit.clone() - E::F::one()));
    }
}

fn constrain_bits_equal<E: EvalAtRow>(
    eval: &mut E,
    lhs: &[E::F; WORD_BIT_COLS],
    rhs: &[E::F; WORD_BIT_COLS],
) {
    for i in 0..WORD_BIT_COLS {
        eval.add_constraint(lhs[i].clone() - rhs[i].clone());
    }
}

fn pack_round_group_exprs<E: EvalAtRow>(
    bits: &[E::F; WORD_BIT_COLS],
    groups: &RoundGroups,
) -> [E::F; GROUPS_PER_ROUND_PARTITION] {
    let mut out: [E::F; GROUPS_PER_ROUND_PARTITION] = std::array::from_fn(|_| f_zero::<E>());
    for (group_idx, group) in groups
        .s
        .iter()
        .chain(groups.s_complement.iter())
        .enumerate()
    {
        let mut acc = f_zero::<E>();
        for (position, &bit_idx) in group.iter().enumerate() {
            acc += f_const::<E>(1u32 << position) * bits[bit_idx as usize].clone();
        }
        out[group_idx] = acc;
    }
    out
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
    // Drift guard: the `RangeKind` must match the addend count published
    // by `crate::headroom`. If a future edit grows or shrinks an add at
    // a call site without bumping the audit (and hence `RangeKind`), the
    // mismatch is caught here in debug builds rather than silently
    // changing the carry range a downstream lookup pins. `Range_16` is a
    // terminal-limb check, never an add-carry, so we reject it outright.
    use crate::components::RangeKind;
    let expected_addends = match range_kind {
        RangeKind::Range2 => 2,
        RangeKind::Range4 => 4,
        RangeKind::Range5 => 5,
        RangeKind::Range16 => panic!(
            "Range16 is the terminal 16-bit limb check; do not use it for mod-2³² add carries"
        ),
    };
    // Mn2: hard assert so release builds (round-trip prove/verify, the
    // end-to-end tests) also catch a mis-paired addend count vs.
    // `RangeKind`. The guard runs once per emit, so the cost is
    // negligible compared to the constraint emission itself.
    assert_eq!(
        addends.len(),
        expected_addends,
        "addend count {} mismatches RangeKind::{:?} (expected {} per crate::headroom audit)",
        addends.len(),
        range_kind,
        expected_addends,
    );

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
    wire_range_check::<E>(
        eval,
        enabler.clone(),
        carry_lo.clone(),
        range_kind,
        relations,
    );
    wire_range_check::<E>(eval, enabler, carry_hi.clone(), range_kind, relations);
}

/// Fire one `add_to_relation(rel, +enabler, &[value])` against the chosen
/// `Range_k` channel. Used for both mod-2³² add carries
/// (`Range_2`/`4`/`5`, via [`emit_mod_2_32_add_linear`]) and terminal
/// `h_out` digest limbs (`Range_16`, fired directly from
/// [`Sha256Eval::evaluate`]). Inlined helper so call sites stay short.
fn wire_range_check<E: EvalAtRow>(
    eval: &mut E,
    enabler: E::F,
    value: E::F,
    kind: crate::components::RangeKind,
    relations: &Sha256Relations,
) {
    use crate::components::RangeKind;
    let mult = enabler;
    match kind {
        RangeKind::Range2 => eval.add_to_relation(RelationEntry::base(
            &relations.range.range_2,
            mult,
            &[value],
        )),
        RangeKind::Range4 => eval.add_to_relation(RelationEntry::base(
            &relations.range.range_4,
            mult,
            &[value],
        )),
        RangeKind::Range5 => eval.add_to_relation(RelationEntry::base(
            &relations.range.range_5,
            mult,
            &[value],
        )),
        RangeKind::Range16 => eval.add_to_relation(RelationEntry::base(
            &relations.range.range_16,
            mult,
            &[value],
        )),
    }
}

#[cfg(test)]
mod tests {
    use crate::constants::{IV, K, N_ROUNDS, N_STATE_WORDS};
    use crate::trace::{generate_trace, min_log_size, Layout};
    use crate::types::WORDS_PER_BLOCK;
    use crate::witness::compute_sha256_witness;
    use stwo::core::fields::m31::BaseField;

    type Trace = Vec<Vec<BaseField>>;

    fn cell(trace: &[Vec<BaseField>], col: usize, slot: usize) -> i64 {
        i64::from(trace[col][slot].0)
    }

    /// `(lo, hi)` of a two-column pair at a slot.
    fn pair(trace: &Trace, cols: (usize, usize), slot: usize) -> (i64, i64) {
        (cell(trace, cols.0, slot), cell(trace, cols.1, slot))
    }

    /// The working-state word entering round `t` at slot position `k`
    /// (`k = 1` → a/e, `k = 4` → d/h), reconstructed exactly the way the
    /// AIR's boundary select does: `h_in` of the block's `t = 0` row for
    /// `t < k`, else `a_new`/`e_new` of row `t − k`.
    fn state_word(
        trace: &Trace,
        log_size: u32,
        b: usize,
        t: usize,
        k: usize,
        h_base: usize, // 0 for the a-side, 4 for the e-side
        new_cols: (usize, usize),
    ) -> (i64, i64) {
        if t < k {
            // h_in[h_base + (k − 1 − t)] on the t = 0 row.
            let j = h_base + (k - 1 - t);
            pair(
                trace,
                Layout::h_in_word(j),
                Layout::round_row_slot(b, 0, log_size),
            )
        } else {
            pair(trace, new_cols, Layout::round_row_slot(b, t - k, log_size))
        }
    }

    /// Assert one mod-2³² limb-add identity: `Σ addends = result + carries`.
    fn assert_add(addends: &[(i64, i64)], result: (i64, i64), carries: (i64, i64), ctx: &str) {
        let sum_lo: i64 = addends.iter().map(|a| a.0).sum();
        let sum_hi: i64 = addends.iter().map(|a| a.1).sum();
        assert_eq!(sum_lo, result.0 + (carries.0 << 16), "lo residual: {ctx}");
        assert_eq!(
            sum_hi + carries.0,
            result.1 + (carries.1 << 16),
            "hi residual: {ctx}"
        );
    }

    /// Verify every linear identity of the rotated AIR on an honest trace:
    /// round adds (with boundary-selected `d`/`h`), schedule recurrence,
    /// IV binding, block chain, and finalization.
    fn check_linear_constraints_on_message(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);

        let r = Layout::round_col();
        let sigma0_c = (r[0], r[1]);
        let sigma1_c = (r[2], r[3]);
        let ch_c = (r[4], r[5]);
        let maj_c = (r[6], r[7]);
        let t1_c = (r[8], r[9]);
        let t2_c = (r[10], r[11]);
        let a_new_c = (r[12], r[13]);
        let e_new_c = (r[14], r[15]);
        let t1_carry = (r[16], r[17]);
        let t2_carry = (r[18], r[19]);
        let e_new_carry = (r[20], r[21]);
        let a_new_carry = (r[22], r[23]);
        let w_c = Layout::schedule_word();

        for b in 0..witness.blocks.len() {
            // IV binding / chain on the t = 0 row.
            let slot0 = Layout::round_row_slot(b, 0, log_size);
            for j in 0..N_STATE_WORDS {
                let h_in = pair(&trace, Layout::h_in_word(j), slot0);
                if b == 0 {
                    let iv = IV[j];
                    assert_eq!(h_in.0 as u32, iv & 0xFFFF, "IV lo j={j}");
                    assert_eq!(h_in.1 as u32, iv >> 16, "IV hi j={j}");
                } else {
                    let prev63 = Layout::round_row_slot(b - 1, N_ROUNDS - 1, log_size);
                    let h_out_prev = pair(&trace, Layout::h_out_word(j), prev63);
                    assert_eq!(h_in, h_out_prev, "chain j={j} b={b}");
                }
            }

            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(b, t, log_size);
                let d = state_word(&trace, log_size, b, t, 4, 0, a_new_c);
                let h_state = state_word(&trace, log_size, b, t, 4, 4, e_new_c);
                let k_t = (i64::from(K[t] & 0xFFFF), i64::from(K[t] >> 16));
                let w_t = pair(&trace, w_c, slot);
                let sigma0 = pair(&trace, sigma0_c, slot);
                let sigma1 = pair(&trace, sigma1_c, slot);
                let ch = pair(&trace, ch_c, slot);
                let maj = pair(&trace, maj_c, slot);
                let t1 = pair(&trace, t1_c, slot);
                let t2 = pair(&trace, t2_c, slot);
                let a_new = pair(&trace, a_new_c, slot);
                let e_new = pair(&trace, e_new_c, slot);

                assert_add(
                    &[h_state, sigma1, ch, k_t, w_t],
                    t1,
                    pair(&trace, t1_carry, slot),
                    &format!("t1 b={b} t={t}"),
                );
                assert_add(
                    &[sigma0, maj],
                    t2,
                    pair(&trace, t2_carry, slot),
                    &format!("t2 b={b} t={t}"),
                );
                assert_add(
                    &[d, t1],
                    e_new,
                    pair(&trace, e_new_carry, slot),
                    &format!("e_new b={b} t={t}"),
                );
                assert_add(
                    &[t1, t2],
                    a_new,
                    pair(&trace, a_new_carry, slot),
                    &format!("a_new b={b} t={t}"),
                );

                // Schedule recurrence (t ≥ 16 rows).
                if t >= 16 {
                    let e = Layout::schedule_entry();
                    let s0 = (cell(&trace, e[0], slot), cell(&trace, e[1], slot));
                    let s1 = (cell(&trace, e[2], slot), cell(&trace, e[3], slot));
                    let carries = (cell(&trace, e[4], slot), cell(&trace, e[5], slot));
                    let at =
                        |k: usize| pair(&trace, w_c, Layout::round_row_slot(b, t - k, log_size));
                    assert_add(
                        &[s1, at(7), s0, at(16)],
                        w_t,
                        carries,
                        &format!("schedule b={b} t={t}"),
                    );
                }
            }

            // Finalization on the t = 63 row.
            let slot63 = Layout::round_row_slot(b, N_ROUNDS - 1, log_size);
            for j in 0..N_STATE_WORDS {
                let h_in = pair(&trace, Layout::h_in_word(j), slot0);
                let working = if j < 4 {
                    pair(
                        &trace,
                        a_new_c,
                        Layout::round_row_slot(b, N_ROUNDS - 1 - j, log_size),
                    )
                } else {
                    pair(
                        &trace,
                        e_new_c,
                        Layout::round_row_slot(b, N_ROUNDS - 1 - (j - 4), log_size),
                    )
                };
                let h_out = pair(&trace, Layout::h_out_word(j), slot63);
                let carries = pair(&trace, Layout::final_carry(j), slot63);
                assert_add(
                    &[h_in, working],
                    h_out,
                    carries,
                    &format!("finalization b={b} j={j}"),
                );
            }
        }
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
        check_linear_constraints_on_message(&[0x42; 150]);
    }

    /// §8.1 duplicate operand bits match their originating cells: on
    /// every non-boundary row, `b_bits = a_bits@(t−1)`, `c_bits =
    /// a_bits@(t−2)`; e-side symmetric. Boundary rows are tied to `h_in`
    /// by word recomposition in the AIR.
    #[test]
    fn reuse_chain_duplicates_match_their_sources() {
        let witness = compute_sha256_witness(&[0x24; 100]);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for b in 0..witness.blocks.len() {
            for t in 0..N_ROUNDS {
                let slot = Layout::round_row_slot(b, t, log_size);
                for bit in 0..crate::trace::WORD_BIT_COLS {
                    let b_dup = cell(&trace, Layout::round_operand_bit(1, bit), slot);
                    let c_dup = cell(&trace, Layout::round_operand_bit(2, bit), slot);
                    let f_dup = cell(&trace, Layout::round_operand_bit(4, bit), slot);
                    let g_dup = cell(&trace, Layout::round_operand_bit(5, bit), slot);
                    let a_at = |tt: usize| {
                        cell(
                            &trace,
                            Layout::round_operand_bit(0, bit),
                            Layout::round_row_slot(b, tt, log_size),
                        )
                    };
                    let e_at = |tt: usize| {
                        cell(
                            &trace,
                            Layout::round_operand_bit(3, bit),
                            Layout::round_row_slot(b, tt, log_size),
                        )
                    };
                    if t > 0 {
                        assert_eq!(b_dup, a_at(t - 1), "b_bit b={b} t={t} bit={bit}");
                        assert_eq!(f_dup, e_at(t - 1), "f_bit b={b} t={t} bit={bit}");
                    }
                    if t > 1 {
                        assert_eq!(c_dup, a_at(t - 2), "c_bit b={b} t={t} bit={bit}");
                        assert_eq!(g_dup, e_at(t - 2), "g_bit b={b} t={t} bit={bit}");
                    }
                }
            }
        }
    }

    /// Chain rejection: mutating block 1's `h_in` breaks the chain residual.
    #[test]
    fn chain_constraint_rejects_h_in_mutation_on_block_1() {
        let witness = compute_sha256_witness(&[0x24; 100]); // 2 blocks
        assert!(witness.blocks.len() >= 2);
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);

        let slot0_b1 = Layout::round_row_slot(1, 0, log_size);
        let (lo_col, _) = Layout::h_in_word(3);
        trace[lo_col][slot0_b1] += BaseField::from(1u32);

        let prev63 = Layout::round_row_slot(0, N_ROUNDS - 1, log_size);
        let h_in = cell(&trace, lo_col, slot0_b1);
        let (out_lo, _) = Layout::h_out_word(3);
        let h_out_prev = cell(&trace, out_lo, prev63);
        assert_ne!(h_in, h_out_prev, "mutated chain must produce a residual");
    }

    /// Every padding-role identity (P.A–P.H), evaluated at each block's
    /// `t = 15` row with the message words read from rows `t = 0..16`.
    /// Returns the residuals so negative tests can assert non-zero.
    fn padding_residuals(trace: &Trace, log_size: u32, b: usize) -> Vec<i64> {
        let slot = Layout::round_row_slot(b, 15, log_size);
        let w = |j: usize| -> (i64, i64) {
            pair(
                trace,
                Layout::schedule_word(),
                Layout::round_row_slot(b, j, log_size),
            )
        };
        let is_marker = cell(trace, Layout::COL_IS_MARKER_BLOCK, slot);
        let is_length = cell(trace, Layout::COL_IS_LENGTH_BLOCK, slot);
        let is_length_only = cell(trace, Layout::COL_IS_LENGTH_ONLY_BLOCK, slot);
        let is_marker_only = cell(trace, Layout::COL_IS_MARKER_ONLY_BLOCK, slot);
        let post_strict_15 = cell(trace, Layout::COL_MARKER_WORD_POST_STRICT_15, slot);
        let mword: Vec<i64> = (0..WORDS_PER_BLOCK)
            .map(|j| cell(trace, Layout::is_marker_word(j), slot))
            .collect();
        let bsel: Vec<i64> = (0..4)
            .map(|k| cell(trace, Layout::marker_byte_sel(k), slot))
            .collect();
        let mbyte: Vec<i64> = (0..4)
            .map(|k| cell(trace, Layout::marker_word_byte(k), slot))
            .collect();

        let mut res = Vec::new();
        // P.A binary
        for &f in [
            is_marker,
            is_length,
            is_length_only,
            is_marker_only,
            post_strict_15,
        ]
        .iter()
        {
            res.push(f * (1 - f));
        }
        for &f in mword.iter().chain(bsel.iter()) {
            res.push(f * (1 - f));
        }
        // P.B one-hot sums
        res.push(mword.iter().sum::<i64>() - is_marker);
        res.push(bsel.iter().sum::<i64>() - is_marker);
        // P.C aux definitions
        res.push(is_length_only - (1 - is_marker) * is_length);
        res.push(is_marker_only - is_marker * (1 - is_length));
        // cumulative marker-word prefix
        let mut cum = vec![0i64; WORDS_PER_BLOCK];
        for j in 1..WORDS_PER_BLOCK {
            cum[j] = cum[j - 1] + mword[j - 1];
        }
        // P.C'
        res.push(post_strict_15 - cum[15] * (1 - is_length));
        // P.D byte assembly
        let mut sum_hi = 0i64;
        let mut sum_lo = 0i64;
        for j in 0..WORDS_PER_BLOCK {
            sum_hi += mword[j] * w(j).1;
            sum_lo += mword[j] * w(j).0;
        }
        res.push(sum_hi - 256 * mbyte[0] - mbyte[1]);
        res.push(sum_lo - 256 * mbyte[2] - mbyte[3]);
        // P.E marker byte is 0x80
        for k in 0..4 {
            res.push(bsel[k] * (mbyte[k] - 0x80));
        }
        // P.F bytes after the marker byte are zero
        let mut cum_b = 0i64;
        for k in 0..4 {
            res.push(cum_b * mbyte[k]);
            cum_b += bsel[k];
        }
        // P.G words after the marker are zero (length exception)
        for j in 0..14 {
            let gate = cum[j] + is_length_only;
            res.push(gate * w(j).0);
            res.push(gate * w(j).1);
        }
        res.push(post_strict_15 * w(15).0);
        res.push(post_strict_15 * w(15).1);
        // P.H length-field encoding
        let w14 = w(14);
        let w15 = w(15);
        res.push(is_length * (w14.0 - cell(trace, Layout::COL_BIT_LENGTH_W14_LO, slot)));
        res.push(is_length * (w14.1 - cell(trace, Layout::COL_BIT_LENGTH_W14_HI, slot)));
        res.push(is_length * (w15.0 - cell(trace, Layout::COL_BIT_LENGTH_W15_LO, slot)));
        res.push(is_length * (w15.1 - cell(trace, Layout::COL_BIT_LENGTH_W15_HI, slot)));
        res
    }

    fn assert_padding_holds_for_message(msg: &[u8]) {
        let witness = compute_sha256_witness(msg);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        for b in 0..witness.blocks.len() {
            for (i, r) in padding_residuals(&trace, log_size, b).iter().enumerate() {
                assert_eq!(*r, 0, "padding residual {i} on block {b}");
            }
        }
    }

    #[test]
    fn padding_constraints_hold_for_empty_message() {
        assert_padding_holds_for_message(b"");
    }

    #[test]
    fn padding_constraints_hold_for_abc() {
        assert_padding_holds_for_message(b"abc");
    }

    #[test]
    fn padding_constraints_hold_for_56_byte_message() {
        assert_padding_holds_for_message(&[7u8; 56]);
    }

    #[test]
    fn padding_constraints_hold_for_multi_block_message() {
        assert_padding_holds_for_message(&[9u8; 150]);
    }

    #[test]
    fn padding_rejects_marker_byte_sel_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::round_row_slot(0, 15, log_size);
        // Move the byte selector to a different position.
        for k in 0..4 {
            let c = Layout::marker_byte_sel(k);
            let v = trace[c][slot];
            trace[c][slot] = BaseField::from(1u32) - v;
        }
        let res = padding_residuals(&trace, log_size, 0);
        assert!(
            res.iter().any(|&r| r != 0),
            "mutated byte selector must produce a residual"
        );
    }

    #[test]
    fn padding_rejects_bit_length_limb_mutation() {
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        let slot = Layout::round_row_slot(0, 15, log_size);
        trace[Layout::COL_BIT_LENGTH_W15_LO][slot] += BaseField::from(8u32);
        let res = padding_residuals(&trace, log_size, 0);
        assert!(
            res.iter().any(|&r| r != 0),
            "mutated bit-length limb must produce a residual"
        );
    }

    #[test]
    fn padding_rejects_non_zero_fill_word_mutation() {
        // A 3-byte message: marker at byte 3 of W[0], everything after must
        // be zero. Injecting a non-zero fill word must trip P.G.
        let witness = compute_sha256_witness(b"abc");
        let log_size = min_log_size(witness.blocks.len());
        let mut trace = generate_trace(&witness, log_size);
        // W[5] lives on row t = 5.
        let slot5 = Layout::round_row_slot(0, 5, log_size);
        trace[Layout::COL_W_LO][slot5] += BaseField::from(3u32);
        let res = padding_residuals(&trace, log_size, 0);
        assert!(
            res.iter().any(|&r| r != 0),
            "non-zero fill word must produce a residual"
        );
    }
}
