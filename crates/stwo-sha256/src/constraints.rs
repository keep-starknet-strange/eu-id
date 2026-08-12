//! AIR evaluator for the SHA-256 component.
//!
//! This module implements [`FrameworkEval`] for [`crate::trace`]. It checks the
//! IV, schedule, compression rounds, additions, and block chain. Bit planes
//! constrain the SHA Boolean functions.
//!
//! Range lookups constrain carries and digest bytes. Padding constraints check
//! the marker, zero region, and bit length. Trace reads must follow the write
//! order that [`crate::trace::Layout`] documents.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry, ORIGINAL_TRACE_IDX};

use crate::components::{is_first_row_column_id, round_cyclic_column_ids};
use crate::constants::{DIGEST_BYTES, IV, N_INPUT_WORDS, N_STATE_WORDS, WORD_BYTES};
use crate::relations::Sha256Relations;
use crate::trace::WORD_BIT_COLS;
use crate::types::LIMB_BITS;

enum WordBitMasks<F> {
    Sparse([[F; 3]; WORD_BIT_COLS]),
    Full([[F; 16]; WORD_BIT_COLS]),
}

/// AIR evaluator over the rotated one-row-per-round layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (the smallest power of two **strictly**
    /// greater than `64 · block count`, per [`crate::trace::min_log_size`]).
    pub log_size: u32,
    /// The four active `Range_k` channels plus cross-component digest and
    /// selected-field channels.
    pub relations: Sha256Relations,
    /// Yield the final digest bytes on the packed digest channel when set.
    ///
    /// This yield is the producer side of the digest binding.
    /// A standalone proof has no digest consumer.
    /// The standalone proof leaves this option disabled.
    /// The combined prover enables it with the P-256 `z` consumer.
    /// The AIR always constrains the digest columns.
    /// This option controls only the cross-module yield.
    pub expose_digest: bool,
    /// Whether the complete padded stream provider is active.
    pub expose_field: bool,
    /// Post-tree-1 claimed-sum mask challenge. When present, the final logical
    /// LogUp site is `beta * mask / 1`, read from four committed trace columns.
    pub claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for Sha256Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Base constraints have degree three or less.
        // A boundary gate has degree two and multiplies a linear identity.
        // `finalize_logup_batched` uses four fractions per interaction column.
        // The resulting LogUp constraint has degree five or less.
        // `log_size + 2` supplies the required composition domain.
        // The engine uses `K = 2` with `log_blowup = 2`.
        // Pair-batched producer constraints use `log_size + 1`.
        self.log_size + 2
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
        let first_row = eval.get_preprocessed_column(is_first_row_column_id());

        // ---- header ----
        //
        // Read `enabler` with the `[0, -1, 1]` cross-row mask.
        // The contiguity constraint uses `enabler_prev`.
        // The digest gate uses `enabler_next`.
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
        // {2, 7, 15, 16}. The `t = 15` padding and field families read the
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
        // Consume each physical W-bit column exactly once. The standalone
        // path needs only the three SHA and padding offsets; the optional
        // packed-stream provider requests all W[0..15] offsets at t=15.
        let w_bits_m = if !self.expose_field {
            WordBitMasks::Sparse(std::array::from_fn(|_| {
                eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -2, -15])
            }))
        } else {
            WordBitMasks::Full(std::array::from_fn(|_| {
                eval.next_interaction_mask(
                    ORIGINAL_TRACE_IDX,
                    [
                        0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14, -15,
                    ],
                )
            }))
        };
        let w_bit_at = |bit: usize, offset: usize| -> E::F {
            match &w_bits_m {
                WordBitMasks::Full(full) => full[bit][offset].clone(),
                WordBitMasks::Sparse(sparse) => match offset {
                    0 => sparse[bit][0].clone(),
                    2 => sparse[bit][1].clone(),
                    15 => sparse[bit][2].clone(),
                    _ => unreachable!("sparse W-bit masks contain offsets 0, 2, and 15"),
                },
            }
        };
        let w_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bit_at(i, 0));

        // ---- round family: outputs, carries, Σ-decodes, packed groups ----
        //
        // Column order matches `trace::write_round_row`: σ0, σ1, ch, maj,
        // t1 and t2 read at offset 0. a_new and e_new also read at offsets
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

        // ---- schedule family (live t ≥ 16) ----
        let s0 = (eval.next_trace_mask(), eval.next_trace_mask());
        let s1 = (eval.next_trace_mask(), eval.next_trace_mask());
        let sched_carry_lo = eval.next_trace_mask();
        let sched_carry_hi = eval.next_trace_mask();

        // ---- t = 0 family ----
        //
        // Read `msg_start` at offset −15.
        // The packed-stream provider on row `t = 15` uses this block-zero value.
        let [msg_start, _, msg_start_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -15, 1]);

        // `h_in`: this block's input state (t = 0 row), laid out (lo, hi)
        // per word — reads interleave accordingly. Offsets −1..−3 feed the
        // Working-state boundary selects occur on rows t ∈ {1, 2, 3}. Offset −63
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
            eval.add_constraint(msg_start.clone() * (h_in_lo[j][0].clone() - iv_lo));
            eval.add_constraint(msg_start.clone() * (h_in_hi[j][0].clone() - iv_hi));
        }

        // Working-state words of `h_in` that recompose against committed
        // boolean bit-planes on the t = 0 row (b/c/f/g operand range checks).
        let h_in_word =
            |j: usize| -> (E::F, E::F) { (h_in_lo[j][0].clone(), h_in_hi[j][0].clone()) };
        let h_in_1 = h_in_word(1);
        let h_in_2 = h_in_word(2);
        let h_in_5 = h_in_word(5);
        let h_in_6 = h_in_word(6);

        // ---- schedule constraints (gate: enabler · is_schedule) ----
        //
        // W[t] = σ1(W[t−2]) + W[t−7] + σ0(W[t−15]) + W[t−16] (mod 2³²).
        // Recompose the sigma words ungated from the already-committed W bits.
        // Only the recurrence that consumes them is schedule-gated.
        let w_m15_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bit_at(i, 15));
        let w_m2_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bit_at(i, 2));
        let lower_sigma0_bits = lower_sigma0_expr_bits::<E>(&w_m15_bits);
        let lower_sigma1_bits = lower_sigma1_expr_bits::<E>(&w_m2_bits);
        constrain_word_recomposition_ungated::<E>(&mut eval, &s0, &lower_sigma0_bits);
        constrain_word_recomposition_ungated::<E>(&mut eval, &s1, &lower_sigma1_bits);
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
        // The state for round `t` comes from an earlier row or `h_in`.
        // Preprocessed round indicators select the source.
        // Each selection has degree two.
        // An `enabler`-gated linear identity gives a maximum degree of three.
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
        // Only `d` and `h` enter the round additions as words. The `a` and `e`
        // values enter through their bit planes. The `b`, `c`, `f`, and `g`
        // values also enter through committed bit planes.
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

        // The four mod-2³² adds of the round. K[t] comes from the
        // preprocessed cyclic columns. `h`/`d` are boundary selects.
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
        // on the t = 63 row. Offset −1 feeds the block-chain constraint on
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
        // t = 63 row. `h_in[j]` is the same block's t = 0 row (offset −63).
        // `working[j]` is the state after round 63 — `a_new`/`e_new` of
        // this row and the three before it. The trace commits all addends.
        // The degree-two gate keeps each constraint at degree three or less.
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

        // Connect each continuation block input to the prior block output.
        // Offset −1 selects the prior `t = 63` row.
        // `enabler·is_round_0 − msg_start` enables only continuation rows.
        // IV binding controls the anchor row.
        let chain_gate = gate_r0.clone() - msg_start.clone();
        for j in 0..N_STATE_WORDS {
            eval.add_constraint(
                chain_gate.clone() * (h_in_lo[j][0].clone() - h_out_prev[j].0.clone()),
            );
            eval.add_constraint(
                chain_gate.clone() * (h_in_hi[j][0].clone() - h_out_prev[j].1.clone()),
            );
        }

        // ---- digest provider: is_msg_last gate, byte view, yield ----
        //
        // `is_msg_last = enabler · is_round_63 · (1 − enabler_next)`: 1
        // only at the last real row. `min_log_size` always adds a padding
        // successor after the final block's t = 63 row.
        let is_msg_last = eval.next_trace_mask();
        eval.add_constraint(
            is_msg_last.clone()
                - gate_r63.clone() * (msg_start_next.clone() + E::F::one() - enabler_next.clone()),
        );

        // Digest byte view (t = 63 rows): per state word `j` the cells are
        // `[hi.b1, hi.b0, lo.b1, lo.b0]`. Each limb recomposes as
        // `limb = 256·b1 + b0`. Every byte is `Range_8`-pinned here, so the
        // recomposition also pins each limb to 16 bits without a 2¹⁶-row table.
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
        for byte in &digest_bytes {
            wire_range_check::<E>(
                &mut eval,
                gate_r63.clone(),
                byte.clone(),
                crate::components::RangeKind::Range8,
                &self.relations,
            );
        }
        // ---- §10.4 padding-role constraints (t = 15 rows) ----
        //
        // Identical algebra to the wide layout. The block's message words
        // `W[j]` are the `W` columns of rows `t = j`, i.e. `w[15 − j]` from
        // here. On every row outside a real t = 15 row all padding cells
        // are zero, so each identity holds vacuously.
        let is_marker_block = eval.next_trace_mask();
        let is_length_block = eval.next_trace_mask();
        let is_marker_word: [E::F; N_INPUT_WORDS] = std::array::from_fn(|_| eval.next_trace_mask());
        let marker_byte_sel: [E::F; WORD_BYTES] = std::array::from_fn(|_| eval.next_trace_mask());
        let marker_word_byte: [E::F; WORD_BYTES] = std::array::from_fn(|_| eval.next_trace_mask());
        let bit_length_w14_lo = eval.next_trace_mask();
        let bit_length_w14_hi = eval.next_trace_mask();
        let bit_length_w15_lo = eval.next_trace_mask();
        let bit_length_w15_hi = eval.next_trace_mask();

        // The block's message word `W[j]`, from the t = 15 row's viewpoint.
        let w_msg = |j: usize| -> &(E::F, E::F) { &w[15 - j] };

        // (P.A) Binary checks (ungated — all cells are 0 off-family).
        for flag in [&is_marker_block, &is_length_block] {
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
        for flag in [&is_marker_block, &is_length_block] {
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

        // (P.C) Derive the live auxiliary expression instead of committing it.
        let is_length_only_block =
            (E::F::one() - is_marker_block.clone()) * is_length_block.clone();

        // Cumulative one-hot marker-word prefix sums.
        let mut cum_marker_word: [E::F; N_INPUT_WORDS] =
            std::array::from_fn(|_| E::F::from(M31::from(0u32)));
        for j in 1..N_INPUT_WORDS {
            cum_marker_word[j] = cum_marker_word[j - 1].clone() + is_marker_word[j - 1].clone();
        }

        // (P.C') Derive the marker-word post-strict expression in the AIR.
        let marker_word_post_strict_15 =
            cum_marker_word[15].clone() * (E::F::one() - is_length_block.clone());

        // (P.D) Marker-word byte assembly.
        let byte_base = E::F::from(M31::from(1u32 << 8));
        let mut sum_w_hi = E::F::from(M31::from(0u32));
        let mut sum_w_lo = E::F::from(M31::from(0u32));
        for (j, is_marker) in is_marker_word.iter().enumerate().take(N_INPUT_WORDS) {
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
        for b in 0..WORD_BYTES {
            eval.add_constraint(
                marker_byte_sel[b].clone() * (marker_word_byte[b].clone() - marker_value.clone()),
            );
        }

        // (P.F) Bytes strictly after the marker byte are zero.
        let mut cum_byte_sel = E::F::from(M31::from(0u32));
        for b in 0..WORD_BYTES {
            eval.add_constraint(cum_byte_sel.clone() * marker_word_byte[b].clone());
            cum_byte_sel += marker_byte_sel[b].clone();
        }

        // (P.G) Words strictly after the marker word are zero (length-field
        // exception. See the wide-layout derivation for the W[14]/W[15]
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

        // ---- packed active prefix and message metadata ----
        eval.add_constraint(
            enabler.clone() * (E::F::one() - enabler_prev.clone()) - first_row.clone(),
        );
        eval.add_constraint(
            enabler_prev.clone() * (E::F::one() - enabler.clone()) * (E::F::one() - r0.clone()),
        );
        eval.add_constraint(msg_start.clone() * (msg_start.clone() - E::F::one()));
        eval.add_constraint(msg_start.clone() * (E::F::one() - gate_r0.clone()));
        eval.add_constraint(first_row.clone() * (msg_start.clone() - E::F::one()));

        let [msg_id, msg_id_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [msg_block, msg_block_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        eval.add_constraint(first_row.clone() * msg_id.clone());
        eval.add_constraint(
            (enabler.clone() - gate_r0.clone()) * (msg_id.clone() - msg_id_prev.clone()),
        );
        eval.add_constraint(
            (gate_r0.clone() - first_row.clone())
                * (msg_id.clone() - msg_id_prev.clone() - msg_start.clone()),
        );
        eval.add_constraint(msg_start.clone() * msg_block.clone());
        eval.add_constraint(
            (enabler.clone() - gate_r0.clone()) * (msg_block.clone() - msg_block_prev.clone()),
        );
        eval.add_constraint(
            (gate_r0.clone() - msg_start.clone())
                * (msg_block.clone() - msg_block_prev - E::F::one()),
        );

        if self.expose_digest {
            let mut tuple = Vec::with_capacity(1 + DIGEST_BYTES);
            tuple.push(msg_id.clone());
            tuple.extend(digest_bytes.iter().cloned());
            eval.add_to_relation(RelationEntry::base(
                &self.relations.packed_digest,
                -is_msg_last.clone(),
                &tuple,
            ));
        }

        // ---- full padded-message provider (t = 15 rows) ----
        if self.expose_field {
            let base = E::F::from(M31::from(crate::relations::PACKED_SHA_STREAM_FIELD_BASE));
            for byte_in_block in 0..crate::constants::BLOCK_BYTES {
                let word_idx = byte_in_block / WORD_BYTES;
                let byte_in_word = byte_in_block % WORD_BYTES;
                let first_bit = (WORD_BYTES - 1 - byte_in_word) * 8;
                let round_offset = 15 - word_idx;
                let value = (0..8).fold(E::F::from(M31::from(0u32)), |acc, bit| {
                    acc + w_bit_at(first_bit + bit, round_offset)
                        * E::F::from(M31::from(1u32 << bit))
                });
                let byte_index = msg_block.clone()
                    * E::F::from(M31::from(crate::constants::BLOCK_BYTES as u32))
                    + E::F::from(M31::from(byte_in_block as u32));
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.field.field,
                    -gate_r15.clone(),
                    &[base.clone() + msg_id.clone(), byte_index, value],
                ));
            }
        }

        if let Some(beta) = self.claim_mask_beta {
            air_core::claim_mask::add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_batched(crate::interaction::SHA_CONSUMER_LOGUP_BATCH);

        eval
    }
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

/// Emit the two linear constraints of one limb-grouped mod-2³² add.
///
/// For `addends = [a, b, c, …]` (each `(lo, hi)`) and result `r = (lo, hi)`,
/// constrains:
///
/// `Σ aᵢ.lo = r.lo + 2¹⁶ · carry_lo`
/// `Σ aᵢ.hi + carry_lo = r.hi + 2¹⁶ · carry_hi`
///
/// Modulo 2³² discards `carry_hi`.
/// A `Range_k` lookup constrains both carry limbs to `[0, k)`.
/// `Range_2` supports two addends.
/// `Range_4` supports the four-addend schedule recurrence.
/// `Range_5` supports the five-addend `T1`.
/// See [`crate::headroom`] for the audited bounds.
///
/// Multiply the linear constraints by `enabler`. Padding rows then have no
/// active constraint. Also use `enabler` as the carry-lookup multiplicity.
/// Zero-valued padding-row carries do not change the LogUp balance.
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
    // The `RangeKind` must match the audited addend count.
    // A debug assertion detects a count mismatch.
    // `Range_8` constrains terminal bytes, not addition carries.
    use crate::components::RangeKind;
    let expected_addends = match range_kind {
        RangeKind::Range2 => 2,
        RangeKind::Range4 => 4,
        RangeKind::Range5 => 5,
        RangeKind::Range8 => {
            panic!("Range8 is the terminal byte check; do not use it for mod-2³² add carries")
        }
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

    // Check carry ranges through the family's `Range_k` channel. Set the
    // multiplicity to `enabler`. Padding rows do not change the row-zero
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
/// `h_out` digest bytes (`Range_8`, fired directly from
/// [`Sha256Eval::evaluate`]). The AIR recomposes each checked byte pair into
/// its 16-bit limb. Inlined helper so call sites stay short.
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
        RangeKind::Range8 => eval.add_to_relation(RelationEntry::base(
            &relations.range.range_8,
            mult,
            &[value],
        )),
    }
}
