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

/// AIR evaluator over the three-seed-row plus 64-round layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (the smallest power of two **strictly**
    /// greater than `67 · block count`, per [`crate::trace::min_log_size`]).
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
        // Base constraints have degree four or less. The ceiling is the
        // r15-gated, derived padding-role expression multiplied by W.
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
        // Block-cyclic selectors for three seed rows followed by 64 rounds.
        let cyclic = round_cyclic_column_ids();
        let k_lo = eval.get_preprocessed_column(cyclic[0].clone());
        let k_hi = eval.get_preprocessed_column(cyclic[1].clone());
        let block_start = eval.get_preprocessed_column(cyclic[2].clone());
        let r0 = eval.get_preprocessed_column(cyclic[3].clone());
        let r15 = eval.get_preprocessed_column(cyclic[4].clone());
        let r63 = eval.get_preprocessed_column(cyclic[5].clone());
        let is_sched = eval.get_preprocessed_column(cyclic[6].clone());
        let is_round = eval.get_preprocessed_column(cyclic[7].clone());
        let round_index = eval.get_preprocessed_column(cyclic[8].clone());
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
        let gate_round = enabler.clone() * is_round.clone();
        let gate_block_start = enabler.clone() * block_start.clone();
        let gate_r0 = enabler.clone() * r0.clone();
        let gate_r63 = enabler.clone() * r63.clone();
        let gate_sched = enabler.clone() * is_sched.clone();
        let gate_input = enabler.clone() * (is_round.clone() - is_sched.clone());

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
        // Current W plus the two schedule-sigma offsets. Field exposure now
        // emits four bytes on each input-word row, so it also uses offset 0.
        let w_bits_m: [[E::F; 3]; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -2, -15]));
        let w_bit_at = |bit: usize, offset: usize| -> E::F {
            match offset {
                0 => w_bits_m[bit][0].clone(),
                2 => w_bits_m[bit][1].clone(),
                15 => w_bits_m[bit][2].clone(),
                _ => unreachable!("W-bit masks contain offsets 0, 2, and 15"),
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
        let a_new_lo = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3]);
        let a_new_hi = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3]);
        let e_new_lo = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3]);
        let e_new_hi = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3]);
        let a_new = (a_new_lo[0].clone(), a_new_hi[0].clone());
        let e_new = (e_new_lo[0].clone(), e_new_hi[0].clone());

        let t1_carry = (eval.next_trace_mask(), eval.next_trace_mask());
        let t2_carry = (eval.next_trace_mask(), eval.next_trace_mask());
        let e_new_carry = (eval.next_trace_mask(), eval.next_trace_mask());
        let a_new_carry = (eval.next_trace_mask(), eval.next_trace_mask());

        let a_bits_m: [[E::F; 8]; WORD_BIT_COLS] = std::array::from_fn(|_| {
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -63, -64, -65, -66])
        });
        let e_bits_m: [[E::F; 8]; WORD_BIT_COLS] = std::array::from_fn(|_| {
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, -2, -3, -63, -64, -65, -66])
        });
        let a_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| a_bits_m[i][0].clone());
        let b_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| a_bits_m[i][1].clone());
        let c_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| a_bits_m[i][2].clone());
        let d_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| a_bits_m[i][3].clone());
        let e_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| e_bits_m[i][0].clone());
        let f_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| e_bits_m[i][1].clone());
        let g_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| e_bits_m[i][2].clone());
        let h_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| e_bits_m[i][3].clone());

        // ---- schedule family (live t ≥ 16) ----
        let s0 = (eval.next_trace_mask(), eval.next_trace_mask());
        let s1 = (eval.next_trace_mask(), eval.next_trace_mask());
        let sched_carry_lo = eval.next_trace_mask();
        let sched_carry_hi = eval.next_trace_mask();

        // msg_start is committed on seed row zero. Offset -3 reads it from
        // round zero; +1 from round 63 reads the next block's seed zero.
        let [msg_start, msg_start_at_round0, msg_start_next] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -3, 1]);

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

        // Current and preceding rolling rows are a/b/c/d and e/f/g/h.
        let a_in = word_from_bits::<E>(&a_bits);
        let e_in = word_from_bits::<E>(&e_bits);
        let d_in = word_from_bits::<E>(&d_bits);
        let h_in_state = word_from_bits::<E>(&h_bits);
        let initial_state = [
            a_in.clone(),
            word_from_bits::<E>(&b_bits),
            word_from_bits::<E>(&c_bits),
            d_in.clone(),
            e_in.clone(),
            word_from_bits::<E>(&f_bits),
            word_from_bits::<E>(&g_bits),
            h_in_state.clone(),
        ];

        // Every packed message start binds its seed/round-zero state to IV.
        for (word, &iv_word) in initial_state.iter().zip(&IV) {
            eval.add_constraint(
                msg_start_at_round0.clone()
                    * (word.0.clone() - E::F::from(M31::from(iv_word & 0xffff))),
            );
            eval.add_constraint(
                msg_start_at_round0.clone()
                    * (word.1.clone() - E::F::from(M31::from(iv_word >> LIMB_BITS))),
            );
        }

        // ---- round constraints ----
        constrain_boolean_bits::<E>(&mut eval, &w_bits);
        constrain_boolean_bits::<E>(&mut eval, &a_bits);
        constrain_boolean_bits::<E>(&mut eval, &e_bits);
        constrain_word_recomposition::<E>(&mut eval, gate_round.clone(), &w[0], &w_bits);

        // After round zero, each row's rolling a/e input equals the previous
        // row's round output. Seed rows supply the round-zero exception.
        let gate_after_r0 = gate_round.clone() - gate_r0.clone();
        eval.add_constraint(gate_after_r0.clone() * (a_in.0.clone() - a_new_lo[1].clone()));
        eval.add_constraint(gate_after_r0.clone() * (a_in.1.clone() - a_new_hi[1].clone()));
        eval.add_constraint(gate_after_r0.clone() * (e_in.0.clone() - e_new_lo[1].clone()));
        eval.add_constraint(gate_after_r0 * (e_in.1.clone() - e_new_hi[1].clone()));

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
            gate_round.clone(),
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
            gate_round.clone(),
            &[sigma0.clone(), maj.clone()],
            &t2,
            &t2_carry.0,
            &t2_carry.1,
            crate::components::RangeKind::Range2,
            &self.relations,
        );
        emit_mod_2_32_add_linear(
            &mut eval,
            gate_round.clone(),
            &[d_in.clone(), t1.clone()],
            &e_new,
            &e_new_carry.0,
            &e_new_carry.1,
            crate::components::RangeKind::Range2,
            &self.relations,
        );
        emit_mod_2_32_add_linear(
            &mut eval,
            gate_round.clone(),
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

        // Offset -4 maps a continuation block's round zero past its three
        // seed rows to the preceding block's round 63.
        let mut h_out: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (E::F::from(M31::from(0u32)), E::F::from(M31::from(0u32))));
        let mut h_out_prev: [(E::F, E::F); N_STATE_WORDS] =
            std::array::from_fn(|_| (E::F::from(M31::from(0u32)), E::F::from(M31::from(0u32))));
        for j in 0..N_STATE_WORDS {
            let [lo_cur, lo_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -4]);
            let [hi_cur, hi_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -4]);
            h_out[j] = (lo_cur, hi_cur);
            h_out_prev[j] = (lo_prev, hi_prev);
        }

        // Padding aliases the first 30 of these 32 physical cells: all 16
        // final carries, then the first 14 h_out limbs. The t=15 and t=63
        // preprocessed selectors are disjoint.
        let aliased: [E::F; crate::trace::PADDING_ROW_COLS] = std::array::from_fn(|i| {
            if i < 2 * N_STATE_WORDS {
                let (word, hi) = (i / 2, i % 2 == 1);
                if hi {
                    final_carries[word].1.clone()
                } else {
                    final_carries[word].0.clone()
                }
            } else {
                let i = i - 2 * N_STATE_WORDS;
                let (word, hi) = (i / 2, i % 2 == 1);
                if hi {
                    h_out[word].1.clone()
                } else {
                    h_out[word].0.clone()
                }
            }
        });
        let neither_r15_nor_r63 = E::F::one() - r15.clone() - r63.clone();
        for cell in &aliased {
            eval.add_constraint(neither_r15_nor_r63.clone() * cell.clone());
        }
        let not_r63 = E::F::one() - r63.clone();
        eval.add_constraint(not_r63.clone() * h_out[N_STATE_WORDS - 1].0.clone());
        eval.add_constraint(not_r63 * h_out[N_STATE_WORDS - 1].1.clone());

        // Finalization reads h_in from rolling offsets 63..66 and the
        // post-round state from a_new/e_new at offsets 0..3.
        let working = |j: usize| -> (E::F, E::F) {
            match j {
                0..=3 => (a_new_lo[j].clone(), a_new_hi[j].clone()),
                4..=7 => (e_new_lo[j - 4].clone(), e_new_hi[j - 4].clone()),
                _ => unreachable!(),
            }
        };
        let h_in_final: [(E::F, E::F); N_STATE_WORDS] = std::array::from_fn(|j| {
            let (masks, offset) = if j < 4 {
                (&a_bits_m, 4 + j)
            } else {
                (&e_bits_m, j)
            };
            let bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|bit| masks[bit][offset].clone());
            word_from_bits::<E>(&bits)
        });
        for j in 0..N_STATE_WORDS {
            emit_mod_2_32_add_linear(
                &mut eval,
                gate_r63.clone(),
                &[h_in_final[j].clone(), working(j)],
                &h_out[j],
                &final_carries[j].0,
                &final_carries[j].1,
                crate::components::RangeKind::Range2,
                &self.relations,
            );
        }

        // Continuation seed bits equal the prior block's output. Message
        // starts are instead IV-bound above.
        let chain_gate = gate_r0.clone() - msg_start_at_round0.clone();
        for j in 0..N_STATE_WORDS {
            eval.add_constraint(
                chain_gate.clone() * (initial_state[j].0.clone() - h_out_prev[j].0.clone()),
            );
            eval.add_constraint(
                chain_gate.clone() * (initial_state[j].1.clone() - h_out_prev[j].1.clone()),
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
        // These are views over the aliased finalization region. Every P.*
        // identity below uses bare r15 so it also binds disabled t=15 rows,
        // while ignoring live t=63 finalization values.
        let is_marker_block = aliased[0].clone();
        let is_length_block = aliased[1].clone();
        let is_marker_word: [E::F; N_INPUT_WORDS] = std::array::from_fn(|j| aliased[2 + j].clone());
        let marker_byte_sel: [E::F; WORD_BYTES] =
            std::array::from_fn(|b| aliased[2 + N_INPUT_WORDS + b].clone());
        let marker_word_byte: [E::F; WORD_BYTES] =
            std::array::from_fn(|b| aliased[2 + N_INPUT_WORDS + WORD_BYTES + b].clone());
        let bit_length_base = 2 + N_INPUT_WORDS + 2 * WORD_BYTES;
        let bit_length_w14_lo = aliased[bit_length_base].clone();
        let bit_length_w14_hi = aliased[bit_length_base + 1].clone();
        let bit_length_w15_lo = aliased[bit_length_base + 2].clone();
        let bit_length_w15_hi = aliased[bit_length_base + 3].clone();

        // The block's message word `W[j]`, from the t = 15 row's viewpoint.
        let w_msg = |j: usize| -> &(E::F, E::F) { &w[15 - j] };

        // (P.A) Binary checks.
        for flag in [&is_marker_block, &is_length_block] {
            eval.add_constraint(r15.clone() * flag.clone() * (E::F::one() - flag.clone()));
        }
        for bit in is_marker_word.iter() {
            eval.add_constraint(r15.clone() * bit.clone() * (E::F::one() - bit.clone()));
        }
        for bit in marker_byte_sel.iter() {
            eval.add_constraint(r15.clone() * bit.clone() * (E::F::one() - bit.clone()));
        }

        // (P.A') Mn1: pin the padding-role flags to 0 on disabled rows.
        let one_minus_enabler = E::F::one() - enabler.clone();
        for flag in [&is_marker_block, &is_length_block] {
            eval.add_constraint(r15.clone() * one_minus_enabler.clone() * flag.clone());
        }

        // (P.B) One-hot sums match the block role.
        let sum_is_marker_word: E::F = is_marker_word
            .iter()
            .cloned()
            .fold(E::F::from(M31::from(0u32)), |acc, b| acc + b);
        eval.add_constraint(r15.clone() * (sum_is_marker_word - is_marker_block.clone()));
        let sum_marker_byte_sel: E::F = marker_byte_sel
            .iter()
            .cloned()
            .fold(E::F::from(M31::from(0u32)), |acc, b| acc + b);
        eval.add_constraint(r15.clone() * (sum_marker_byte_sel - is_marker_block.clone()));

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
            r15.clone()
                * (sum_w_hi
                    - byte_base.clone() * marker_word_byte[0].clone()
                    - marker_word_byte[1].clone()),
        );
        eval.add_constraint(
            r15.clone()
                * (sum_w_lo
                    - byte_base.clone() * marker_word_byte[2].clone()
                    - marker_word_byte[3].clone()),
        );

        // (P.E) The marker byte is `0x80`.
        let marker_value = E::F::from(M31::from(0x80u32));
        for b in 0..WORD_BYTES {
            eval.add_constraint(
                r15.clone()
                    * marker_byte_sel[b].clone()
                    * (marker_word_byte[b].clone() - marker_value.clone()),
            );
        }

        // (P.F) Bytes strictly after the marker byte are zero.
        let mut cum_byte_sel = E::F::from(M31::from(0u32));
        for b in 0..WORD_BYTES {
            eval.add_constraint(r15.clone() * cum_byte_sel.clone() * marker_word_byte[b].clone());
            cum_byte_sel += marker_byte_sel[b].clone();
        }

        // (P.G) Words strictly after the marker word are zero (length-field
        // exception. See the wide-layout derivation for the W[14]/W[15]
        // case analysis).
        for (j, cum_marker) in cum_marker_word.iter().enumerate().take(14) {
            let gate = r15.clone() * (cum_marker.clone() + is_length_only_block.clone());
            eval.add_constraint(gate.clone() * w_msg(j).0.clone());
            eval.add_constraint(gate * w_msg(j).1.clone());
        }
        let gate_post_strict_15 = r15.clone() * marker_word_post_strict_15.clone();
        eval.add_constraint(gate_post_strict_15.clone() * w_msg(15).0.clone());
        eval.add_constraint(gate_post_strict_15 * w_msg(15).1.clone());

        // (P.H) Length-field encoding.
        let gate_length = r15.clone() * is_length_block.clone();
        eval.add_constraint(gate_length.clone() * (w_msg(14).0.clone() - bit_length_w14_lo));
        eval.add_constraint(gate_length.clone() * (w_msg(14).1.clone() - bit_length_w14_hi));
        eval.add_constraint(gate_length.clone() * (w_msg(15).0.clone() - bit_length_w15_lo));
        eval.add_constraint(gate_length * (w_msg(15).1.clone() - bit_length_w15_hi));

        // ---- packed active prefix and message metadata ----
        eval.add_constraint(
            enabler.clone() * (E::F::one() - enabler_prev.clone()) - first_row.clone(),
        );
        eval.add_constraint(
            enabler_prev.clone()
                * (E::F::one() - enabler.clone())
                * (E::F::one() - block_start.clone()),
        );
        eval.add_constraint(msg_start.clone() * (msg_start.clone() - E::F::one()));
        eval.add_constraint(msg_start.clone() * (E::F::one() - gate_block_start.clone()));
        eval.add_constraint(first_row.clone() * (msg_start.clone() - E::F::one()));

        let [msg_id, msg_id_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        let [msg_block, msg_block_prev] = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1]);
        eval.add_constraint(first_row.clone() * msg_id.clone());
        eval.add_constraint(
            (enabler.clone() - gate_block_start.clone()) * (msg_id.clone() - msg_id_prev.clone()),
        );
        eval.add_constraint(
            (gate_block_start.clone() - first_row.clone())
                * (msg_id.clone() - msg_id_prev.clone() - msg_start.clone()),
        );
        eval.add_constraint(msg_start.clone() * msg_block.clone());
        eval.add_constraint(
            (enabler.clone() - gate_block_start.clone())
                * (msg_block.clone() - msg_block_prev.clone()),
        );
        eval.add_constraint(
            (gate_block_start.clone() - msg_start.clone())
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

        // ---- full padded-message provider (four bytes per input-word row) ----
        if self.expose_field {
            let base = E::F::from(M31::from(crate::relations::PACKED_SHA_STREAM_FIELD_BASE));
            for byte_in_word in 0..WORD_BYTES {
                let first_bit = (WORD_BYTES - 1 - byte_in_word) * 8;
                let value = (0..8).fold(E::F::from(M31::from(0u32)), |acc, bit| {
                    acc + w_bit_at(first_bit + bit, 0) * E::F::from(M31::from(1u32 << bit))
                });
                let byte_index = msg_block.clone()
                    * E::F::from(M31::from(crate::constants::BLOCK_BYTES as u32))
                    + round_index.clone() * E::F::from(M31::from(WORD_BYTES as u32))
                    + E::F::from(M31::from(byte_in_word as u32));
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.field.field,
                    -gate_input.clone(),
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

fn word_from_bits<E: EvalAtRow>(bits: &[E::F; WORD_BIT_COLS]) -> (E::F, E::F) {
    (
        limb_sum::<E>(bits, 0),
        limb_sum::<E>(bits, LIMB_BITS as usize),
    )
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

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_constraint_framework::expr::ExprEvaluator;

    #[test]
    fn symbolic_degree_fits_declared_bound_with_all_optional_sites() {
        let log_size = 14;
        let eval = Sha256Eval {
            log_size,
            relations: Sha256Relations::dummy(),
            expose_digest: true,
            expose_field: true,
            claim_mask_beta: Some(QM31::from_u32_unchecked(3, 5, 7, 11)),
        };
        let declared = eval.max_constraint_log_degree_bound();
        let measured = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds()
            .into_iter()
            .max()
            .unwrap_or(0) as u32;
        let supported = (1u32 << (declared - log_size)) + 1;
        assert_eq!(measured, 5);
        assert!(
            measured <= supported,
            "degree {measured} exceeds {supported}"
        );
    }
}
