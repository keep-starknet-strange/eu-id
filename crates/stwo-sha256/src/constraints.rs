//! AIR evaluator for the SHA-256 component.
//!
//! Implements [`FrameworkEval`] for the three-seed-row plus 64-round layout
//! in [`crate::trace`]. Linear constraints bind the IV, mod-2³² additions,
//! rolling round state, block chain, and final state. Other constraints bind the `σ`,
//! `Σ`, `Maj`, and `Ch` outputs directly from Boolean bits and bind the
//! working-state aliases.
//! Separate bit recompositions bind each 16-bit word limb. `Range_{2,4,5}`
//! lookups range-check addition carries. `Range_8` lookups range-check the
//! final digest bytes in `crate::digest_bridge`.
//!
//! The padding constraints bind the FIPS 180-4 §5.1.1 structure. They bind
//! the `0x80` marker position, zero bytes after the marker, and the bit length
//! in `W[14]` and `W[15]`. Each 67-row block region represents one 64-byte
//! block. Integration modules bind the length and marker position to the mdoc
//! parser stream.
//!
//! Each `next_trace_mask` call must use the column order and row offsets in
//! [`crate::trace::Layout`].

use num_traits::{One, Zero};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry, ORIGINAL_TRACE_IDX};

use crate::components::{
    is_first_round_column_id_ns, is_first_row_column_id_ns, round_cyclic_column_ids_ns,
};
use crate::constants::{IV, N_STATE_WORDS};
use crate::field_exposure::{FieldExposure, FULL_PADDED_STREAM_SITES_PER_ROW};
use crate::relations::Sha256Relations;
use crate::trace::{ROWS_PER_BLOCK, WORD_BIT_COLS};
use crate::types::{BYTES_PER_WORD, LIMB_BITS, WORDS_PER_BLOCK};

/// LogUp batch size of the main `Sha256Eval` consumer: 4 fractions fold into
/// one `SecureField` interaction column (`finalize_logup_batched(4)`).
///
/// Degree budget: with every consumer denominator degree ≤ 1 and numerator
/// degree ≤ 2, the batched LogUp constraint has degree
/// `max(1 + Σ deg dᵢ, maxᵢ(deg nᵢ + Σ_{j≠i} deg dⱼ)) = max(1+4, 2+3) = 5`,
/// covered by `max_constraint_log_degree_bound = log_size + 2` (D ≤ 5).
/// The trace generator (`crate::interaction`) and the interaction-column
/// sizing (`crate::air`) both read this constant so the three never drift.
pub const LOGUP_BATCH: usize = 4;

/// Offset from one block row to the same row in the previous block.
const PREVIOUS_BLOCK_OFFSET: isize = -(ROWS_PER_BLOCK as isize);

/// Offset from round 15 to round zero of the next block.
const NEXT_BLOCK_ROUND_ZERO_FROM_ROUND_15: isize = ROWS_PER_BLOCK as isize - 15;

/// AIR evaluator for the three-seed-row and 64-round layout.
#[derive(Clone)]
pub struct Sha256Eval {
    /// `log2` of the row count (the smallest power of two **strictly**
    /// greater than `67 · block count`, per [`crate::trace::min_log_size`]).
    pub log_size: u32,
    /// LogUp relation bundle for range checks, digest limbs, and field bytes.
    pub relations: Sha256Relations,
    /// Optional complete padded-stream provider. The active mode uses one
    /// block-counter column and yields all constrained message bytes.
    pub field_exposure: FieldExposure,
    /// Namespace for consumer-only preprocessed columns.
    pub instance_namespace: String,
    /// Optional zero-sum claim mask, anchored after tree 1.
    pub claim_mask_beta: Option<QM31>,
}

impl FrameworkEval for Sha256Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Base constraints are degree ≤ 3. Full padded-stream mode
        // adds one degree-4 final-counter identity
        // (`gate_r15 · (1-enabler_after_block) · (counter-expected)`).
        // The binding term is the batch-4 LogUp finalizer
        // (`finalize_logup_batched(LOGUP_BATCH)`): four degree-1 denominators
        // and degree-≤ 2 numerators fold to a degree-5 constraint (see
        // [`LOGUP_BATCH`]), so the budget is `log_size + 2` (D ≤ 5).
        self.log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // ---- preprocessed block-cyclic columns ----
        let cyclic = round_cyclic_column_ids_ns(&self.instance_namespace);
        let k_lo = eval.get_preprocessed_column(cyclic[0].clone());
        let k_hi = eval.get_preprocessed_column(cyclic[1].clone());
        let r0 = eval.get_preprocessed_column(cyclic[2].clone());
        let r15 = eval.get_preprocessed_column(cyclic[3].clone());
        let r63 = eval.get_preprocessed_column(cyclic[4].clone());
        let is_sched = eval.get_preprocessed_column(cyclic[5].clone());
        let is_round = eval.get_preprocessed_column(cyclic[6].clone());
        let round_index = eval.get_preprocessed_column(cyclic[7].clone());
        let is_first_row =
            eval.get_preprocessed_column(is_first_row_column_id_ns(&self.instance_namespace));
        let is_first_round =
            eval.get_preprocessed_column(is_first_round_column_id_ns(&self.instance_namespace));

        // ---- header ----
        //
        let [enabler, enabler_prev, enabler_next, enabler_after_block] = eval
            .next_interaction_mask(
                ORIGINAL_TRACE_IDX,
                [0, -1, 1, NEXT_BLOCK_ROUND_ZERO_FROM_ROUND_15],
            );
        eval.add_constraint(enabler.clone() * (E::F::one() - enabler.clone()));
        eval.add_constraint(
            enabler.clone() * (E::F::one() - enabler_prev.clone()) - is_first_row.clone(),
        );
        eval.add_constraint(is_first_round.clone() * (E::F::one() - enabler.clone()));

        let gate_round = enabler.clone() * is_round.clone();
        let gate_r0 = enabler.clone() * r0.clone();
        let gate_r15 = enabler.clone() * r15.clone();
        let gate_r63 = enabler.clone() * r63.clone();
        let gate_sched = enabler.clone() * is_sched.clone();
        let gate_input = enabler.clone() * (is_round.clone() - is_sched.clone());

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

        // ---- round family: outputs, carries, Boolean operands ----
        //
        // Column order matches `trace::write_round_row`: σ0, σ1, ch, maj,
        // t1, t2 read at offset 0; a_new / e_new additionally at offsets
        // −1..−3 (they carry the final working state across rows).
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

        // The current and preceding three rows give a/b/c/d and e/f/g/h.
        // Offsets 63..66 recover the block input during finalization.
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
        let sched_sigma0_bits: [E::F; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let sched_sigma1_bits: [E::F; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_trace_mask());

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

        for (word, &iv_word) in initial_state.iter().zip(&IV) {
            eval.add_constraint(
                is_first_round.clone() * (word.0.clone() - E::F::from(M31::from(iv_word & 0xffff))),
            );
            eval.add_constraint(
                is_first_round.clone()
                    * (word.1.clone() - E::F::from(M31::from(iv_word >> LIMB_BITS))),
            );
        }

        // ---- round constraints ----
        constrain_boolean_bits::<E>(&mut eval, &w_bits);
        constrain_boolean_bits::<E>(&mut eval, &a_bits);
        constrain_boolean_bits::<E>(&mut eval, &e_bits);
        constrain_boolean_bits::<E>(&mut eval, &sched_sigma0_bits);
        constrain_boolean_bits::<E>(&mut eval, &sched_sigma1_bits);

        constrain_word_recomposition::<E>(&mut eval, gate_round.clone(), &w[0], &w_bits);
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
        // preprocessed cyclic columns; `h`/`d` are boundary selects.
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
        let not_r63 = E::F::one() - r63.clone();
        for (carry, output) in final_carries.iter().zip(&h_out) {
            for cell in [&carry.0, &carry.1, &output.0, &output.1] {
                eval.add_constraint(not_r63.clone() * cell.clone());
            }
        }

        // Finalization reads the input state from the rolling bit lanes at
        // offsets 63..66 and the post-round state from a_new/e_new at 0..3.
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

        // Continuation seed bits must be the exact canonical bit view of the
        // previous block output.
        let chain_gate = gate_r0.clone() - is_first_round.clone();
        for j in 0..N_STATE_WORDS {
            eval.add_constraint(
                chain_gate.clone() * (initial_state[j].0.clone() - h_out_prev[j].0.clone()),
            );
            eval.add_constraint(
                chain_gate.clone() * (initial_state[j].1.clone() - h_out_prev[j].1.clone()),
            );
        }

        // ---- final-state provider ----
        // `is_last_block = enabler · is_round_63 · (1 − enabler_next)`: 1
        // only at the last real row (the final block's t = 63 row, whose
        // successor is padding — guaranteed by `min_log_size`).
        let is_last_block = eval.next_trace_mask();
        eval.add_constraint(
            is_last_block.clone() - gate_r63.clone() * (E::F::one() - enabler_next.clone()),
        );

        let digest_limbs: [E::F; 2 * N_STATE_WORDS] = std::array::from_fn(|index| {
            let word = index / 2;
            if index.is_multiple_of(2) {
                h_out[word].0.clone()
            } else {
                h_out[word].1.clone()
            }
        });
        eval.add_to_relation(RelationEntry::base(
            &self.relations.digest.limbs,
            -is_last_block.clone(),
            &digest_limbs,
        ));

        // ---- padding-role constraints (t = 15 rows) ----
        //
        // The block's message words `W[j]` are the `W` columns of rows
        // `t = j`, or `w[15 - j]` from this row. All padding cells are zero
        // outside an active round-15 row.
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

        let not_r15 = E::F::one() - r15.clone();
        for cell in [
            &is_marker_block,
            &is_length_block,
            &is_length_only_block,
            &is_marker_only_block,
            &marker_word_post_strict_15,
            &bit_length_w14_lo,
            &bit_length_w14_hi,
            &bit_length_w15_lo,
            &bit_length_w15_hi,
        ] {
            eval.add_constraint(not_r15.clone() * cell.clone());
        }
        for cell in is_marker_word
            .iter()
            .chain(&marker_byte_sel)
            .chain(&marker_word_byte)
        {
            eval.add_constraint(not_r15.clone() * cell.clone());
        }

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

        // (P.A') Pin the padding-role flags to 0 on disabled rows.
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

        // (P.G) Words after the marker word are zero. W[14] and W[15] can
        // contain the length field.
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

        // ---- field provider (four bytes on each input-word row) ----
        if let Some((field_id, padded_len)) = self.field_exposure.full_padded_stream() {
            let [block_counter, block_counter_prev, block_counter_prev_block] =
                eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -1, PREVIOUS_BLOCK_OFFSET]);
            eval.add_constraint(
                (E::F::one() - is_round.clone() + is_sched.clone()) * block_counter.clone(),
            );
            eval.add_constraint((E::F::one() - enabler.clone()) * block_counter.clone());
            eval.add_constraint(is_first_round.clone() * block_counter.clone());
            eval.add_constraint(
                (gate_input.clone() - gate_r0.clone())
                    * (block_counter.clone() - block_counter_prev.clone()),
            );
            eval.add_constraint(
                chain_gate.clone()
                    * (block_counter.clone() - block_counter_prev_block - E::F::one()),
            );
            let expected_last_block = padded_len / crate::constants::BLOCK_BYTES - 1;
            eval.add_constraint(
                gate_r15.clone()
                    * (E::F::one() - enabler_after_block.clone())
                    * (block_counter.clone() - E::F::from(M31::from(expected_last_block as u32))),
            );

            for byte_in_word in 0..FULL_PADDED_STREAM_SITES_PER_ROW {
                let first_bit = (BYTES_PER_WORD - 1 - byte_in_word) * 8;
                let mut byte = E::F::zero();
                for bit in 0..8 {
                    byte += E::F::from(M31::from(1u32 << bit)) * w_bits[first_bit + bit].clone();
                }
                let byte_index = block_counter.clone()
                    * E::F::from(M31::from(crate::constants::BLOCK_BYTES as u32))
                    + round_index.clone() * E::F::from(M31::from(BYTES_PER_WORD as u32))
                    + E::F::from(M31::from(byte_in_word as u32));
                let tuple = [E::F::from(M31::from(field_id)), byte_index, byte];
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.field.field,
                    -gate_input.clone(),
                    &tuple,
                ));
            }
        }

        if let Some(beta) = self.claim_mask_beta {
            air_core::claim_mask::add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_batched(LOGUP_BATCH);

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

fn constrain_bits_equal<E: EvalAtRow>(
    eval: &mut E,
    lhs: &[E::F; WORD_BIT_COLS],
    rhs: &[E::F; WORD_BIT_COLS],
) {
    for i in 0..WORD_BIT_COLS {
        eval.add_constraint(lhs[i].clone() - rhs[i].clone());
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
    // The `RangeKind` must match the addend count in `crate::headroom`.
    // The debug check detects a mismatch at the call site. `Range_8` is a
    // byte check and cannot check an addition carry.
    use crate::components::RangeKind;
    let expected_addends = match range_kind {
        RangeKind::Range2 => 2,
        RangeKind::Range4 => 4,
        RangeKind::Range5 => 5,
        RangeKind::Range8 => {
            panic!("Range8 is the terminal byte check; do not use it for mod-2³² add carries")
        }
    };
    // Check the addend count in release and debug builds.
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
/// (`Range_2`/`4`/`5`, via [`emit_mod_2_32_add_linear`]). The digest bridge
/// emits `Range_8` lookups.
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

    /// The rolling state word at offset `k - 1` from round `t`.
    fn state_word(
        trace: &Trace,
        log_size: u32,
        b: usize,
        t: usize,
        k: usize,
        h_base: usize, // 0 for the a-side, 4 for the e-side
        _new_cols: (usize, usize),
    ) -> (i64, i64) {
        let natural =
            b * crate::trace::ROWS_PER_BLOCK + crate::trace::STATE_SEED_ROWS + t - (k - 1);
        let slot = Layout::row_slot(natural, log_size);
        let lane = usize::from(h_base == 4);
        let word = (0..crate::trace::WORD_BIT_COLS).fold(0u32, |value, bit| {
            value | (trace[Layout::round_operand_bit(lane, bit)][slot].0 << bit)
        });
        (i64::from(word & 0xffff), i64::from(word >> 16))
    }

    fn input_state_word(trace: &Trace, log_size: u32, block: usize, word: usize) -> (i64, i64) {
        if word < 4 {
            state_word(trace, log_size, block, 0, word + 1, 0, (0, 0))
        } else {
            state_word(trace, log_size, block, 0, word - 3, 4, (0, 0))
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
            for (j, &iv) in IV.iter().enumerate().take(N_STATE_WORDS) {
                let h_in = input_state_word(&trace, log_size, b, j);
                if b == 0 {
                    assert_eq!(h_in.0 as u32, iv & 0xFFFF, "IV lo j={j}");
                    assert_eq!(h_in.1 as u32, iv >> 16, "IV hi j={j}");
                } else {
                    let prev63 = Layout::round_row_slot(b - 1, N_ROUNDS - 1, log_size);
                    let h_out_prev = pair(&trace, Layout::h_out_word(j), prev63);
                    assert_eq!(h_in, h_out_prev, "chain j={j} b={b}");
                }
            }

            for (t, &round_constant) in K.iter().enumerate().take(N_ROUNDS) {
                let slot = Layout::round_row_slot(b, t, log_size);
                let d = state_word(&trace, log_size, b, t, 4, 0, a_new_c);
                let h_state = state_word(&trace, log_size, b, t, 4, 4, e_new_c);
                let k_t = (
                    i64::from(round_constant & 0xFFFF),
                    i64::from(round_constant >> 16),
                );
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
                let h_in = input_state_word(&trace, log_size, b, j);
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

    /// Each round after round zero receives the preceding round output.
    #[test]
    fn reuse_chain_duplicates_match_their_sources() {
        let witness = compute_sha256_witness(&[0x24; 100]);
        let log_size = min_log_size(witness.blocks.len());
        let trace = generate_trace(&witness, log_size);
        let r = Layout::round_col();
        for b in 0..witness.blocks.len() {
            for t in 0..N_ROUNDS {
                if t > 0 {
                    let a = state_word(&trace, log_size, b, t, 1, 0, (0, 0));
                    let e = state_word(&trace, log_size, b, t, 1, 4, (0, 0));
                    let previous = Layout::round_row_slot(b, t - 1, log_size);
                    assert_eq!(a, pair(&trace, (r[12], r[13]), previous));
                    assert_eq!(e, pair(&trace, (r[14], r[15]), previous));
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

        let seed = Layout::seed_row_slot(1, 0, log_size);
        let bit_col = Layout::round_operand_bit(0, 0);
        trace[bit_col][seed] = BaseField::from(1u32 - trace[bit_col][seed].0);

        let prev63 = Layout::round_row_slot(0, N_ROUNDS - 1, log_size);
        let h_in = input_state_word(&trace, log_size, 1, 3).0;
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
        let mut cum = [0i64; WORDS_PER_BLOCK];
        for j in 1..WORDS_PER_BLOCK {
            cum[j] = cum[j - 1] + mword[j - 1];
        }
        // P.C'
        res.push(post_strict_15 - cum[15] * (1 - is_length));
        // P.D byte assembly
        let mut sum_hi = 0i64;
        let mut sum_lo = 0i64;
        for (j, &marker_word) in mword.iter().enumerate().take(WORDS_PER_BLOCK) {
            sum_hi += marker_word * w(j).1;
            sum_lo += marker_word * w(j).0;
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
        for (j, &marker_prefix) in cum.iter().enumerate().take(14) {
            let gate = marker_prefix + is_length_only;
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
