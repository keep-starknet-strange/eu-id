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
use crate::constants::{DIGEST_BYTES, IV, N_STATE_WORDS};
use crate::field_exposure::FieldExposure;
use crate::relations::Sha256Relations;
use crate::trace::WORD_BIT_COLS;
use crate::types::{BYTES_PER_WORD, LIMB_BITS, WORDS_PER_BLOCK};

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
    /// Yield the final digest bytes on the `Sha256Digest` channel when set.
    ///
    /// This yield is the producer side of the digest binding.
    /// A standalone proof has no digest consumer.
    /// The standalone proof leaves this option disabled.
    /// The combined prover enables it with the P-256 `z` consumer.
    /// The AIR always constrains the digest columns.
    /// This option controls only the cross-module yield.
    pub expose_digest: bool,
    /// Credential field byte exposure.
    ///
    /// The AIR derives configured bytes from the boolean W bit planes.
    /// It yields them on their target block through `Sha256Field`.
    /// Predicate consumers require these exact bytes.
    /// Multi-block exposure adds a block counter and one selector per target.
    /// A standalone proof uses an empty exposure.
    /// A yield without a consumer would leave a nonzero claim sum.
    pub field_exposure: FieldExposure,
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
        // `is_first_row` pins exactly one anchor row (natural row 0 = block
        // 0, round 0) for IV binding.
        let is_first_row = eval.get_preprocessed_column(is_first_row_column_id());

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
        // Consume each physical W-bit column exactly once. An empty exposure
        // needs only the three SHA and padding offsets. Field exposures request
        // all W[0..15] offsets so t=15 can form arbitrary message bytes.
        let w_bits_m = if self.field_exposure.is_empty() {
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
        let sched_sigma0_bits: [E::F; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let sched_sigma1_bits: [E::F; WORD_BIT_COLS] =
            std::array::from_fn(|_| eval.next_trace_mask());

        // ---- t = 0 family ----
        //
        // Read `is_first_block` at offset −15.
        // The field exposure on row `t = 15` uses this block-zero value.
        let [is_first_block, is_first_block_m15] =
            eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, -15]);
        // C1 anchors: pin `is_first_block ≡ is_first_row` and require a real
        // trace row at the anchor.
        eval.add_constraint(is_first_block.clone() - is_first_row.clone());
        eval.add_constraint(is_first_row.clone() * (E::F::one() - enabler.clone()));

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
            eval.add_constraint(is_first_block.clone() * (h_in_lo[j][0].clone() - iv_lo));
            eval.add_constraint(is_first_block.clone() * (h_in_hi[j][0].clone() - iv_hi));
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
        // Check the lower-sigma bit formulas without a gate. This choice keeps
        // `gate_sched` out of their degree-three XOR expressions. Apply the
        // gate only to linear recomposition into live schedule limbs.
        let w_m15_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bit_at(i, 15));
        let w_m2_bits: [E::F; WORD_BIT_COLS] = std::array::from_fn(|i| w_bit_at(i, 2));
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
        // `enabler·is_round_0 − is_first_block` enables only continuation rows.
        // IV binding controls the anchor row.
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
        // only at the last real row. `min_log_size` always adds a padding
        // successor after the final block's t = 63 row.
        let is_last_block = eval.next_trace_mask();
        eval.add_constraint(
            is_last_block.clone() - gate_r63.clone() * (E::F::one() - enabler_next.clone()),
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
        if self.expose_digest {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.digest.digest,
                -is_last_block.clone(),
                &digest_bytes,
            ));
        }

        // ---- §10.4 padding-role constraints (t = 15 rows) ----
        //
        // Identical algebra to the wide layout. The block's message words
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

        // ---- C1 contiguity (aux column `enabler_step`) ----
        let enabler_step = eval.next_trace_mask();
        eval.add_constraint(
            enabler_step.clone() - enabler.clone() * (E::F::one() - enabler_prev.clone()),
        );
        eval.add_constraint((E::F::one() - is_first_row.clone()) * enabler_step.clone());

        // ---- field provider (target block t = 15 rows) ----
        //
        // Each exposed byte is a linear expression over the recomposed Boolean
        // W bit planes. The existing first-block flag gates block-zero
        // exposure. Multi-block exposure adds a witness block counter and one
        // selector for each target block.
        if !self.field_exposure.is_empty() {
            // Block counter: read at [0, -1] to pin its step behaviour. It is a
            // base/witness column carrying `block_idx` on every row.
            let block_counter = if self.field_exposure.needs_dynamic_block_columns() {
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
            // One selector per distinct target block (multi-block only).
            let selectors: Vec<E::F> = if self.field_exposure.needs_dynamic_block_columns() {
                (0..self.field_exposure.target_blocks().len())
                    .map(|_| eval.next_trace_mask())
                    .collect()
            } else {
                Vec::new()
            };
            let block_zero_selector = is_first_block_m15;
            if self.field_exposure.needs_dynamic_block_columns() {
                let b = block_counter
                    .as_ref()
                    .expect("multi-block field exposure has a block counter");
                // Pin each selector: boolean, live only on `t = 15`, and hot
                // only when the counter equals its target block.
                for (&target_block, selector) in
                    self.field_exposure.target_blocks().iter().zip(&selectors)
                {
                    eval.add_constraint(selector.clone() * (selector.clone() - E::F::one()));
                    eval.add_constraint(selector.clone() * (E::F::one() - gate_r15.clone()));
                    eval.add_constraint(
                        selector.clone() * (b.clone() - E::F::from(M31::from(target_block as u32))),
                    );
                }
            }

            for y in self.field_exposure.yields() {
                let selector = if self.field_exposure.needs_dynamic_block_columns() {
                    selectors[self
                        .field_exposure
                        .target_blocks()
                        .binary_search(&y.block_idx)
                        .expect("yield target is in target_blocks")]
                    .clone()
                } else {
                    block_zero_selector.clone()
                };
                // W bits are LSB-first. Big-endian byte positions 0..3 map
                // to bit ranges 24..31, 16..23, 8..15, and 0..7.
                let first_bit = (BYTES_PER_WORD - 1 - y.byte_in_word) * 8;
                let round_offset = 15 - y.word_idx;
                let value = (0..8).fold(E::F::from(M31::from(0u32)), |acc, bit| {
                    acc + w_bit_at(first_bit + bit, round_offset)
                        * E::F::from(M31::from(1u32 << bit))
                });
                let tuple = [
                    E::F::from(M31::from(y.field_id)),
                    E::F::from(M31::from(y.byte_index)),
                    value,
                ];
                eval.add_to_relation(RelationEntry::base(
                    &self.relations.field.field,
                    -selector.clone(),
                    &tuple,
                ));
            }

            // Full padded-message stream. One fixed lookup site per byte
            // position emits on every real block's t=15 row, so the width is
            // independent of the number of blocks. A consumer that walks
            // byte_index 0..N sees the exact compression input. This input
            // includes the SHA marker, zero padding, and length word.
            if let Some(field_id) = self.field_exposure.padded_stream_field_id() {
                let b = block_counter
                    .as_ref()
                    .expect("padded stream exposure has a block counter");
                for byte_in_block in 0..crate::constants::BLOCK_BYTES {
                    let word_idx = byte_in_block / BYTES_PER_WORD;
                    let byte_in_word = byte_in_block % BYTES_PER_WORD;
                    let first_bit = (BYTES_PER_WORD - 1 - byte_in_word) * 8;
                    let round_offset = 15 - word_idx;
                    let value = (0..8).fold(E::F::from(M31::from(0u32)), |acc, bit| {
                        acc + w_bit_at(first_bit + bit, round_offset)
                            * E::F::from(M31::from(1u32 << bit))
                    });
                    let byte_index = b.clone()
                        * E::F::from(M31::from(crate::constants::BLOCK_BYTES as u32))
                        + E::F::from(M31::from(byte_in_block as u32));
                    eval.add_to_relation(RelationEntry::base(
                        &self.relations.field.field,
                        -gate_r15.clone(),
                        &[E::F::from(M31::from(field_id)), byte_index, value],
                    ));
                }
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
    use crate::air::Sha256Prover;
    use crate::constants::{IV, K, N_ROUNDS, N_STATE_WORDS};
    use crate::field_exposure::FieldExposure;
    use crate::relations::Sha256Relations;
    use crate::trace::{generate_trace, min_log_size, Layout};
    use crate::types::WORDS_PER_BLOCK;
    use crate::witness::compute_sha256_witness;
    use air_core::AirProver;
    use stwo::core::fields::m31::BaseField;
    use stwo_constraint_framework::expr::ExprEvaluator;
    use stwo_constraint_framework::FrameworkEval;

    use super::Sha256Eval;

    type Trace = Vec<Vec<BaseField>>;

    #[test]
    fn sha_expression_degree_matches_declared_bound() {
        const LOG_SIZE: u32 = 17;
        let evaluator = Sha256Eval {
            log_size: LOG_SIZE,
            relations: Sha256Relations::dummy(),
            expose_digest: false,
            field_exposure: FieldExposure::empty(),
            claim_mask_beta: None,
        };
        let declared = evaluator.max_constraint_log_degree_bound();
        let max_degree = evaluator
            .clone()
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds()
            .into_iter()
            .max()
            .unwrap_or(0) as u32;
        let required = LOG_SIZE
            + (max_degree.saturating_sub(1))
                .next_power_of_two()
                .trailing_zeros()
                .max(1);

        assert_eq!(
            max_degree, 5,
            "SHA AIR degree changed; review its owner bound"
        );
        assert_eq!(declared, required);
    }

    #[test]
    fn sha_prover_owner_covers_main_and_fixed_table_bounds() {
        let witness = compute_sha256_witness(b"owner-bound");
        for (log_size, expected) in [(15, 17), (16, 18), (20, 22)] {
            let prover = Sha256Prover::new(&witness, log_size);
            assert_eq!(
                prover.max_constraint_log_degree_bound(),
                expected,
                "log size {log_size}"
            );
        }
    }

    fn cell(trace: &[Vec<BaseField>], col: usize, slot: usize) -> i64 {
        i64::from(trace[col][slot].0)
    }

    /// `(lo, hi)` of a two-column pair at a slot.
    fn pair(trace: &Trace, cols: (usize, usize), slot: usize) -> (i64, i64) {
        (cell(trace, cols.0, slot), cell(trace, cols.1, slot))
    }

    /// Return the state word for round `t` and slot position `k`.
    ///
    /// Use `h_in` from row `t = 0` when `t < k`.
    /// Otherwise, use `a_new` or `e_new` from row `t − k`.
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

    /// Verify all linear identities on an honest trace.
    ///
    /// The check covers round additions, schedule recurrence, IV binding,
    /// block chaining, and finalization.
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

    /// Duplicate operand bits match their source cells.
    ///
    /// On non-boundary rows, `b_bits = a_bits@(t−1)`.
    /// Also, `c_bits = a_bits@(t−2)`.
    /// The e-side is symmetric.
    /// AIR word recomposition binds boundary rows to `h_in`.
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
        let mut cum = [0i64; WORDS_PER_BLOCK];
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
