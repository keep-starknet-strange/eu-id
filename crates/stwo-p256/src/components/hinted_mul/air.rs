//! AIR for the hinted mod-p multiplication (see the module docs in [`super`]
//! for the three carry identities and the integer-lifting bounds worksheet).
//!
//! Each multiplication uses one row.
//! Three ungated extension-field constraints prove the carry identities.
//! Their coefficients are powers of channel challenge `z`.
//! The channel draws `z` after the base-trace commitment.
//! Zero padding rows satisfy the identities without a gate.
//!
//! Range13 checks all 13-bit limbs.
//! A signed table checks carry high parts in `[−12, 12]`.

use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::ComponentProver;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry, TraceLocationAllocator,
    ORIGINAL_TRACE_IDX,
};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};
use stwo_p256_utils::scalar_arithmetic::words_to_limbs;

use crate::components::projective_rcb_mul::relation::ProjectiveRcbMulResultRelation;
use crate::constants::P256_MODULUS;
use crate::range_checks::{
    add_range_check, range_check_value_column_id, RangeCheckClaim, RangeCheckEval,
    RangeCheckRelation, SignedCarryRangeClaim, SignedCarryRangeEval, RANGE13_BITS,
};

use super::trace::{
    gen_hinted_mul_schedule_columns, hinted_mul_schedule_active_id,
    hinted_mul_schedule_mul_index_id, hinted_mul_schedule_proj_mul_id,
    hinted_mul_schedule_source_index_id, HintedMulRelations, HintedMulTraceClaim,
    HINTED_MUL_PROJ_MUL_COLUMNS,
};
use super::witness::{HINTED_MUL_C_COEFFS, HINTED_MUL_H_COEFFS, HINTED_MUL_Q_LIMBS};

/// Signed-table parameters for the carry high parts.
pub const HINTED_MUL_H_HI_EQUATION: &str = "hinted_mul_h_hi";
pub const HINTED_MUL_H_HI_TABLE_LOG_SIZE: u32 = 5;

// ---- Formula offset unions (masks walk coset order, a source referencing
// group mul `j` at silo row `k` lives at offset `j − k`). Offset index 0 is
// always `0` (the current cell). Verified from the spec table numerically. ----
const A_OFFS_N: usize = 9;
const A_OFFS: [isize; A_OFFS_N] = [0, -1, -2, -3, -4, -6, -9, -10, -11];
const B_OFFS_N: usize = 4;
const B_OFFS: [isize; B_OFFS_N] = [0, -1, -2, -4];
const R_OFFS_N: usize = 13;
const R_OFFS: [isize; R_OFFS_N] = [0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12];
const OP_OFFS_N: usize = 15;
const OP_OFFS: [isize; OP_OFFS_N] = [
    0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14,
];
const OINF_OFFS_N: usize = 3;
const OINF_OFFS: [isize; OINF_OFFS_N] = [0, -13, -14];

/// The post-commitment challenge: `z` and everything `evaluate` derives from
/// it. Drawn via [`HintedMulChallenge::draw`] at the same transcript position
/// as the LogUp relations (after the base-tree commitment).
#[derive(Clone, Debug)]
pub struct HintedMulChallenge {
    /// `z^0 … z^(HINTED_MUL_C_COEFFS − 1)`.
    pub z_powers: [SecureField; HINTED_MUL_C_COEFFS],
    /// `P(z)` for the field prime's limb polynomial.
    pub p_at_z: SecureField,
    /// `z − β`.
    pub z_minus_beta: SecureField,
}

impl HintedMulChallenge {
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self::from_z(channel.draw_secure_felt())
    }

    pub fn from_z(z: SecureField) -> Self {
        let one = SecureField::from(M31::from_u32_unchecked(1));
        let mut z_powers = [one; HINTED_MUL_C_COEFFS];
        for i in 1..HINTED_MUL_C_COEFFS {
            z_powers[i] = z_powers[i - 1] * z;
        }
        let p_limbs = words_to_limbs(&P256_MODULUS);
        let mut p_at_z = SecureField::from(M31::from_u32_unchecked(0));
        for (i, &limb) in p_limbs.iter().enumerate() {
            p_at_z += z_powers[i] * SecureField::from(M31::from_u32_unchecked(limb));
        }
        let beta = SecureField::from(M31::from_u32_unchecked(1 << LIMB_BITS));
        Self {
            z_powers,
            p_at_z,
            z_minus_beta: z - beta,
        }
    }
}

pub type HintedMulComponent = FrameworkComponent<HintedMulEval>;

type HintedMulEvalGroup<F> = (Vec<F>, Vec<F>, Vec<F>, Vec<F>);

#[derive(Clone)]
pub struct HintedMulEval {
    pub log_size: u32,
    pub preprocessed_namespace: Option<String>,
    pub challenge: HintedMulChallenge,
    pub range13: RangeCheckRelation,
    pub signed_h: RangeCheckRelation,
    pub mul_result: ProjectiveRcbMulResultRelation,
    /// EC-op header link consumed on proj group header rows.
    pub header: super::EcOpHeaderRelation,
    /// Signed-carry table for the projective formula carries.
    pub signed_formula: RangeCheckRelation,
}

impl FrameworkEval for HintedMulEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(self.schedule_active_id());
        let source_index = eval.get_preprocessed_column(self.schedule_source_index_id());
        let mul_index = eval.get_preprocessed_column(self.schedule_mul_index_id());

        // Base columns in `push_row_values` order. Every limb is range-checked
        // as it is read, which keeps the logup emission order identical to the
        // column order (the interaction generator mirrors exactly this).
        //
        // Read formula sources at their row-relative offsets.
        // A source for multiplication `j` is on row `j`.
        // Offset zero supplies the current values for all existing uses.
        // Quotient, carry, and input-infinity columns use one offset.
        let read_range13 = |eval: &mut E, count: usize| -> Vec<E::F> {
            (0..count)
                .map(|_| {
                    let mask = eval.next_trace_mask();
                    add_range_check(eval, &self.range13, active.clone(), mask.clone());
                    mask
                })
                .collect()
        };
        // Masked family reads: each column yields its masks at the family's
        // offset union. Offset 0 is range-checked (active-gated) as the current
        // value. Returns per-limb offset arrays.
        let a_masks: Vec<[E::F; A_OFFS_N]> = (0..N_LIMBS)
            .map(|_| {
                let m = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, A_OFFS);
                add_range_check(&mut eval, &self.range13, active.clone(), m[0].clone());
                m
            })
            .collect();
        let b_masks: Vec<[E::F; B_OFFS_N]> = (0..N_LIMBS)
            .map(|_| {
                let m = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, B_OFFS);
                add_range_check(&mut eval, &self.range13, active.clone(), m[0].clone());
                m
            })
            .collect();
        let a: Vec<E::F> = a_masks.iter().map(|m| m[0].clone()).collect();
        let b: Vec<E::F> = b_masks.iter().map(|m| m[0].clone()).collect();

        let mut groups: Vec<HintedMulEvalGroup<E::F>> = Vec::new();
        // RESULT masks (group 2's value): captured during the group loop.
        let mut r_masks: Vec<[E::F; R_OFFS_N]> = Vec::new();
        for g in 0..3 {
            let q = read_range13(&mut eval, HINTED_MUL_Q_LIMBS);
            let value = if g == 2 {
                let masks: Vec<[E::F; R_OFFS_N]> = (0..N_LIMBS)
                    .map(|_| {
                        let m = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, R_OFFS);
                        add_range_check(&mut eval, &self.range13, active.clone(), m[0].clone());
                        m
                    })
                    .collect();
                let value: Vec<E::F> = masks.iter().map(|m| m[0].clone()).collect();
                r_masks = masks;
                value
            } else {
                read_range13(&mut eval, N_LIMBS)
            };
            let h_lo = read_range13(&mut eval, HINTED_MUL_H_COEFFS);
            let h_hi: Vec<E::F> = (0..HINTED_MUL_H_COEFFS)
                .map(|_| {
                    let mask = eval.next_trace_mask();
                    add_range_check(&mut eval, &self.signed_h, active.clone(), mask.clone());
                    mask
                })
                .collect();
            groups.push((q, value, h_lo, h_hi));
        }

        // Append header flags after the witness block.
        // The column order is `op`, `output_inf`, `lhs_inf`, and `rhs_inf`.
        // Read `op` at offsets from 0 through -14.
        // Read `output_inf` at offsets -13 and -14.
        // The header constraints gate the Boolean flags.
        let op_masks = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, OP_OFFS);
        let oinf_masks = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, OINF_OFFS);
        let lhs_inf = eval.next_trace_mask();
        let rhs_inf = eval.next_trace_mask();
        let flags: Vec<E::F> = vec![
            op_masks[0].clone(),
            oinf_masks[0].clone(),
            lhs_inf.clone(),
            rhs_inf.clone(),
        ];
        let one_ef = E::F::from(M31::from_u32_unchecked(1));
        // Read all 15 `is_proj_mul_k` one-hot selectors.
        // `is_proj_mul_0` gates the header relations.
        // The other selectors gate formulas for each multiplication index.
        // Boolean constraints cover each declared preprocessed column.
        let is_proj: Vec<E::F> = (0..HINTED_MUL_PROJ_MUL_COLUMNS)
            .map(|k| eval.get_preprocessed_column(self.schedule_proj_mul_id(k)))
            .collect();
        for flag in &is_proj {
            eval.add_constraint(flag.clone() * (one_ef.clone() - flag.clone()));
        }
        let is_proj_0 = is_proj[0].clone();
        for flag in &flags {
            // Boolean (ungated, deg 2).
            eval.add_constraint(flag.clone() * (one_ef.clone() - flag.clone()));
            // Zero off proj-header rows: (1 - is_proj_0)·flag = 0 (deg 2).
            eval.add_constraint((one_ef.clone() - is_proj_0.clone()) * flag.clone());
        }

        // Provide only the operand and result limbs that consumers use.
        // Projective consumers use six narrow slots in each group.
        // Final-add and public-key consumers use every slot in their source ranges.
        // The role numerators are:
        //   LHS:    wide + is_proj_{0,1,13,14}  = active − Σ_{k=2..12} is_proj_k
        //   RHS:    wide + is_proj_{0,1}        = active − Σ_{k=2..14} is_proj_k
        //   RESULT: wide                        = active − Σ_{k=0..14} is_proj_k
        // All degree 1 (preprocessed columns only).
        let mut proj_2_12 = E::F::from(M31::from_u32_unchecked(0));
        for flag in is_proj.iter().take(13).skip(2) {
            proj_2_12 += flag.clone();
        }
        let proj_13_14 = is_proj[13].clone() + is_proj[14].clone();
        let proj_0_1 = is_proj[0].clone() + is_proj[1].clone();
        let lhs_numerator = active.clone() - proj_2_12.clone();
        let rhs_numerator = active.clone() - proj_2_12.clone() - proj_13_14.clone();
        let result_numerator = active.clone() - proj_0_1 - proj_2_12 - proj_13_14;
        let result = &groups[2].1;
        for (role, limbs, numerator) in [
            (0u32, &a, lhs_numerator),
            (1u32, &b, rhs_numerator),
            (2u32, result, result_numerator),
        ] {
            let mut values = Vec::with_capacity(3 + N_LIMBS);
            values.push(source_index.clone());
            values.push(mul_index.clone());
            values.push(E::F::from(M31::from_u32_unchecked(role)));
            values.extend(limbs.iter().cloned());
            eval.add_to_relation(RelationEntry::base(&self.mul_result, -numerator, &values));
        }
        // CONSUME (+is_proj_0) the EC-op header tuple on each proj group's
        // header row (mul_index == 0): (source_index, op, output_inf, lhs_inf,
        // rhs_inf). The flags live on the header row itself, so read at offset 0.
        eval.add_to_relation(RelationEntry::base(
            &self.header,
            is_proj_0.clone(),
            &[
                source_index.clone(),
                flags[0].clone(),
                flags[1].clone(),
                flags[2].clone(),
                flags[3].clone(),
            ],
        ));

        // Apply three ungated carry identities at `z`.
        // Their degree is at most two.
        let at_z = |limbs: &[E::F], shift: usize| -> E::EF {
            let mut acc = E::EF::from(SecureField::from(M31::from_u32_unchecked(0)));
            for (i, limb) in limbs.iter().enumerate() {
                acc += E::EF::from(self.challenge.z_powers[shift + i]) * limb.clone();
            }
            acc
        };
        let beta = E::F::from(M31::from_u32_unchecked(1 << LIMB_BITS));
        let h_at_z = |h_lo: &[E::F], h_hi: &[E::F]| -> E::EF {
            let mut acc = E::EF::from(SecureField::from(M31::from_u32_unchecked(0)));
            for i in 0..HINTED_MUL_H_COEFFS {
                acc += E::EF::from(self.challenge.z_powers[i])
                    * (h_lo[i].clone() + beta.clone() * h_hi[i].clone());
            }
            acc
        };

        let a_at_z = at_z(&a, 0);
        let b_lo_at_z = at_z(&b[..N_LIMBS / 2], 0);
        let b_hi_at_z = at_z(&b[N_LIMBS / 2..], 0);
        let p_at_z = E::EF::from(self.challenge.p_at_z);
        let z_minus_beta = E::EF::from(self.challenge.z_minus_beta);

        // (1) A(z)·B_lo(z) − Q1(z)·P(z) − M1(z) − (z−β)·H1(z) = 0
        // (2) A(z)·B_hi(z) − Q2(z)·P(z) − M2(z) − (z−β)·H2(z) = 0
        for (half_at_z, (q, value, h_lo, h_hi)) in [b_lo_at_z, b_hi_at_z]
            .into_iter()
            .zip(groups.iter().take(2))
        {
            eval.add_constraint(
                a_at_z.clone() * half_at_z
                    - at_z(q, 0) * p_at_z.clone()
                    - at_z(value, 0)
                    - z_minus_beta.clone() * h_at_z(h_lo, h_hi),
            );
        }
        // (3) M1(z) + z^10·M2(z) − Q3(z)·P(z) − R(z) − (z−β)·H3(z) = 0
        let (q3, r, h3_lo, h3_hi) = &groups[2];
        eval.add_constraint(
            at_z(&groups[0].1, 0) + at_z(&groups[1].1, N_LIMBS / 2)
                - at_z(q3, 0) * p_at_z
                - at_z(r, 0)
                - z_minus_beta * h_at_z(h3_lo, h3_hi),
        );

        // Bind the EC formula for each multiplication index.
        self.evaluate_formula(
            &mut eval,
            &active,
            &is_proj,
            &a_masks,
            &b_masks,
            &r_masks,
            &op_masks,
            &oinf_masks,
        );

        eval.finalize_logup_in_pairs();
        eval
    }
}

impl HintedMulEval {
    fn namespace_id(&self, id: PreProcessedColumnId) -> PreProcessedColumnId {
        namespace_hinted_mul_schedule_id(self.preprocessed_namespace.as_deref(), id)
    }

    fn schedule_active_id(&self) -> PreProcessedColumnId {
        self.namespace_id(hinted_mul_schedule_active_id(self.log_size))
    }

    fn schedule_source_index_id(&self) -> PreProcessedColumnId {
        self.namespace_id(hinted_mul_schedule_source_index_id(self.log_size))
    }

    fn schedule_mul_index_id(&self) -> PreProcessedColumnId {
        self.namespace_id(hinted_mul_schedule_mul_index_id(self.log_size))
    }

    fn schedule_proj_mul_id(&self, k: usize) -> PreProcessedColumnId {
        self.namespace_id(hinted_mul_schedule_proj_mul_id(self.log_size, k))
    }
}

/// Find the mask index of `target` within an offset array (panics if absent —
/// a spec/offset-union mismatch, caught by `assert_constraints` in tests).
fn offs_index(offsets: &[isize], target: isize) -> usize {
    offsets
        .iter()
        .position(|&o| o == target)
        .expect("formula source offset must be in the declared union")
}

impl HintedMulEval {
    /// Phase-2 formula binding: read the new columns and emit the per-mul_index
    /// operand/output constraints from the shared spec table.
    #[allow(clippy::too_many_arguments)]
    fn evaluate_formula<E: EvalAtRow>(
        &self,
        eval: &mut E,
        active: &E::F,
        is_proj: &[E::F],
        a_masks: &[[E::F; A_OFFS_N]],
        b_masks: &[[E::F; B_OFFS_N]],
        r_masks: &[[E::F; R_OFFS_N]],
        op_masks: &[E::F; OP_OFFS_N],
        oinf_masks: &[E::F; OINF_OFFS_N],
    ) {
        use super::formula_bind::{
            add_muxed_combo_reduction, add_muxed_equality, constant_bigint, curve_b_bigint,
            one_bigint, term, RedTarget, ReductionWitness, Src, FORMULA_SPEC,
        };
        use crate::limbs::P256EvalBigInt;

        // Read new columns in layout order (out_val, slot0 q+carries, slot1
        // q+carries). Range/signed checks emit AFTER the header consume (matching
        // the interaction descriptor order). The q columns have no range checks.
        let out_val: [E::F; N_LIMBS] = core::array::from_fn(|_| {
            let m = eval.next_trace_mask();
            add_range_check(eval, &self.range13, active.clone(), m.clone());
            m
        });
        let read_slot = |eval: &mut E| -> ReductionWitness<E> {
            let q = eval.next_trace_mask(); // NO range check on q.
            let carries: [E::F; N_LIMBS] = core::array::from_fn(|_| {
                let c = eval.next_trace_mask();
                add_range_check(eval, &self.signed_formula, active.clone(), c.clone());
                c
            });
            ReductionWitness { q, carries }
        };
        let slot0 = read_slot(eval);
        let slot1 = read_slot(eval);

        let one_c = constant_bigint::<E>(&one_bigint());
        let curve_b_c = constant_bigint::<E>(&curve_b_bigint());

        // Resolve a spec `Src` to an `[E::F; N_LIMBS]` limb array at silo row `k`.
        let resolve = |src: Src, k: usize| -> [E::F; N_LIMBS] {
            match src {
                Src::OwnA => core::array::from_fn(|i| a_masks[i][0].clone()),
                Src::A(j) => {
                    let idx = offs_index(&A_OFFS, j as isize - k as isize);
                    core::array::from_fn(|i| a_masks[i][idx].clone())
                }
                Src::B(j) => {
                    let idx = offs_index(&B_OFFS, j as isize - k as isize);
                    core::array::from_fn(|i| b_masks[i][idx].clone())
                }
                Src::R(j) => {
                    let idx = offs_index(&R_OFFS, j as isize - k as isize);
                    core::array::from_fn(|i| r_masks[i][idx].clone())
                }
                Src::One => core::array::from_fn(|i| one_c.limbs()[i].clone()),
                Src::CurveB => core::array::from_fn(|i| curve_b_c.limbs()[i].clone()),
            }
        };

        let own_a: [E::F; N_LIMBS] = core::array::from_fn(|i| a_masks[i][0].clone());
        let own_b: [E::F; N_LIMBS] = core::array::from_fn(|i| b_masks[i][0].clone());
        for (k, spec) in FORMULA_SPEC.iter().enumerate() {
            let gate = is_proj[k].clone();
            let op_k = op_masks[k].clone(); // op@−k (OP_OFFS[k] == −k).
            let slot0_target = match spec.slot0.map(|r| r.target) {
                Some(RedTarget::OwnA) => own_a.clone(),
                Some(RedTarget::OutVal) => out_val.clone(),
                Some(RedTarget::OwnB) => unreachable!("slot0 never targets b"),
                None => own_a.clone(),
            };

            // Muxed reductions (degenerate-eq combos fold into the mux).
            if let Some(red) = &spec.slot0 {
                let d_srcs: Vec<P256EvalBigInt<E>> = red
                    .double
                    .iter()
                    .map(|st| P256EvalBigInt::<E>::from_limbs(resolve(st.src, k)))
                    .collect();
                let m_srcs: Vec<P256EvalBigInt<E>> = red
                    .mixed
                    .iter()
                    .map(|st| P256EvalBigInt::<E>::from_limbs(resolve(st.src, k)))
                    .collect();
                let d_terms: Vec<_> = red
                    .double
                    .iter()
                    .zip(&d_srcs)
                    .map(|(st, s)| term(st.coeff, s))
                    .collect();
                let m_terms: Vec<_> = red
                    .mixed
                    .iter()
                    .zip(&m_srcs)
                    .map(|(st, s)| term(st.coeff, s))
                    .collect();
                add_muxed_combo_reduction(
                    eval,
                    &gate,
                    &op_k,
                    &slot0_target,
                    &d_terms,
                    &m_terms,
                    &slot0,
                );
            }
            if let Some(red) = &spec.slot1 {
                let d_srcs: Vec<P256EvalBigInt<E>> = red
                    .double
                    .iter()
                    .map(|st| P256EvalBigInt::<E>::from_limbs(resolve(st.src, k)))
                    .collect();
                let m_srcs: Vec<P256EvalBigInt<E>> = red
                    .mixed
                    .iter()
                    .map(|st| P256EvalBigInt::<E>::from_limbs(resolve(st.src, k)))
                    .collect();
                let d_terms: Vec<_> = red
                    .double
                    .iter()
                    .zip(&d_srcs)
                    .map(|(st, s)| term(st.coeff, s))
                    .collect();
                let m_terms: Vec<_> = red
                    .mixed
                    .iter()
                    .zip(&m_srcs)
                    .map(|(st, s)| term(st.coeff, s))
                    .collect();
                add_muxed_combo_reduction(eval, &gate, &op_k, &own_b, &d_terms, &m_terms, &slot1);
            }

            // Pure muxed equalities.
            for eq in spec.eqs {
                let x = if eq.is_a { &own_a } else { &own_b };
                let d = eq.double.map(|s| resolve(s, k));
                let m = eq.mixed.map(|s| resolve(s, k));
                add_muxed_equality(eval, &gate, &op_k, x, d.as_ref(), m.as_ref());
            }
        }

        // Affine/inf shared constraints (both kinds, S-gated by is_proj_k).
        let one_ef = E::F::from(M31::from_u32_unchecked(1));
        // row 13: is_proj_13·(1−output_inf@−13)·(R13@0 − out_val@0) per limb.
        let is_proj_13 = is_proj[13].clone();
        let oinf_13 = oinf_masks[offs_index(&OINF_OFFS, -13)].clone();
        let r13: [E::F; N_LIMBS] = core::array::from_fn(|i| r_masks[i][0].clone());
        // r_masks holds RESULT limbs at offset 0 = R(mul_index) of THIS row. On
        // row 13 that is R(13). The affine binding uses R(13)@0 (this row's
        // result) which under is_proj_13 is exactly R13.
        let finite_13 = is_proj_13.clone() * (one_ef.clone() - oinf_13.clone());
        for i in 0..N_LIMBS {
            eval.add_constraint(finite_13.clone() * (r13[i].clone() - out_val[i].clone()));
        }
        // Row 13 constrains `is_proj_13 · output_inf@−13 · b@0` per limb.
        // Infinity makes `z3` zero, and `z3 = b(M13)`.
        let inf_13 = is_proj_13 * oinf_13;
        for i in 0..N_LIMBS {
            eval.add_constraint(inf_13.clone() * b_masks[i][0].clone());
        }
        // row 14: is_proj_14·(1−output_inf@−14)·(R14@0 − out_val@0) per limb.
        let is_proj_14 = is_proj[14].clone();
        let oinf_14 = oinf_masks[offs_index(&OINF_OFFS, -14)].clone();
        let r14: [E::F; N_LIMBS] = core::array::from_fn(|i| r_masks[i][0].clone());
        let finite_14 = is_proj_14.clone() * (one_ef.clone() - oinf_14);
        for i in 0..N_LIMBS {
            eval.add_constraint(finite_14.clone() * (r14[i].clone() - out_val[i].clone()));
        }

        // out_val hygiene: (1 − is_proj_13 − is_proj_14)·out_val_limb = 0.
        let not_out_row = one_ef.clone() - is_proj[13].clone() - is_proj[14].clone();
        for limb in out_val.iter() {
            eval.add_constraint(not_out_row.clone() * limb.clone());
        }
    }
}

/// Standalone slice: the check component plus its table providers (Range13,
/// the h_hi signed table, and the Phase-2 formula signed table at the projective
/// bound).
pub struct HintedMulSliceComponents {
    pub check: HintedMulComponent,
    pub range13: Option<FrameworkComponent<RangeCheckEval>>,
    pub signed_h: FrameworkComponent<SignedCarryRangeEval>,
    pub signed_formula: Option<FrameworkComponent<SignedCarryRangeEval>>,
}

impl HintedMulSliceComponents {
    pub fn new(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        claimed_sums: &HintedMulSliceClaimedSums,
        challenge: &HintedMulChallenge,
        relations: &HintedMulRelations,
    ) -> Self {
        Self::new_inner(
            allocator,
            log_size,
            claimed_sums,
            challenge,
            relations,
            true,
            true,
            None,
        )
    }

    pub(crate) fn new_without_range13_and_signed_formula_provider_with_preprocessed_namespace(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        claimed_sums: &HintedMulSliceClaimedSums,
        challenge: &HintedMulChallenge,
        relations: &HintedMulRelations,
        namespace: Option<&str>,
    ) -> Self {
        Self::new_inner(
            allocator,
            log_size,
            claimed_sums,
            challenge,
            relations,
            false,
            false,
            namespace,
        )
    }

    fn new_inner(
        allocator: &mut TraceLocationAllocator,
        log_size: u32,
        claimed_sums: &HintedMulSliceClaimedSums,
        challenge: &HintedMulChallenge,
        relations: &HintedMulRelations,
        include_range13_provider: bool,
        include_signed_formula_provider: bool,
        preprocessed_namespace: Option<&str>,
    ) -> Self {
        Self {
            check: HintedMulComponent::new(
                allocator,
                HintedMulEval {
                    log_size,
                    preprocessed_namespace: preprocessed_namespace.map(str::to_string),
                    challenge: challenge.clone(),
                    range13: relations.range13.clone(),
                    signed_h: relations.signed_h.clone(),
                    mul_result: relations.mul_result.clone(),
                    header: relations.header.clone(),
                    signed_formula: relations.signed_formula.clone(),
                },
                claimed_sums.check,
            ),
            range13: include_range13_provider.then(|| {
                FrameworkComponent::new(
                    allocator,
                    RangeCheckEval::new(relations.range13.clone(), RANGE13_BITS),
                    claimed_sums.range13,
                )
            }),
            signed_h: FrameworkComponent::new(
                allocator,
                SignedCarryRangeEval::new(
                    relations.signed_h.clone(),
                    HINTED_MUL_H_HI_TABLE_LOG_SIZE,
                    HINTED_MUL_H_HI_EQUATION,
                ),
                claimed_sums.signed_h,
            ),
            signed_formula: include_signed_formula_provider.then(|| {
                FrameworkComponent::new(
                    allocator,
                    SignedCarryRangeEval::new(
                        relations.signed_formula.clone(),
                        crate::projective_air::projective_rcb_signed_carry_log_size(),
                        crate::projective_air::PROJECTIVE_RCB_SIGNED_CARRY_EQUATION,
                    ),
                    claimed_sums.signed_formula,
                )
            }),
        }
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        let mut components: Vec<&dyn ComponentProver<SimdBackend>> = vec![&self.check];
        if let Some(range13) = &self.range13 {
            components.push(range13);
        }
        components.push(&self.signed_h);
        if let Some(signed_formula) = &self.signed_formula {
            components.push(signed_formula);
        }
        components
    }

    pub fn components(&self) -> Vec<&dyn stwo::core::air::Component> {
        let mut components: Vec<&dyn stwo::core::air::Component> = vec![&self.check];
        if let Some(range13) = &self.range13 {
            components.push(range13);
        }
        components.push(&self.signed_h);
        if let Some(signed_formula) = &self.signed_formula {
            components.push(signed_formula);
        }
        components
    }
}

pub struct HintedMulSliceClaimedSums {
    pub check: SecureField,
    pub range13: SecureField,
    pub signed_h: SecureField,
    pub signed_formula: SecureField,
}

/// Shape claim for the monolithic proof (mixed into the channel).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HintedMulProofClaim {
    pub log_size: u32,
}

impl HintedMulProofClaim {
    pub fn from_trace(claim: &HintedMulTraceClaim) -> Self {
        Self {
            log_size: claim.log_size(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        hinted_mul_slice_preprocessed_ids(self.log_size)
    }
}

/// Per-relation claimed sums of the hinted-mul trio in the monolithic proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HintedMulProofInteractionClaim {
    /// Total logup sum of the check component (its own claimed_sum).
    pub claimed_sum: SecureField,
    pub range13: SecureField,
    pub signed_h: SecureField,
    /// Phase-2 formula signed-carry provider sum.
    pub signed_formula: SecureField,
}

impl HintedMulProofInteractionClaim {
    pub fn zero() -> Self {
        let zero = SecureField::from(M31::from_u32_unchecked(0));
        Self {
            claimed_sum: zero,
            range13: zero,
            signed_h: zero,
            signed_formula: zero,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.claimed_sum,
            self.range13,
            self.signed_h,
            self.signed_formula,
        ]);
    }

    pub(crate) fn total(&self) -> SecureField {
        self.claimed_sum + self.range13 + self.signed_h + self.signed_formula
    }
}

pub fn hinted_mul_signed_table_claim() -> SignedCarryRangeClaim {
    SignedCarryRangeClaim::new(
        HINTED_MUL_H_HI_TABLE_LOG_SIZE,
        super::witness::HINTED_MUL_H_HI_BOUND,
        HINTED_MUL_H_HI_EQUATION,
    )
}

/// Preprocessed ids in commit order: schedule (active, source_index,
/// mul_index, then the 15 `is_proj_mul_k` one-hots), Range13 value, signed
/// table. Mirrors `gen_hinted_mul_slice_preprocessed_trace` /
/// `gen_hinted_mul_schedule_columns` column order exactly.
pub fn hinted_mul_slice_preprocessed_ids(log_size: u32) -> Vec<PreProcessedColumnId> {
    let signed = hinted_mul_signed_table_claim();
    let mut ids = vec![
        hinted_mul_schedule_active_id(log_size),
        hinted_mul_schedule_source_index_id(log_size),
        hinted_mul_schedule_mul_index_id(log_size),
    ];
    ids.extend(
        (0..HINTED_MUL_PROJ_MUL_COLUMNS).map(|k| hinted_mul_schedule_proj_mul_id(log_size, k)),
    );
    ids.push(range_check_value_column_id(RANGE13_BITS));
    ids.push(crate::range_checks::signed_carry_value_column_id(
        &signed.equation_name,
    ));
    ids.push(crate::range_checks::signed_carry_active_column_id(
        &signed.equation_name,
    ));
    // Phase-2 formula signed-carry table (projective bound) value/active ids.
    // Dedup-safe: in the monolithic proof these dedup by equation name against
    // the projective-source providers' identical columns.
    let formula_signed = crate::projective_air::projective_rcb_signed_carry_claim();
    ids.push(crate::range_checks::signed_carry_value_column_id(
        &formula_signed.equation_name,
    ));
    ids.push(crate::range_checks::signed_carry_active_column_id(
        &formula_signed.equation_name,
    ));
    ids
}

pub fn namespace_hinted_mul_schedule_ids(
    namespace: Option<&str>,
    ids: Vec<PreProcessedColumnId>,
) -> Vec<PreProcessedColumnId> {
    ids.into_iter()
        .map(|id| namespace_hinted_mul_schedule_id(namespace, id))
        .collect()
}

fn namespace_hinted_mul_schedule_id(
    namespace: Option<&str>,
    id: PreProcessedColumnId,
) -> PreProcessedColumnId {
    let Some(namespace) = namespace else {
        return id;
    };
    if id.id.starts_with("hinted_mul_schedule_") {
        PreProcessedColumnId {
            id: format!("{namespace}/{}", id.id),
        }
    } else {
        id
    }
}

pub fn gen_hinted_mul_slice_preprocessed_trace(
    claim: &HintedMulTraceClaim,
) -> stwo::core::ColumnVec<crate::scalar::scalar_mod_mul::columns::M31ColumnEval> {
    let mut columns = gen_hinted_mul_schedule_columns(claim);
    columns.push(RangeCheckClaim::new(RANGE13_BITS).gen_preprocessed_column());
    let signed = hinted_mul_signed_table_claim();
    columns.push(signed.gen_value_column());
    columns.push(signed.gen_active_column());
    let formula_signed = crate::projective_air::projective_rcb_signed_carry_claim();
    columns.push(formula_signed.gen_value_column());
    columns.push(formula_signed.gen_active_column());
    columns
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use std::ops::Deref;
    use stwo::core::channel::{Blake2sChannel, Blake2sM31Channel};
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
    use stwo::prover::poly::circle::PolyOps;
    use stwo::prover::{prove, CommitmentSchemeProver};
    use stwo_constraint_framework::{
        assert_constraints_on_trace, FrameworkEval as _, PREPROCESSED_TRACE_IDX,
    };

    use super::super::trace::{
        gen_hinted_mul_base_trace, gen_hinted_mul_interaction_trace,
        hinted_mul_formula_signed_uses, hinted_mul_range13_uses, hinted_mul_signed_uses,
        HintedMulScheduledRow,
    };
    use super::super::witness::HintedMulWitness;
    use super::*;
    use crate::debug::MockCommitmentScheme;
    use crate::range_checks::RangeCheckInteractionClaim;

    fn test_claim(muls: usize) -> HintedMulTraceClaim {
        let rows = (0..muls)
            .map(|i| {
                let mut a = [0u32; N_LIMBS];
                let mut b = [0u32; N_LIMBS];
                // Spread bits across limbs so convolutions and carries are
                // exercised. Keep limbs 13-bit.
                for k in 0..N_LIMBS {
                    a[k] = ((i as u32 + 1) * 2741 + 97 * k as u32) % 8192;
                    b[k] = ((i as u32 + 3) * 4099 + 53 * k as u32) % 8192;
                }
                HintedMulScheduledRow {
                    source_index: i as u32 / 4,
                    mul_index: i as u32 % 4,
                    witness: HintedMulWitness::new(&a, &b).expect("witness builds"),
                    // proj_scope=false ⇒ is_proj_mul_0 is all-zero, the header
                    // consume contributes exactly 0, and the balance check
                    // (which excludes the mul-result provides) is unaffected.
                    op_double: false,
                    lhs_inf: false,
                    rhs_inf: false,
                    output_inf: false,
                    proj_scope: false,
                    formula: super::super::formula_bind::FormulaRowCells::default(),
                }
            })
            .collect();
        HintedMulTraceClaim { rows }
    }

    fn dummy_relations() -> HintedMulRelations {
        let mut channel = Blake2sM31Channel::default();
        HintedMulRelations {
            range13: RangeCheckRelation::draw(&mut channel),
            signed_h: RangeCheckRelation::draw(&mut channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(&mut channel),
            header: super::super::EcOpHeaderRelation::draw(&mut channel),
            signed_formula: RangeCheckRelation::draw(&mut channel),
        }
    }

    /// Trace-domain constraint check of the check component alone (honest
    /// completeness at an arbitrary z. Honest traces satisfy the identities
    /// at EVERY z).
    #[test]
    fn hinted_mul_honest_trace_satisfies_constraints() {
        let claim = test_claim(5);
        let log_size = claim.log_size();
        let relations = dummy_relations();
        let challenge =
            HintedMulChallenge::from_z(SecureField::from_m31_array(core::array::from_fn(|i| {
                M31::from_u32_unchecked(17 + 13 * i as u32)
            })));

        let schedule = gen_hinted_mul_schedule_columns(&claim);
        let base = gen_hinted_mul_base_trace(&claim);
        let (interaction, interaction_claim) =
            gen_hinted_mul_interaction_trace(&claim, &base, &schedule, &relations);

        let mut commitment_scheme = MockCommitmentScheme::default();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(gen_hinted_mul_slice_preprocessed_trace(&claim));
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base);
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.finalize_interaction();

        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(
            &hinted_mul_slice_preprocessed_ids(log_size),
        );
        let components = HintedMulSliceComponents::new(
            &mut allocator,
            log_size,
            &HintedMulSliceClaimedSums {
                check: interaction_claim.claimed_sum,
                range13: SecureField::from(M31::from_u32_unchecked(0)),
                signed_h: SecureField::from(M31::from_u32_unchecked(0)),
                signed_formula: SecureField::from(M31::from_u32_unchecked(0)),
            },
            &challenge,
            &relations,
        );

        let trace = commitment_scheme.trace_domain_evaluations();
        let mut component_trace = trace
            .sub_tree(components.check.trace_locations())
            .map(|tree| tree.into_iter().cloned().collect_vec());
        component_trace[PREPROCESSED_TRACE_IDX] = components
            .check
            .preprocessed_column_indices()
            .iter()
            .map(|idx| trace[PREPROCESSED_TRACE_IDX][*idx])
            .collect();
        let component_eval = components.check.deref();
        assert_constraints_on_trace(
            &component_trace,
            log_size,
            |eval| {
                let _ = component_eval.evaluate(eval);
            },
            components.check.claimed_sum(),
        );
    }

    /// Confirms a complete standalone PCS proof and verification.
    ///
    /// This test also checks the component degree bound with OODS and FRI.
    #[test]
    fn hinted_mul_slice_proves_and_verifies() {
        run_slice(None).expect("honest hinted-mul slice proves and verifies");
    }

    /// Forged result limb: identities are violated at the drawn z. The prover
    /// must fail (constraints unsatisfied).
    #[test]
    fn hinted_mul_slice_rejects_forged_result_limb() {
        let result = run_slice(Some(Box::new(|claim: &mut HintedMulTraceClaim| {
            let row = &mut claim.rows[1].witness;
            row.r[0] = (row.r[0] + 1) % 8192;
        })));
        assert!(result.is_err(), "forged r limb must not prove");
    }

    /// Forged quotient limb: same rejection through identity 1.
    #[test]
    fn hinted_mul_slice_rejects_forged_quotient_limb() {
        let result = run_slice(Some(Box::new(|claim: &mut HintedMulTraceClaim| {
            let row = &mut claim.rows[0].witness;
            row.q1[2] = (row.q1[2] + 1) % 8192;
        })));
        assert!(result.is_err(), "forged q1 limb must not prove");
    }

    /// Forged carry coefficient: rejection through its identity.
    #[test]
    fn hinted_mul_slice_rejects_forged_carry() {
        let result = run_slice(Some(Box::new(|claim: &mut HintedMulTraceClaim| {
            let row = &mut claim.rows[2].witness;
            row.h3[7] += 1;
        })));
        assert!(result.is_err(), "forged h3 coefficient must not prove");
    }

    type Mutation = Box<dyn Fn(&mut HintedMulTraceClaim)>;

    /// Build a projection-scope claim from the shared sample EC trace.
    /// The trace contains Double, finite MixedAdd, and an infinity-operand no-op.
    /// The formula constraints run on these rows.
    fn sample_proj_claim() -> HintedMulTraceClaim {
        let trace = super::super::formula_bind::sample_projective_trace();
        let rcb =
            crate::projective_air::ProjectiveRcbAirTraceClaim::from_projective_trace_lite(&trace)
                .expect("proj rcb claim");
        HintedMulTraceClaim::from_projective_rcb(&rcb).expect("hinted claim builds")
    }

    /// Completeness: a proj-scope claim with the formula constraints live proves
    /// and verifies (Double + finite MixedAdd + no-op source ops).
    #[test]
    fn hinted_mul_slice_formula_live_proves() {
        run_slice_with(sample_proj_claim())
            .expect("proj-scope slice with live formula constraints proves");
    }

    /// Adversarial: forge one result limb of a group mul (breaks the operand/
    /// affine binding and the carry identity) → prove must fail.
    #[test]
    fn hinted_mul_slice_formula_rejects_forged_result_limb() {
        let mut claim = sample_proj_claim();
        // Row 5 of the Double group (mul_index 5, b·R2): flip a result limb.
        let row = claim.rows.iter_mut().find(|r| r.mul_index == 7).unwrap();
        row.witness.r[0] = (row.witness.r[0] + 1) % 8192;
        assert!(
            run_slice_with(claim).is_err(),
            "forged group result limb must not prove"
        );
    }

    /// Adversarial: forge one reduction carry (breaks the slot recurrence) →
    /// prove must fail.
    #[test]
    fn hinted_mul_slice_formula_rejects_forged_carry() {
        let mut claim = sample_proj_claim();
        let row = claim.rows.iter_mut().find(|r| r.mul_index == 6).unwrap();
        row.formula.slot0.1[3] += 1;
        assert!(
            run_slice_with(claim).is_err(),
            "forged reduction carry must not prove"
        );
    }

    /// Adversarial: flip the op flag on a proj group header row (the mux then
    /// selects the wrong kind's combos) → prove must fail (constraint/balance).
    #[test]
    fn hinted_mul_slice_formula_rejects_flipped_op_flag() {
        let mut claim = sample_proj_claim();
        // Flip op on the first group header (mul_index 0, proj_scope).
        let row = claim
            .rows
            .iter_mut()
            .find(|r| r.proj_scope && r.mul_index == 0)
            .unwrap();
        row.op_double = !row.op_double;
        assert!(
            run_slice_with(claim).is_err(),
            "flipped header op flag must not prove"
        );
    }

    /// Drives the standalone slice end to end: commit preprocessed → commit
    /// base (check columns + the two deterministic provider multiplicities) →
    /// draw z + relations → commit interaction → prove → verify. Mutations
    /// are applied to the claim BEFORE trace generation, exactly like a
    /// malicious prover supplying a forged witness.
    fn run_slice(mutate: Option<Mutation>) -> Result<(), String> {
        let mut claim = test_claim(6);
        if let Some(mutate) = mutate {
            mutate(&mut claim);
        }
        run_slice_with(claim)
    }

    /// Slice driver over an arbitrary (possibly proj-scope) claim.
    fn run_slice_with(claim: HintedMulTraceClaim) -> Result<(), String> {
        let log_size = claim.log_size();
        let ids = hinted_mul_slice_preprocessed_ids(log_size);
        let config = PcsConfig {
            pow_bits: 0,
            fri_config: FriConfig::new(5, 2, 16, 1),
            lifting_log_size: None,
        };
        // Range13's provider table at log13 usually dominates. The Phase-2
        // formula signed table (projective bound) may be larger, so take the max.
        let max_bound = (RANGE13_BITS + 1)
            .max(crate::projective_air::projective_rcb_signed_carry_log_size() + 1);
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(max_bound + config.fri_config.log_blowup_factor)
                .circle_domain()
                .half_coset,
        );
        let mut channel = Blake2sChannel::default();
        let mut commitment_scheme =
            CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

        let preprocessed = gen_hinted_mul_slice_preprocessed_trace(&claim);
        let preprocessed_bounds: Vec<u32> =
            preprocessed.iter().map(|c| c.domain.log_size()).collect();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(preprocessed);
        tree_builder.commit(&mut channel);

        // Base tree: check columns, then the (deterministic, pre-randomness)
        // provider multiplicities, in component-allocation order.
        let base = gen_hinted_mul_base_trace(&claim);
        let range13_claim = RangeCheckClaim::new(RANGE13_BITS);
        let range13_multiplicity =
            range13_claim.gen_multiplicity_trace(hinted_mul_range13_uses(&claim));
        let signed_claim = hinted_mul_signed_table_claim();
        let signed_multiplicity =
            signed_claim.gen_multiplicity_trace(hinted_mul_signed_uses(&claim));
        let formula_signed_claim = crate::projective_air::projective_rcb_signed_carry_claim();
        let formula_signed_multiplicity =
            formula_signed_claim.gen_multiplicity_trace(hinted_mul_formula_signed_uses(&claim));
        let mut base_tree = base.clone();
        base_tree.push(range13_multiplicity.clone());
        base_tree.push(signed_multiplicity.clone());
        base_tree.push(formula_signed_multiplicity.clone());
        let base_bounds: Vec<u32> = base_tree.iter().map(|c| c.domain.log_size()).collect();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base_tree);
        tree_builder.commit(&mut channel);

        // Post-commitment randomness: z first, then the LogUp relations.
        let challenge = HintedMulChallenge::draw(&mut channel);
        let relations = HintedMulRelations {
            range13: RangeCheckRelation::draw(&mut channel),
            signed_h: RangeCheckRelation::draw(&mut channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(&mut channel),
            header: super::super::EcOpHeaderRelation::draw(&mut channel),
            signed_formula: RangeCheckRelation::draw(&mut channel),
        };

        let schedule = gen_hinted_mul_schedule_columns(&claim);
        let (check_interaction, interaction_claim) =
            gen_hinted_mul_interaction_trace(&claim, &base, &schedule, &relations);
        let (range13_interaction, range13_provider) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &range13_multiplicity,
                &range13_claim.gen_preprocessed_column(),
                &relations.range13,
            );
        let (signed_interaction, signed_provider) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &signed_multiplicity,
                &signed_claim.gen_value_column(),
                &relations.signed_h,
            );
        let (formula_signed_interaction, formula_signed_provider) =
            RangeCheckInteractionClaim::gen_interaction_trace(
                &formula_signed_multiplicity,
                &formula_signed_claim.gen_value_column(),
                &relations.signed_formula,
            );

        // The check's range/signed consumers must balance against the three
        // providers. The mul-result provides have no consumer in this
        // standalone slice and are excluded (mirrors the projective harness).
        let mul_result_provider =
            crate::components::hinted_mul::trace::hinted_mul_result_provider_sum(
                &claim, &relations,
            );
        // This slice has no provider for the header consume.
        // Exclude that term from the standalone balance.
        let header_consume =
            crate::components::hinted_mul::trace::hinted_mul_header_consume_sum(&claim, &relations);
        let balance = interaction_claim.claimed_sum - mul_result_provider - header_consume
            + range13_provider.claimed_sum
            + signed_provider.claimed_sum
            + formula_signed_provider.claimed_sum;
        if balance != SecureField::from(M31::from_u32_unchecked(0)) {
            return Err("range relations unbalanced".to_string());
        }

        let mut interaction_tree = check_interaction;
        interaction_tree.extend(range13_interaction);
        interaction_tree.extend(signed_interaction);
        interaction_tree.extend(formula_signed_interaction);
        let interaction_bounds: Vec<u32> = interaction_tree
            .iter()
            .map(|c| c.domain.log_size())
            .collect();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction_tree);
        tree_builder.commit(&mut channel);

        let claimed_sums = HintedMulSliceClaimedSums {
            check: interaction_claim.claimed_sum,
            range13: range13_provider.claimed_sum,
            signed_h: signed_provider.claimed_sum,
            signed_formula: formula_signed_provider.claimed_sum,
        };
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = HintedMulSliceComponents::new(
            &mut allocator,
            log_size,
            &claimed_sums,
            &challenge,
            &relations,
        );
        let proof = prove(
            &components.component_provers(),
            &mut channel,
            commitment_scheme,
        )
        .map_err(|error| format!("prove failed: {error}"))?;

        // Verify with a new transcript and the same draw order.
        // This local test does not pin the tree-0 root.
        // Production verification must pin this root.
        let mut channel = Blake2sChannel::default();
        let commitment_scheme_verifier =
            &mut stwo::core::pcs::CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
        commitment_scheme_verifier.commit(proof.commitments[0], &preprocessed_bounds, &mut channel);
        commitment_scheme_verifier.commit(proof.commitments[1], &base_bounds, &mut channel);
        let verifier_challenge = HintedMulChallenge::draw(&mut channel);
        let verifier_relations = HintedMulRelations {
            range13: RangeCheckRelation::draw(&mut channel),
            signed_h: RangeCheckRelation::draw(&mut channel),
            mul_result: ProjectiveRcbMulResultRelation::draw(&mut channel),
            header: super::super::EcOpHeaderRelation::draw(&mut channel),
            signed_formula: RangeCheckRelation::draw(&mut channel),
        };
        commitment_scheme_verifier.commit(proof.commitments[2], &interaction_bounds, &mut channel);
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = HintedMulSliceComponents::new(
            &mut allocator,
            log_size,
            &claimed_sums,
            &verifier_challenge,
            &verifier_relations,
        );
        stwo::core::verifier::verify(
            &components.components(),
            &mut channel,
            commitment_scheme_verifier,
            proof,
        )
        .map_err(|error| format!("verify failed: {error}"))
    }
}
