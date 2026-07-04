//! AIR constraint evaluation for the prepared-table family: the EC-row and
//! projective-source `FrameworkEval` impls, the in-AIR negation/pinning
//! constraint builders, and the eval-side point reader.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::{P256_3GX, P256_3GY, P256_MODULUS};
use crate::limbs::{P256EvalBigInt, P256M31BigInt};
use crate::prepared_point::{PREPARED_BASE_COUNT, TABLE16_INDEX};
use crate::projective_air::{PROJECTIVE_RCB_MUL_ROLE_LHS, PROJECTIVE_RCB_MUL_ROLE_RHS};
use crate::types::U256;

use super::*;

#[derive(Clone)]
pub struct PreparedTableEcRowEval {
    pub log_size: u32,
    pub relation: PreparedTableEcRowRelation,
    /// Monolithic full-table pinning relations. `None` => legacy slice.
    pub pinning: Option<PreparedTablePinningRelations>,
}

impl FrameworkEval for PreparedTableEcRowEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Must stay at +1: the prove pipeline rejects a per-component bound of
        // `log_size + 2` (OODS composition check fails even with degree-3
        // constraints), so every constraint here is kept at degree <= 3 by
        // solo LogUp batching (see PREPARED_CONSUMER_LOGUP_BATCH).
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let row_index = eval.get_preprocessed_column(prepared_table_ec_row_index_column_id());
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let kind_flags: [E::F; PREPARED_TABLE_EC_KIND_FLAGS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let op = eval.next_trace_mask();
        let table_index = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let neg = PreparedTableEcEvalPoint::read(&mut eval);
        let neg_carries: [E::F; PREPARED_TABLE_EC_NEG_CARRY_COLUMNS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(active.clone() * (source_index.clone() - row_index));

        let mut kind_sum = E::F::from(M31::from_u32_unchecked(0));
        for flag in &kind_flags {
            eval.add_constraint(flag.clone() * (flag.clone() - one.clone()));
            eval.add_constraint((one.clone() - active.clone()) * flag.clone());
            kind_sum += flag.clone();
        }
        eval.add_constraint(active.clone() * (kind_sum - one.clone()));

        let double_flag = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_P].clone()
            + kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
        eval.add_constraint(active.clone() * (op.clone() - double_flag.clone()));

        let mut expected_table_index = E::F::from(M31::from_u32_unchecked(0));
        for base_index in 0..PREPARED_BASE_COUNT {
            expected_table_index += kind_flags[PREPARED_TABLE_EC_KIND_BASE_START + base_index]
                .clone()
                * E::F::from(M31::from_u32_unchecked(base_index as u32));
        }
        expected_table_index += kind_flags[PREPARED_TABLE_EC_KIND_TABLE16].clone()
            * E::F::from(M31::from_u32_unchecked(TABLE16_INDEX));
        eval.add_constraint(active.clone() * (table_index.clone() - expected_table_index));

        eval.add_constraint(double_flag.clone() * (rhs.inf.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);
        neg.add_constraints(&mut eval, &active, &one);

        // In-AIR negation: on DoubleR, `neg = -lhs (= -R)`; on AddR2R,
        // `neg = -output (= -R3)`. Prove `neg.x = src.x` and the limb addition
        // `neg.y + src.y = p` via the witnessed boolean carries. On all other
        // rows `neg = 0` and `neg_carries = 0` (gated away below).
        let neg_flag = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone()
            + kind_flags[PREPARED_TABLE_EC_KIND_ADD_R2R].clone();
        let src = prepared_table_ec_negation_source::<E>(&kind_flags, &lhs, &output);
        add_negation_constraints(&mut eval, &neg_flag, &src, &neg, &neg_carries, &one);
        // Rows that do not witness a negation must carry `neg = 0` and zero carries.
        let not_neg = active.clone() - neg_flag.clone();
        for value in neg
            .x
            .iter()
            .chain(neg.y.iter())
            .cloned()
            .chain(core::iter::once(neg.inf.clone()))
            .chain(neg_carries.iter().cloned())
        {
            eval.add_constraint(not_neg.clone() * value);
        }

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
            table_index.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        let relation_values = prepared_table_ec_row_relation_values(
            &[
                source_index,
                sig_id.clone(),
                cert_id.clone(),
                op,
                table_index,
            ],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            -active.clone(),
            &relation_values,
        ));

        if let Some(pinning) = &self.pinning {
            // cert_id must be boolean so `is_cert0 = 1 - cert_id` selects cert0.
            eval.add_constraint(active.clone() * cert_id.clone() * (cert_id.clone() - one.clone()));
            add_pinning_emissions(
                &mut eval,
                pinning,
                &active,
                &sig_id,
                &cert_id,
                &kind_flags,
                &lhs,
                &rhs,
                &output,
                &neg,
            );
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

// --- Shared pinning emission schedule ---------------------------------------
//
// Both `add_pinning_emissions` (AIR) and `gen_prepared_table_ec_row_pinned_*`
// (interaction trace) iterate this single static list so the AIR numerators and
// the committed logup fractions are the SAME low-degree polynomials in the same
// order (lessons.md #39, #42). Each entry contributes exactly one logup fraction
// per row; the numerator is the signed multiplicity times the gate product
// (which is zero unless the row's kind/cert matches).

/// Select the negation source point: `lhs` on `DoubleR` rows, `output` on
/// `AddR2R` rows, `0` elsewhere. Exactly one kind flag is set on a neg row.
fn prepared_table_ec_negation_source<E: EvalAtRow>(
    kind_flags: &[E::F; PREPARED_TABLE_EC_KIND_FLAGS],
    lhs: &PreparedTableEcEvalPoint<E::F>,
    output: &PreparedTableEcEvalPoint<E::F>,
) -> PreparedTableEcEvalPoint<E::F> {
    let double_r = kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
    let add_r2r = kind_flags[PREPARED_TABLE_EC_KIND_ADD_R2R].clone();
    let select = |a: &E::F, b: &E::F| double_r.clone() * a.clone() + add_r2r.clone() * b.clone();
    PreparedTableEcEvalPoint {
        x: core::array::from_fn(|i| select(&lhs.x[i], &output.x[i])),
        y: core::array::from_fn(|i| select(&lhs.y[i], &output.y[i])),
        inf: select(&lhs.inf, &output.inf),
    }
}

/// Constrain `neg = -src` (gated by `neg_flag`): `neg.x = src.x`, `neg.inf =
/// src.inf`, and the limb addition `neg.y + src.y = p` via boolean carries. All
/// constraints stay degree ≤ 2: the boolean carry constraint is ungated (carries
/// on non-neg rows are forced to zero by the `not_neg` padding loop).
fn add_negation_constraints<E: EvalAtRow>(
    eval: &mut E,
    neg_flag: &E::F,
    src: &PreparedTableEcEvalPoint<E::F>,
    neg: &PreparedTableEcEvalPoint<E::F>,
    neg_carries: &[E::F; PREPARED_TABLE_EC_NEG_CARRY_COLUMNS],
    one: &E::F,
) {
    let limb_base = E::F::from(M31::from_u32_unchecked(1u32 << LIMB_BITS));
    let p_limbs = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_MODULUS));
    eval.add_constraint(neg_flag.clone() * (neg.inf.clone() - src.inf.clone()));
    for i in 0..N_LIMBS {
        eval.add_constraint(neg_flag.clone() * (neg.x[i].clone() - src.x[i].clone()));
        // Boolean carry (ungated; degree 2).
        let carry = neg_carries[i].clone();
        eval.add_constraint(carry.clone() * (carry.clone() - one.clone()));
        let prev_carry = if i == 0 {
            E::F::from(M31::from_u32_unchecked(0))
        } else {
            neg_carries[i - 1].clone()
        };
        let p_limb = E::F::from(p_limbs.limbs()[i]);
        // neg.y[i] + src.y[i] + prev_carry - p[i] - carry * 2^13 = 0.
        eval.add_constraint(
            neg_flag.clone()
                * (neg.y[i].clone() + src.y[i].clone() + prev_carry
                    - p_limb
                    - carry * limb_base.clone()),
        );
    }
    // The most-significant carry must vanish: neg.y + src.y == p exactly.
    eval.add_constraint(neg_flag.clone() * neg_carries[N_LIMBS - 1].clone());
}

/// Build a `CertBaseRelation` tuple `(sig_id, cert_id, point.x[..], point.y[..])`
/// for the cell's base point.
fn cert_base_relation_values<F: Clone + From<M31>>(
    sig_id: &F,
    cert_id: &F,
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; CERT_BASE_RELATION_ARITY] {
    core::array::from_fn(|index| match index {
        0 => sig_id.clone(),
        1 => cert_id.clone(),
        2..=21 => point.x[index - 2].clone(),
        22..=41 => point.y[index - 2 - N_LIMBS].clone(),
        _ => unreachable!("cert base relation index in range"),
    })
}

/// Build a `PreparedTableCanonicalRelation` tuple `(sig_id, cert_id, role, point[41])`.
fn canonical_relation_values<F: Clone + From<M31>>(
    sig_id: &F,
    cert_id: &F,
    role: u32,
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; PREPARED_TABLE_CANONICAL_RELATION_ARITY] {
    let point_values = point.relation_values();
    core::array::from_fn(|index| match index {
        0 => sig_id.clone(),
        1 => cert_id.clone(),
        2 => F::from(M31::from_u32_unchecked(role)),
        3..=43 => point_values[index - 3].clone(),
        _ => unreachable!("canonical relation index in range"),
    })
}

/// The fixed constant `3·G` as an eval point (cert0's pinned `P3`).
fn three_g_point<F: Clone + From<M31>>() -> PreparedTableEcEvalPoint<F> {
    let x = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GX));
    let y = P256M31BigInt::from_u256(&U256::from_le_u64s(&P256_3GY));
    PreparedTableEcEvalPoint {
        x: core::array::from_fn(|i| F::from(x.limbs()[i])),
        y: core::array::from_fn(|i| F::from(y.limbs()[i])),
        inf: F::from(M31::from_u32_unchecked(0)),
    }
}

/// Emit the fixed `PIN_SCHEDULE` of `CertBaseRelation` +
/// `PreparedTableCanonicalRelation` fractions for one EC row. Every row emits the
/// SAME ordered set of entries; numerators are gated to zero when the row's
/// kind/cert does not match. Mirrored exactly by
/// `gen_prepared_table_ec_row_pinned_interaction_trace`.
#[allow(clippy::too_many_arguments)]
fn add_pinning_emissions<E: EvalAtRow>(
    eval: &mut E,
    pinning: &PreparedTablePinningRelations,
    active: &E::F,
    sig_id: &E::F,
    cert_id: &E::F,
    kind_flags: &[E::F; PREPARED_TABLE_EC_KIND_FLAGS],
    lhs: &PreparedTableEcEvalPoint<E::F>,
    rhs: &PreparedTableEcEvalPoint<E::F>,
    output: &PreparedTableEcEvalPoint<E::F>,
    neg: &PreparedTableEcEvalPoint<E::F>,
) {
    let is_cert0 = active.clone() - cert_id.clone();
    let three_g = three_g_point::<E::F>();
    for entry in PIN_SCHEDULE {
        let mut gate = E::F::from(M31::from_u32_unchecked(1));
        for &k in entry.kinds {
            gate *= kind_flags[k].clone();
        }
        if entry.cert0_only {
            gate *= is_cert0.clone();
        }
        let point = match entry.point {
            PinPoint::Lhs => lhs,
            PinPoint::Rhs => rhs,
            PinPoint::Output => output,
            PinPoint::Neg => neg,
            PinPoint::ConstThreeG => &three_g,
        };
        let numerator = signed_numerator::<E>(gate, entry.mult);
        match entry.relation {
            PinRelation::CertBase => eval.add_to_relation(RelationEntry::base(
                &pinning.cert_base,
                numerator,
                &cert_base_relation_values::<E::F>(sig_id, cert_id, point),
            )),
            PinRelation::Canonical(role) => eval.add_to_relation(RelationEntry::base(
                &pinning.canonical,
                numerator,
                &canonical_relation_values::<E::F>(sig_id, cert_id, role, point),
            )),
        }
    }

    // FinalCheckHint: yield `R_i` (= `lhs`) once per active `DoubleR` row, gated
    // `active * DoubleR_flag`, multiplicity `-1`. Always emitted (one fraction
    // per row) so the AIR numerator and the interaction trace stay in lockstep;
    // the numerator is zero on non-`DoubleR`/padding rows. The relation tuple is
    // the canonical-pinned `R_i`, so this forwards an already-bound value.
    if let Some(final_check_hint) = &pinning.final_check_hint {
        let gate = active.clone() * kind_flags[PREPARED_TABLE_EC_KIND_DOUBLE_R].clone();
        eval.add_to_relation(RelationEntry::base(
            final_check_hint,
            -gate,
            &final_check_hint_relation_values::<E::F>(sig_id, cert_id, lhs),
        ));
    }
}

/// Build a `FinalCheckHintRelation` tuple `(sig_id, cert_id, point[41])`.
fn final_check_hint_relation_values<F: Clone + From<M31>>(
    sig_id: &F,
    cert_id: &F,
    point: &PreparedTableEcEvalPoint<F>,
) -> [F; FINAL_CHECK_HINT_RELATION_ARITY] {
    let point_values = point.relation_values();
    core::array::from_fn(|index| match index {
        0 => sig_id.clone(),
        1 => cert_id.clone(),
        2..=42 => point_values[index - 2].clone(),
        _ => unreachable!("final check hint relation index in range"),
    })
}

/// `mult · gate` as a base-field numerator (`mult` may be negative).
fn signed_numerator<E: EvalAtRow>(gate: E::F, mult: i32) -> E::F {
    let magnitude = E::F::from(M31::from_u32_unchecked(mult.unsigned_abs()));
    let scaled = gate * magnitude;
    if mult < 0 {
        -scaled
    } else {
        scaled
    }
}

#[derive(Clone)]
pub struct PreparedTableProjectiveSourceEval {
    pub log_size: u32,
    pub relation: PreparedTableEcRowRelation,
    /// The hinted provider's mul relation: 6 narrow per-group consumes
    /// (M0/M1 lhs+rhs, M13/M14 lhs) bind the consumer's committed points to
    /// the silo group's operand columns; all other operand/result binding
    /// lives silo-side (hinted_mul formula_bind).
    pub mul_result: crate::projective_air::ProjectiveRcbMulResultRelation,
    /// EC-op header link: PROVIDED (`−has_muls`) here, CONSUMED by the silo.
    pub header: crate::components::hinted_mul::EcOpHeaderRelation,
}

impl FrameworkEval for PreparedTableProjectiveSourceEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let source_index = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let cert_id = eval.next_trace_mask();
        let op = eval.next_trace_mask();
        let table_index = eval.next_trace_mask();
        let lhs = PreparedTableEcEvalPoint::read(&mut eval);
        let rhs = PreparedTableEcEvalPoint::read(&mut eval);
        let output = PreparedTableEcEvalPoint::read(&mut eval);
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(op.clone() * (op.clone() - one.clone()));
        lhs.add_constraints(&mut eval, &active, &one);
        rhs.add_constraints(&mut eval, &active, &one);
        output.add_constraints(&mut eval, &active, &one);

        for value in [
            source_index.clone(),
            sig_id.clone(),
            cert_id.clone(),
            op.clone(),
            table_index.clone(),
        ] {
            eval.add_constraint((one.clone() - active.clone()) * value);
        }

        // Group-existence gate (≡ the old committed `has_muls`): the silo emits
        // a 15-mul group for Double (op == 1) and finite-operand MixedAdd, ZERO
        // for an infinity-operand MixedAdd. `active − (1−op)·rhs.inf` equals
        // `active·(1 − (1−op)·rhs.inf)` on every row because `op` and `rhs.inf`
        // are zeroed on padding (constraints above). Degree 2.
        let gate = active.clone() - (one.clone() - op.clone()) * rhs.inf();

        let relation_values = prepared_table_ec_row_relation_values(
            &[
                source_index.clone(),
                sig_id,
                cert_id,
                op.clone(),
                table_index,
            ],
            &lhs,
            &rhs,
            &output,
        );
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            active.clone(),
            &relation_values,
        ));
        // The 6 narrow mul-result consumes (`+gate`): pin the consumer's own
        // committed point coordinates to the silo group's operand columns.
        add_projective_source_narrow_mul_consumes(
            &mut eval,
            &self.mul_result,
            &source_index,
            &op,
            &gate,
            &lhs,
            &rhs,
            &output,
        );

        // Infinity-operand no-op: `lhs + ∞ = lhs` has no silo group, so pin the
        // output to the accumulator directly. `noop = (1−op)·rhs.inf` equals
        // `active·(1−op)·rhs.inf` on every row (padding zeroing above); the
        // copies are degree 3.
        let noop = (one.clone() - op.clone()) * rhs.inf();
        let (lhs_x, lhs_y) = (lhs.x_bigint(), lhs.y_bigint());
        let (out_x, out_y) = (output.x_bigint(), output.y_bigint());
        for i in 0..N_LIMBS {
            eval.add_constraint(
                noop.clone() * (out_x.limbs()[i].clone() - lhs_x.limbs()[i].clone()),
            );
            eval.add_constraint(
                noop.clone() * (out_y.limbs()[i].clone() - lhs_y.limbs()[i].clone()),
            );
        }
        eval.add_constraint(noop.clone() * (output.inf() - lhs.inf()));

        // EC-op header YIELD (−gate): tuple
        // (source_index, op, output_inf, lhs_inf, rhs_inf), consumed 1:1 by the
        // silo group header. Same tuple/order as the fake-GLV source.
        eval.add_to_relation(RelationEntry::base(
            &self.header,
            -gate,
            &[
                source_index.clone(),
                op.clone(),
                output.inf(),
                lhs.inf(),
                rhs.inf(),
            ],
        ));

        eval.finalize_logup_batched(
            crate::components::fake_glv::prepared_table::interaction::PREPARED_CONSUMER_LOGUP_BATCH,
        );
        eval
    }
}

/// Emit the 6 narrow `ProjectiveRcbMulResultRelation` consumes shared by both
/// projective-source consumers (prepared_table + fake_glv ec_source), in this
/// fixed order: M0.lhs, M0.rhs, M1.lhs, M1.rhs, M13.lhs, M14.lhs. Tuples are
/// built from the consumer's OWN committed point columns per the op kind:
///   M0.lhs = lhs.x (both kinds)      M0.rhs = op·lhs.x + (1−op)·rhs.x
///   M1.lhs = lhs.y                   M1.rhs = op·lhs.y + (1−op)·rhs.y
///   M13.lhs = output.x               M14.lhs = output.y
/// matching the silo's per-group operand layout (Double: M0 = x1·x1,
/// MixedAdd: M0 = x1·x2, …; M13/M14 lhs = affine output coords). The numerator
/// is the group-existence `gate`; the silo provides exactly these slots on proj
/// rows (per-slot provide masks).
#[allow(clippy::too_many_arguments)]
pub(crate) fn add_projective_source_narrow_mul_consumes<E: EvalAtRow>(
    eval: &mut E,
    relation: &crate::projective_air::ProjectiveRcbMulResultRelation,
    source_index: &E::F,
    op: &E::F,
    gate: &E::F,
    lhs: &PreparedTableEcEvalPoint<E::F>,
    rhs: &PreparedTableEcEvalPoint<E::F>,
    output: &PreparedTableEcEvalPoint<E::F>,
) {
    let one = E::F::from(M31::from_u32_unchecked(1));
    let mixed = one - op.clone();
    let (lhs_x, lhs_y) = (lhs.x_bigint(), lhs.y_bigint());
    let (rhs_x, rhs_y) = (rhs.x_bigint(), rhs.y_bigint());
    let (out_x, out_y) = (output.x_bigint(), output.y_bigint());
    let own = |a: &crate::limbs::P256BigInt<E::F>| -> Vec<E::F> { a.limbs().to_vec() };
    let mix =
        |a: &crate::limbs::P256BigInt<E::F>, b: &crate::limbs::P256BigInt<E::F>| -> Vec<E::F> {
            (0..N_LIMBS)
                .map(|i| op.clone() * a.limbs()[i].clone() + mixed.clone() * b.limbs()[i].clone())
                .collect()
        };
    let slots: [(u32, u32, Vec<E::F>); 6] = [
        (0, PROJECTIVE_RCB_MUL_ROLE_LHS, own(&lhs_x)),
        (0, PROJECTIVE_RCB_MUL_ROLE_RHS, mix(&lhs_x, &rhs_x)),
        (1, PROJECTIVE_RCB_MUL_ROLE_LHS, own(&lhs_y)),
        (1, PROJECTIVE_RCB_MUL_ROLE_RHS, mix(&lhs_y, &rhs_y)),
        (13, PROJECTIVE_RCB_MUL_ROLE_LHS, own(&out_x)),
        (14, PROJECTIVE_RCB_MUL_ROLE_LHS, own(&out_y)),
    ];
    for (mul, role, limbs) in slots {
        let mut values = Vec::with_capacity(3 + N_LIMBS);
        values.push(source_index.clone());
        values.push(E::F::from(M31::from_u32_unchecked(mul)));
        values.push(E::F::from(M31::from_u32_unchecked(role)));
        values.extend(limbs);
        eval.add_to_relation(RelationEntry::base(relation, gate.clone(), &values));
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedTableEcEvalPoint<F> {
    x: [F; N_LIMBS],
    y: [F; N_LIMBS],
    inf: F,
}

impl<F: Clone> PreparedTableEcEvalPoint<F> {
    pub(crate) fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS] {
        core::array::from_fn(|index| match index {
            0..=19 => self.x[index].clone(),
            20..=39 => self.y[index - N_LIMBS].clone(),
            40 => self.inf.clone(),
            _ => unreachable!("prepared-table EC point relation index is in range"),
        })
    }

    /// The point's infinity flag (C5 plumbing: used to compute the `has_muls`
    /// gate — an infinity MixedAdd operand makes the silo emit zero muls).
    pub(crate) fn inf(&self) -> F {
        self.inf.clone()
    }

    /// The affine `x` coordinate limbs as a [`P256BigInt`] (C5-2: the Double-op
    /// formula binds the silo mul operands to the input point's coordinates).
    pub(crate) fn x_bigint(&self) -> crate::limbs::P256BigInt<F> {
        crate::limbs::P256BigInt::from_limbs(self.x.clone())
    }

    /// The affine `y` coordinate limbs as a [`P256BigInt`] (C5-2 Double-op
    /// formula operand binding; see [`Self::x_bigint`]).
    pub(crate) fn y_bigint(&self) -> crate::limbs::P256BigInt<F> {
        crate::limbs::P256BigInt::from_limbs(self.y.clone())
    }
}

impl<F> PreparedTableEcEvalPoint<F> {
    pub(crate) fn read<E: EvalAtRow<F = F>>(eval: &mut E) -> Self {
        Self {
            x: core::array::from_fn(|_| eval.next_trace_mask()),
            y: core::array::from_fn(|_| eval.next_trace_mask()),
            inf: eval.next_trace_mask(),
        }
    }
}

impl<F> PreparedTableEcEvalPoint<F>
where
    F: Clone + core::ops::Add<Output = F> + core::ops::Sub<Output = F> + core::ops::Mul<Output = F>,
{
    pub(crate) fn add_constraints<E: EvalAtRow<F = F>>(&self, eval: &mut E, active: &F, one: &F) {
        eval.add_constraint(self.inf.clone() * (self.inf.clone() - one.clone()));
        for limb in self.x.iter().chain(self.y.iter()) {
            eval.add_constraint(self.inf.clone() * limb.clone());
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }
        eval.add_constraint((one.clone() - active.clone()) * self.inf.clone());
    }
}

fn prepared_table_ec_row_relation_values<F: Clone>(
    header: &[F; 5],
    lhs: &impl PreparedTableEcPointLike<F>,
    rhs: &impl PreparedTableEcPointLike<F>,
    output: &impl PreparedTableEcPointLike<F>,
) -> [F; PREPARED_TABLE_EC_ROW_RELATION_ARITY] {
    let lhs = lhs.relation_values();
    let rhs = rhs.relation_values();
    let output = output.relation_values();
    core::array::from_fn(|index| match index {
        0..=4 => header[index].clone(),
        5..=45 => lhs[index - 5].clone(),
        46..=86 => rhs[index - 46].clone(),
        87..=127 => output[index - 87].clone(),
        _ => unreachable!("prepared-table EC row relation index is in range"),
    })
}

impl<F: Clone> PreparedTableEcPointLike<F> for PreparedTableEcEvalPoint<F> {
    fn relation_values(&self) -> [F; PREPARED_TABLE_EC_POINT_COLUMNS] {
        self.relation_values()
    }
}
