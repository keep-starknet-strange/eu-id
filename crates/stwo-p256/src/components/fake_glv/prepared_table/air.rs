//! AIR constraint evaluation for the prepared-table family: the EC-row and
//! projective-source `FrameworkEval` impls, the in-AIR negation/pinning
//! constraint builders, and the eval-side point reader.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};
use stwo_p256_utils::constants::{LIMB_BITS, N_LIMBS};

use crate::constants::{P256_3GX, P256_3GY, P256_MODULUS};
use crate::limbs::P256M31BigInt;
use crate::prepared_point::{PREPARED_BASE_COUNT, TABLE16_INDEX};
use crate::projective_air::{ConsumedMulLimbs, ProjectiveRcbMulComponentRelations};
use crate::components::gamma_digest::{
    yield_gamma_digest, GammaChallenge, GammaDigestRelation, GAMMA_TAG_PREPARED_RANGE13,
    GAMMA_TAG_PREPARED_SIGNED,
};
use crate::types::U256;

use super::super::ec_source::double_formula::{bind_double_formula, DoubleFormulaColumns};
use super::super::ec_source::mixed_add_formula::{bind_mixed_add_formula, MixedAddFormulaColumns};
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
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(active.clone()),
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

        eval.finalize_logup();
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
            gate = gate * kind_flags[k].clone();
        }
        if entry.cert0_only {
            gate = gate * is_cert0.clone();
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
            PinRelation::CertBase => eval.add_to_relation(RelationEntry::new(
                &pinning.cert_base,
                numerator,
                &cert_base_relation_values::<E::F>(sig_id, cert_id, point),
            )),
            PinRelation::Canonical(role) => eval.add_to_relation(RelationEntry::new(
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
        eval.add_to_relation(RelationEntry::new(
            final_check_hint,
            -E::EF::from(gate),
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


/// `mult · gate` as an extension-field numerator (`mult` may be negative).
fn signed_numerator<E: EvalAtRow>(gate: E::F, mult: i32) -> E::EF {
    let magnitude = E::F::from(M31::from_u32_unchecked(mult.unsigned_abs()));
    let scaled = E::EF::from(gate * magnitude);
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
    /// C5 plumbing: relations bundle carrying `mul_result`, consumed for the
    /// prepared-table EC ops (the `[0, source_offset)` slice of the silo).
    pub mul_relations: ProjectiveRcbMulComponentRelations,
    /// γ-digest reshape (docs/gamma-digest-design.md): the formula blocks'
    /// range13 + signed-carry values are bound into two per-row digests
    /// yielded on this relation; the tall expander components re-expand them
    /// and emit the actual range uses against the sub-graph's providers.
    pub gamma_digest: GammaDigestRelation,
    pub gamma_challenge: GammaChallenge,
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
        // C5 plumbing: consumed silo mul limbs (read after the points, matching
        // the base-trace layout).
        let mut consumed_muls = ConsumedMulLimbs::<E>::read(&mut eval);
        // C5-2: the Double-formula working values + reduction witnesses, then
        // the MixedAdd block, read LAST (matching the base-trace layout
        // appended after the consumed-mul block).
        let double_columns = DoubleFormulaColumns::<E>::read(&mut eval);
        let mixed_columns = MixedAddFormulaColumns::<E>::read(&mut eval);
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

        // C5 plumbing: `has_muls` gate (1 for Double / finite-operand MixedAdd,
        // 0 for an infinity-operand MixedAdd no-op). expected = 1 - (1 - op)·
        // operand_inf, operand = `rhs`. Prepared-table ops all use finite base
        // operands so this is 1 in practice, but the gate keeps the consumer
        // robust and symmetric with the fake-GLV source.
        let expected_has_muls = one.clone() - (one.clone() - op.clone()) * rhs.inf();
        consumed_muls.constrain_has_muls(&mut eval, &active, &expected_has_muls);
        // Operand dedup: install the dropped slots' consume expressions.
        consumed_muls.fill_dropped(&crate::projective_air::ConsumedMulWiring {
            op: op.clone(),
            x1: lhs.x_bigint(),
            y1: lhs.y_bigint(),
            x2: rhs.x_bigint(),
            y2: rhs.y_bigint(),
            output_x: output.x_bigint(),
            output_y: output.y_bigint(),
            z3_double: double_columns.z3.clone(),
            z3_mixed: mixed_columns.z3.clone(),
        });

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
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(active.clone()),
            &relation_values,
        ));
        // CONSUME (use, `+has_muls`) the silo's proven mul limbs for this
        // prepared-table op, keyed identically to the silo's provided yields.
        consumed_muls.consume(&mut eval, &self.mul_relations.mul_result, &source_index);

        // C5-2: constrain the Double-op coordinate formula. `double_active`
        // (= active·op) is 1 only on active Double rows (op==1 == DOUBLE);
        // MixedAdd (op==0) and padding (active==0) are unaffected.
        let double_active = active.clone() * op.clone();
        let muls_view = consumed_muls.view();
        // The binders COLLECT their range13 values; together with the signed
        // reduction carries they feed the two γ-digest yields below (fixed
        // order: Double block then MixedAdd block).
        let mut range13_values: Vec<E::F> = Vec::new();
        let mut signed_carry_values: Vec<E::F> = Vec::new();
        bind_double_formula(
            &mut eval,
            &double_active,
            &lhs.x_bigint(),
            &lhs.y_bigint(),
            &output.x_bigint(),
            &output.y_bigint(),
            &output.inf(),
            &muls_view,
            &double_columns,
            &mut range13_values,
        );
        // Collect the Double reduction carries for the signed-carry digest,
        // and force the Double-formula working values + reduction witnesses to
        // zero on non-Double / padding rows.
        for reduction in &double_columns.reductions {
            for carry in &reduction.carries {
                signed_carry_values.push(carry.clone());
            }
        }
        let not_double = one.clone() - double_active.clone();
        for value in double_columns
            .x3
            .limbs()
            .iter()
            .chain(double_columns.y3.limbs())
            .chain(double_columns.z3.limbs())
        {
            eval.add_constraint(not_double.clone() * value.clone());
        }
        for reduction in &double_columns.reductions {
            eval.add_constraint(not_double.clone() * reduction.q.clone());
            for carry in &reduction.carries {
                eval.add_constraint(not_double.clone() * carry.clone());
            }
        }

        // C5-2: constrain the MixedAdd-op coordinate formula. `mixed_active`
        // (= active·(1−op)) is 1 only on active MixedAdd rows; the formula is
        // additionally gated by `has_muls` inside the binder (an
        // infinity-operand MixedAdd is a 0-mul no-op constrained `output =
        // lhs`).
        let mixed_active = active.clone() * (one.clone() - op.clone());
        bind_mixed_add_formula(
            &mut eval,
            &mixed_active,
            &rhs.inf(),
            &lhs.x_bigint(),
            &lhs.y_bigint(),
            &rhs.x_bigint(),
            &rhs.y_bigint(),
            &lhs.inf(),
            &output.x_bigint(),
            &output.y_bigint(),
            &output.inf(),
            &muls_view,
            &mixed_columns,
            &mut range13_values,
        );
        // Collect the MixedAdd reduction carries for the signed-carry digest,
        // and force the MixedAdd working values + reduction witnesses to zero
        // on non-MixedAdd / padding rows.
        for reduction in &mixed_columns.reductions {
            for carry in &reduction.carries {
                signed_carry_values.push(carry.clone());
            }
        }
        let not_mixed = one.clone() - mixed_active.clone();
        for value in mixed_columns
            .x3
            .limbs()
            .iter()
            .chain(mixed_columns.y3.limbs())
            .chain(mixed_columns.z3.limbs())
        {
            eval.add_constraint(not_mixed.clone() * value.clone());
        }
        for reduction in &mixed_columns.reductions {
            eval.add_constraint(not_mixed.clone() * reduction.q.clone());
            for carry in &reduction.carries {
                eval.add_constraint(not_mixed.clone() * carry.clone());
            }
        }
        // γ-digest yields (one per kind), keyed by the shared preprocessed
        // row-index column; presence = `active` (the tall expanders'
        // preprocessed schedule is the anchor).
        let row_index = eval.get_preprocessed_column(prepared_table_ec_row_index_column_id());
        yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            GAMMA_TAG_PREPARED_RANGE13,
            row_index.clone(),
            active.clone(),
            M31::from_u32_unchecked(0),
            &range13_values,
        );
        yield_gamma_digest(
            &mut eval,
            &self.gamma_digest,
            &self.gamma_challenge,
            GAMMA_TAG_PREPARED_SIGNED,
            row_index,
            active.clone(),
            crate::range_checks::encode_signed_carry(0),
            &signed_carry_values,
        );

        eval.finalize_logup_batched(
            &crate::components::fake_glv::prepared_table::interaction::prepared_consumer_logup_batching(),
        );
        eval
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

