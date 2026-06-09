//! Interaction-trace (LogUp) generation for the FinalAdd component: the
//! per-family fraction builders and the `FinalAddInteractionClaim` accumulator.
//!
//! Split out of `mod.rs` (pure relocation, no behavioral change).

use stwo::core::{
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    utils::{bit_reverse_index, coset_index_to_circle_domain_index},
};
use stwo::prover::backend::simd::{
    m31::{LOG_N_LANES, N_LANES},
    qm31::PackedQM31,
};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

use crate::limbs::P256M31BigInt;
use crate::projective_air::{
    projective_rcb_mul_padding_fraction_pairs, projective_rcb_mul_row_fraction_count,
    projective_rcb_mul_row_fraction_pairs, ProjectiveRcbMulRow,
};
use crate::range_checks::{
    encode_signed_carry, RangeCheckClaim, RangeCheckInteractionClaim, RANGE13_BITS, RANGE16_BITS,
};
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;

use super::*;

#[derive(Clone, Debug)]
pub struct FinalAddInteractionClaim {
    pub mul: SecureField,
    pub raw_product_chunk: SecureField,
    pub folded_contribution: SecureField,
    pub folded_digit: SecureField,
    pub check: SecureField,
    pub range13: RangeCheckInteractionClaim,
    pub raw_product_carry16: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
    /// FinalCheckHint consumer sum (use, `+active`) for `R_1`, `R_2`.
    pub hint_consumer_claimed_sum: SecureField,
    /// FinalAddOutput provider sum (yield, `-active`).
    pub output_provider_claimed_sum: SecureField,
}

impl FinalAddInteractionClaim {
    pub fn zero() -> Self {
        let zero = secure_zero();
        Self {
            mul: zero,
            raw_product_chunk: zero,
            folded_contribution: zero,
            folded_digit: zero,
            check: zero,
            range13: RangeCheckInteractionClaim { claimed_sum: zero },
            raw_product_carry16: RangeCheckInteractionClaim { claimed_sum: zero },
            signed_carry: RangeCheckInteractionClaim { claimed_sum: zero },
            hint_consumer_claimed_sum: zero,
            output_provider_claimed_sum: zero,
        }
    }

    /// Internal total: every relation that nets to zero WITHIN the sub-graph.
    /// `mul_limb`/raw/fold families + `FinalAddMulResult` + own range13/signed
    /// carry providers all balance internally; the boundary-crossing relations
    /// (`FinalCheckHint`, `FinalAddOutput`) are excluded.
    pub fn internal_total(&self) -> SecureField {
        self.mul
            + self.raw_product_chunk
            + self.folded_contribution
            + self.folded_digit
            + self.check
            + self.range13.claimed_sum
            + self.raw_product_carry16.claimed_sum
            + self.signed_carry.claimed_sum
            - self.hint_consumer_claimed_sum
            - self.output_provider_claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.mul,
            self.raw_product_chunk,
            self.folded_contribution,
            self.folded_digit,
            self.check,
            self.range13.claimed_sum,
            self.raw_product_carry16.claimed_sum,
            self.signed_carry.claimed_sum,
            self.hint_consumer_claimed_sum,
            self.output_provider_claimed_sum,
        ]);
    }
}

pub fn gen_final_add_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_sizes: FinalAddLogSizes,
) -> Result<(Vec<M31ColumnEval>, FinalAddInteractionClaim), FinalAddError> {
    let mut columns = Vec::new();

    // Mul family: standard mul fractions ++ FinalAddMulResult provider, one
    // LogupTraceGenerator / one finalize_last.
    let (mul_interaction, mul_sum) =
        gen_mul_family_interaction_trace(claim, relations, log_sizes.mul);
    columns.extend(mul_interaction);

    // Three non-mul families, reused unchanged.
    let (projective_traces, projective_claim) =
        claim.mul_trace.gen_interaction_trace(&relations.mul);
    columns.extend(projective_traces.raw_product_chunk);
    columns.extend(projective_traces.folded_contribution);
    columns.extend(projective_traces.folded_digit);

    // Check family (consumers + output provider).
    let (check_interaction, check_sum, hint_sum, output_sum) =
        gen_check_interaction_trace(claim, relations, log_sizes.check);
    columns.extend(check_interaction);

    // Shared range providers.
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let range13_values = range13.gen_preprocessed_column();
    let range13_multiplicity = range13.gen_multiplicity_trace(final_add_range13_uses(claim));
    let (range13_trace, range13_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
        &range13_multiplicity,
        &range13_values,
        &relations.mul.range13,
    );
    columns.extend(range13_trace);

    let raw_product_carry16 = RangeCheckClaim::new(RANGE16_BITS);
    let raw_product_carry16_values = raw_product_carry16.gen_preprocessed_column();
    let raw_product_carry16_multiplicity =
        raw_product_carry16.gen_multiplicity_trace(final_add_raw_product_carry16_uses(claim));
    let (raw_product_carry16_trace, raw_product_carry16_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(
            &raw_product_carry16_multiplicity,
            &raw_product_carry16_values,
            &relations.mul.raw_product_carry16,
        );
    columns.extend(raw_product_carry16_trace);

    let signed_carry = final_add_signed_carry_claim();
    let signed_carry_values = signed_carry.gen_value_column();
    let signed_carry_multiplicity =
        signed_carry.gen_multiplicity_trace(final_add_signed_carry_uses(claim)?);
    let (signed_carry_trace, signed_carry_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(
            &signed_carry_multiplicity,
            &signed_carry_values,
            &relations.mul.signed_carry,
        );
    columns.extend(signed_carry_trace);

    Ok((
        columns,
        FinalAddInteractionClaim {
            mul: mul_sum,
            raw_product_chunk: projective_claim.raw_product_chunk,
            folded_contribution: projective_claim.folded_contribution,
            folded_digit: projective_claim.folded_digit,
            check: check_sum,
            range13: range13_claim,
            raw_product_carry16: raw_product_carry16_claim,
            signed_carry: signed_carry_claim,
            hint_consumer_claimed_sum: hint_sum,
            output_provider_claimed_sum: output_sum,
        },
    ))
}

fn gen_mul_family_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_size: u32,
) -> (Vec<M31ColumnEval>, SecureField) {
    let padded_rows = 1usize << log_size;
    let standard_count = projective_rcb_mul_row_fraction_count();
    let provider_count = FINAL_ADD_MUL_PROVIDER_FRACTIONS;
    let total = standard_count + provider_count;

    let mut storage: Vec<Vec<(SecureField, SecureField)>> = (0..padded_rows)
        .map(|_| {
            let mut v = projective_rcb_mul_padding_fraction_pairs();
            v.extend((0..provider_count).map(|_| (secure_zero(), secure_one())));
            v
        })
        .collect();

    for (mul_index, mul) in claim.mul_trace.rows[0].muls.iter().enumerate() {
        let coset_index = mul_index;
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        let mut pairs = projective_rcb_mul_row_fraction_pairs(0, mul_index, mul, &relations.mul);
        pairs.extend(provider_fraction_pairs(mul_index, mul, &relations.result));
        storage[row] = pairs;
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    for column in 0..total {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (numerator, denominator) = storage[row][column];
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    logup.finalize_last()
}

fn provider_fraction_pairs(
    mul_index: usize,
    mul: &ProjectiveRcbMulRow,
    relation: &FinalAddMulResultRelation,
) -> Vec<(SecureField, SecureField)> {
    let mut pairs = Vec::with_capacity(FINAL_ADD_MUL_PROVIDER_FRACTIONS);
    for (role, limbs) in [
        (ROLE_LHS, mul.trace.lhs.limbs()),
        (ROLE_RHS, mul.trace.rhs.limbs()),
        (ROLE_RESULT, mul.trace.result.limbs()),
    ] {
        for (limb_index, limb) in limbs.iter().enumerate() {
            pairs.push((
                secure_from_i64(-1),
                relation.combine(&[
                    M31::from_u32_unchecked(mul_index as u32),
                    M31::from_u32_unchecked(role),
                    M31::from_u32_unchecked(limb_index as u32),
                    *limb,
                ]),
            ));
        }
    }
    pairs
}

#[allow(clippy::type_complexity)]
fn gen_check_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_size: u32,
) -> (Vec<M31ColumnEval>, SecureField, SecureField, SecureField) {
    let padded_rows = 1usize << log_size;
    let (fractions, hint_sum, output_sum) = check_fraction_pairs(claim, relations);
    let fraction_count = fractions.len();

    let active_row = bit_reverse_index(coset_index_to_circle_domain_index(0, log_size), log_size);
    let mut storage: Vec<Vec<(SecureField, SecureField)>> = (0..padded_rows)
        .map(|_| vec![(secure_zero(), secure_one()); fraction_count])
        .collect();
    storage[active_row] = fractions;

    let mut logup = LogupTraceGenerator::new(log_size);
    for column in 0..fraction_count {
        let mut col = logup.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerators = [secure_zero(); N_LANES];
            let mut denominators = [secure_one(); N_LANES];
            for lane in 0..N_LANES {
                let row = vec_row * N_LANES + lane;
                let (numerator, denominator) = storage[row][column];
                numerators[lane] = numerator;
                denominators[lane] = denominator;
            }
            col.write_frac(
                vec_row,
                PackedQM31::from_array(numerators),
                PackedQM31::from_array(denominators),
            );
        }
        col.finalize_col();
    }
    let (trace, check_sum) = logup.finalize_last();
    (trace, check_sum, hint_sum, output_sum)
}

/// Check consumer/provider fractions, in the EXACT order `FinalAddCheckEval`
/// emits them:
/// 1. hint consume R_1 (sig,0), R_2 (sig,1)  (use, +active)
/// 2. mul-result consume tuples (mul 0..1, roles lhs/rhs/result)  (use, +active)
/// 3. output provide (sig, x3)  (yield, -active)
/// 4. range13 uses for witnessed limbs
/// 5. signed-carry uses for the 3·N_LIMBS carries
fn check_fraction_pairs(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
) -> (Vec<(SecureField, SecureField)>, SecureField, SecureField) {
    let mut pairs = Vec::new();
    let mut hint_sum = secure_zero();
    let mut output_sum = secure_zero();

    // 1. hint consumes, numerator `(1 - inf)` (active row only): an inactive
    //    cert (inf == 1) contributes a zero-numerator fraction so it has no
    //    yield to match.
    for (cert_id, point) in [(0u32, &claim.r1), (1u32, &claim.r2)] {
        let numerator = if point.inf.0 == 1 {
            secure_zero()
        } else {
            secure_from_i64(1)
        };
        let mut values = Vec::with_capacity(FINAL_CHECK_HINT_RELATION_ARITY);
        values.push(claim.sig_id);
        values.push(M31::from_u32_unchecked(cert_id));
        values.extend(point.x.limbs().iter().copied());
        values.extend(point.y.limbs().iter().copied());
        values.push(point.inf);
        let denom = relations.hint.combine(&values);
        pairs.push((numerator, denom));
        hint_sum += numerator / denom;
    }

    // 2. mul-result consumes.
    let consume = |pairs: &mut Vec<(SecureField, SecureField)>,
                   mul_index: u32,
                   role: u32,
                   value: &P256M31BigInt| {
        for (limb_index, limb) in value.limbs().iter().enumerate() {
            pairs.push((
                secure_from_i64(1),
                relations.result.combine(&[
                    M31::from_u32_unchecked(mul_index),
                    M31::from_u32_unchecked(role),
                    M31::from_u32_unchecked(limb_index as u32),
                    *limb,
                ]),
            ));
        }
    };
    consume(&mut pairs, MUL_LAMBDA_DX, ROLE_LHS, &claim.lambda);
    consume(&mut pairs, MUL_LAMBDA_DX, ROLE_RHS, &claim.dx);
    consume(&mut pairs, MUL_LAMBDA_DX, ROLE_RESULT, &claim.dy);
    consume(&mut pairs, MUL_LAMBDA_SQUARED, ROLE_LHS, &claim.lambda);
    consume(&mut pairs, MUL_LAMBDA_SQUARED, ROLE_RHS, &claim.lambda);
    consume(&mut pairs, MUL_LAMBDA_SQUARED, ROLE_RESULT, &claim.lamsq);
    consume(&mut pairs, MUL_DX_INV, ROLE_LHS, &claim.dx);
    consume(&mut pairs, MUL_DX_INV, ROLE_RHS, &claim.dx_inv);
    // dx · dx_inv result = both_finite (1 if both finite, else 0).
    consume(
        &mut pairs,
        MUL_DX_INV,
        ROLE_RESULT,
        &dx_inv_result_value(claim),
    );
    // Task 6 doubling: MUL_X1_SQUARED proves `r1.x · r1.x ≡ x1_sq (mod p)`,
    // consumed by the check eval the same way as the other muls so its
    // provider/consumer pair balances in the FinalAddInternal totals.
    consume(&mut pairs, MUL_X1_SQUARED, ROLE_LHS, &claim.r1.x);
    consume(&mut pairs, MUL_X1_SQUARED, ROLE_RHS, &claim.r1.x);
    consume(&mut pairs, MUL_X1_SQUARED, ROLE_RESULT, &claim.x1_sq);

    // 3. output provide.
    {
        let mut values = Vec::with_capacity(FINAL_ADD_OUTPUT_RELATION_ARITY);
        values.push(claim.sig_id);
        values.extend(claim.x3.limbs().iter().copied());
        let denom = relations.output.combine(&values);
        pairs.push((secure_from_i64(-1), denom));
        output_sum += secure_from_i64(-1) / denom;
    }

    // 4. range13 uses.
    for value in [
        &claim.r1.x,
        &claim.r1.y,
        &claim.r2.x,
        &claim.r2.y,
        &claim.dx,
        &claim.dy,
        &claim.lambda,
        &claim.lamsq,
        &claim.x3,
        &claim.dx_inv,
        &dx_inv_result_value(claim),
        // Task 6: every limb of `x1_sq` is also range-checked by the AIR
        // (see the `.chain(columns.x1_sq.limbs())` in the eval's range13
        // chain), so the trace gen must emit matching multiplicities.
        &claim.x1_sq,
    ] {
        for limb in value.limbs() {
            pairs.push((secure_from_i64(1), relations.mul.range13.combine(&[*limb])));
        }
    }

    // 5. signed-carry uses.
    for carry in claim
        .dx_carries
        .iter()
        .chain(claim.dy_carries.iter())
        .chain(claim.x3_carries.iter())
    {
        pairs.push((
            secure_from_i64(1),
            relations
                .mul
                .signed_carry
                .combine(&[encode_signed_carry(*carry)]),
        ));
    }

    (pairs, hint_sum, output_sum)
}
