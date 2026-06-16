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
use crate::range_checks::{RangeCheckClaim, RangeCheckInteractionClaim, RANGE13_BITS};
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;
use stwo_p256_utils::constants::N_LIMBS;

use super::*;

#[derive(Clone, Debug)]
pub struct FinalAddInteractionClaim {
    pub claimed_sum: SecureField,
    pub range13: RangeCheckInteractionClaim,
    pub signed_carry: RangeCheckInteractionClaim,
    /// γ-digest tall expanders (range13 kind, signed kind) + the check's
    /// yield fractions folded into the check component's claimed sum.
    pub gamma_range13: crate::components::gamma_digest::GammaTallInteractionClaim,
    pub gamma_signed: crate::components::gamma_digest::GammaTallInteractionClaim,
}

impl FinalAddInteractionClaim {
    pub fn zero() -> Self {
        let zero = secure_zero();
        Self {
            claimed_sum: zero,
            range13: RangeCheckInteractionClaim { claimed_sum: zero },
            signed_carry: RangeCheckInteractionClaim { claimed_sum: zero },
            gamma_range13: crate::components::gamma_digest::GammaTallInteractionClaim::zero(),
            gamma_signed: crate::components::gamma_digest::GammaTallInteractionClaim::zero(),
        }
    }

    pub fn total(&self) -> SecureField {
        self.claimed_sum
            + self.range13.claimed_sum
            + self.signed_carry.claimed_sum
            + self.gamma_range13.claimed_sum
            + self.gamma_signed.claimed_sum
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.claimed_sum,
            self.range13.claimed_sum,
            self.signed_carry.claimed_sum,
        ]);
        self.gamma_range13.mix_into(channel);
        self.gamma_signed.mix_into(channel);
    }
}

pub fn gen_final_add_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_sizes: FinalAddLogSizes,
) -> Result<(Vec<M31ColumnEval>, FinalAddInteractionClaim), FinalAddError> {
    let mut columns = Vec::new();

    // Check family (consumers + output provider). The four muls are proven by
    // hinted-mul rows; the check consumes them via wide tuples.
    let (
        check_interaction,
        check_sum,
        _hint_sum,
        _sign_sum,
        _output_sum,
        _mul_result_sum,
        _gamma_yield_sum,
    ) = gen_check_interaction_trace(claim, relations, log_sizes.check);
    columns.extend(check_interaction);

    // γ-digest tall expanders (range13 kind, signed kind).
    let [gamma_range13_instance, gamma_signed_instance] = super::final_add_gamma_instances(claim);
    let (gamma_range13_trace, gamma_range13_claim) =
        crate::components::gamma_digest::gen_gamma_tall_interaction_trace(
            &gamma_range13_instance,
            &relations.gamma_challenge,
            &relations.gamma_digest,
            &relations.range13,
        );
    columns.extend(gamma_range13_trace);
    let (gamma_signed_trace, gamma_signed_claim) =
        crate::components::gamma_digest::gen_gamma_tall_interaction_trace(
            &gamma_signed_instance,
            &relations.gamma_challenge,
            &relations.gamma_digest,
            &relations.signed_carry,
        );
    columns.extend(gamma_signed_trace);

    // Shared range providers.
    let range13 = RangeCheckClaim::new(RANGE13_BITS);
    let range13_values = range13.gen_preprocessed_column();
    let range13_multiplicity = range13.gen_multiplicity_trace(final_add_range13_uses(claim));
    let (range13_trace, range13_claim) = RangeCheckInteractionClaim::gen_interaction_trace(
        &range13_multiplicity,
        &range13_values,
        &relations.range13,
    );
    columns.extend(range13_trace);

    let signed_carry = final_add_signed_carry_claim();
    let signed_carry_values = signed_carry.gen_value_column();
    let signed_carry_multiplicity =
        signed_carry.gen_multiplicity_trace(final_add_signed_carry_uses(claim)?);
    let (signed_carry_trace, signed_carry_claim) =
        RangeCheckInteractionClaim::gen_interaction_trace(
            &signed_carry_multiplicity,
            &signed_carry_values,
            &relations.signed_carry,
        );
    columns.extend(signed_carry_trace);

    Ok((
        columns,
        FinalAddInteractionClaim {
            claimed_sum: check_sum,
            range13: range13_claim,
            signed_carry: signed_carry_claim,
            gamma_range13: gamma_range13_claim,
            gamma_signed: gamma_signed_claim,
        },
    ))
}

fn gen_check_interaction_trace(
    claim: &FinalAddClaim,
    relations: &FinalAddRelations,
    log_size: u32,
) -> (
    Vec<M31ColumnEval>,
    SecureField,
    SecureField,
    SecureField,
    SecureField,
    SecureField,
    SecureField,
) {
    let padded_rows = 1usize << log_size;
    let (fractions, hint_sum, sign_sum, output_sum, mul_result_sum, gamma_yield_sum) =
        check_fraction_pairs(claim, relations);
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
    (
        trace,
        check_sum,
        hint_sum,
        sign_sum,
        output_sum,
        mul_result_sum,
        gamma_yield_sum,
    )
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
) -> (
    Vec<(SecureField, SecureField)>,
    SecureField,
    SecureField,
    SecureField,
    SecureField,
    SecureField,
) {
    let mut pairs = Vec::new();
    let mut hint_sum = secure_zero();
    let mut sign_sum = secure_zero();
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

    // 1b. sign consumes (same gate/numerator as the hint consume), binding the
    //     witnessed per-cert bit to the fake_glv_scalar provider. MUST mirror
    //     the AIR-eval emission order (right after the hint consumes).
    for (cert_id, point, bit) in [
        (0u32, &claim.r1, claim.sign_b1),
        (1u32, &claim.r2, claim.sign_b2),
    ] {
        let numerator = if point.inf.0 == 1 {
            secure_zero()
        } else {
            secure_from_i64(1)
        };
        let values = [claim.sig_id, M31::from_u32_unchecked(cert_id), bit];
        let denom = relations.sign.combine(&values);
        pairs.push((numerator, denom));
        sign_sum += numerator / denom;
    }

    // 2. mul-result consumes (wide tuples against the hinted provider).
    let mut mul_result_sum = secure_zero();
    let mul_source = M31::from_u32_unchecked(claim.hinted_source_offset) + claim.sig_id;
    let mut consume = |pairs: &mut Vec<(SecureField, SecureField)>,
                       mul_index: u32,
                       role: u32,
                       value: &P256M31BigInt| {
        let mut values = Vec::with_capacity(3 + N_LIMBS);
        values.push(mul_source);
        values.push(M31::from_u32_unchecked(mul_index));
        values.push(M31::from_u32_unchecked(role));
        values.extend(value.limbs().iter().copied());
        let denom = relations.mul_result.combine(&values);
        pairs.push((secure_from_i64(1), denom));
        mul_result_sum += secure_from_i64(1) / denom;
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

    // 4. γ-digest yields (−1 on the single active row), range13 kind then
    //    signed kind, mirroring the eval's collection order.
    let mut gamma_yield_sum = secure_zero();
    for instance in super::final_add_gamma_instances(claim) {
        let digest = crate::components::gamma_digest::gamma_digest_of_values(
            &relations.gamma_challenge,
            instance.pad_value,
            &instance.padded_group_values(0),
        );
        let tuple = crate::components::gamma_digest::gamma_digest_tuple(
            instance.layout.tag,
            M31::from_u32_unchecked(0),
            digest,
        );
        let denom: SecureField = relations.gamma_digest.combine(&tuple);
        pairs.push((secure_from_i64(-1), denom));
        gamma_yield_sum += secure_from_i64(-1) / denom;
    }

    (
        pairs,
        hint_sum,
        sign_sum,
        output_sum,
        mul_result_sum,
        gamma_yield_sum,
    )
}
