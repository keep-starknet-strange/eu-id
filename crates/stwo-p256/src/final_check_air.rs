//! FinalEcdsaCheck AIR — increment 6.2 (in-AIR `x mod n` reduction).
//!
//! Goal of this slot in [`crate::proof::P256_PROOF_COMPONENT_SLOTS`] is to make
//! verifier acceptance of an ECDSA signature depend on
//! `x(u1·G + u2·Q) mod n == r`.
//!
//! Increment 6.1 (`r_check` as a free witness) only bound the AIR's
//! `r_check` row to the public signature `r` through
//! [`EcdsaResultRelation`]. That left an unconstrained witness gap because
//! the prover could pick `r_check` freely.
//!
//! Increment 6.2 closes part of that gap by adding a same-row digest
//! reduction constraint:
//!
//! ```text
//! r_check + r_x_ge_n · n = r_x
//! r_x   < 2^256          (top limb in 9-bit range)
//! r_check < n            (canonical-less-than helper)
//! r_x_ge_n in {0, 1}
//! ```
//!
//! `r_x` is the witnessed x-coordinate of the final ECDSA point
//! `R = u1·G + u2·Q`. The reduction is sound because `p < 2n` for P-256,
//! so a single subtraction takes any `r_x ∈ [0, 2^256)` into `[0, n)`. The
//! same `add_digest_reduction` helper used by `scalar_setup_air` for the
//! digest-mod-n step is reused here verbatim.
//!
//! **Remaining gap (future increments):** `r_x` is still a free witness in
//! this AIR — nothing yet enforces `r_x = (h1 + h2).x` where
//! `h1 = u1·G` and `h2 = u2·Q` are read from the fake-GLV chain final
//! accumulators. A follow-up increment will bind `r_x` (and a witnessed
//! `r_y`, `r_inf`) to the chain outputs via
//! [`crate::scalar::fake_glv_chain_continuity::FakeGlvChainAccumulatorRelation`]
//! and a single rcb mixed-add row. Until then, the reduction step alone is
//! verified.

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{
        m31::{PackedM31, LOG_N_LANES},
        qm31::PackedQM31,
        SimdBackend,
    },
    ComponentProver,
};
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::N_LIMBS;
use stwo_p256_utils::scalar_arithmetic::{
    CanonicalLtTrace, DigestReductionTrace, P256_ORDER as P256_ORDER_WORDS,
};

use crate::final_check::FinalEcdsaCheckClaim;
use crate::limbs::{P256BigInt, P256M31BigInt};
use crate::public_inputs::{PublicEcdsaInputClaim, PublicEcdsaInstance};
use crate::range_checks::{
    decode_signed_carry, encode_signed_carry, RangeCheckRelation,
};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};
use crate::scalar::setup_air::{
    add_digest_reduction, DigestReductionColumns, DigestReductionRelations,
};

/// `(sig_id, r[N_LIMBS])`.
pub const ECDSA_RESULT_RELATION_ARITY: usize = 1 + N_LIMBS;

relation!(EcdsaResultRelation, ECDSA_RESULT_RELATION_ARITY);

/// Trace columns per row of the FinalEcdsaCheck AIR:
///
/// - 1: `active` selector
/// - 1: `sig_id`
/// - N_LIMBS: `r_check` (bound to public `r` via [`EcdsaResultRelation`])
/// - N_LIMBS: `r_x` (witnessed x-coordinate of `R = u1·G + u2·Q`)
/// - 1: `r_x_ge_n` (whether `r_x ≥ n`)
/// - N_LIMBS: signed carries for the reduction recurrence
/// - N_LIMBS: `r_check < n` slack
/// - N_LIMBS: `r_check < n` boolean carries
const FINAL_CHECK_TRACE_COLUMNS: usize = 2 + 5 * N_LIMBS + 1;

pub type FinalCheckAirComponent = FrameworkComponent<FinalCheckAirEval>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalCheckAirProofClaim {
    pub log_size: u32,
}

impl FinalCheckAirProofClaim {
    pub fn from_claim(claim: &PublicEcdsaInputClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.instances.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalCheckAirInteractionClaim {
    pub claimed_sum: SecureField,
    pub result_consumer_claimed_sum: SecureField,
    pub range13_consumer_claimed_sum: SecureField,
    pub range9_consumer_claimed_sum: SecureField,
    pub signed_carry_consumer_claimed_sum: SecureField,
    /// FinalAddOutput consumer sum (use, `+active`) binding `r_x`.
    pub final_add_output_consumer_claimed_sum: SecureField,
}

impl FinalCheckAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
            result_consumer_claimed_sum: secure_zero(),
            range13_consumer_claimed_sum: secure_zero(),
            range9_consumer_claimed_sum: secure_zero(),
            signed_carry_consumer_claimed_sum: secure_zero(),
            final_add_output_consumer_claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub struct FinalCheckAirComponents {
    pub check: FinalCheckAirComponent,
}

#[derive(Clone)]
pub struct FinalCheckAirRelations<'a> {
    pub result: &'a EcdsaResultRelation,
    pub range13: &'a RangeCheckRelation,
    pub range9: &'a RangeCheckRelation,
    pub signed_carry: &'a RangeCheckRelation,
    /// Binds `r_x` to the proven `x(u1·G + u2·Q)` forwarded by `final_add_air`.
    pub final_add_output: &'a crate::final_add_air::FinalAddOutputRelation,
}

impl FinalCheckAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FinalCheckAirProofClaim,
        interaction_claim: &FinalCheckAirInteractionClaim,
        relations: FinalCheckAirRelations<'_>,
    ) -> Self {
        Self {
            check: FinalCheckAirComponent::new(
                allocator,
                FinalCheckAirEval {
                    log_size: claim.log_size,
                    result_relation: relations.result.clone(),
                    range13: relations.range13.clone(),
                    range9: relations.range9.clone(),
                    signed_carry: relations.signed_carry.clone(),
                    final_add_output: relations.final_add_output.clone(),
                },
                interaction_claim.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![&self.check as &dyn Component]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.check as &dyn ComponentProver<SimdBackend>]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        self.check.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.check.max_constraint_log_degree_bound()
    }
}

#[derive(Clone)]
pub struct FinalCheckAirEval {
    pub log_size: u32,
    pub result_relation: EcdsaResultRelation,
    pub range13: RangeCheckRelation,
    pub range9: RangeCheckRelation,
    pub signed_carry: RangeCheckRelation,
    pub final_add_output: crate::final_add_air::FinalAddOutputRelation,
}

impl FrameworkEval for FinalCheckAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let r_check = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let r_x = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let r_x_ge_n = eval.next_trace_mask();
        let reduction_carries: [E::F; N_LIMBS] = core::array::from_fn(|_| eval.next_trace_mask());
        let r_check_lt_slack =
            P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let r_check_lt_carries: [E::F; N_LIMBS] =
            core::array::from_fn(|_| eval.next_trace_mask());
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        // Padding rows expose neither `sig_id` nor `r_check` outputs.
        eval.add_constraint((one.clone() - active.clone()) * sig_id.clone());
        for limb in r_check.limbs() {
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }
        // `r_x_ge_n` is gated to zero on padding rows so a stray witness can't
        // sneak a non-canonical reduction into a padded slot.
        eval.add_constraint((one.clone() - active.clone()) * r_x_ge_n.clone());

        // Same-row digest reduction: `r_check = r_x mod n` with one
        // subtraction. `add_digest_reduction` enforces:
        //   - r_x_ge_n in {0, 1}
        //   - r_x[i] - r_check[i] - r_x_ge_n * n[i] + prev_carry - B * carries[i] = 0
        //   - final carry = 0
        //   - r_x < 2^256 (top limb Range9)
        //   - r_check < n (canonical-LT helper)
        // All gated by `active`. Padding rows must still carry valid
        // canonical-LT witnesses (handled by trace gen).
        let r_x_limbs: [E::F; N_LIMBS] = core::array::from_fn(|i| r_x.limbs()[i].clone());
        let reduction_columns = DigestReductionColumns {
            z: r_x,
            z_red: r_check.clone(),
            z_ge_n: r_x_ge_n,
            carries: reduction_carries,
            z_red_lt_n_slack: r_check_lt_slack.clone(),
            z_red_lt_n_carries: r_check_lt_carries,
        };
        let reduction_relations = DigestReductionRelations {
            range13: &self.range13,
            range9: &self.range9,
            signed_carry: &self.signed_carry,
        };
        add_digest_reduction(
            &mut eval,
            reduction_relations,
            active.clone(),
            &reduction_columns,
        );
        let _ = r_check_lt_slack; // kept above for ownership; helper consumed it
        let r_check = reduction_columns.z_red;

        let mut values = Vec::with_capacity(ECDSA_RESULT_RELATION_ARITY);
        values.push(sig_id.clone());
        values.extend(r_check.limbs().iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.result_relation,
            E::EF::from(active.clone()),
            &values,
        ));

        // Bind `r_x` to the proven `x(u1·G + u2·Q)`: consume (use, `+active`)
        // the `FinalAddOutputRelation` tuple `(sig_id, r_x)` provided by
        // `final_add_air`. LogUp balance forces `r_x == x(R_1 + R_2)`.
        let mut output_values = Vec::with_capacity(1 + N_LIMBS);
        output_values.push(sig_id);
        output_values.extend(r_x_limbs.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.final_add_output,
            E::EF::from(active),
            &output_values,
        ));
        eval.finalize_logup();
        eval
    }
}

/// Public-input side: provide `(sig_id, r)` per instance as an initial LogUp
/// claim (no trace), mirroring `public_ecdsa_provider_claimed_sum`.
pub fn ecdsa_result_provider_claimed_sum(
    instances: &[PublicEcdsaInstance<M31>],
    relation: &EcdsaResultRelation,
) -> SecureField {
    instances
        .iter()
        .map(|instance| {
            let denominator: SecureField = relation.combine(&result_values(instance));
            -SecureField::from(M31::from_u32_unchecked(1)) / denominator
        })
        .sum()
}

pub fn gen_final_check_air_base_trace(
    final_check: &FinalEcdsaCheckClaim,
    proof_claim: FinalCheckAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(final_check.rows.len() <= row_count);
    let n_words = P256_ORDER_WORDS;
    let padding_lt = CanonicalLtTrace::new("padding_r_check", &[0u64; 4], "n", &n_words)
        .expect("0 is below the P-256 scalar order");

    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); row_count]; FINAL_CHECK_TRACE_COLUMNS];

    // Pre-fill padding-row canonical-LT slack/carries so the ungated
    // constraints inside `add_canonical_lt_fixed_bound` hold on every row.
    for row in 0..row_count {
        let mut offset = lt_slack_offset();
        for limb in padding_lt.slack.iter() {
            columns[offset][row] = M31::from_u32_unchecked(*limb);
            offset += 1;
        }
        debug_assert_eq!(offset, lt_carry_offset());
        for carry in padding_lt.carries.iter() {
            columns[offset][row] = encode_signed_carry(*carry);
            offset += 1;
        }
        debug_assert_eq!(offset, FINAL_CHECK_TRACE_COLUMNS);
    }

    for (row, final_row) in final_check.rows.iter().enumerate() {
        // Active row: write witnesses derived from the FinalEcdsaCheckClaim row.
        columns[0][row] = M31::from_u32_unchecked(1);
        columns[1][row] = final_row.sig_id;

        // r_check = expected_r = public.r, bound by EcdsaResultRelation.
        let r_check_limbs = final_row.expected_r.limbs();
        for (limb_index, limb) in r_check_limbs.iter().enumerate() {
            columns[2 + limb_index][row] = *limb;
        }

        // r_x = R.x (witnessed; not yet bound to chain outputs).
        let r_x_words = final_row.r_point.x.to_u256().to_le_u64s();
        let reduction = DigestReductionTrace::new(&r_x_words, &n_words)
            .expect("R.x reduces mod n: covered by FinalEcdsaCheckClaim::verify");
        debug_assert_eq!(reduction.z_ge_n, final_row.r_x_ge_n.0);
        debug_assert_eq!(
            reduction.z_red,
            limbs_to_array(final_row.expected_r.limbs()),
            "FinalEcdsaCheckClaim's expected_r must equal R.x mod n",
        );

        let mut offset = 2 + N_LIMBS;
        for limb in reduction.z.iter() {
            columns[offset][row] = M31::from_u32_unchecked(*limb);
            offset += 1;
        }
        debug_assert_eq!(offset, r_x_ge_n_offset());
        columns[offset][row] = M31::from_u32_unchecked(reduction.z_ge_n);
        offset += 1;
        debug_assert_eq!(offset, reduction_carry_offset());
        for carry in reduction.carries.iter() {
            columns[offset][row] = encode_signed_carry(*carry);
            offset += 1;
        }
        debug_assert_eq!(offset, lt_slack_offset());
        for limb in reduction.z_red_lt_n.slack.iter() {
            columns[offset][row] = M31::from_u32_unchecked(*limb);
            offset += 1;
        }
        debug_assert_eq!(offset, lt_carry_offset());
        for carry in reduction.z_red_lt_n.carries.iter() {
            columns[offset][row] = encode_signed_carry(*carry);
            offset += 1;
        }
        debug_assert_eq!(offset, FINAL_CHECK_TRACE_COLUMNS);
    }

    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_final_check_air_interaction_trace(
    base: &[M31ColumnEval],
    relations: FinalCheckAirRelations<'_>,
) -> (ColumnVec<M31ColumnEval>, FinalCheckAirInteractionClaim) {
    assert_eq!(base.len(), FINAL_CHECK_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let active_col = 0;

    // Order mirrors `FinalCheckAirEval::evaluate`: first
    // `add_digest_reduction` emits z + signed_carry per limb, then
    // canonical_lt emits value + slack per limb, then the result entry.
    for limb in 0..N_LIMBS {
        let z_relation = if limb == N_LIMBS - 1 {
            relations.range9
        } else {
            relations.range13
        };
        append_range_column(
            &mut logup,
            base,
            active_col,
            z_relation,
            r_x_offset() + limb,
        );
        append_range_column(
            &mut logup,
            base,
            active_col,
            relations.signed_carry,
            reduction_carry_offset() + limb,
        );
    }
    for limb in 0..N_LIMBS {
        append_range_column(
            &mut logup,
            base,
            active_col,
            relations.range13,
            r_check_offset() + limb,
        );
        append_range_column(
            &mut logup,
            base,
            active_col,
            relations.range13,
            lt_slack_offset() + limb,
        );
    }
    // Result relation: consumer emits (active / combine(result, values)).
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            PackedQM31::from(base[active_col].data[vec_row]),
            relations
                .result
                .combine(&result_packed_values_from_base(base, vec_row)),
        );
    }
    col.finalize_col();

    // FinalAddOutput relation: consumer emits (active / combine(sig_id, r_x)).
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            PackedQM31::from(base[active_col].data[vec_row]),
            relations
                .final_add_output
                .combine(&final_add_output_packed_values_from_base(base, vec_row)),
        );
    }
    col.finalize_col();

    let (trace, claimed_sum) = logup.finalize_last();

    // Per-relation consumer claimed sums (used to verify per-relation balance).
    let result_consumer_claimed_sum: SecureField = active_rows(base)
        .map(|row| -> SecureField {
            let denominator: SecureField = relations.result.combine(&result_values_from_base(&row));
            SecureField::from(row[0]) / denominator
        })
        .sum();
    let range13_consumer_claimed_sum = sum_consumer_fractions(
        relations.range13,
        final_check_range13_uses_from_base(base).into_iter(),
    );
    let range9_consumer_claimed_sum = sum_consumer_fractions(
        relations.range9,
        final_check_range9_uses_from_base(base).into_iter(),
    );
    let signed_carry_consumer_claimed_sum = sum_consumer_fractions(
        relations.signed_carry,
        final_check_signed_carry_uses_from_base(base)
            .into_iter()
            .map(encode_signed_carry),
    );
    let final_add_output_consumer_claimed_sum: SecureField = active_rows(base)
        .map(|row| -> SecureField {
            let denominator: SecureField =
                relations.final_add_output.combine(&final_add_output_values_from_base(&row));
            SecureField::from(row[0]) / denominator
        })
        .sum();

    (
        trace,
        FinalCheckAirInteractionClaim {
            claimed_sum,
            result_consumer_claimed_sum,
            range13_consumer_claimed_sum,
            range9_consumer_claimed_sum,
            signed_carry_consumer_claimed_sum,
            final_add_output_consumer_claimed_sum,
        },
    )
}

/// FinalAddOutput tuple `(sig_id, r_x[N_LIMBS])` packed values from base columns.
fn final_add_output_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; 1 + N_LIMBS] {
    core::array::from_fn(|index| {
        if index == 0 {
            base[1].data[vec_row]
        } else {
            base[r_x_offset() + (index - 1)].data[vec_row]
        }
    })
}

fn final_add_output_values_from_base(row: &[M31]) -> [M31; 1 + N_LIMBS] {
    core::array::from_fn(|index| {
        if index == 0 {
            row[1]
        } else {
            row[r_x_offset() + (index - 1)]
        }
    })
}

fn append_range_column(
    logup: &mut LogupTraceGenerator,
    base: &[M31ColumnEval],
    active_col: usize,
    relation: &RangeCheckRelation,
    value_col: usize,
) {
    let log_size = base[0].domain.log_size();
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let numerator = PackedQM31::from(base[active_col].data[vec_row]);
        let denominator = relation.combine(&[base[value_col].data[vec_row]]);
        col.write_frac(vec_row, numerator, denominator);
    }
    col.finalize_col();
}

/// Per-active-row range13 uses, matching the emission order in
/// [`FinalCheckAirEval::evaluate`]: `add_digest_reduction` range-checks the
/// non-top `r_x` limbs as Range13, then `add_canonical_lt_fixed_bound`
/// range-checks both the value (`r_check`) and the slack limbs.
pub(crate) fn final_check_range13_uses_from_base(base: &[M31ColumnEval]) -> Vec<M31> {
    let mut uses = Vec::new();
    for row in active_rows(base) {
        for limb in 0..N_LIMBS - 1 {
            uses.push(row[r_x_offset() + limb]);
        }
        for limb in 0..N_LIMBS {
            uses.push(row[r_check_offset() + limb]);
            uses.push(row[lt_slack_offset() + limb]);
        }
    }
    uses
}

/// Per-active-row range9 uses: top limb of `r_x` bounding `r_x < 2^256`.
pub(crate) fn final_check_range9_uses_from_base(base: &[M31ColumnEval]) -> Vec<M31> {
    active_rows(base)
        .map(|row| row[r_x_offset() + N_LIMBS - 1])
        .collect()
}

/// Per-active-row signed-carry uses: digest reduction signed limb carries.
pub(crate) fn final_check_signed_carry_uses_from_base(base: &[M31ColumnEval]) -> Vec<i64> {
    let mut uses = Vec::new();
    for row in active_rows(base) {
        for limb in 0..N_LIMBS {
            uses.push(decode_signed_carry(row[reduction_carry_offset() + limb]));
        }
    }
    uses
}

fn sum_consumer_fractions<I: Iterator<Item = M31>>(
    relation: &RangeCheckRelation,
    values: I,
) -> SecureField {
    values
        .map(|value| {
            let denominator: SecureField = relation.combine(&[value]);
            SecureField::from(M31::from_u32_unchecked(1)) / denominator
        })
        .sum()
}

fn result_values(instance: &PublicEcdsaInstance<M31>) -> [M31; ECDSA_RESULT_RELATION_ARITY] {
    core::array::from_fn(|index| {
        if index == 0 {
            instance.sig_id
        } else {
            instance.r.limbs()[index - 1]
        }
    })
}

fn result_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; ECDSA_RESULT_RELATION_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
}

fn result_values_from_base(row: &[M31]) -> [M31; ECDSA_RESULT_RELATION_ARITY] {
    core::array::from_fn(|index| row[1 + index])
}

fn active_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count)
        .map(move |row| {
            let vec_row = row / (1 << LOG_N_LANES);
            let lane = row % (1 << LOG_N_LANES);
            base.iter()
                .map(|column| column.data[vec_row].to_array()[lane])
                .collect::<Vec<_>>()
        })
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
}

const fn r_check_offset() -> usize {
    2
}

const fn r_x_offset() -> usize {
    2 + N_LIMBS
}

const fn r_x_ge_n_offset() -> usize {
    2 + 2 * N_LIMBS
}

const fn reduction_carry_offset() -> usize {
    2 + 2 * N_LIMBS + 1
}

const fn lt_slack_offset() -> usize {
    2 + 3 * N_LIMBS + 1
}

const fn lt_carry_offset() -> usize {
    2 + 4 * N_LIMBS + 1
}

fn limbs_to_array(limbs: &[M31; N_LIMBS]) -> [u32; N_LIMBS] {
    core::array::from_fn(|i| limbs[i].0)
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}

#[allow(dead_code)]
const _P256_M31_BIGINT_UNUSED_IMPORT_GUARD: Option<P256M31BigInt> = None;
