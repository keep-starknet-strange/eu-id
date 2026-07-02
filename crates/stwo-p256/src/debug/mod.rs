#[cfg(test)]
use std::ops::Deref;

#[cfg(test)]
use itertools::Itertools;
#[cfg(test)]
use num_traits::Zero;
#[cfg(test)]
use stwo::core::channel::Blake2sM31Channel;
use stwo::core::fields::m31::M31;
#[cfg(test)]
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::ColumnVec;
use stwo::prover::backend::{Backend, Column};
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
#[cfg(test)]
use stwo_constraint_framework::TraceLocationAllocator;
#[cfg(test)]
use stwo_constraint_framework::{
    assert_constraints_on_trace, FrameworkComponent, FrameworkEval, PREPROCESSED_TRACE_IDX,
};
#[cfg(test)]
use stwo_p256_utils::constants::N_LIMBS;
#[cfg(test)]
use stwo_p256_utils::scalar_arithmetic::{
    CanonicalLtTrace, DigestReductionTrace, ScalarFieldMulTrace, P256_ORDER,
};

#[cfg(test)]
use crate::constants::P256_MODULUS;
#[cfg(test)]
use crate::final_add_air::FinalAddOutputRelation;
#[cfg(test)]
use crate::final_check_air::{
    gen_final_check_air_interaction_trace, EcdsaResultRelation, FinalCheckAirComponents,
    FinalCheckAirProofClaim, FinalCheckAirRelations,
};
#[cfg(test)]
use crate::range_checks::encode_signed_carry;
#[cfg(test)]
use crate::range_checks::RangeCheckRelation;
#[cfg(test)]
use crate::scalar::scalar_mod_mul::columns::m31_column_eval;
#[cfg(test)]
use crate::scalar::scalar_mod_mul::columns::M31ColumnEval;

#[cfg(test)]
use crate::scalar::scalar_mod_mul::claim::{
    gen_base_trace, gen_interaction_trace, gen_preprocessed_trace, preprocessed_column_ids,
    ScalarModMulComponents,
};
#[cfg(test)]
use crate::scalar::scalar_mod_mul::layout::ScalarModMulRelationAudit;
#[cfg(test)]
use crate::scalar::scalar_mod_mul::providers::LookupProviderClaims;
#[cfg(test)]
use crate::scalar::scalar_mod_mul::relation::ScalarModMulLookupRelations;
#[cfg(test)]
use crate::scalar::scalar_mod_mul::{
    ScalarModMulClaim, ScalarModMulMergedRows, ScalarModMulTraceRows,
};

#[cfg(test)]
const TEST_MUL_ID: u32 = 3;
#[derive(Default)]
pub struct MockCommitmentScheme {
    trees: TreeVec<ColumnVec<Vec<M31>>>,
}

impl MockCommitmentScheme {
    pub fn tree_builder(&mut self) -> MockTreeBuilder<'_> {
        MockTreeBuilder {
            tree_index: self.trees.len(),
            evals: Vec::new(),
            commitment_scheme: self,
        }
    }

    pub fn next_interaction(&mut self, evals: ColumnVec<Vec<M31>>) {
        self.trees.push(evals);
    }

    pub fn trace_domain_evaluations(&self) -> TreeVec<ColumnVec<&Vec<M31>>> {
        self.trees.as_cols_ref()
    }
}

pub struct MockTreeBuilder<'a> {
    tree_index: usize,
    evals: ColumnVec<Vec<M31>>,
    commitment_scheme: &'a mut MockCommitmentScheme,
}

impl MockTreeBuilder<'_> {
    pub fn extend_evals<B: Backend>(
        &mut self,
        columns: impl IntoIterator<Item = CircleEvaluation<B, M31, BitReversedOrder>>,
    ) -> TreeSubspan {
        let col_start = self.evals.len();
        self.evals
            .extend(columns.into_iter().map(|column| column.to_cpu()));
        let col_end = self.evals.len();
        TreeSubspan {
            tree_index: self.tree_index,
            col_start,
            col_end,
        }
    }

    pub fn finalize_interaction(self) {
        self.commitment_scheme.next_interaction(self.evals);
    }
}

#[cfg(test)]
fn assert_scalar_components(trace: TreeVec<Vec<&Vec<M31>>>, components: &ScalarModMulComponents) {
    println!("canonical");
    assert_component(&components.canonical, &trace);

    println!("ab_chunks");
    assert_component(&components.ab_chunks, &trace);

    println!("qn_chunks");
    assert_component(&components.qn_chunks, &trace);

    println!("accumulators");
    assert_component(&components.accumulators, &trace);

    println!("reduction_digits");
    assert_component(&components.reduction_digits, &trace);

    println!("range13");
    assert_component(&components.range13, &trace);

    println!("signed_carry");
    assert_component(&components.signed_carry, &trace);
}

#[cfg(test)]
fn assert_component<E: FrameworkEval + Sync>(
    component: &FrameworkComponent<E>,
    trace: &TreeVec<Vec<&Vec<M31>>>,
) {
    let mut component_trace = trace
        .sub_tree(component.trace_locations())
        .map(|tree| tree.into_iter().cloned().collect_vec());
    component_trace[PREPROCESSED_TRACE_IDX] = component
        .preprocessed_column_indices()
        .iter()
        .map(|idx| trace[PREPROCESSED_TRACE_IDX][*idx])
        .collect();

    let component_eval = component.deref();
    assert_constraints_on_trace(
        &component_trace,
        component.log_size(),
        |eval| {
            let _ = component_eval.evaluate(eval);
        },
        component.claimed_sum(),
    );
}

#[cfg(test)]
fn scalar(value: u64) -> [u64; 4] {
    [value, 0, 0, 0]
}

#[cfg(test)]
/// Assert the complete scalar modular multiplication proof slice on trace-domain rows.
///
/// This mirrors Falcon's debug harness shape: build three mock commitment trees
/// (preprocessed, base, interaction), allocate all components against the same
/// preprocessed-column list, print each component name, then run
/// `assert_constraints_on_trace` component by component.
pub fn assert_scalar_mod_mul_constraints(rows: &ScalarModMulMergedRows) {
    let lookup_claims = LookupProviderClaims::scalar_mod_mul();
    let claim = ScalarModMulClaim::from_rows(rows);

    let preprocessed_ids = preprocessed_column_ids(&claim, &lookup_claims);
    let preprocessed = gen_preprocessed_trace(rows, &lookup_claims, &preprocessed_ids);
    let base = gen_base_trace(rows, &lookup_claims);

    let mut dummy_channel = Blake2sM31Channel::default();
    let relations = ScalarModMulLookupRelations::draw(&mut dummy_channel);
    let (interaction, interaction_claim) =
        gen_interaction_trace(rows, &claim, &lookup_claims, &relations);

    let mut commitment_scheme = MockCommitmentScheme::default();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed);
    tree_builder.finalize_interaction();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.finalize_interaction();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.finalize_interaction();

    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    let components = ScalarModMulComponents::new(
        &mut allocator,
        &claim,
        &interaction_claim,
        &lookup_claims,
        &relations,
    );
    assert_scalar_components(commitment_scheme.trace_domain_evaluations(), &components);

    assert_eq!(
        interaction_claim.claimed_sum(),
        SecureField::zero(),
        "invalid logup sum"
    );
}

#[cfg(test)]
/// Assert the FinalEcdsaCheck AIR on trace-domain rows for a hand-built base
/// trace (the component declares no preprocessed columns; relations are drawn
/// from a dummy channel, mirroring the other debug harnesses).
///
/// This swaps PCS/FRI for a direct trace-domain constraint check using the
/// same interaction-trace generator and component allocation as the proof
/// path. Cross-component LogUp balance is intentionally not asserted: in
/// isolation the component's range/result consumers have no providers. Used
/// by the canonical-`r_x` (`x + p`) adversarial tests.
pub fn assert_final_check_air_constraints(base: ColumnVec<M31ColumnEval>) {
    let mut dummy_channel = Blake2sM31Channel::default();
    let result_relation = EcdsaResultRelation::draw(&mut dummy_channel);
    let range13 = RangeCheckRelation::draw(&mut dummy_channel);
    let range9 = RangeCheckRelation::draw(&mut dummy_channel);
    let signed_carry = RangeCheckRelation::draw(&mut dummy_channel);
    let final_add_output = FinalAddOutputRelation::draw(&mut dummy_channel);
    let relations = FinalCheckAirRelations {
        result: &result_relation,
        range13: &range13,
        range9: &range9,
        signed_carry: &signed_carry,
        final_add_output: &final_add_output,
    };

    let log_size = base[0].domain.log_size();
    let (interaction, interaction_claim) =
        gen_final_check_air_interaction_trace(&base, relations.clone());

    let mut commitment_scheme = MockCommitmentScheme::default();
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(Vec::<M31ColumnEval>::new());
    tree_builder.finalize_interaction();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(base);
    tree_builder.finalize_interaction();

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.finalize_interaction();

    let mut allocator = TraceLocationAllocator::default();
    let components = FinalCheckAirComponents::new(
        &mut allocator,
        FinalCheckAirProofClaim { log_size },
        &interaction_claim,
        relations,
    );
    let trace = commitment_scheme.trace_domain_evaluations();
    assert_component(&components.check, &trace);
}

#[cfg(test)]
fn honest_scalar_mod_mul_rows() -> ScalarModMulTraceRows {
    let trace = ScalarFieldMulTrace::new("debug_mul", &scalar(7), &scalar(11), &P256_ORDER)
        .expect("valid scalar mod-mul trace");
    ScalarModMulTraceRows::new(TEST_MUL_ID, &trace).expect("trace rows generate")
}

#[test]
fn scalar_mod_mul_debug_assert_constraints_pass_for_honest_trace() {
    let rows = ScalarModMulMergedRows::new(vec![honest_scalar_mod_mul_rows()]);
    assert!(ScalarModMulRelationAudit::from_rows(&rows).is_balanced());
    assert_scalar_mod_mul_constraints(&rows);
}

#[test]
fn scalar_mod_mul_debug_canonical_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.canonical_scalars[0].value[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&ScalarModMulMergedRows::new(vec![rows]));
    assert!(!audit.is_balanced());
    assert!(audit.scalar_limb.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_ab_chunk_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.ab_chunks[0].digits[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&ScalarModMulMergedRows::new(vec![rows]));
    assert!(!audit.is_balanced());
    assert!(audit.product_chunk_digit.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_qn_chunk_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.qn_chunks[0].quotient_limbs[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&ScalarModMulMergedRows::new(vec![rows]));
    assert!(!audit.is_balanced());
    assert!(audit.scalar_limb.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_accumulator_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.accumulators[0].terms[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&ScalarModMulMergedRows::new(vec![rows]));
    assert!(!audit.is_balanced());
    assert!(audit.product_chunk_digit.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_reduction_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.reduction_digits[0].result_limb += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&ScalarModMulMergedRows::new(vec![rows]));
    assert!(!audit.is_balanced());
    assert!(audit.scalar_limb.nonzero_entries() > 0);
}

/// `p + addend` as LE u64 words (must stay below `2^256`). Used to build the
/// non-canonical `x + p` attack witness.
#[cfg(test)]
fn p_plus(addend: u64) -> [u64; 4] {
    let mut words = P256_MODULUS;
    let mut carry = u128::from(addend);
    for word in words.iter_mut() {
        let sum = u128::from(*word) + carry;
        *word = sum as u64;
        carry = sum >> 64;
    }
    assert_eq!(carry, 0, "p + addend must stay below 2^256");
    words
}

/// Build a single-active-row FinalEcdsaCheck base trace for the witnessed
/// `r_x` value `v` (any `v < 2^256`). The digest-reduction witnesses
/// (`r_check = v mod n`, `r_check < n`) are derived honestly — they exist for
/// every `v < 2^256` — while the `r_x < p` slack/carries are supplied by the
/// caller, because for `v >= p` no valid witness exists (that is the attack
/// the canonical-LT must reject).
#[cfg(test)]
fn final_check_base_columns(
    v_words: &[u64; 4],
    lt_p_slack: [u32; N_LIMBS],
    lt_p_carries: [i64; N_LIMBS],
) -> ColumnVec<M31ColumnEval> {
    use stwo::prover::backend::simd::m31::LOG_N_LANES;

    let log_size = LOG_N_LANES;
    let rows = 1usize << log_size;
    let m = M31::from_u32_unchecked;

    let reduction =
        DigestReductionTrace::new(v_words, &P256_ORDER).expect("any v < 2^256 reduces mod n");
    let padding_lt_n = CanonicalLtTrace::new("padding_r_check", &[0u64; 4], "n", &P256_ORDER)
        .expect("0 is below the P-256 scalar order");
    let padding_lt_p = CanonicalLtTrace::new("padding_r_x", &[0u64; 4], "p", &P256_MODULUS)
        .expect("0 is below the P-256 field prime");

    // Layout mirrors `final_check_air`: active, sig_id, r_check, r_x,
    // r_x_ge_n, reduction carries, r_check<n slack/carries, r_x<p
    // slack/carries.
    let total_columns = 2 + 7 * N_LIMBS + 1;
    let mut columns = vec![vec![m(0); rows]; total_columns];

    // Every row (padding included) carries valid `0 < bound` canonical-LT
    // witnesses because the gadget equations are ungated.
    for row in 0..rows {
        for (i, limb) in padding_lt_n.slack.iter().enumerate() {
            columns[2 + 3 * N_LIMBS + 1 + i][row] = m(*limb);
        }
        for (i, carry) in padding_lt_n.carries.iter().enumerate() {
            columns[2 + 4 * N_LIMBS + 1 + i][row] = encode_signed_carry(*carry);
        }
        for (i, limb) in padding_lt_p.slack.iter().enumerate() {
            columns[2 + 5 * N_LIMBS + 1 + i][row] = m(*limb);
        }
        for (i, carry) in padding_lt_p.carries.iter().enumerate() {
            columns[2 + 6 * N_LIMBS + 1 + i][row] = encode_signed_carry(*carry);
        }
    }

    // Active row 0.
    columns[0][0] = m(1);
    columns[1][0] = m(1);
    for (i, limb) in reduction.z_red.iter().enumerate() {
        columns[2 + i][0] = m(*limb);
    }
    for (i, limb) in reduction.z.iter().enumerate() {
        columns[2 + N_LIMBS + i][0] = m(*limb);
    }
    columns[2 + 2 * N_LIMBS][0] = m(reduction.z_ge_n);
    for (i, carry) in reduction.carries.iter().enumerate() {
        columns[2 + 2 * N_LIMBS + 1 + i][0] = encode_signed_carry(*carry);
    }
    for (i, limb) in reduction.z_red_lt_n.slack.iter().enumerate() {
        columns[2 + 3 * N_LIMBS + 1 + i][0] = m(*limb);
    }
    for (i, carry) in reduction.z_red_lt_n.carries.iter().enumerate() {
        columns[2 + 4 * N_LIMBS + 1 + i][0] = encode_signed_carry(*carry);
    }
    for (i, limb) in lt_p_slack.iter().enumerate() {
        columns[2 + 5 * N_LIMBS + 1 + i][0] = m(*limb);
    }
    for (i, carry) in lt_p_carries.iter().enumerate() {
        columns[2 + 6 * N_LIMBS + 1 + i][0] = encode_signed_carry(*carry);
    }

    columns
        .into_iter()
        .map(|values| m31_column_eval(log_size, values))
        .collect()
}

#[test]
fn final_check_debug_honest_canonical_r_x_passes() {
    let v = scalar(41);
    let lt_p = CanonicalLtTrace::new("r_x", &v, "p", &P256_MODULUS).expect("41 < p");
    let base = final_check_base_columns(&v, lt_p.slack, lt_p.carries);
    assert_final_check_air_constraints(base);
}

#[test]
fn final_check_debug_rejects_non_canonical_r_x_plus_p() {
    // The `x + p` attack: witness `r_x = p + 41 ≡ 41 (mod p)`, which shifts
    // the published `r = r_x mod n` because `p mod n != 0`. Every
    // digest-reduction witness is internally valid for this `r_x` — before
    // the `r_x < p` canonical-LT was added, this trace satisfied the full
    // FinalEcdsaCheck AIR. No valid `r_x < p` witness exists (here the
    // malicious prover writes zeros), so the ungated canonical-LT recurrence
    // must fail.
    //
    // The constraint violation panics inside `evaluate` while its `LogupAtRow`
    // is still live, and that guard's unwind-time assert turns the panic into
    // a SIGABRT (lessons.md #18), which `#[should_panic]` cannot observe. Run
    // the forged assert in a child process instead and require that the child
    // dies: the parent FAILS iff the AIR accepts the forgery.
    if std::env::var_os("FINAL_CHECK_FORGED_ORACLE_CHILD").is_some() {
        let v = p_plus(41);
        let base = final_check_base_columns(&v, [0; N_LIMBS], [0; N_LIMBS]);
        assert_final_check_air_constraints(base);
        return; // reached only if the AIR accepted the forged trace
    }
    let exe = std::env::current_exe().expect("test binary path");
    let output = std::process::Command::new(exe)
        .args([
            "--exact",
            "debug::final_check_debug_rejects_non_canonical_r_x_plus_p",
            "--test-threads=1",
        ])
        .env("FINAL_CHECK_FORGED_ORACLE_CHILD", "1")
        .output()
        .expect("forged-r_x oracle child spawns");
    assert!(
        !output.status.success(),
        "non-canonical r_x = x + p must be rejected by the FinalEcdsaCheck AIR",
    );
}
