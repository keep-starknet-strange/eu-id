use std::ops::Deref;

use itertools::Itertools;
use num_traits::Zero;
use stwo::core::channel::Blake2sM31Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::ColumnVec;
use stwo::prover::backend::{Backend, Column};
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{
    assert_constraints_on_trace, FrameworkComponent, FrameworkEval, TraceLocationAllocator,
    PREPROCESSED_TRACE_IDX,
};
#[cfg(test)]
use stwo_p256_utils::scalar_arithmetic::{ScalarFieldMulTrace, P256_ORDER};

use crate::scalar::scalar_mod_mul::claim::{
    gen_base_trace, gen_interaction_trace, gen_preprocessed_trace, preprocessed_column_ids,
    ScalarModMulComponents,
};
#[cfg(test)]
use crate::scalar::scalar_mod_mul::layout::ScalarModMulRelationAudit;
use crate::scalar::scalar_mod_mul::providers::LookupProviderClaims;
use crate::scalar::scalar_mod_mul::relation::ScalarModMulLookupRelations;
use crate::scalar::scalar_mod_mul::{ScalarModMulClaim, ScalarModMulTraceRows};

#[cfg(test)]
const TEST_MUL_ID: u32 = 3;
/// Assert the complete scalar modular multiplication proof slice on trace-domain rows.
///
/// This mirrors Falcon's debug harness shape: build three mock commitment trees
/// (preprocessed, base, interaction), allocate all components against the same
/// preprocessed-column list, print each component name, then run
/// `assert_constraints_on_trace` component by component.
pub fn assert_scalar_mod_mul_constraints(rows: &ScalarModMulTraceRows) {
    let lookup_claims = LookupProviderClaims::scalar_mod_mul();
    let claim = ScalarModMulClaim::from_rows(rows);

    let preprocessed_ids = preprocessed_column_ids(&claim, &lookup_claims);
    let preprocessed = gen_preprocessed_trace(rows, &lookup_claims, &preprocessed_ids);
    let base = gen_base_trace(rows, &lookup_claims);

    let mut dummy_channel = Blake2sM31Channel::default();
    let relations = ScalarModMulLookupRelations::draw(&mut dummy_channel);
    let (interaction, interaction_claim) = gen_interaction_trace(rows, &lookup_claims, &relations);

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
    assert_components(commitment_scheme.trace_domain_evaluations(), &components);

    assert_eq!(
        interaction_claim.claimed_sum(),
        SecureField::zero(),
        "invalid logup sum"
    );
}

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

fn assert_components(trace: TreeVec<Vec<&Vec<M31>>>, components: &ScalarModMulComponents) {
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
fn honest_scalar_mod_mul_rows() -> ScalarModMulTraceRows {
    let trace = ScalarFieldMulTrace::new("debug_mul", &scalar(7), &scalar(11), &P256_ORDER)
        .expect("valid scalar mod-mul trace");
    ScalarModMulTraceRows::new(TEST_MUL_ID, &trace).expect("trace rows generate")
}

#[test]
fn scalar_mod_mul_debug_assert_constraints_pass_for_honest_trace() {
    let rows = honest_scalar_mod_mul_rows();
    assert!(ScalarModMulRelationAudit::from_rows(&rows).is_balanced());
    assert_scalar_mod_mul_constraints(&rows);
}

#[test]
fn scalar_mod_mul_debug_canonical_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.canonical_scalars[0].value[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&rows);
    assert!(!audit.is_balanced());
    assert!(audit.scalar_limb.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_ab_chunk_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.ab_chunks[0].digits[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&rows);
    assert!(!audit.is_balanced());
    assert!(audit.product_chunk_digit.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_qn_chunk_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.qn_chunks[0].quotient_limbs[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&rows);
    assert!(!audit.is_balanced());
    assert!(audit.scalar_limb.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_accumulator_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.accumulators[0].terms[0] += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&rows);
    assert!(!audit.is_balanced());
    assert!(audit.product_chunk_digit.nonzero_entries() > 0);
}

#[test]
fn scalar_mod_mul_debug_reduction_mutation_breaks_relation_balance() {
    let mut rows = honest_scalar_mod_mul_rows();
    rows.reduction_digits[0].result_limb += M31::from_u32_unchecked(1);
    let audit = ScalarModMulRelationAudit::from_rows(&rows);
    assert!(!audit.is_balanced());
    assert!(audit.scalar_limb.nonzero_entries() > 0);
}
