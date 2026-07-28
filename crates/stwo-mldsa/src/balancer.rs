//! Test-side LogUp balancer component: yields or consumes a fixed list of
//! tuples against a cross-component relation so a component under standalone test
//! is self-balancing. In the full composition (M6) the real counterpart
//! component (coeffs / the sponge) replaces the balancer — the relation contract
//! is identical, so nothing in the component-under-test changes.
//!
//! Each active row commits one tuple's cells as base columns and emits a single
//! `±1 / combine(tuple)` fraction. `sign_positive` picks yield (−, provider) vs
//! consume (+, requester) to cancel the component-under-test's opposite sign.

use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use crate::air_util::{circle_row_to_coset, col_eval, m31, ColEval};
use crate::binding::{CCellRelation, HashIoRelation, WCellRelation};

/// The relations a balancer can target (the cross-component bindings).
#[derive(Clone)]
pub enum BalancerRelation {
    WCell(WCellRelation),
    CCell(CCellRelation),
    HashIo(HashIoRelation),
}

impl BalancerRelation {
    fn combine_m31(&self, values: &[M31]) -> SecureField {
        match self {
            BalancerRelation::WCell(r) => r.combine(values),
            BalancerRelation::CCell(r) => r.combine(values),
            BalancerRelation::HashIo(r) => r.combine(values),
        }
    }
    fn add_entry<E: EvalAtRow>(&self, eval: &mut E, num: E::EF, values: &[E::F]) {
        match self {
            BalancerRelation::WCell(r) => eval.add_to_relation(RelationEntry::new(r, num, values)),
            BalancerRelation::CCell(r) => eval.add_to_relation(RelationEntry::new(r, num, values)),
            BalancerRelation::HashIo(r) => eval.add_to_relation(RelationEntry::new(r, num, values)),
        }
    }
}

/// Number of interaction columns a balancer contributes (one batched fraction).
pub const BALANCER_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

#[derive(Clone)]
pub struct BalancerEval {
    pub log_size: u32,
    pub arity: usize,
    pub relation: BalancerRelation,
    /// `true` → consume (+1 numerator); `false` → yield (−1).
    pub sign_positive: bool,
}

impl FrameworkEval for BalancerEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let enabler = eval.next_trace_mask();
        let cells: Vec<E::F> = (0..self.arity).map(|_| eval.next_trace_mask()).collect();
        let num = if self.sign_positive {
            E::EF::from(enabler.clone())
        } else {
            -E::EF::from(enabler.clone())
        };
        self.relation.add_entry(&mut eval, num, &cells);
        eval.finalize_logup();
        eval
    }
}

/// Base trace: `enabler` + `arity` tuple columns. Padding rows have enabler = 0
/// and zero tuple cells.
pub fn gen_balancer_trace(log_size: u32, tuples: &[Vec<u32>]) -> Vec<ColEval> {
    let rows = 1usize << log_size;
    assert!(tuples.len() <= rows, "balancer tuples exceed padded rows");
    let arity = tuples.first().map(|t| t.len()).unwrap_or(0);
    let mut enabler = vec![m31(0); rows];
    let mut cols: Vec<Vec<M31>> = (0..arity).map(|_| vec![m31(0); rows]).collect();
    for (row, tup) in tuples.iter().enumerate() {
        enabler[row] = m31(1);
        for (c, &v) in tup.iter().enumerate() {
            cols[c][row] = m31(v);
        }
    }
    let mut out = vec![col_eval(log_size, enabler)];
    out.extend(cols.into_iter().map(|v| col_eval(log_size, v)));
    out
}

/// The balancer trace is `1 + arity` base columns.
pub fn balancer_base_cols(arity: usize) -> usize {
    1 + arity
}

/// Interaction trace: one `±1 / combine(tuple)` fraction per row.
pub fn gen_balancer_interaction(
    log_size: u32,
    tuples: &[Vec<u32>],
    relation: &BalancerRelation,
    sign_positive: bool,
) -> (Vec<ColEval>, SecureField) {
    let row_lookup = circle_row_to_coset(log_size);
    let zero = SecureField::from(m31(0));
    let one = SecureField::one();
    let signed_one = if sign_positive { one } else { -one };

    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vr| {
        let mut n = [zero; N_LANES];
        let mut d = [one; N_LANES];
        for lane in 0..N_LANES {
            let coset = row_lookup[vr * N_LANES + lane];
            if coset < tuples.len() {
                let cells: Vec<M31> = tuples[coset].iter().map(|&v| m31(v)).collect();
                n[lane] = signed_one;
                d[lane] = relation.combine_m31(&cells);
            }
        }
        (PackedQM31::from_array(n), PackedQM31::from_array(d))
    });
    logup.finalize_last()
}
