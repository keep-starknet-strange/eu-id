//! Range-check table providers for `mldsa_coeffs`.
//!
//! The composed statement uses one table of `(value, bound_id)` tuples. The id
//! is a fixed namespace, so a value present in a wider range cannot satisfy a
//! lookup made against a tighter range. Standalone coeffs proofs retain the
//! per-kind provider wrappers below, but all providers use the same arity-2
//! relation and the same fixed ids.

use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use super::relations::RangeRelation;
use crate::air_util::{col_eval, m31, ColEval};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcKind {
    Rc9,
    Rc13,
    Rc8,
    Rc7,
    Ternary,
}

impl RcKind {
    pub const ALL: [RcKind; 5] = [
        RcKind::Rc9,
        RcKind::Rc13,
        RcKind::Rc8,
        RcKind::Rc7,
        RcKind::Ternary,
    ];
    pub const RANGE: [RcKind; 4] = [RcKind::Rc9, RcKind::Rc13, RcKind::Rc8, RcKind::Rc7];

    pub const fn n_values(self) -> usize {
        match self {
            RcKind::Rc9 => 1 << 9,
            RcKind::Rc13 => 1 << 13,
            RcKind::Rc8 => 1 << 8,
            RcKind::Rc7 => 1 << 7,
            RcKind::Ternary => 3,
        }
    }

    pub const fn value_at(self, i: usize) -> u32 {
        i as u32
    }

    pub const fn bound_id(self) -> u32 {
        match self {
            RcKind::Rc9 => 0,
            RcKind::Rc13 => 1,
            RcKind::Rc8 => 2,
            RcKind::Rc7 => 3,
            RcKind::Ternary => 4,
        }
    }

    pub const fn row_base(self) -> usize {
        match self {
            RcKind::Rc9 => 0,
            RcKind::Rc13 => RcKind::Rc9.n_values(),
            RcKind::Rc8 => RcKind::Rc9.n_values() + RcKind::Rc13.n_values(),
            RcKind::Rc7 => {
                RcKind::Rc9.n_values() + RcKind::Rc13.n_values() + RcKind::Rc8.n_values()
            }
            RcKind::Ternary => {
                RcKind::Rc9.n_values()
                    + RcKind::Rc13.n_values()
                    + RcKind::Rc8.n_values()
                    + RcKind::Rc7.n_values()
            }
        }
    }

    pub const fn log_size(self) -> u32 {
        let bits = usize::BITS - (self.n_values() - 1).leading_zeros();
        if bits < LOG_N_LANES {
            LOG_N_LANES
        } else {
            bits
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            RcKind::Rc9 => "rc9",
            RcKind::Rc13 => "rc13",
            RcKind::Rc8 => "rc8",
            RcKind::Rc7 => "rc7",
            RcKind::Ternary => "ternary",
        }
    }

    pub fn value_column_id(self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("mldsa_{}_value", self.name()),
        }
    }
}

pub const RANGE_TABLE_ACTIVE_ROWS: usize = RcKind::Ternary.row_base() + RcKind::Ternary.n_values();
pub const PADDING_BOUND_ID: u32 = RcKind::ALL.len() as u32;

pub const fn range_table_log_size() -> u32 {
    14
}

pub fn range_table_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    ["mldsa_range_value", "mldsa_range_bound_id"]
        .into_iter()
        .map(|id| PreProcessedColumnId { id: id.to_string() })
        .collect()
}

fn range_table_columns() -> (Vec<M31>, Vec<M31>) {
    let rows = 1usize << range_table_log_size();
    let mut values = vec![m31(0); rows];
    let mut ids = vec![m31(PADDING_BOUND_ID); rows];
    // Stable id assignment: rc9=0, rc13=1, rc8=2, rc7=3, ternary=4.
    // The id in slot 1 makes all five value domains disjoint in one relation.
    for kind in RcKind::ALL {
        for value in 0..kind.n_values() {
            let row = kind.row_base() + value;
            values[row] = m31(value as u32);
            ids[row] = m31(kind.bound_id());
        }
    }
    (values, ids)
}

pub fn gen_range_table_preprocessed() -> Vec<ColEval> {
    let (values, ids) = range_table_columns();
    vec![
        col_eval(range_table_log_size(), values),
        col_eval(range_table_log_size(), ids),
    ]
}

pub fn gen_range_table_multiplicities(uses: [&[u32]; 5]) -> ColEval {
    let mut values = vec![m31(0); 1usize << range_table_log_size()];
    for (kind, counts) in RcKind::ALL.into_iter().zip(uses) {
        assert_eq!(counts.len(), kind.n_values());
        for (value, &count) in counts.iter().enumerate() {
            values[kind.row_base() + value] = m31(count);
        }
    }
    col_eval(range_table_log_size(), values)
}

pub fn gen_range_table_interaction(
    multiplicity: &ColEval,
    relation: &RangeRelation,
) -> (Vec<ColEval>, SecureField) {
    let preprocessed = gen_range_table_preprocessed();
    let mut logup = LogupTraceGenerator::new(range_table_log_size());
    logup.col_from_fn(|row| {
        let denominator: PackedQM31 =
            relation.combine(&[preprocessed[0].data[row], preprocessed[1].data[row]]);
        (-PackedQM31::from(multiplicity.data[row]), denominator)
    });
    logup.finalize_last()
}

#[derive(Clone)]
pub struct RangeTableEval {
    pub relation: RangeRelation,
}

impl FrameworkEval for RangeTableEval {
    fn log_size(&self) -> u32 {
        range_table_log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        range_table_log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let ids = range_table_preprocessed_ids();
        let value = eval.get_preprocessed_column(ids[0].clone());
        let bound_id = eval.get_preprocessed_column(ids[1].clone());
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[value, bound_id],
        ));
        eval.finalize_logup();
        eval
    }
}

pub type RangeTableComponent = FrameworkComponent<RangeTableEval>;
pub const RANGE_TABLE_COMPONENTS: usize = 1;
pub const RANGE_TABLE_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

// Standalone coeffs-proof compatibility. These providers remain split only in
// that test harness; their relation and fixed tuple ids are identical to the
// composed statement's combined provider.
pub fn gen_table_preprocessed(kind: RcKind) -> ColEval {
    let rows = 1usize << kind.log_size();
    col_eval(
        kind.log_size(),
        (0..rows)
            .map(|i| m31(if i < kind.n_values() { i as u32 } else { 0 }))
            .collect(),
    )
}

pub fn gen_table_multiplicities(kind: RcKind, uses: &[u32]) -> ColEval {
    assert_eq!(uses.len(), kind.n_values());
    let rows = 1usize << kind.log_size();
    col_eval(
        kind.log_size(),
        (0..rows)
            .map(|i| m31(if i < uses.len() { uses[i] } else { 0 }))
            .collect(),
    )
}

pub fn gen_table_interaction(
    kind: RcKind,
    multiplicity: &ColEval,
    relation: &RangeRelation,
) -> (Vec<ColEval>, SecureField) {
    let value = gen_table_preprocessed(kind);
    let bound_id = PackedM31::from(m31(kind.bound_id()));
    let mut logup = LogupTraceGenerator::new(kind.log_size());
    logup.col_from_fn(|row| {
        let denominator: PackedQM31 = relation.combine(&[value.data[row], bound_id]);
        (-PackedQM31::from(multiplicity.data[row]), denominator)
    });
    logup.finalize_last()
}

#[derive(Clone)]
pub struct RcTableEval {
    pub kind: RcKind,
    pub relation: RangeRelation,
}

impl FrameworkEval for RcTableEval {
    fn log_size(&self) -> u32 {
        self.kind.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.kind.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(self.kind.value_column_id());
        let multiplicity = eval.next_trace_mask();
        let bound_id = E::F::from(m31(self.kind.bound_id()));
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[value, bound_id],
        ));
        eval.finalize_logup();
        eval
    }
}

pub type RcTableComponent = FrameworkComponent<RcTableEval>;
pub const RC_TABLE_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combined_table_covers_disjoint_domains_and_zero_multiplicity_padding() {
        let (values, ids) = range_table_columns();
        for kind in RcKind::ALL {
            for value in 0..kind.n_values() {
                let row = kind.row_base() + value;
                assert_eq!(values[row].0, value as u32);
                assert_eq!(ids[row].0, kind.bound_id());
            }
        }
        assert_eq!(RANGE_TABLE_ACTIVE_ROWS, 9_091);
        for row in RANGE_TABLE_ACTIVE_ROWS..1usize << range_table_log_size() {
            assert_eq!(values[row].0, 0);
            assert_eq!(ids[row].0, PADDING_BOUND_ID);
        }
    }
}
