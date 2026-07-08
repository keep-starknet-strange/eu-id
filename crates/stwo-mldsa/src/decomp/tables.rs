//! Range-check table providers for `mldsa_decomp`: `Rc4` (2^4, w1/w1'), `Rc13`
//! (2^13), `Rc7` (2^7), `Rc8` (2^8). Same provider shape as `coeffs::tables`
//! (preprocessed value column `0..2^bits` + witness multiplicity column, yielding
//! `−mult / (z − value)`); one provider component per relation instance.

use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use super::relations::RcRelation;
use crate::air_util::{col_eval, m31, ColEval};

/// The four range-check widths used by decomp.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcKind {
    Rc4,
    Rc13,
    Rc7,
    Rc8,
}

impl RcKind {
    pub const ALL: [RcKind; 4] = [RcKind::Rc4, RcKind::Rc13, RcKind::Rc7, RcKind::Rc8];

    pub const fn n_values(self) -> usize {
        match self {
            RcKind::Rc4 => 1 << 4,
            RcKind::Rc13 => 1 << 13,
            RcKind::Rc7 => 1 << 7,
            RcKind::Rc8 => 1 << 8,
        }
    }

    pub const fn log_size(self) -> u32 {
        let n = self.n_values();
        let bits = usize::BITS - (n - 1).leading_zeros();
        if bits < LOG_N_LANES {
            LOG_N_LANES
        } else {
            bits
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            RcKind::Rc4 => "rc4",
            RcKind::Rc13 => "rc13",
            RcKind::Rc7 => "rc7",
            RcKind::Rc8 => "rc8",
        }
    }

    pub fn value_column_id(self) -> PreProcessedColumnId {
        PreProcessedColumnId { id: format!("mldsa_decomp_{}_value", self.name()) }
    }
}

/// Preprocessed value column `[0, 1, …, n−1, 0, 0, …]`.
pub fn gen_table_preprocessed(kind: RcKind) -> ColEval {
    let log_size = kind.log_size();
    let rows = 1usize << log_size;
    let n = kind.n_values();
    let values = (0..rows).map(|i| m31(if i < n { i as u32 } else { 0 })).collect();
    col_eval(log_size, values)
}

/// Multiplicity column: how many times each table value is consumed.
pub fn gen_table_multiplicities(kind: RcKind, uses: &[u32]) -> ColEval {
    let log_size = kind.log_size();
    let rows = 1usize << log_size;
    let n = kind.n_values();
    assert_eq!(uses.len(), n, "one multiplicity per table value");
    let values = (0..rows).map(|i| m31(if i < n { uses[i] } else { 0 })).collect();
    col_eval(log_size, values)
}

/// Interaction column for a table provider: `−mult / (z − value)` per packed row.
pub fn gen_table_interaction(
    kind: RcKind,
    multiplicity: &ColEval,
    relation: &RcRelation,
) -> (Vec<ColEval>, SecureField) {
    let log_size = kind.log_size();
    let value = gen_table_preprocessed(kind);
    let mut logup = LogupTraceGenerator::new(log_size);
    logup.col_from_fn(|vec_row| {
        let denom: PackedQM31 = relation.combine(&[value.data[vec_row]]);
        let numerator = -PackedQM31::from(multiplicity.data[vec_row]);
        (numerator, denom)
    });
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, claimed_sum)
}

/// A range-check table provider component.
#[derive(Clone)]
pub struct RcTableEval {
    pub kind: RcKind,
    pub relation: RcRelation,
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
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            core::slice::from_ref(&value),
        ));
        eval.finalize_logup();
        eval
    }
}

pub type RcTableComponent = FrameworkComponent<RcTableEval>;

/// Interaction-column count of a table provider (one batched logup column).
pub const RC_TABLE_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

/// Multiplicity accumulators for the four tables.
#[derive(Clone)]
pub struct RcUses {
    pub rc4: Vec<u32>,
    pub rc13: Vec<u32>,
    pub rc7: Vec<u32>,
    pub rc8: Vec<u32>,
}

impl RcUses {
    pub fn new() -> Self {
        Self {
            rc4: vec![0; 1 << 4],
            rc13: vec![0; 1 << 13],
            rc7: vec![0; 1 << 7],
            rc8: vec![0; 1 << 8],
        }
    }

    pub fn for_kind(&self, kind: RcKind) -> &[u32] {
        match kind {
            RcKind::Rc4 => &self.rc4,
            RcKind::Rc13 => &self.rc13,
            RcKind::Rc7 => &self.rc7,
            RcKind::Rc8 => &self.rc8,
        }
    }
}

impl Default for RcUses {
    fn default() -> Self {
        Self::new()
    }
}
