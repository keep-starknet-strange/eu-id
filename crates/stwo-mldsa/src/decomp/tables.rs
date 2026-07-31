//! Range-check table providers for `mldsa_decomp`: `Rc4` (2^4, w1/w1'), `Rc13`
//! (2^13), `Rc7` (2^7), `Rc8` (2^8). Same provider shape as `coeffs::tables`
//! (preprocessed value column `0..2^bits` + witness multiplicity column, yielding
//! `−mult / (z − value)`); one provider component per relation instance.

use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, Relation, RelationEntry};

use super::relations::RcRelation;
use crate::air_util::{
    gen_value_table_interaction, gen_value_table_multiplicities, gen_value_table_preprocessed,
    table_log_size, value_table_preprocessed_id, ColEval,
};

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
        table_log_size(self.n_values())
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
        value_table_preprocessed_id(self.log_size(), self.n_values())
    }
}

/// Preprocessed value column `[0, 1, …, n−1, 0, 0, …]`.
pub fn gen_table_preprocessed(kind: RcKind) -> ColEval {
    gen_value_table_preprocessed(kind.log_size(), kind.n_values())
}

/// Multiplicity column: how many times each table value is consumed.
pub fn gen_table_multiplicities(kind: RcKind, uses: &[u32]) -> ColEval {
    gen_value_table_multiplicities(kind.log_size(), kind.n_values(), uses)
}

/// Interaction column for a table provider: `−mult / (z − value)` per packed row.
pub fn gen_table_interaction(
    kind: RcKind,
    multiplicity: &ColEval,
    relation: &RcRelation,
) -> (Vec<ColEval>, SecureField) {
    gen_value_table_interaction(
        kind.log_size(),
        gen_table_preprocessed(kind),
        multiplicity,
        |value| relation.combine(&[value]),
    )
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
