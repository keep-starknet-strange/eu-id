//! Range-check table providers for `sampleinball_fsm`: `Rc8` (2^8, index/byte
//! margins + sorted `daddr`), `Rc9` (2^9, coefficient `c+1` bound), and `Rc11`
//! (2^11, offline-memory timestamp diff `dts` < N+3τ+N = 659). Same provider
//! shape as `decomp::tables`.

use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, Relation, RelationEntry};

use super::relations::RcRelation;
use crate::air_util::{
    gen_value_table_interaction, gen_value_table_multiplicities, gen_value_table_preprocessed,
    table_log_size, value_table_preprocessed_id, ColEval,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcKind {
    Rc8,
    Rc9,
    Rc11,
}

impl RcKind {
    pub const ALL: [RcKind; 3] = [RcKind::Rc8, RcKind::Rc9, RcKind::Rc11];

    pub const fn n_values(self) -> usize {
        match self {
            RcKind::Rc8 => 1 << 8,
            RcKind::Rc9 => 1 << 9,
            RcKind::Rc11 => 1 << 11,
        }
    }

    pub const fn log_size(self) -> u32 {
        table_log_size(self.n_values())
    }

    pub fn name(self) -> &'static str {
        match self {
            RcKind::Rc8 => "rc8",
            RcKind::Rc9 => "rc9",
            RcKind::Rc11 => "rc11",
        }
    }

    pub fn value_column_id(self) -> PreProcessedColumnId {
        value_table_preprocessed_id(self.log_size(), self.n_values())
    }
}

pub fn gen_table_preprocessed(kind: RcKind) -> ColEval {
    gen_value_table_preprocessed(kind.log_size(), kind.n_values())
}

pub fn gen_table_multiplicities(kind: RcKind, uses: &[u32]) -> ColEval {
    gen_value_table_multiplicities(kind.log_size(), kind.n_values(), uses)
}

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

pub const RC_TABLE_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

#[derive(Clone)]
pub struct RcUses {
    pub rc8: Vec<u32>,
    pub rc9: Vec<u32>,
    pub rc11: Vec<u32>,
}

impl RcUses {
    pub fn new() -> Self {
        Self {
            rc8: vec![0; 1 << 8],
            rc9: vec![0; 1 << 9],
            rc11: vec![0; 1 << 11],
        }
    }

    pub fn for_kind(&self, kind: RcKind) -> &[u32] {
        match kind {
            RcKind::Rc8 => &self.rc8,
            RcKind::Rc9 => &self.rc9,
            RcKind::Rc11 => &self.rc11,
        }
    }
}

impl Default for RcUses {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_value_tables_share_one_preprocessed_id() {
        assert_eq!(
            RcKind::Rc8.value_column_id(),
            crate::decomp::tables::RcKind::Rc8.value_column_id()
        );
        assert_ne!(RcKind::Rc8.value_column_id(), RcKind::Rc9.value_column_id());
    }
}
