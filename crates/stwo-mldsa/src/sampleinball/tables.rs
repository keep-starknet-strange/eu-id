//! Range-check table providers for `sampleinball_fsm`: `Rc8` (2^8, index/byte
//! margins + sorted `daddr`), `Rc9` (2^9, ternary `{0,1,2}` membership), and
//! `Rc11` (2^11, offline-memory timestamp diff `dts` < N+3τ+N = 659). Same
//! provider shape as `decomp::tables`.

use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
};

use super::relations::RcRelation;
use crate::air_util::{col_eval, m31, ColEval};

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
            RcKind::Rc8 => "rc8",
            RcKind::Rc9 => "rc9",
            RcKind::Rc11 => "rc11",
        }
    }

    pub fn value_column_id(self) -> PreProcessedColumnId {
        PreProcessedColumnId { id: format!("mldsa_sib_{}_value", self.name()) }
    }
}

pub fn gen_table_preprocessed(kind: RcKind) -> ColEval {
    let log_size = kind.log_size();
    let rows = 1usize << log_size;
    let n = kind.n_values();
    let values = (0..rows).map(|i| m31(if i < n { i as u32 } else { 0 })).collect();
    col_eval(log_size, values)
}

pub fn gen_table_multiplicities(kind: RcKind, uses: &[u32]) -> ColEval {
    let log_size = kind.log_size();
    let rows = 1usize << log_size;
    let n = kind.n_values();
    assert_eq!(uses.len(), n, "one multiplicity per table value");
    let values = (0..rows).map(|i| m31(if i < n { uses[i] } else { 0 })).collect();
    col_eval(log_size, values)
}

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
    logup.finalize_last()
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

pub type RcTableComponent = FrameworkComponent<RcTableEval>;

pub const RC_TABLE_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;

#[derive(Clone)]
pub struct RcUses {
    pub rc8: Vec<u32>,
    pub rc9: Vec<u32>,
    pub rc11: Vec<u32>,
}

impl RcUses {
    pub fn new() -> Self {
        Self { rc8: vec![0; 1 << 8], rc9: vec![0; 1 << 9], rc11: vec![0; 1 << 11] }
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
