use crate::types::Trace;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::Column;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

/// Minimum log_size required by the SIMD backend (16 lanes).
const MIN_LOG_SIZE: u32 = 4;

relation!(NatTableElements, 1);

pub(crate) fn table_log_size(acceptable: &[u32]) -> u32 {
    let padded = (acceptable.len() as u32).next_power_of_two();
    padded.ilog2().max(MIN_LOG_SIZE)
}

pub(crate) fn acceptable_col_id(acceptable: &[u32]) -> PreProcessedColumnId {
    let ids: Vec<String> = acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/{}", ids.join(",")),
    }
}

pub(crate) fn generate_acceptable_table(acceptable: &[u32]) -> Trace {
    let log_size = table_log_size(acceptable);
    let total_size = 1 << log_size;
    let domain = CanonicCoset::new(log_size).circle_domain();

    let mut col = BaseColumn::zeros(total_size);
    for (i, &code) in acceptable.iter().enumerate() {
        col.set(i, M31::from_u32_unchecked(code));
    }
    // Padding rows remain 0 — no valid ISO code is 0, so they are never matched.

    vec![CircleEvaluation::new(domain, col)]
}

#[derive(Clone)]
pub(crate) struct NatTableEval {
    pub acceptable: Vec<u32>,
    pub lookup_elements: NatTableElements,
}

pub(crate) type NatTableComponent = FrameworkComponent<NatTableEval>;

impl FrameworkEval for NatTableEval {
    fn log_size(&self) -> u32 {
        table_log_size(&self.acceptable)
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let acc_nat_code = eval.get_preprocessed_column(acceptable_col_id(&self.acceptable));
        let mult = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::from(mult),
            &[acc_nat_code],
        ));
        eval.finalize_logup();
        eval
    }
}
