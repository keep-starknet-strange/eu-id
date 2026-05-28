use crate::nat::types::PublicInput;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

relation!(NatTableElements, 1);

pub(crate) fn acceptable_col_id(acceptable: &[u32]) -> PreProcessedColumnId {
    let ids: Vec<String> = acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/{}", ids.join(",")),
    }
}

#[derive(Clone)]
pub(crate) struct NatTableEval {
    pub public: PublicInput,
    pub lookup_elements: NatTableElements,
}

pub(crate) type NatTableComponent = FrameworkComponent<NatTableEval>;

impl FrameworkEval for NatTableEval {
    fn log_size(&self) -> u32 {
        self.public.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let acc_nat_code = eval.get_preprocessed_column(acceptable_col_id(&self.public.acceptable));
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
