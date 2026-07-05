use crate::nat::types::{PublicInput, PublicInputKind};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

relation!(NatTableElements, 1);

/// Preprocessed accepted-set table id. It encodes both the code space (`kind`)
/// and the exact accepted codes, so a preprocessed column with this id is the
/// same fixed table for every module that shares it — the dedup/fingerprint
/// guard rejects any two modules that reuse the id with different content.
pub fn acceptable_col_id(public: &PublicInput) -> PreProcessedColumnId {
    let kind = match public.kind {
        PublicInputKind::IsoNumeric => "iso",
        PublicInputKind::Alpha2 => "alpha2",
    };
    let ids: Vec<String> = public.acceptable.iter().map(|c| c.to_string()).collect();
    PreProcessedColumnId {
        id: format!("nat/acceptable/{kind}/{}", ids.join(",")),
    }
}

#[derive(Clone)]
pub struct NatTableEval {
    pub public: PublicInput,
    pub lookup_elements: NatTableElements,
}

pub type NatTableComponent = FrameworkComponent<NatTableEval>;

impl FrameworkEval for NatTableEval {
    fn log_size(&self) -> u32 {
        self.public.log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let acc_nat_code = eval.get_preprocessed_column(acceptable_col_id(&self.public));
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
