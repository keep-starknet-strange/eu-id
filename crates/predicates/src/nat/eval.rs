use crate::nat::table::NatTableElements;
use crate::nat::witness::WitnessData;
use num_traits::One;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

#[derive(Clone)]
pub(super) struct NationalityEval {
    pub lookup_elements: NatTableElements,
}

pub(super) type NationalityComponent = FrameworkComponent<NationalityEval>;

impl FrameworkEval for NationalityEval {
    fn log_size(&self) -> u32 {
        WitnessData::log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        WitnessData::log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let nationality = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            E::EF::one(),
            &[nationality],
        ));
        eval.finalize_logup();
        eval
    }
}
