use crate::types::Column;
use num_traits::{One, Zero};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

relation!(RangeCheckLookupElements, 1);

#[derive(Debug, Clone)]
pub struct RangeCheck(pub u32);

impl RangeCheck {

    pub fn field_size(&self) -> u32 {
        (self.0 + 1).next_power_of_two()
    }

    pub fn log_size(&self) -> u32 {
        self.field_size().ilog2()
    }

    pub fn preprocessed_column(&self) -> Column {
        let field_size = self.field_size();
        Column::new(
            CanonicCoset::new(self.log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..=self.0)
                    .map(M31::from_u32_unchecked)
                    .chain((self.0 + 1..field_size).map(|_| M31::zero())),
            ),
        )
    }

    pub fn id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("range_check_[0, {}]", self.0),
        }
    }

    pub fn claim(&self) -> Claim {
        Claim { log_size: self.log_size() }
    }

    pub fn eval(&self, relation: RangeCheckLookupElements) -> Eval {
        Eval {
            claim: self.claim(),
            relation,
            relation_col_id: self.id(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Claim {
    pub log_size: u32,
}

impl Claim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }

    pub fn gen_multiplicity_col(&self, values: &[Vec<M31>]) -> Column {
        let mut res = vec![M31::zero(); 1 << self.log_size as usize];

        for col in values {
            for value in col {
                res[value.0 as usize] += M31::one();
            }
        }

        CircleEvaluation::new(
            CanonicCoset::new(self.log_size).circle_domain(),
            BaseColumn::from_iter(res),
        )
    }
}

pub struct Eval {
    pub claim: Claim,
    pub relation: RangeCheckLookupElements,
    pub relation_col_id: PreProcessedColumnId,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let multiplicity = eval.next_trace_mask();
        let preprocessed = eval.get_preprocessed_column(self.relation_col_id.clone());

        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity),
            &[preprocessed]
        ));

        eval.finalize_logup();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;
