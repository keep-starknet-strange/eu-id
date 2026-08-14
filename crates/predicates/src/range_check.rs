use crate::types::Column;
use crate::utils::random_m31_cell;
use air_core::claim_mask::{add_claim_mask_fraction, CLAIM_MASK_MIN_LOG_SIZE};
use num_traits::{One, Zero};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

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
        Claim {
            log_size: self.log_size(),
        }
    }

    pub fn eval(&self, relation: RangeCheckLookupElements) -> Eval {
        Eval {
            claim: self.claim(),
            relation,
            relation_col_id: self.id(),
        }
    }

    // Class-D multiplicity blinding.
    //
    // A committed range multiplicity column can reveal witness-dependent counts.
    // Class D extends the table to a masking domain.
    // Its reserved suffix contains fresh random multiplicities over dummy keys.
    // Dummy keys start at `field_size`.
    // Honest consumers use only values below `field_size`.
    // The trusted `is_dummy` selector gives each dummy row a zero numerator.
    // Thus, the random suffix does not change the balance.

    /// The blinded (Class-D) preprocessed value column id. Namespaced apart
    /// from [`id`](Self::id) so a blinded and a plain table of the same range
    /// never alias in the preprocessed dedup.
    pub fn blind_value_id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("range_check_blind_value_[0, {}]", self.0),
        }
    }

    /// The blinded (Class-D) preprocessed `is_dummy` selector id.
    pub fn blind_dummy_id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("range_check_blind_dummy_[0, {}]", self.0),
        }
    }

    /// The committed row count of the Class-D blinded table. Claim-masked
    /// components need at least 512 rows, so small ranges extend their reserved
    /// dummy region instead of changing the reachable real range.
    pub fn blind_log_size(&self) -> u32 {
        (self.log_size() + 1).max(CLAIM_MASK_MIN_LOG_SIZE)
    }

    /// Class-D preprocessed value column. The reachable prefix is the real range
    /// `[0, N]` followed by the same zero padding as [`Self::preprocessed_column`].
    /// remaining rows hold reserved dummy keys starting at `field_size`.
    pub fn blind_preprocessed_column(&self) -> Column {
        let field_size = self.field_size();
        let total_size = 1u32 << self.blind_log_size();
        Column::new(
            CanonicCoset::new(self.blind_log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..=self.0)
                    .map(M31::from_u32_unchecked)
                    .chain((self.0 + 1..field_size).map(|_| M31::zero()))
                    .chain((field_size..total_size).map(M31::from_u32_unchecked)),
            ),
        )
    }

    /// Class-D preprocessed `is_dummy` selector: `0` over the reachable table
    /// capacity and `1` over every reserved dummy row.
    pub fn blind_dummy_column(&self) -> Column {
        let field_size = self.field_size();
        let total_size = 1u32 << self.blind_log_size();
        Column::new(
            CanonicCoset::new(self.blind_log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..field_size)
                    .map(|_| M31::zero())
                    .chain((field_size..total_size).map(|_| M31::one())),
            ),
        )
    }

    /// A [`BlindEval`] Class-D provider for this range, reading its own
    /// namespaced preprocessed columns.
    pub fn blind_eval(&self, relation: RangeCheckLookupElements) -> BlindEval {
        BlindEval {
            log_size: self.blind_log_size(),
            relation,
            value_id: self.blind_value_id(),
            dummy_id: self.blind_dummy_id(),
            claim_mask_beta: None,
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

    /// Class-D blinded multiplicity column over the padded blinded domain: real
    /// counts in the reachable range capacity, fresh random cells on every
    /// reserved dummy row. The dummy cells are the mask. The [`BlindEval`]'s
    /// `+is_dummy·mult` twin makes any value there balance to zero.
    pub fn gen_blind_multiplicity_col(&self, values: &[Vec<M31>]) -> Column {
        let real = 1usize << self.log_size as usize;
        let blind_log_size = (self.log_size + 1).max(CLAIM_MASK_MIN_LOG_SIZE);
        let mut res = vec![M31::zero(); 1 << blind_log_size as usize];

        for col in values {
            for value in col {
                res[value.0 as usize] += M31::one();
            }
        }
        for slot in res.iter_mut().skip(real) {
            *slot = random_m31_cell();
        }

        CircleEvaluation::new(
            CanonicCoset::new(blind_log_size).circle_domain(),
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
            &[preprocessed],
        ));

        eval.finalize_logup();
        eval
    }
}

pub type Component = FrameworkComponent<Eval>;

/// Provides a Class-D multiplicity-blinded range table.
///
/// Evaluates the padded blinded domain.
///
/// The reachable prefix contains the real range.
/// The suffix contains reserved dummy keys.
/// Each row emits one gated relation entry.
/// Its numerator is `-(1 − is_dummy) · multiplicity`.
///
/// A real row has numerator `-multiplicity`.
/// This is the same value as the unblinded table.
/// A dummy row has numerator `0` for every random multiplicity.
///
/// Thus, blind multiplicities do not change the global balance.
/// The trusted `is_dummy` selector prevents a prover from activating a dummy row.
/// Both the key and gate use committed or preprocessed data.
/// The gated product has degree 2 and stays within the degree-3 budget.
#[derive(Clone)]
pub struct BlindEval {
    pub log_size: u32,
    pub relation: RangeCheckLookupElements,
    pub value_id: PreProcessedColumnId,
    pub dummy_id: PreProcessedColumnId,
    pub claim_mask_beta: Option<QM31>,
}

impl BlindEval {
    pub fn with_claim_mask(mut self, beta: Option<QM31>) -> Self {
        self.claim_mask_beta = beta;
        self
    }
}

impl FrameworkEval for BlindEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(self.value_id.clone());
        let is_dummy = eval.get_preprocessed_column(self.dummy_id.clone());
        let multiplicity = eval.next_trace_mask();
        // Single gated yield `-(1 − is_dummy)·multiplicity`: `-m` on real rows
        // (is_dummy = 0), identically `0` on dummy rows for any committed `m`.
        // Degree 2 (preprocessed × trace).
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from((one - is_dummy) * multiplicity),
            &[value],
        ));
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup();
        eval
    }
}

pub type BlindComponent = FrameworkComponent<BlindEval>;

#[cfg(test)]
mod class_d_tests {
    use super::*;
    use stwo::prover::backend::Column as _;

    /// Class-D: the blinded range table keeps `[0, N]` (then zero padding) in
    /// the reachable prefix and reserves every remaining row for unreachable
    /// dummy keys. `is_dummy` selects exactly that suffix.
    #[test]
    fn blinded_range_reserves_unreachable_dummy_keys() {
        let rc = RangeCheck(31);
        let field_size = rc.field_size();
        let value = rc.blind_preprocessed_column();
        let dummy = rc.blind_dummy_column();

        assert_eq!(value.domain.log_size(), rc.blind_log_size());
        // Real region: values 0..=31 then zero padding, is_dummy = 0.
        for v in 0..=rc.0 {
            assert_eq!(value.values.at(v as usize).0, v);
        }
        for i in 0..field_size as usize {
            assert_eq!(dummy.values.at(i).0, 0, "real row {i} must not be a dummy");
        }
        // Dummy region: keys field_size..2·field_size, unreachable (honest uses
        // are all < field_size), is_dummy = 1.
        for row in field_size as usize..1 << rc.blind_log_size() {
            assert_eq!(dummy.values.at(row).0, 1, "upper row {row} must be a dummy");
            assert!(
                value.values.at(row).0 >= field_size,
                "dummy key must be unreachable (>= field_size)"
            );
        }
        assert!(rc.blind_log_size() >= CLAIM_MASK_MIN_LOG_SIZE);
    }

    /// Confirms that the blinded multiplicity column masks real counts.
    ///
    /// The reachable prefix contains real counts.
    /// The dummy suffix contains fresh random cells.
    #[test]
    fn blinded_multiplicity_masks_real_counts_with_fresh_dummies() {
        let rc = RangeCheck(31);
        let claim = rc.claim();
        let real = 1usize << claim.log_size;
        let uses = vec![M31::from_u32_unchecked(7)];

        let first = claim.gen_blind_multiplicity_col(std::slice::from_ref(&uses));
        let second = claim.gen_blind_multiplicity_col(&[uses]);
        assert_eq!(first.values.at(7).0, 1, "used value 7 has count 1");

        let upper_first: Vec<u32> = (real..1 << rc.blind_log_size())
            .map(|i| first.values.at(i).0)
            .collect();
        let upper_second: Vec<u32> = (real..1 << rc.blind_log_size())
            .map(|i| second.values.at(i).0)
            .collect();
        assert_ne!(
            upper_first, upper_second,
            "dummy multiplicities must be fresh per generation"
        );
    }
}
