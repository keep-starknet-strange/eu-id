use crate::types::Column;
use crate::utils::random_m31_cell;
use num_traits::{One, Zero};
use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
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

    // ---- Class D multiplicity blinding (Q-015 §4b / p4c Class D) ----
    //
    // The committed multiplicity column of a range table leaks: each row's
    // count is a function of the private witness (which delta value the proof
    // looked up), and every proof-side opening of the column is a linear
    // functional over the full domain. Class D extends the table one log larger
    // and fills the new upper half with fresh random multiplicities over
    // RESERVED dummy keys `[field_size, 2·field_size)`. Those keys are
    // UNREACHABLE by honest consumers, which only ever look up values proven
    // `< field_size` (the membership lookup against the real `[0, N]` region is
    // exactly what forces that), so soundness is unaffected. Balance is
    // preserved by the intra-component cancelling `+is_dummy·mult` emit in the
    // eval: on a dummy row the two entries net `(−m + m)/(z − combine) = 0` for
    // ANY random `m`. The mirror of `stwo-p256`'s `BlindRangeCheckEval`.

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

    /// `log_size + 1`: the committed row count of the Class-D blinded table.
    pub fn blind_log_size(&self) -> u32 {
        self.log_size() + 1
    }

    /// Class-D preprocessed value column. Lower half is the real range
    /// `[0, N]` followed by the same zero padding as [`preprocessed_column`];
    /// upper half holds the reserved dummy keys `[field_size, 2·field_size)`.
    pub fn blind_preprocessed_column(&self) -> Column {
        let field_size = self.field_size();
        Column::new(
            CanonicCoset::new(self.blind_log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..=self.0)
                    .map(M31::from_u32_unchecked)
                    .chain((self.0 + 1..field_size).map(|_| M31::zero()))
                    .chain((field_size..2 * field_size).map(M31::from_u32_unchecked)),
            ),
        )
    }

    /// Class-D preprocessed `is_dummy` selector: `0` over the real lower half,
    /// `1` over the reserved dummy upper half.
    pub fn blind_dummy_column(&self) -> Column {
        let field_size = self.field_size();
        Column::new(
            CanonicCoset::new(self.blind_log_size()).circle_domain(),
            BaseColumn::from_iter(
                (0..field_size)
                    .map(|_| M31::zero())
                    .chain((0..field_size).map(|_| M31::one())),
            ),
        )
    }

    /// A [`BlindEval`] Class-D provider for this range, reading its own
    /// namespaced preprocessed columns.
    pub fn blind_eval(&self, relation: RangeCheckLookupElements) -> BlindEval {
        BlindEval {
            real_log_size: self.log_size(),
            relation,
            value_id: self.blind_value_id(),
            dummy_id: self.blind_dummy_id(),
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

    /// Class-D blinded multiplicity column over the `log_size + 1` domain: real
    /// counts on the lower half, fresh random blind cells on the reserved dummy
    /// upper half. The dummy cells are the mask; the [`BlindEval`]'s
    /// `+is_dummy·mult` twin makes any value there balance to zero.
    pub fn gen_blind_multiplicity_col(&self, values: &[Vec<M31>]) -> Column {
        let real = 1usize << self.log_size as usize;
        let blind_log_size = self.log_size + 1;
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

/// Class-D multiplicity-blinded range-table provider (Q-015 §4b / p4c Class D).
///
/// Identical to [`Eval`] but over the `real_log_size + 1` domain. Reads the
/// preprocessed value column (real range on the lower half, reserved dummy keys
/// on the upper half) and the `is_dummy` selector, then emits two entries per
/// row against the same relation and value:
/// - `-multiplicity` (the normal yield);
/// - `+is_dummy · multiplicity` (the cancelling twin).
///
/// On a real row (`is_dummy = 0`) only the `-multiplicity` yield fires — exactly
/// the unblinded table. On a dummy row the pair nets `0` for ANY random `m`, so
/// the blind multiplicities never touch the global balance. Both entries read
/// the same committed cell and the same preprocessed key, so there is no free
/// claimed-sum term. `is_dummy · multiplicity` is preprocessed × trace = degree
/// 2, within the `D ≤ 3` budget under `max_constraint_log_degree_bound =
/// log_size + 1`.
#[derive(Clone)]
pub struct BlindEval {
    pub real_log_size: u32,
    pub relation: RangeCheckLookupElements,
    pub value_id: PreProcessedColumnId,
    pub dummy_id: PreProcessedColumnId,
}

impl FrameworkEval for BlindEval {
    fn log_size(&self) -> u32 {
        self.real_log_size + 1
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.real_log_size + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(self.value_id.clone());
        let is_dummy = eval.get_preprocessed_column(self.dummy_id.clone());
        let multiplicity = eval.next_trace_mask();
        // Normal yield on every row.
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            -E::EF::from(multiplicity.clone()),
            std::slice::from_ref(&value),
        ));
        // Cancelling twin on dummy rows: nets `(−m + m)/(z − dummy) = 0` there,
        // and `+0` on real rows. Degree 2 (preprocessed × trace).
        eval.add_to_relation(RelationEntry::new(
            &self.relation,
            E::EF::from(is_dummy * multiplicity),
            &[value],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type BlindComponent = FrameworkComponent<BlindEval>;

#[cfg(test)]
mod class_d_tests {
    use super::*;
    use stwo::prover::backend::Column as _;

    /// Class-D: the blinded range table doubles the domain, keeps the real range
    /// `[0, N]` (then zero padding) on the lower half, and reserves the
    /// unreachable dummy keys `[field_size, 2·field_size)` on the upper half;
    /// `is_dummy` selects exactly the upper half.
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
        for i in 0..field_size as usize {
            let row = field_size as usize + i;
            assert_eq!(dummy.values.at(row).0, 1, "upper row {row} must be a dummy");
            assert!(
                value.values.at(row).0 >= field_size,
                "dummy key must be unreachable (>= field_size)"
            );
        }
    }

    /// Class-D: the blinded multiplicity column carries real counts on the lower
    /// half and fresh randomness on the reserved dummy upper half, so its
    /// committed openings mask the real counts.
    #[test]
    fn blinded_multiplicity_masks_real_counts_with_fresh_dummies() {
        let rc = RangeCheck(31);
        let claim = rc.claim();
        let real = 1usize << claim.log_size;
        let uses = vec![M31::from_u32_unchecked(7)];

        let first = claim.gen_blind_multiplicity_col(std::slice::from_ref(&uses));
        let second = claim.gen_blind_multiplicity_col(&[uses]);
        assert_eq!(first.values.at(7).0, 1, "used value 7 has count 1");

        let upper_first: Vec<u32> = (real..1 << (claim.log_size + 1))
            .map(|i| first.values.at(i).0)
            .collect();
        let upper_second: Vec<u32> = (real..1 << (claim.log_size + 1))
            .map(|i| second.values.at(i).0)
            .collect();
        assert_ne!(
            upper_first, upper_second,
            "dummy multiplicities must be fresh per generation"
        );
    }
}
