//! Constraint side of the range-check providers.

use stwo::core::fields::m31::M31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

use super::{
    range_check_dummy_column_id, range_check_value_column_id, signed_carry_active_column_id,
    signed_carry_value_column_id, RangeCheckRelation,
};

/// Provider for the unary range table `0..2^log_size`.
///
/// The preprocessed column [`range_check_value_column_id`] must be populated
/// with `[0, 1, …, 2^log_size − 1]` by
/// [`super::RangeCheckClaim::gen_preprocessed_column`]. This component
/// does not constrain the table contents.
#[derive(Clone, Debug)]
pub struct RangeCheckEval {
    pub relation: RangeCheckRelation,
    pub log_size: u32,
}

impl RangeCheckEval {
    pub fn new(relation: RangeCheckRelation, log_size: u32) -> Self {
        Self { relation, log_size }
    }
}

impl FrameworkEval for RangeCheckEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(range_check_value_column_id(self.log_size));
        let multiplicity = eval.next_trace_mask();
        eval.add_to_relation(RelationEntry::base(&self.relation, -multiplicity, &[value]));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type RangeCheckComponent = FrameworkComponent<RangeCheckEval>;

/// Provides a Class-D multiplicity-blinded range table.
///
/// Uses a committed domain one log unit larger than [`RangeCheckEval`].
///
/// The lower half contains the real range `[0, 2^real)`.
/// The upper half contains reserved dummy keys.
/// The preprocessed `is_dummy` selector marks the upper half.
/// The multiplicity column contains real counts and random dummy cells.
///
/// ## LogUp (balance preserved, blind cells free)
///
/// ONE gated entry per row against the relation: numerator
/// `-(1 − is_dummy) · multiplicity` at the same `value`.
///
/// A real row uses numerator `-multiplicity`.
/// A dummy row uses numerator zero for all multiplicity values.
/// Thus, random dummy values do not change the global balance.
/// One gated fraction replaces two canceling fractions.
///
/// ## Soundness (reservation argument)
///
/// Consumers emit only values less than `2^real`.
/// Thus, no consumer can use a dummy key.
/// Preprocessed value `is_dummy` forces a zero numerator in the complete dummy region.
/// The resulting balance equals the balance of the unprotected table.
/// The committed key and preprocessed gate prevent a free claimed-sum term.
///
/// ## Degree
///
/// `(1 − is_dummy) · multiplicity` is preprocessed × trace = degree 2, within
/// the `D ≤ 3` budget under `max_constraint_log_degree_bound = log_size + 1`.
#[derive(Clone, Debug)]
pub struct BlindRangeCheckEval {
    pub relation: RangeCheckRelation,
    /// The real table width. The committed domain is `real_log_size + 1`.
    pub real_log_size: u32,
    /// Preprocessed value-column id (namespaced tables pass their own).
    pub value_id: PreProcessedColumnId,
    /// Preprocessed is_dummy selector id (namespaced tables pass their own).
    pub dummy_id: PreProcessedColumnId,
}

impl BlindRangeCheckEval {
    /// Reference table using the generic `p256_range{real}_value` /
    /// `p256_range{real}_dummy` preprocessed ids.
    pub fn new(relation: RangeCheckRelation, real_log_size: u32) -> Self {
        Self {
            relation,
            real_log_size,
            value_id: range_check_value_column_id(real_log_size),
            dummy_id: range_check_dummy_column_id(real_log_size),
        }
    }
}

impl FrameworkEval for BlindRangeCheckEval {
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
        // Single gated yield: `-(1 − is_dummy)·multiplicity`. `-multiplicity` on
        // real rows (is_dummy = 0), identically `0` on dummy rows (is_dummy = 1)
        // for any committed `m`. Degree 2 (preprocessed × trace).
        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_to_relation(RelationEntry::base(
            &self.relation,
            -((one - is_dummy) * multiplicity),
            &[value],
        ));
        eval.finalize_logup();
        eval
    }
}

pub type BlindRangeCheckComponent = FrameworkComponent<BlindRangeCheckEval>;

/// Provider for a centered signed-carry table padded to a power of two.
///
/// Constraints:
/// 1. `active · (active − 1) = 0` — `active` is boolean.
/// 2. `(1 − active) · multiplicity = 0` — padding multiplicity is zero, so
///    a provide against a padding row cannot service any use.
#[derive(Clone, Debug)]
pub struct SignedCarryRangeEval {
    pub relation: RangeCheckRelation,
    pub log_size: u32,
    pub equation_name: String,
}

impl SignedCarryRangeEval {
    pub fn new(
        relation: RangeCheckRelation,
        log_size: u32,
        equation_name: impl Into<String>,
    ) -> Self {
        Self {
            relation,
            log_size,
            equation_name: equation_name.into(),
        }
    }

    pub fn value_column_id(&self) -> PreProcessedColumnId {
        signed_carry_value_column_id(&self.equation_name)
    }

    pub fn active_column_id(&self) -> PreProcessedColumnId {
        signed_carry_active_column_id(&self.equation_name)
    }
}

impl FrameworkEval for SignedCarryRangeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let value = eval.get_preprocessed_column(self.value_column_id());
        let active = eval.get_preprocessed_column(self.active_column_id());
        let multiplicity = eval.next_trace_mask();
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint((one - active) * multiplicity.clone());
        eval.add_to_relation(RelationEntry::base(&self.relation, -multiplicity, &[value]));
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type SignedCarryRangeComponent = FrameworkComponent<SignedCarryRangeEval>;

#[cfg(test)]
mod tests {
    use super::super::{RANGE11_BITS, RANGE13_BITS, RANGE7_BITS, RANGE9_BITS};
    use super::*;
    use num_traits::Zero;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::TraceLocationAllocator;

    fn dummy() -> RangeCheckRelation {
        RangeCheckRelation::dummy()
    }

    #[test]
    fn range_check_eval_reports_its_log_size() {
        for bits in [RANGE13_BITS, RANGE11_BITS, RANGE9_BITS, RANGE7_BITS] {
            assert_eq!(RangeCheckEval::new(dummy(), bits).log_size(), bits);
        }
    }

    #[test]
    fn range_check_component_allocates_one_preprocessed_column() {
        let eval = RangeCheckEval::new(dummy(), RANGE13_BITS);
        let preprocessed = [range_check_value_column_id(RANGE13_BITS)];
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed);

        let component = RangeCheckComponent::new(&mut allocator, eval, SecureField::zero());

        assert_eq!(component.preprocessed_column_indices().len(), 1);
        assert_eq!(component.trace_locations().len(), 3);
    }

    #[test]
    fn signed_carry_provider_allocates_value_and_active_columns() {
        let eval = SignedCarryRangeEval::new(dummy(), 3, "test");
        let preprocessed = [eval.value_column_id(), eval.active_column_id()];
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed);

        let component = SignedCarryRangeComponent::new(&mut allocator, eval, SecureField::zero());

        assert_eq!(component.preprocessed_column_indices().len(), 2);
        assert_eq!(component.trace_locations().len(), 3);
    }
}
