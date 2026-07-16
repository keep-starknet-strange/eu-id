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
/// [`super::RangeCheckClaim::gen_preprocessed_column`]; this component
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

/// Class-D multiplicity-blinded range-table provider (Q-015 §4b / p4c Class D).
///
/// Identical to [`RangeCheckEval`] but over a domain one log larger. The
/// preprocessed `value` column is `[0, 1, …, 2^(real+1) − 1]` — the lower half
/// is the real range `[0, 2^real)`, the upper half is the reserved dummy keys
/// `[2^real, 2^(real+1))` no honest consumer can emit. The preprocessed
/// `is_dummy` selector is `1` over the dummy region. The committed
/// multiplicity column carries real counts on the lower half and fresh random
/// blind cells on the upper half.
///
/// ## LogUp (balance preserved, blind cells free)
///
/// ONE gated entry per row against the relation: numerator
/// `-(1 − is_dummy) · multiplicity` at the same `value`.
///
/// On a real row (`is_dummy = 0`) the numerator is `-multiplicity`, exactly as
/// the unblinded table. On a dummy row (`is_dummy = 1`) the numerator is
/// identically `0` for ANY `m`, so the random blind multiplicities never touch
/// the global balance while staying in the committed multiplicity column as the
/// mask. This replaces the earlier cancelling PAIR (`-mult` and `+is_dummy·mult`)
/// with a single fraction at half the interaction/quotient cost.
///
/// ## Soundness (reservation argument)
///
/// Honest consumers only ever emit values proven `< 2^real` (that is the whole
/// point of a `[0, 2^real)` range check), so no honest use can land on a dummy
/// key. The dummy region therefore cannot service any consumer; it exists only
/// to hold the mask. `is_dummy` is PREPROCESSED (trusted), so a malicious prover
/// cannot un-gate a dummy row to provide a real key: the numerator is forced to
/// `0` over the whole dummy region. The resulting balance is exactly the
/// unblinded table's, and both key and gate come from committed/preprocessed
/// data, so there is no free claimed-sum term (the P4b blind_claim-hole caution).
///
/// ## Degree
///
/// `(1 − is_dummy) · multiplicity` is preprocessed × trace = degree 2, within
/// the `D ≤ 3` budget under `max_constraint_log_degree_bound = log_size + 1`.
#[derive(Clone, Debug)]
pub struct BlindRangeCheckEval {
    pub relation: RangeCheckRelation,
    /// The real table width; the committed domain is `real_log_size + 1`.
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
