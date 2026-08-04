use crate::nat::eval::{NationalityComponent, NationalityEval};
use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::{allowed_col_id, first_col_id, row_index_col_id};
use crate::nat::table::{
    acceptable_col_id, acceptable_dummy_col_id, signed_valid_col_id, signed_valid_dummy_col_id,
    NatTableComponent, NatTableEval,
};
use crate::nat::types::PublicInput;
use air_core::relations::FieldBytesRelation;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

/// Preprocessed column ids this predicate contributes, in commit order. The
/// orchestrator concatenates these to seed the shared allocator.
pub fn preprocessed_column_ids(public: &PublicInput) -> Vec<PreProcessedColumnId> {
    vec![
        allowed_col_id(),
        row_index_col_id(),
        first_col_id(),
        // Class-D blinded accepted-set table: value + is_dummy.
        acceptable_col_id(public),
        acceptable_dummy_col_id(public),
        signed_valid_col_id(),
        signed_valid_dummy_col_id(),
    ]
}

#[allow(clippy::too_many_arguments)]
pub fn components(
    allocator: &mut TraceLocationAllocator,
    public: &PublicInput,
    lookup_elements: LookupElements,
    nat_binding: Option<FieldBytesRelation>,
    nat_claimed_sum: QM31,
    table_claimed_sum: QM31,
    claim_mask_beta: Option<QM31>,
) -> (NationalityComponent, NatTableComponent) {
    let nat_component = NationalityComponent::new(
        allocator,
        NationalityEval {
            lookup_elements: lookup_elements.clone(),
            nat_binding,
            claim_mask_beta,
        },
        nat_claimed_sum,
    );

    let table_component = NatTableComponent::new(
        allocator,
        NatTableEval {
            public: public.clone(),
            accepted_elements: lookup_elements.nat_table,
            signed_valid_elements: lookup_elements.signed_valid,
            claim_mask_beta,
        },
        table_claimed_sum,
    );

    (nat_component, table_component)
}
