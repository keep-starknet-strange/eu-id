use crate::nat::eval::{NationalityComponent, NationalityEval};
use crate::nat::lookup_elements::LookupElements;
use crate::nat::table::{acceptable_col_id, NatTableComponent, NatTableEval};
use crate::nat::types::PublicInput;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::TraceLocationAllocator;

fn make_allocator(public: &PublicInput) -> TraceLocationAllocator {
    TraceLocationAllocator::new_with_preprocessed_columns(&[acceptable_col_id(&public.acceptable)])
}

pub fn components(
    public: &PublicInput,
    lookup_elements: LookupElements,
    nat_claimed_sum: QM31,
    table_claimed_sum: QM31,
) -> (NationalityComponent, NatTableComponent) {
    let mut allocator = make_allocator(public);

    let nat_component = NationalityComponent::new(
        &mut allocator,
        NationalityEval {
            lookup_elements: lookup_elements.clone(),
        },
        nat_claimed_sum,
    );

    let table_component = NatTableComponent::new(
        &mut allocator,
        NatTableEval {
            public: public.clone(),
            lookup_elements: lookup_elements.nat_table,
        },
        table_claimed_sum,
    );

    (nat_component, table_component)
}
