use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::witness::WitnessData;
use crate::age::types::PublicInput;
use crate::utils::field_const;
use air_core::relations::{field_id, FieldBytesRelation};
use num_traits::One;
use stwo::core::fields::m31::BaseField;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

#[derive(Clone)]
pub struct AgeRangeCheckEval {
    pub(super) public: PublicInput,
    pub(super) lookup_elements: LookupElements,
    /// The shared credential-field channel, when the DOB↔credential binding is
    /// wired (`docs/ROADMAP_E2E` §6.6). `None` for a standalone age proof — then
    /// this component is byte-for-byte the unbound predicate and stays internally
    /// balanced. `Some(relation)` adds the three binding columns, the byte↔packed
    /// reconciliation, and the four DOB-byte *require* terms.
    pub(super) dob_binding: Option<FieldBytesRelation>,
}

impl FrameworkEval for AgeRangeCheckEval {
    fn log_size(&self) -> u32 {
        WitnessData::log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        WitnessData::log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let birth_day = eval.next_trace_mask();
        let birth_month = eval.next_trace_mask();
        let birth_year = eval.next_trace_mask();
        let max_days = eval.next_trace_mask();

        let day_delta = eval.next_trace_mask();
        let month_delta = eval.next_trace_mask();
        let year_delta = eval.next_trace_mask();
        let day_borrow = eval.next_trace_mask();
        let month_borrow = eval.next_trace_mask();

        // Credential-field binding columns (§6.6). Read here, immediately after
        // the base witness columns, so they occupy this component's trace slots
        // `9..12` — the order the witness generator commits them and the
        // `air_core` allocator assigns. The base-value clones are captured before
        // the statement constraints below consume `birth_*`.
        let dob_binding = self.dob_binding.as_ref().map(|relation| {
            let bind_active = eval.next_trace_mask();
            let year_hi = eval.next_trace_mask();
            let year_lo = eval.next_trace_mask();
            (
                relation,
                bind_active,
                year_hi,
                year_lo,
                birth_year.clone(),
                birth_month.clone(),
                birth_day.clone(),
            )
        });

        eval.add_constraint(day_borrow.clone() * (field_const::<E>(1) - day_borrow.clone()));
        eval.add_constraint(month_borrow.clone() * (field_const::<E>(1) - month_borrow.clone()));

        let cutoff = self.public.cutoff_date();

        eval.add_constraint(
            field_const::<E>(cutoff.day) - birth_day.clone()
                + field_const::<E>(32) * day_borrow.clone()
                - day_delta.clone(),
        );
        eval.add_constraint(
            field_const::<E>(cutoff.month) - birth_month.clone() - day_borrow.clone()
                + field_const::<E>(16) * month_borrow.clone()
                - month_delta.clone(),
        );
        eval.add_constraint(
            field_const::<E>(cutoff.year)
                - birth_year.clone()
                - month_borrow.clone()
                - year_delta.clone(),
        );

        let bounds = self.public.bounds;
        let table_index = (birth_year - field_const::<E>(bounds.min_supported_year))
            * BaseField::from_u32_unchecked(12)
            + birth_month
            - field_const::<E>(1);
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.calendar,
            E::EF::one(),
            &[table_index, max_days.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.valid_day,
            E::EF::one(),
            &[max_days, birth_day],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.day_delta,
            E::EF::one(),
            &[day_delta],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.month_delta,
            E::EF::one(),
            &[month_delta],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.year_delta,
            E::EF::one(),
            &[year_delta],
        ));

        // Credential-field binding (§6.6), after the statement's own lookups so
        // the existing interaction columns are unchanged and the binding
        // fractions append. `bind_active` is boolean and selects the single row
        // whose requires fire; the reconciliation ties the packed `birth_year` to
        // its two exposed bytes (`month`/`day` are single bytes, bound directly);
        // the four requires cancel SHA's `−is_first_block` yield iff the bytes
        // the age module reasons about are the credential's signed DOB bytes.
        if let Some((relation, bind_active, year_hi, year_lo, birth_year, birth_month, birth_day)) =
            dob_binding
        {
            eval.add_constraint(bind_active.clone() * (field_const::<E>(1) - bind_active.clone()));
            eval.add_constraint(
                birth_year - field_const::<E>(256) * year_hi.clone() - year_lo.clone(),
            );
            let mult = E::EF::from(bind_active);
            for (byte_index, value) in [
                (0u32, year_hi),
                (1, year_lo),
                (2, birth_month),
                (3, birth_day),
            ] {
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    mult.clone(),
                    &[
                        field_const::<E>(field_id::DOB),
                        field_const::<E>(byte_index),
                        value,
                    ],
                ));
            }
        }

        eval.finalize_logup();
        eval
    }
}

pub type AgeRangeCheckComponent = FrameworkComponent<AgeRangeCheckEval>;
