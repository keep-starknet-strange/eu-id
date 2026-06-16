use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::witness::WitnessData;
use crate::age::types::PublicInput;
use crate::utils::field_const;
use num_traits::One;
use stwo::core::fields::m31::BaseField;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

#[derive(Clone)]
pub struct AgeRangeCheckEval {
    pub(super) public: PublicInput,
    pub(super) lookup_elements: LookupElements,
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

        eval.finalize_logup();
        eval
    }
}

pub type AgeRangeCheckComponent = FrameworkComponent<AgeRangeCheckEval>;
