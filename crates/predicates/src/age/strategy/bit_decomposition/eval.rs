use crate::age::calendar::{CalendarElements, ValidDayElements};
use crate::age::strategy::bit_decomposition::witness::WitnessData;
use crate::age::strategy::bit_decomposition::witness::{DAY_OFFSET_BITS, MONTH_OFFSET_BITS};
use crate::age::types::{PublicInput, DATE_MONTH_BASE, DATE_YEAR_BASE};
use crate::utils::{bit_sum, constrain_bits, field_const, read_bits, read_bits_dynamic};
use num_traits::One;
use stwo::core::fields::m31::BaseField;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

pub(super) struct BitDecompositionEval {
    pub(super) public: PublicInput,
    pub(super) calendar_elements: CalendarElements,
    pub(super) valid_day_elements: ValidDayElements,
}

impl FrameworkEval for BitDecompositionEval {
    fn log_size(&self) -> u32 {
        WitnessData::log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        WitnessData::log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let dob_year = eval.next_trace_mask();
        let dob_month = eval.next_trace_mask();
        let dob_day = eval.next_trace_mask();
        let age_slack = eval.next_trace_mask();
        let max_days = eval.next_trace_mask();

        let bounds = self.public.bounds;
        let year_offset_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let year_bound_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.year_offset_bits());
        let month_offset_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let month_bound_slack_bits = read_bits::<E, MONTH_OFFSET_BITS>(&mut eval);
        let day_offset_bits = read_bits::<E, DAY_OFFSET_BITS>(&mut eval);
        let age_slack_bits = read_bits_dynamic::<E>(&mut eval, bounds.age_slack_bits());

        constrain_bits(&mut eval, &year_offset_bits);
        constrain_bits(&mut eval, &year_bound_slack_bits);
        constrain_bits(&mut eval, &month_offset_bits);
        constrain_bits(&mut eval, &month_bound_slack_bits);
        constrain_bits(&mut eval, &day_offset_bits);
        constrain_bits(&mut eval, &age_slack_bits);

        let year_offset = bit_sum::<E>(&year_offset_bits);
        let year_bound_slack = bit_sum::<E>(&year_bound_slack_bits);
        let month_offset = bit_sum::<E>(&month_offset_bits);
        let month_bound_slack = bit_sum::<E>(&month_bound_slack_bits);
        let day_offset = bit_sum::<E>(&day_offset_bits);
        let age_slack_from_bits = bit_sum::<E>(&age_slack_bits);

        eval.add_constraint(
            dob_year.clone() - field_const::<E>(bounds.min_supported_year) - year_offset.clone(),
        );
        eval.add_constraint(field_const::<E>(bounds.year_span()) - year_offset - year_bound_slack);
        eval.add_constraint(dob_month.clone() - field_const::<E>(1) - month_offset.clone());
        eval.add_constraint(field_const::<E>(11) - month_offset - month_bound_slack);
        eval.add_constraint(dob_day.clone() - field_const::<E>(1) - day_offset);
        eval.add_constraint(age_slack.clone() - age_slack_from_bits);

        let cutoff_key = self.public.cutoff_date().key();
        let dob_key = dob_year.clone() * BaseField::from_u32_unchecked(DATE_YEAR_BASE)
            + dob_month.clone() * BaseField::from_u32_unchecked(DATE_MONTH_BASE)
            + dob_day.clone();
        eval.add_constraint(field_const::<E>(cutoff_key) - dob_key - age_slack);

        let table_index = (dob_year - field_const::<E>(bounds.min_supported_year))
            * BaseField::from_u32_unchecked(12)
            + dob_month
            - field_const::<E>(1);
        eval.add_to_relation(RelationEntry::new(
            &self.calendar_elements,
            E::EF::one(),
            &[table_index, max_days.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.valid_day_elements,
            E::EF::one(),
            &[max_days, dob_day],
        ));

        eval.finalize_logup();
        eval
    }
}

pub(super) type AgeBitDecompositionComponent = FrameworkComponent<BitDecompositionEval>;
