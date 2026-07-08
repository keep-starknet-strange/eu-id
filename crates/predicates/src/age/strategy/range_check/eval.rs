use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::preprocessed::active_col_id;
use crate::age::strategy::range_check::witness::{
    DobBindingMode, WitnessData, DOB_TEXT_DIGITS, DOB_TEXT_DIGIT_BITS, DOB_TEXT_LEN,
};
use crate::age::types::PublicInput;
use crate::utils::field_const;
use air_core::relations::{field_id, FieldBytesRelation};
use stwo::core::fields::m31::BaseField;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

#[derive(Clone)]
pub struct AgeRangeCheckEval {
    pub(super) public: PublicInput,
    pub(super) lookup_elements: LookupElements,
    /// The shared credential-field channel, when the DOB↔credential binding is
    /// wired. `None` for a standalone age proof — then this component is
    /// byte-for-byte the unbound predicate and stays internally balanced.
    /// `Some(relation)` adds the binding columns, the byte↔date reconciliation,
    /// and the DOB-byte *require* terms.
    pub(super) dob_binding: Option<FieldBytesRelation>,
    pub(super) dob_binding_mode: Option<DobBindingMode>,
}

impl FrameworkEval for AgeRangeCheckEval {
    fn log_size(&self) -> u32 {
        WitnessData::log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        WitnessData::log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Class-C: the single-row `active` selector gates every constraint and
        // lookup use. `2^LOG_SIZE − 1` blind rows carry fresh randomness and are
        // unconstrained here (`active = 0`). Degree budget: gating a degree-2
        // constraint by `active` (preprocessed, degree 1) yields degree 3 ≤
        // `log_size + 1` bound.
        let active = eval.get_preprocessed_column(active_col_id());

        let birth_day = eval.next_trace_mask();
        let birth_month = eval.next_trace_mask();
        let birth_year = eval.next_trace_mask();
        let max_days = eval.next_trace_mask();

        let day_delta = eval.next_trace_mask();
        let month_delta = eval.next_trace_mask();
        let year_delta = eval.next_trace_mask();
        let day_borrow = eval.next_trace_mask();
        let month_borrow = eval.next_trace_mask();

        // Credential-field binding columns. Read here, immediately after the
        // base witness columns, so they occupy this component's trace slots — the
        // order the witness generator commits them and the `air_core` allocator
        // assigns. The base-value clones are captured before the statement
        // constraints below consume `birth_*`. The single-row require selector is
        // the preprocessed `active` column (no `bind_active` trace column).
        let dob_binding = self.dob_binding.as_ref().map(|relation| {
            match self
                .dob_binding_mode
                .expect("DOB binding mode must be set with DOB relation")
            {
                DobBindingMode::Packed => {
                    let year_hi = eval.next_trace_mask();
                    let year_lo = eval.next_trace_mask();
                    DobBindingMasks::Packed {
                        relation,
                        year_hi,
                        year_lo,
                        birth_year: birth_year.clone(),
                        birth_month: birth_month.clone(),
                        birth_day: birth_day.clone(),
                    }
                }
                DobBindingMode::Text => {
                    let bytes: [E::F; DOB_TEXT_LEN] =
                        std::array::from_fn(|_| eval.next_trace_mask());
                    let digit_bits: [[E::F; DOB_TEXT_DIGIT_BITS]; DOB_TEXT_DIGITS] =
                        std::array::from_fn(|_| std::array::from_fn(|_| eval.next_trace_mask()));
                    DobBindingMasks::Text {
                        relation,
                        bytes,
                        digit_bits,
                        birth_year: birth_year.clone(),
                        birth_month: birth_month.clone(),
                        birth_day: birth_day.clone(),
                    }
                }
            }
        });

        eval.add_constraint(
            active.clone() * day_borrow.clone() * (field_const::<E>(1) - day_borrow.clone()),
        );
        eval.add_constraint(
            active.clone() * month_borrow.clone() * (field_const::<E>(1) - month_borrow.clone()),
        );

        let cutoff = self.public.cutoff_date();

        eval.add_constraint(
            active.clone()
                * (field_const::<E>(cutoff.day) - birth_day.clone()
                    + field_const::<E>(32) * day_borrow.clone()
                    - day_delta.clone()),
        );
        eval.add_constraint(
            active.clone()
                * (field_const::<E>(cutoff.month) - birth_month.clone() - day_borrow.clone()
                    + field_const::<E>(16) * month_borrow.clone()
                    - month_delta.clone()),
        );
        eval.add_constraint(
            active.clone()
                * (field_const::<E>(cutoff.year)
                    - birth_year.clone()
                    - month_borrow.clone()
                    - year_delta.clone()),
        );

        let bounds = self.public.bounds;
        let table_index = (birth_year - field_const::<E>(bounds.min_supported_year))
            * BaseField::from_u32_unchecked(12)
            + birth_month
            - field_const::<E>(1);
        let use_mult = E::EF::from(active.clone());
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.calendar,
            use_mult.clone(),
            &[table_index, max_days.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.valid_day,
            use_mult.clone(),
            &[max_days, birth_day],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.day_delta,
            use_mult.clone(),
            &[day_delta],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.month_delta,
            use_mult.clone(),
            &[month_delta],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.year_delta,
            use_mult,
            &[year_delta],
        ));

        // Credential-field binding, after the statement's own lookups so the
        // existing interaction columns are unchanged and the binding fractions
        // append. The preprocessed `active` selects the single row whose requires
        // fire; the reconciliation ties the packed `birth_year` to its two
        // exposed bytes (`month`/`day` are single bytes, bound directly); the
        // four requires cancel SHA's `−is_first_block` yield iff the bytes the
        // age module reasons about are the credential's signed DOB bytes.
        if let Some(binding) = dob_binding {
            emit_dob_binding(&mut eval, active.clone(), binding);
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

pub type AgeRangeCheckComponent = FrameworkComponent<AgeRangeCheckEval>;

/// The DOB-binding trace masks, per mode. `Packed` exposes the two big-endian
/// year bytes; `Text` exposes the ten `YYYY-MM-DD` bytes plus the per-digit
/// 4-bit decomposition columns.
enum DobBindingMasks<'a, F> {
    Packed {
        relation: &'a FieldBytesRelation,
        year_hi: F,
        year_lo: F,
        birth_year: F,
        birth_month: F,
        birth_day: F,
    },
    Text {
        relation: &'a FieldBytesRelation,
        bytes: [F; DOB_TEXT_LEN],
        digit_bits: [[F; DOB_TEXT_DIGIT_BITS]; DOB_TEXT_DIGITS],
        birth_year: F,
        birth_month: F,
        birth_day: F,
    },
}

fn emit_dob_binding<E: EvalAtRow>(eval: &mut E, active: E::F, binding: DobBindingMasks<'_, E::F>) {
    match binding {
        DobBindingMasks::Packed {
            relation,
            year_hi,
            year_lo,
            birth_year,
            birth_month,
            birth_day,
        } => {
            eval.add_constraint(
                active.clone()
                    * (birth_year - field_const::<E>(256) * year_hi.clone() - year_lo.clone()),
            );
            let mult = E::EF::from(active);
            for (byte_index, value) in [
                (0u32, year_hi),
                (1, year_lo),
                (2, birth_month),
                (3, birth_day),
            ] {
                require_dob_byte(eval, relation, mult.clone(), byte_index, value);
            }
        }
        DobBindingMasks::Text {
            relation,
            bytes,
            digit_bits,
            birth_year,
            birth_month,
            birth_day,
        } => {
            // The two `-` separators pin positions 4 and 7 to 0x2D.
            eval.add_constraint(
                active.clone() * (bytes[4].clone() - field_const::<E>(b'-' as u32)),
            );
            eval.add_constraint(
                active.clone() * (bytes[7].clone() - field_const::<E>(b'-' as u32)),
            );

            // Recompose each digit from four booleans and cap it at 9 (bits 3&2
            // and 3&1 cannot both be set) — a range check without a table. Every
            // constraint gated by `active`.
            let digit_positions = [0usize, 1, 2, 3, 5, 6, 8, 9];
            let mut digits = Vec::with_capacity(DOB_TEXT_DIGITS);
            for (digit_idx, &byte_pos) in digit_positions.iter().enumerate() {
                let bits = &digit_bits[digit_idx];
                for bit in bits {
                    eval.add_constraint(
                        active.clone() * bit.clone() * (field_const::<E>(1) - bit.clone()),
                    );
                }
                let digit = bytes[byte_pos].clone() - field_const::<E>(b'0' as u32);
                let recomposed = bits[0].clone()
                    + field_const::<E>(2) * bits[1].clone()
                    + field_const::<E>(4) * bits[2].clone()
                    + field_const::<E>(8) * bits[3].clone();
                eval.add_constraint(active.clone() * (digit.clone() - recomposed));
                eval.add_constraint(active.clone() * bits[3].clone() * bits[2].clone());
                eval.add_constraint(active.clone() * bits[3].clone() * bits[1].clone());
                digits.push(digit);
            }

            eval.add_constraint(
                active.clone()
                    * (birth_year
                        - field_const::<E>(1000) * digits[0].clone()
                        - field_const::<E>(100) * digits[1].clone()
                        - field_const::<E>(10) * digits[2].clone()
                        - digits[3].clone()),
            );
            eval.add_constraint(
                active.clone()
                    * (birth_month - field_const::<E>(10) * digits[4].clone() - digits[5].clone()),
            );
            eval.add_constraint(
                active.clone()
                    * (birth_day - field_const::<E>(10) * digits[6].clone() - digits[7].clone()),
            );

            let mult = E::EF::from(active);
            for (byte_index, value) in bytes.into_iter().enumerate() {
                require_dob_byte(eval, relation, mult.clone(), byte_index as u32, value);
            }
        }
    }
}

fn require_dob_byte<E: EvalAtRow>(
    eval: &mut E,
    relation: &FieldBytesRelation,
    mult: E::EF,
    byte_index: u32,
    value: E::F,
) {
    eval.add_to_relation(RelationEntry::new(
        relation,
        mult,
        &[
            field_const::<E>(field_id::DOB),
            field_const::<E>(byte_index),
            value,
        ],
    ));
}
