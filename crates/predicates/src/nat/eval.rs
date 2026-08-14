use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::{allowed_col_id, first_col_id, row_index_col_id};
use crate::nat::witness::WitnessData;
use crate::utils::field_const;
use air_core::claim_mask::add_claim_mask_fraction;
use air_core::relations::{field_id, FieldBytesRelation};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

#[derive(Clone)]
pub struct NationalityEval {
    pub lookup_elements: LookupElements,
    /// The shared credential-field channel, when the nationality↔credential
    /// binding is wired. Every active array entry consumes two bytes from the
    /// semantic mdoc scope. A standalone proof leaves this unwired.
    pub nat_binding: Option<FieldBytesRelation>,
    pub claim_mask_beta: Option<QM31>,
}

pub type NationalityComponent = FrameworkComponent<NationalityEval>;

impl FrameworkEval for NationalityEval {
    fn log_size(&self) -> u32 {
        WitnessData::log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Degree-three constraints need a quotient domain twice the trace
        // domain because the quotient degree is `(degree - 1) * trace_size`.
        WitnessData::log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let allowed = eval.get_preprocessed_column(allowed_col_id());
        let row_index = eval.get_preprocessed_column(row_index_col_id());
        let first = eval.get_preprocessed_column(first_col_id());

        let active = eval.next_trace_mask();
        let last = eval.next_trace_mask();
        let nationality = eval.next_trace_mask();
        let accepted = eval.next_trace_mask();
        let seen_before = eval.next_trace_mask();
        let seen_after = eval.next_trace_mask();
        let nat_binding = self.nat_binding.as_ref().map(|relation| {
            let code_hi = eval.next_trace_mask();
            let code_lo = eval.next_trace_mask();
            (relation, code_hi, code_lo)
        });

        let one = E::F::from(M31::from_u32_unchecked(1));
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(last.clone() * (last.clone() - one.clone()));
        eval.add_constraint(active.clone() * (one.clone() - allowed));
        eval.add_constraint(first.clone() * (active.clone() - one.clone()));
        eval.add_constraint(last.clone() * (one.clone() - active.clone()));
        eval.add_constraint(active.clone() * accepted.clone() * (accepted.clone() - one.clone()));
        eval.add_constraint(
            active.clone() * seen_before.clone() * (seen_before.clone() - one.clone()),
        );
        eval.add_constraint(
            active.clone() * seen_after.clone() * (seen_after.clone() - one.clone()),
        );
        // `seen_after = seen_before OR accepted`.
        eval.add_constraint(
            active.clone()
                * (seen_after.clone() - seen_before.clone() - accepted.clone()
                    + seen_before.clone() * accepted.clone()),
        );
        eval.add_constraint(first.clone() * seen_before.clone());
        eval.add_constraint(last.clone() * (seen_after.clone() - one));

        // A marked entry must occur in the public accepted-set table.
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.nat_table,
            E::EF::from(active.clone() * accepted),
            std::slice::from_ref(&nationality),
        ));
        // Every active signed entry must be an assigned ISO alpha-2 code or one
        // of the exact private-only `QU` and `QS` values.
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.signed_valid,
            E::EF::from(active.clone()),
            std::slice::from_ref(&nationality),
        ));

        // Link the running existential state between adjacent active rows.
        // Current row i's `[i, seen_before]` cancels previous row i-1's
        // `[i, seen_after]`.
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.prefix_transition,
            E::EF::from(active.clone() - first),
            &[row_index.clone(), seen_before],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.prefix_transition,
            -E::EF::from(active.clone() - last),
            &[row_index.clone() + field_const::<E>(1), seen_after],
        ));

        if let Some((relation, code_hi, code_lo)) = nat_binding {
            eval.add_constraint(
                active.clone()
                    * (nationality - field_const::<E>(256) * code_hi.clone() - code_lo.clone()),
            );
            let mult = E::EF::from(active);
            for (byte_offset, value) in [(0u32, code_hi), (1, code_lo)] {
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    mult.clone(),
                    &[
                        field_const::<E>(field_id::NATIONALITY),
                        row_index.clone() * field_const::<E>(2) + field_const::<E>(byte_offset),
                        value,
                    ],
                ));
            }
        }

        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}
