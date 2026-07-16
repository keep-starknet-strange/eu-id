use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::active_col_id;
use crate::nat::witness::WitnessData;
use crate::utils::field_const;
use air_core::relations::{field_id, FieldBytesRelation};
use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

#[derive(Clone)]
pub struct NationalityEval {
    pub lookup_elements: LookupElements,
    /// The shared credential-field channel, when the nationality↔credential
    /// binding is wired. `None` for a standalone nationality proof — then this
    /// component is byte-for-byte the unbound predicate and stays internally
    /// balanced. `Some(relation)` adds the two binding columns, the byte↔code
    /// reconciliation, and the two nationality-byte *require* terms.
    pub nat_binding: Option<FieldBytesRelation>,
}

pub type NationalityComponent = FrameworkComponent<NationalityEval>;

impl FrameworkEval for NationalityEval {
    fn log_size(&self) -> u32 {
        WitnessData::log_size()
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        WitnessData::log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Class-C: the single-row `active` selector gates every constraint and
        // lookup use; the remaining rows are blind rows carrying fresh
        // randomness. Gating a degree-2 constraint by `active` (preprocessed,
        // degree 1) yields degree 3 ≤ the `log_size + 1` bound.
        let active = eval.get_preprocessed_column(active_col_id());
        let nationality = eval.next_trace_mask();

        // Credential-field binding columns. Read here, immediately after the base
        // `nationality` column, so they occupy this component's trace slots — the
        // order the witness generator commits them and the `air_core` allocator
        // assigns. The base-value clone is captured before the membership lookup
        // below consumes `nationality`. The single-row require selector is the
        // preprocessed `active` column (no `bind_active` trace column).
        let nat_binding = self.nat_binding.as_ref().map(|relation| {
            let code_hi = eval.next_trace_mask();
            let code_lo = eval.next_trace_mask();
            (relation, code_hi, code_lo, nationality.clone())
        });

        // Membership: provide the private code into the accepted-set table
        // relation (the `NatTableEval` requires it with `−multiplicity`). The use
        // fires only on the active row.
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements.nat_table,
            E::EF::from(active.clone()),
            &[nationality],
        ));

        // Credential-field binding, after the membership lookup so the existing
        // interaction column is unchanged and the binding fractions append. The
        // preprocessed `active` selects the single row whose requires fire; the
        // reconciliation ties the packed `nationality` to its two exposed
        // big-endian bytes; the two requires cancel SHA's `−is_first_block` yield
        // iff the code the nat module proves membership for is the credential's
        // signed nationality bytes.
        if let Some((relation, code_hi, code_lo, nationality)) = nat_binding {
            eval.add_constraint(
                active.clone()
                    * (nationality - field_const::<E>(256) * code_hi.clone() - code_lo.clone()),
            );
            let mult = E::EF::from(active);
            for (byte_index, value) in [(0u32, code_hi), (1, code_lo)] {
                eval.add_to_relation(RelationEntry::new(
                    relation,
                    mult.clone(),
                    &[
                        field_const::<E>(field_id::NATIONALITY),
                        field_const::<E>(byte_index),
                        value,
                    ],
                ));
            }
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}
