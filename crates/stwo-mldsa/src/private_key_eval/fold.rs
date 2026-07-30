use num_traits::{One, Zero};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, Relation, RelationEntry};

use crate::air_util::{col_eval, m31, ColEval};
use crate::coeffs::layout::{
    POLY_ID_C, POLY_ID_CARRY0, POLY_ID_E0, POLY_ID_V0, POLY_ID_W0, POLY_ID_Z0,
};
use crate::constants::{K, L, N};
use crate::witness::B;

use super::{gen_batched_logup, PrivateDeviceEvals, PrivateKeyEvalRelations, PRIVATE_EVAL_COUNT};

pub const FOLD_LOG_SIZE: u32 = LOG_N_LANES;
pub const FOLD_LOGUP_ENTRIES: usize = PRIVATE_EVAL_COUNT;
pub const FOLD_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE * FOLD_LOGUP_ENTRIES.div_ceil(4);

fn active_id() -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: "mldsa_private_key_fold_active".to_string(),
    }
}

pub fn fold_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    vec![active_id()]
}

pub fn fold_preprocessed_log_sizes() -> Vec<u32> {
    vec![FOLD_LOG_SIZE]
}

pub fn gen_fold_preprocessed() -> Vec<ColEval> {
    let mut active = vec![m31(0); 1usize << FOLD_LOG_SIZE];
    active[0] = m31(1);
    vec![col_eval(FOLD_LOG_SIZE, active)]
}

pub fn fold_interaction_layout() -> Vec<u32> {
    vec![FOLD_LOG_SIZE; FOLD_INTERACTION_COLS]
}

#[derive(Clone)]
pub struct PrivateFoldEval {
    pub rho_rlc: SecureField,
    pub r: SecureField,
    pub s: SecureField,
    pub relations: PrivateKeyEvalRelations,
    pub evals: PrivateDeviceEvals,
}

impl FrameworkEval for PrivateFoldEval {
    fn log_size(&self) -> u32 {
        FOLD_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    // `EvalAtRow::EF` does not promise the `*Assign` traits, so the generic
    // evaluator must spell these updates as ordinary binary operations.
    #[allow(clippy::assign_op_pattern)]
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(active_id());
        for (id, value) in self.evals.as_slice().iter().enumerate() {
            let coords = value.to_m31_array();
            eval.add_to_relation(RelationEntry::base(
                &self.relations.eval,
                active.clone(),
                &[
                    E::F::from(m31(id as u32)),
                    E::F::from(coords[0]),
                    E::F::from(coords[1]),
                    E::F::from(coords[2]),
                    E::F::from(coords[3]),
                ],
            ));
        }

        let one = E::EF::one();
        let r = E::EF::from(self.r);
        let s = E::EF::from(self.s);
        let rho_rlc = E::EF::from(self.rho_rlc);
        let q_hat = one.clone() - E::EF::from(E::F::from(m31(16))) * s.clone()
            + E::EF::from(E::F::from(m31(32))) * s.clone() * s.clone();
        let mut r256 = one.clone();
        for _ in 0..N {
            r256 = r256 * r.clone();
        }
        let x_fold = r256 + one.clone();
        let s_minus_b = s - E::EF::from(E::F::from(m31(B as u32)));

        let value = |id: usize| E::EF::from(self.evals.coeff(id));
        let mut total = E::EF::zero();
        let mut rho_power = one;
        for i in 0..K {
            let mut row = E::EF::zero();
            for j in 0..L {
                row = row + E::EF::from(self.evals.a(i, j)) * value(POLY_ID_Z0 as usize + j);
            }
            row = row - value(POLY_ID_C as usize) * E::EF::from(self.evals.t1(i));
            row = row - value(POLY_ID_W0 as usize + i);
            row = row - x_fold.clone() * value(POLY_ID_V0 as usize + i);
            row = row - q_hat.clone() * value(POLY_ID_E0 as usize + i);
            row = row - s_minus_b.clone() * value(POLY_ID_CARRY0 as usize + i);
            total = total + rho_power.clone() * row;
            rho_power = rho_power * rho_rlc.clone();
        }
        eval.add_constraint(E::EF::from(active) * total);
        eval.finalize_logup_batched(4);
        eval
    }
}

pub fn gen_fold_interaction(
    evals: &PrivateDeviceEvals,
    relation: &crate::coeffs::relations::EvalAtRsRelation,
) -> (Vec<ColEval>, SecureField) {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut rows = vec![vec![(zero, one); FOLD_LOGUP_ENTRIES]; 1usize << FOLD_LOG_SIZE];
    rows[0] = evals
        .as_slice()
        .iter()
        .enumerate()
        .map(|(id, value)| {
            let coords = value.to_m31_array();
            (
                one,
                relation.combine(&[m31(id as u32), coords[0], coords[1], coords[2], coords[3]]),
            )
        })
        .collect();
    gen_batched_logup(FOLD_LOG_SIZE, &rows, FOLD_LOGUP_ENTRIES)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_key_eval::{A_EVAL_BASE, COEFF_EVAL_COUNT, T1_EVAL_BASE, T1_EVAL_COUNT};

    fn native_fold(
        evals: &PrivateDeviceEvals,
        rho_rlc: SecureField,
        r: SecureField,
        s: SecureField,
    ) -> SecureField {
        let one = SecureField::one();
        let q_hat = one - SecureField::from(m31(16)) * s + SecureField::from(m31(32)) * s * s;
        let mut r256 = one;
        for _ in 0..N {
            r256 *= r;
        }
        let x_fold = r256 + one;
        let s_minus_b = s - SecureField::from(m31(B as u32));
        let mut total = SecureField::zero();
        let mut rho_power = one;
        for i in 0..K {
            let mut row = SecureField::zero();
            for j in 0..L {
                row += evals.a(i, j) * evals.coeff(POLY_ID_Z0 as usize + j);
            }
            row -= evals.coeff(POLY_ID_C as usize) * evals.t1(i);
            row -= evals.coeff(POLY_ID_W0 as usize + i);
            row -= x_fold * evals.coeff(POLY_ID_V0 as usize + i);
            row -= q_hat * evals.coeff(POLY_ID_E0 as usize + i);
            row -= s_minus_b * evals.coeff(POLY_ID_CARRY0 as usize + i);
            total += rho_power * row;
            rho_power *= rho_rlc;
        }
        total
    }

    #[test]
    fn exact_ids_and_all_integer_lift_terms_are_live() {
        let rho = SecureField::from(m31(7));
        let r = SecureField::from(m31(11));
        let s = SecureField::from(m31(19));
        let mut values = [SecureField::zero(); PRIVATE_EVAL_COUNT];
        for (id, value) in values.iter_mut().enumerate() {
            *value = SecureField::from(m31((id + 2) as u32));
        }
        let provisional = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        // One free w evaluation closes the scalar fold exactly.
        let residue = native_fold(&provisional, rho, r, s);
        values[POLY_ID_W0 as usize] += residue;
        let honest = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        assert_eq!(native_fold(&honest, rho, r, s), SecureField::zero());

        let live_ids = (0..COEFF_EVAL_COUNT)
            .chain(A_EVAL_BASE..T1_EVAL_BASE)
            .chain(T1_EVAL_BASE..T1_EVAL_BASE + T1_EVAL_COUNT);
        for id in live_ids {
            let mut forged = values;
            forged[id] += SecureField::one();
            let forged = PrivateDeviceEvals::try_from_slice(&forged).unwrap();
            assert_ne!(
                native_fold(&forged, rho, r, s),
                SecureField::zero(),
                "evaluation id {id} was not live in the fold"
            );
        }
    }

    #[test]
    fn fold_interaction_consumes_all_ids_once() {
        let values = [SecureField::zero(); PRIVATE_EVAL_COUNT];
        let evals = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        let (trace, _) =
            gen_fold_interaction(&evals, &crate::coeffs::relations::EvalAtRsRelation::dummy());
        assert_eq!(trace.len(), FOLD_INTERACTION_COLS);
    }
}
