use num_traits::{One, Zero};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::prover::backend::simd::m31::LOG_N_LANES;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, Relation, RelationEntry};

use crate::air_util::{col_eval, enc_signed, m31, ColEval};
use crate::coeffs::layout::{
    POLY_ID_C, POLY_ID_CARRY0, POLY_ID_E0, POLY_ID_V0, POLY_ID_W0, POLY_ID_Z0,
};
use crate::constants::N;
use crate::profile::MlDsaProfile;
use crate::witness::B;

use super::{gen_batched_logup, PrivateDeviceEvals, PrivateKeyEvalRelations, PRIVATE_EVAL_COUNT};

pub const FOLD_LOG_SIZE: u32 = LOG_N_LANES;
pub const FOLD_LOGUP_ENTRIES: usize = PRIVATE_EVAL_COUNT;
pub const FOLD_INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE * FOLD_LOGUP_ENTRIES.div_ceil(4);

#[derive(Clone, Copy, Debug)]
struct FoldFormula {
    az_sign: i64,
    ct1_sign: i64,
    w_sign: i64,
    v_sign: i64,
    e_sign: i64,
    carry_sign: i64,
    q_coefficients: [i64; 3],
    q_override: Option<SecureField>,
    x_constant: i64,
    carry_constant: i64,
}

const EXACT_FOLD_FORMULA: FoldFormula = FoldFormula {
    az_sign: 1,
    ct1_sign: -1,
    w_sign: -1,
    v_sign: -1,
    e_sign: -1,
    carry_sign: -1,
    q_coefficients: [1, -16, 32],
    q_override: None,
    x_constant: 1,
    carry_constant: -(B as i64),
};

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
    pub profile: MlDsaProfile,
    pub rho_rlc: SecureField,
    pub r: SecureField,
    pub s: SecureField,
    pub relations: PrivateKeyEvalRelations,
    pub evals: PrivateDeviceEvals,
}

#[allow(clippy::assign_op_pattern)]
fn fold_total<E: EvalAtRow>(
    evals: &PrivateDeviceEvals,
    profile: MlDsaProfile,
    rho_rlc: SecureField,
    r: SecureField,
    s: SecureField,
    formula: FoldFormula,
) -> E::EF {
    let fixed = |value: i64| E::EF::from(E::F::from(enc_signed(value)));
    let one = E::EF::one();
    let r = E::EF::from(r);
    let s = E::EF::from(s);
    let rho_rlc = E::EF::from(rho_rlc);
    let q_hat = formula.q_override.map(E::EF::from).unwrap_or_else(|| {
        fixed(formula.q_coefficients[0])
            + fixed(formula.q_coefficients[1]) * s.clone()
            + fixed(formula.q_coefficients[2]) * s.clone() * s.clone()
    });
    let mut r256 = one.clone();
    for _ in 0..N {
        r256 = r256 * r.clone();
    }
    let x_fold = r256 + fixed(formula.x_constant);
    let carry_factor = s + fixed(formula.carry_constant);
    let value = |id: usize| E::EF::from(evals.coeff(id));

    let mut total = E::EF::zero();
    let mut rho_power = one;
    for i in 0..profile.k() {
        let mut row = E::EF::zero();
        for j in 0..profile.l() {
            row = row
                + fixed(formula.az_sign)
                    * E::EF::from(evals.a_for(profile, i, j))
                    * value(POLY_ID_Z0 as usize + j);
        }
        row = row + fixed(formula.ct1_sign) * value(POLY_ID_C as usize) * E::EF::from(evals.t1(i));
        row = row + fixed(formula.w_sign) * value(POLY_ID_W0 as usize + i);
        row = row + fixed(formula.v_sign) * x_fold.clone() * value(POLY_ID_V0 as usize + i);
        row = row + fixed(formula.e_sign) * q_hat.clone() * value(POLY_ID_E0 as usize + i);
        row = row
            + fixed(formula.carry_sign) * carry_factor.clone() * value(POLY_ID_CARRY0 as usize + i);
        total = total + rho_power.clone() * row;
        rho_power = rho_power * rho_rlc.clone();
    }
    total
}

impl FrameworkEval for PrivateFoldEval {
    fn log_size(&self) -> u32 {
        FOLD_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

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

        let total = fold_total::<E>(
            &self.evals,
            self.profile,
            self.rho_rlc,
            self.r,
            self.s,
            EXACT_FOLD_FORMULA,
        );
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
    use crate::profile::{ML_DSA_44, ML_DSA_65};
    use air_core::{Air, AirProver, TreeLayout};
    use stwo::core::air::Component;
    use stwo::core::channel::{Blake2sChannel, Channel};
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::{ComponentProver, TreeBuilder};
    use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

    use crate::private_key_eval::{A_EVAL_BASE, COEFF_EVAL_COUNT, T1_EVAL_BASE, T1_EVAL_COUNT};

    fn native_fold_formula(
        evals: &PrivateDeviceEvals,
        profile: MlDsaProfile,
        rho_rlc: SecureField,
        r: SecureField,
        s: SecureField,
        formula: FoldFormula,
    ) -> SecureField {
        let one = SecureField::one();
        let fixed = |value| SecureField::from(enc_signed(value));
        let q_hat = formula.q_override.unwrap_or_else(|| {
            fixed(formula.q_coefficients[0])
                + fixed(formula.q_coefficients[1]) * s
                + fixed(formula.q_coefficients[2]) * s * s
        });
        let mut r256 = one;
        for _ in 0..N {
            r256 *= r;
        }
        let x_fold = r256 + fixed(formula.x_constant);
        let carry_factor = s + fixed(formula.carry_constant);
        let mut total = SecureField::zero();
        let mut rho_power = one;
        for i in 0..profile.k() {
            let mut row = SecureField::zero();
            for j in 0..profile.l() {
                row += fixed(formula.az_sign)
                    * evals.a_for(profile, i, j)
                    * evals.coeff(POLY_ID_Z0 as usize + j);
            }
            row += fixed(formula.ct1_sign) * evals.coeff(POLY_ID_C as usize) * evals.t1(i);
            row += fixed(formula.w_sign) * evals.coeff(POLY_ID_W0 as usize + i);
            row += fixed(formula.v_sign) * x_fold * evals.coeff(POLY_ID_V0 as usize + i);
            row += fixed(formula.e_sign) * q_hat * evals.coeff(POLY_ID_E0 as usize + i);
            row +=
                fixed(formula.carry_sign) * carry_factor * evals.coeff(POLY_ID_CARRY0 as usize + i);
            total += rho_power * row;
            rho_power *= rho_rlc;
        }
        total
    }

    fn native_fold(
        evals: &PrivateDeviceEvals,
        profile: MlDsaProfile,
        rho_rlc: SecureField,
        r: SecureField,
        s: SecureField,
    ) -> SecureField {
        native_fold_formula(evals, profile, rho_rlc, r, s, EXACT_FOLD_FORMULA)
    }

    #[derive(Clone)]
    struct FormulaEval {
        profile: MlDsaProfile,
        evals: PrivateDeviceEvals,
        rho_rlc: SecureField,
        r: SecureField,
        s: SecureField,
        formula: FoldFormula,
    }

    impl FrameworkEval for FormulaEval {
        fn log_size(&self) -> u32 {
            FOLD_LOG_SIZE
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            FOLD_LOG_SIZE + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let fixed_active = eval.get_preprocessed_column(PreProcessedColumnId {
                id: "test_private_fold_active".to_string(),
            });
            let active = eval.next_trace_mask();
            let dummy_interaction =
                eval.next_interaction_mask(stwo_constraint_framework::INTERACTION_TRACE_IDX, [0]);
            eval.add_constraint(active.clone() - fixed_active);
            eval.add_constraint(active.clone() * (E::F::one() - active.clone()));
            eval.add_constraint(dummy_interaction[0].clone());
            eval.add_constraint(
                E::EF::from(active)
                    * fold_total::<E>(
                        &self.evals,
                        self.profile,
                        self.rho_rlc,
                        self.r,
                        self.s,
                        self.formula,
                    ),
            );
            eval
        }
    }

    struct FormulaAir {
        profile: MlDsaProfile,
        evals: PrivateDeviceEvals,
        rho_rlc: SecureField,
        r: SecureField,
        s: SecureField,
        formula: FoldFormula,
        component: Option<FrameworkComponent<FormulaEval>>,
    }

    impl FormulaAir {
        fn new(
            profile: MlDsaProfile,
            evals: PrivateDeviceEvals,
            rho_rlc: SecureField,
            r: SecureField,
            s: SecureField,
            formula: FoldFormula,
        ) -> Self {
            Self {
                profile,
                evals,
                rho_rlc,
                r,
                s,
                formula,
                component: None,
            }
        }
    }

    impl Air for FormulaAir {
        fn mix_public(&self, channel: &mut Blake2sChannel) {
            channel.mix_felts(self.evals.as_slice());
            channel.mix_felts(&[self.rho_rlc, self.r, self.s]);
        }

        fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![FOLD_LOG_SIZE],
                trace: vec![FOLD_LOG_SIZE],
                interaction: vec![FOLD_LOG_SIZE],
            }
        }

        fn claimed_sums(&self) -> Vec<SecureField> {
            Vec::new()
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![PreProcessedColumnId {
                id: "test_private_fold_active".to_string(),
            }]
        }

        fn canonical_preprocessed_columns(
            &mut self,
        ) -> Result<Vec<ColEval>, stwo::core::verifier::VerificationError> {
            let mut active = vec![m31(0); 1usize << FOLD_LOG_SIZE];
            active[0] = m31(1);
            Ok(vec![col_eval(FOLD_LOG_SIZE, active)])
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                FormulaEval {
                    profile: self.profile,
                    evals: self.evals.clone(),
                    rho_rlc: self.rho_rlc,
                    r: self.r,
                    s: self.s,
                    formula: self.formula,
                },
                SecureField::zero(),
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().expect("formula component")]
        }
    }

    impl AirProver for FormulaAir {
        fn max_log_size(&self) -> u32 {
            FOLD_LOG_SIZE
        }

        fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            let mut active = vec![m31(0); 1usize << FOLD_LOG_SIZE];
            active[0] = m31(1);
            tb.extend_evals(vec![col_eval(FOLD_LOG_SIZE, active)]);
        }

        fn preprocessed_column_fingerprints(
            &mut self,
        ) -> Vec<air_core::PreprocessedColumnFingerprint> {
            let ids = self.preprocessed_column_ids();
            let columns = self
                .canonical_preprocessed_columns()
                .expect("test preprocessed column");
            air_core::fingerprint_preprocessed_columns("private_fold_formula_test", &ids, &columns)
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            let mut active = vec![m31(0); 1usize << FOLD_LOG_SIZE];
            active[0] = m31(1);
            tb.extend_evals(vec![col_eval(FOLD_LOG_SIZE, active)]);
        }

        fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(vec![col_eval(
                FOLD_LOG_SIZE,
                vec![m31(0); 1usize << FOLD_LOG_SIZE],
            )]);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self.component.as_ref().expect("formula component")]
        }
    }

    fn forged_formula_evals(
        formula: FoldFormula,
        rho_rlc: SecureField,
        r: SecureField,
        s: SecureField,
    ) -> PrivateDeviceEvals {
        let mut values = [SecureField::zero(); PRIVATE_EVAL_COUNT];
        for (id, value) in values.iter_mut().enumerate() {
            *value = SecureField::from(m31((id + 2) as u32));
        }
        values[POLY_ID_Z0 as usize] = SecureField::one();
        let provisional = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        let residue = native_fold_formula(&provisional, ML_DSA_65, rho_rlc, r, s, formula);
        if formula.az_sign == 1 {
            values[A_EVAL_BASE] -= residue;
        } else {
            assert_eq!(formula.az_sign, -1);
            values[A_EVAL_BASE] += residue;
        }
        let evals = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        assert_eq!(
            native_fold_formula(&evals, ML_DSA_65, rho_rlc, r, s, formula),
            SecureField::zero(),
            "forged formula fixture must satisfy its own equation"
        );
        assert_ne!(
            native_fold(&evals, ML_DSA_65, rho_rlc, r, s),
            SecureField::zero(),
            "forged formula fixture must violate the exact equation"
        );
        evals
    }

    #[test]
    fn malformed_integer_fold_formulas_prove_only_under_the_forged_air() {
        let rho_rlc = SecureField::from(m31(7));
        let r = SecureField::from(m31(11));
        let s = SecureField::from(m31(19));
        let mut cases = Vec::new();
        let mut add = |label, update: fn(&mut FoldFormula)| {
            let mut formula = EXACT_FOLD_FORMULA;
            update(&mut formula);
            cases.push((label, formula));
        };
        add("omitted v correction", |f| f.v_sign = 0);
        add("omitted e correction", |f| f.e_sign = 0);
        add("omitted carry correction", |f| f.carry_sign = 0);
        add("sign-changed A*z term", |f| f.az_sign = -1);
        add("sign-changed c*t1 term", |f| f.ct1_sign = 1);
        add("sign-changed w term", |f| f.w_sign = 1);
        add("sign-changed v term", |f| f.v_sign = 1);
        add("sign-changed e term", |f| f.e_sign = 1);
        add("sign-changed carry term", |f| f.carry_sign = 1);
        add("witness-supplied qHat", |f| {
            f.q_override = Some(SecureField::from(m31(7)))
        });
        add("wrong qHat constant coefficient", |f| {
            f.q_coefficients[0] = 2
        });
        add("wrong qHat linear coefficient", |f| {
            f.q_coefficients[1] = -15
        });
        add("wrong qHat quadratic coefficient", |f| {
            f.q_coefficients[2] = 31
        });
        add("wrong r^256 + 1 factor", |f| f.x_constant = 0);
        add("wrong s - 512 carry factor", |f| f.carry_constant = -511);

        for (label, formula) in cases {
            let evals = forged_formula_evals(formula, rho_rlc, r, s);
            let mut prover = FormulaAir::new(ML_DSA_65, evals.clone(), rho_rlc, r, s, formula);
            let proof = air_core::prove(&mut [&mut prover], PcsConfig::default())
                .unwrap_or_else(|error| panic!("{label}: forged AIR proving failed: {error:?}"));

            let mut forged_verifier =
                FormulaAir::new(ML_DSA_65, evals.clone(), rho_rlc, r, s, formula);
            air_core::verify(&mut [&mut forged_verifier], &proof)
                .unwrap_or_else(|error| panic!("{label}: forged AIR control failed: {error:?}"));

            let mut exact_verifier =
                FormulaAir::new(ML_DSA_65, evals, rho_rlc, r, s, EXACT_FOLD_FORMULA);
            assert!(
                air_core::verify(&mut [&mut exact_verifier], &proof).is_err(),
                "{label}: the exact fold must reject the forged formula proof"
            );
        }
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
        let residue = native_fold(&provisional, ML_DSA_65, rho, r, s);
        values[POLY_ID_W0 as usize] += residue;
        let honest = PrivateDeviceEvals::try_from_slice(&values).unwrap();
        assert_eq!(
            native_fold(&honest, ML_DSA_65, rho, r, s),
            SecureField::zero()
        );

        let live_ids = (0..COEFF_EVAL_COUNT)
            .chain(A_EVAL_BASE..T1_EVAL_BASE)
            .chain(T1_EVAL_BASE..T1_EVAL_BASE + T1_EVAL_COUNT);
        for id in live_ids {
            let mut forged = values;
            forged[id] += SecureField::one();
            let forged = PrivateDeviceEvals::try_from_slice(&forged).unwrap();
            assert_ne!(
                native_fold(&forged, ML_DSA_65, rho, r, s),
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

    #[test]
    fn mldsa44_private_key_evaluations_satisfy_the_exact_fold() {
        use ml_dsa::signature::{Keypair, Signer};
        use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa44, SigningKey};
        use stwo::core::pcs::TreeVec;
        use stwo_constraint_framework::{assert_constraints_on_trace, FrameworkEval};

        let message = b"ML-DSA-44 private fold";
        let key = SigningKey::<MlDsa44>::from_seed(&[0x44; 32].into());
        let public_key: EncodedVerifyingKey<MlDsa44> = key.verifying_key().encode();
        let signature: EncodedSignature<MlDsa44> = key.sign(message).encode();
        let decoded_key =
            crate::reference::encoding::pk_decode_for(ML_DSA_44, public_key.as_slice())
                .expect("decode ML-DSA-44 public key");
        let decoded_signature =
            crate::reference::encoding::sig_decode_for(ML_DSA_44, signature.as_slice())
                .expect("decode ML-DSA-44 signature");
        let (tr, _) = crate::reference::sponge::shake256(&[public_key.as_slice()], 64);
        let input = crate::types::MlDsaVerifyInput::from_decoded_for(
            ML_DSA_44,
            &decoded_key,
            &decoded_signature,
            tr.try_into().expect("64-byte tr"),
            message.to_vec(),
        );
        let witness =
            crate::witness::generate_witness_for(ML_DSA_44, &input).expect("ML-DSA-44 witness");
        let private_witness =
            super::super::PrivateKeyEvalWitness::from_input_for(ML_DSA_44, &input)
                .expect("ML-DSA-44 private-key witness");
        let r = SecureField::from(m31(7));
        let s = SecureField::from(m31(11));
        let rho_rlc = SecureField::from(m31(13));
        let coeffs_log_size =
            crate::air_util::padded_log_size(crate::coeffs::layout::active_rows());
        let coeffs_relations = crate::coeffs::relations::CoeffsRelations::dummy();
        let coeffs = crate::coeffs::gen_coeffs_interaction(
            &witness,
            coeffs_log_size,
            r,
            s,
            &coeffs_relations,
        );
        let coeffs_trace = TreeVec::new(vec![
            crate::coeffs::gen_coeffs_preprocessed_for(ML_DSA_44, coeffs_log_size),
            crate::coeffs::gen_coeffs_base_trace(&witness, coeffs_log_size),
            coeffs.trace.clone(),
        ]);
        let coeffs_trace = coeffs_trace
            .as_ref()
            .map_cols(|column| column.to_cpu().values);
        let coeffs_trace = coeffs_trace.as_cols_ref();
        let coeffs_component = crate::coeffs::CoeffsEval {
            profile: ML_DSA_44,
            log_size: coeffs_log_size,
            r,
            s,
            relations: coeffs_relations,
        };
        assert_constraints_on_trace(
            &coeffs_trace,
            coeffs_log_size,
            |eval| {
                coeffs_component.evaluate(eval);
            },
            coeffs.claimed_sum,
        );
        let private = super::super::gen_private_key_interaction(
            &private_witness,
            r,
            s,
            &super::super::PrivateKeyEvalRelations::dummy(),
        );
        let evals = PrivateDeviceEvals::from_parts(
            &coeffs.group_evals,
            &private.a_evals,
            &private.t1_evals,
        )
        .expect("fixed private evaluation shape");

        assert_eq!(
            native_fold(&evals, ML_DSA_44, rho_rlc, r, s),
            SecureField::zero()
        );
        assert!(evals.as_slice()[46..60].iter().all(SecureField::is_zero));
        assert!(evals.as_slice()[64..66].iter().all(SecureField::is_zero));
    }
}
