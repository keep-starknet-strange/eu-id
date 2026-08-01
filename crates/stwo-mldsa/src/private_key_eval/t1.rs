use num_traits::{One, Zero};
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, Relation, RelationEntry, INTERACTION_TRACE_IDX,
};

use crate::air_util::{col_eval, enc_signed, m31, ColEval};
use crate::coeffs::tables::RcKind;
use crate::coeffs::RcUses;
use crate::constants::{D, K, N};
use crate::profile::MlDsaProfile;
#[cfg(test)]
use crate::profile::ML_DSA_65;
use crate::types::T1Poly;
use crate::witness::B;

use super::{
    gen_batched_logup, range_denominator, range_tuple, PrivateKeyEvalRelations, T1_EVAL_BASE,
};

pub const T1_ACTIVE_ROWS: usize = K * N;
pub const T1_LOG_SIZE: u32 = 11;
pub const T1_BASE_COLS: usize = 5;
pub const T1_LOGUP_ENTRIES: usize = 6;
pub const T1_INTERACTION_COLS: usize =
    SECURE_EXTENSION_DEGREE + SECURE_EXTENSION_DEGREE * T1_LOGUP_ENTRIES.div_ceil(4);

const PRE_NAMES: [&str; 5] = ["active", "eval_start", "eval_end", "poly", "index"];
const COL_LO9: usize = 0;
const COL_HI1: usize = 1;
const COL_DIGIT0: usize = 2;

const _: () = assert!(T1_ACTIVE_ROWS <= 1 << T1_LOG_SIZE);
const _: () = assert!(D == 13);
const _: () = assert!(B == 512);

#[derive(Clone, Copy)]
struct Row {
    poly: usize,
    index: usize,
    eval_start: bool,
    eval_end: bool,
}

fn schedule() -> Vec<Row> {
    let mut rows = Vec::with_capacity(T1_ACTIVE_ROWS);
    for poly in 0..K {
        for position in 0..N {
            rows.push(Row {
                poly,
                index: N - 1 - position,
                eval_start: position == 0,
                eval_end: position + 1 == N,
            });
        }
    }
    rows
}

fn pre_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_t1_{name}"),
    }
}

fn active_id(profile: MlDsaProfile) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mldsa_private_key_t1_{profile:?}_active"),
    }
}

pub fn t1_preprocessed_ids(profile: MlDsaProfile) -> Vec<PreProcessedColumnId> {
    core::iter::once(active_id(profile))
        .chain(PRE_NAMES[1..].iter().map(|name| pre_id(name)))
        .collect()
}

pub fn t1_preprocessed_log_sizes() -> Vec<u32> {
    vec![T1_LOG_SIZE; PRE_NAMES.len()]
}

pub fn gen_t1_preprocessed(profile: MlDsaProfile) -> Vec<ColEval> {
    let mut columns = vec![vec![m31(0); 1usize << T1_LOG_SIZE]; PRE_NAMES.len()];
    for (row, item) in schedule().iter().enumerate() {
        columns[0][row] = m31(u32::from(item.poly < profile.k()));
        columns[1][row] = m31(item.eval_start as u32);
        columns[2][row] = m31(item.eval_end as u32);
        columns[3][row] = m31(item.poly as u32);
        columns[4][row] = m31(item.index as u32);
    }
    columns
        .into_iter()
        .map(|column| col_eval(T1_LOG_SIZE, column))
        .collect()
}

pub fn t1_trace_layout() -> Vec<u32> {
    vec![T1_LOG_SIZE; T1_BASE_COLS]
}

pub fn t1_interaction_layout() -> Vec<u32> {
    vec![T1_LOG_SIZE; T1_INTERACTION_COLS]
}

fn split_t1(value: u32) -> (u32, u32) {
    (value & 0x1ff, value >> 9)
}

fn scaled_digits(value: u32) -> [i64; 3] {
    crate::witness::balanced_digits::<3>((value as i128) << D).map(|digit| digit as i64)
}

pub struct T1Base {
    pub trace: Vec<ColEval>,
    pub range_uses: RcUses,
}

pub fn gen_t1_base(profile: MlDsaProfile, t1: &[T1Poly; K]) -> T1Base {
    let mut columns = vec![vec![m31(0); 1usize << T1_LOG_SIZE]; T1_BASE_COLS];
    let mut range_uses = RcUses::new();
    for (row, item) in schedule().iter().enumerate() {
        if item.poly >= profile.k() {
            continue;
        }
        let value = t1[item.poly][item.index];
        assert!(value < 1 << 10, "non-canonical decoded t1 coefficient");
        let (lo9, hi1) = split_t1(value);
        columns[COL_LO9][row] = m31(lo9);
        columns[COL_HI1][row] = m31(hi1);
        range_uses.record(RcKind::Rc9, lo9);
        for (digit_index, digit) in scaled_digits(value).into_iter().enumerate() {
            columns[COL_DIGIT0 + digit_index][row] = enc_signed(digit);
            range_uses.record(RcKind::Rc9, (digit + 256) as u32);
        }
    }
    T1Base {
        trace: columns
            .into_iter()
            .map(|column| col_eval(T1_LOG_SIZE, column))
            .collect(),
        range_uses,
    }
}

#[derive(Clone)]
pub struct T1Eval {
    pub profile: MlDsaProfile,
    pub r: SecureField,
    pub s: SecureField,
    pub relations: PrivateKeyEvalRelations,
}

fn add_scaling_constraints<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    lo9: E::F,
    hi1: E::F,
    digits: &[E::F; 3],
    digit_adjustment: i64,
) {
    let one = E::F::one();
    eval.add_constraint(active.clone() * hi1.clone() * (one - hi1.clone()));
    let t1_value = lo9 + E::F::from(m31(512)) * hi1;
    let scaled = E::F::from(m31(1 << D)) * t1_value;
    let digit_value = digits[0].clone()
        + E::F::from(m31(B as u32)) * digits[1].clone()
        + E::F::from(m31((B * B) as u32)) * digits[2].clone();
    eval.add_constraint(active * (scaled - digit_value + E::F::from(enc_signed(digit_adjustment))));
}

fn add_horner_constraint<E: EvalAtRow>(
    eval: &mut E,
    active: E::F,
    eval_start: E::F,
    acc_prev: E::EF,
    acc_cur: E::EF,
    digit_row: E::EF,
    r: SecureField,
) {
    let expected_acc = E::EF::from(active)
        * (E::EF::from(E::F::one() - eval_start) * acc_prev * E::EF::from(r) + digit_row);
    eval.add_constraint(acc_cur - expected_acc);
}

impl FrameworkEval for T1Eval {
    fn log_size(&self) -> u32 {
        T1_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(active_id(self.profile));
        let eval_start = eval.get_preprocessed_column(pre_id("eval_start"));
        let eval_end = eval.get_preprocessed_column(pre_id("eval_end"));
        let poly = eval.get_preprocessed_column(pre_id("poly"));
        let index = eval.get_preprocessed_column(pre_id("index"));
        let lo9 = eval.next_trace_mask();
        let hi1 = eval.next_trace_mask();
        let digits: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
        let acc_masks: [[E::F; 2]; SECURE_EXTENSION_DEGREE] =
            core::array::from_fn(|_| eval.next_interaction_mask(INTERACTION_TRACE_IDX, [-1, 0]));
        let acc_prev = E::combine_ef(acc_masks.each_ref().map(|mask| mask[0].clone()));
        let acc_cur = E::combine_ef(acc_masks.each_ref().map(|mask| mask[1].clone()));

        let inactive = E::F::one() - active.clone();
        for value in core::iter::once(&lo9)
            .chain(core::iter::once(&hi1))
            .chain(digits.iter())
        {
            eval.add_constraint(inactive.clone() * value.clone());
        }

        add_scaling_constraints(
            &mut eval,
            active.clone(),
            lo9.clone(),
            hi1.clone(),
            &digits,
            0,
        );

        let mut s_power = SecureField::one();
        let mut digit_row = E::EF::zero();
        for digit in &digits {
            digit_row += E::EF::from(digit.clone()) * E::EF::from(s_power);
            s_power *= self.s;
        }
        add_horner_constraint(
            &mut eval,
            active.clone(),
            eval_start,
            acc_prev,
            acc_cur,
            digit_row,
            self.r,
        );

        eval.add_to_relation(RelationEntry::base(
            &self.relations.t1,
            active.clone(),
            &[poly.clone(), index, lo9.clone(), hi1],
        ));
        eval.add_to_relation(RelationEntry::base(
            &self.relations.range,
            active.clone(),
            &range_tuple::<E>(lo9, RcKind::Rc9),
        ));
        for digit in digits {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range,
                active.clone(),
                &range_tuple::<E>(digit + E::F::from(m31(256)), RcKind::Rc9),
            ));
        }
        let mut tuple = vec![poly + E::F::from(m31(T1_EVAL_BASE as u32))];
        tuple.extend(acc_masks.iter().map(|mask| mask[1].clone()));
        eval.add_to_relation(RelationEntry::base(&self.relations.eval, -eval_end, &tuple));
        eval.finalize_logup_batched(4);
        eval
    }
}

pub struct T1Interaction {
    pub trace: Vec<ColEval>,
    pub evals: Vec<SecureField>,
    pub claimed_sum: SecureField,
}

pub fn gen_t1_interaction(
    profile: MlDsaProfile,
    t1: &[T1Poly; K],
    r: SecureField,
    s: SecureField,
    relations: &PrivateKeyEvalRelations,
) -> T1Interaction {
    let zero = SecureField::zero();
    let one = SecureField::one();
    let mut rows = vec![vec![(zero, one); T1_LOGUP_ENTRIES]; 1usize << T1_LOG_SIZE];
    let mut acc = vec![zero; 1usize << T1_LOG_SIZE];
    let mut evals = vec![zero; K];
    let mut running = zero;
    for (row, item) in schedule().iter().enumerate() {
        if item.poly >= profile.k() {
            acc[row] = zero;
            if item.eval_end {
                rows[row][T1_LOGUP_ENTRIES - 1] = (
                    -one,
                    relations.eval.combine(&[
                        m31((T1_EVAL_BASE + item.poly) as u32),
                        m31(0),
                        m31(0),
                        m31(0),
                        m31(0),
                    ]),
                );
            }
            continue;
        }
        let value = t1[item.poly][item.index];
        let (lo9, hi1) = split_t1(value);
        let digits = scaled_digits(value);
        let digit_row = SecureField::from(enc_signed(digits[0]))
            + s * SecureField::from(enc_signed(digits[1]))
            + s * s * SecureField::from(enc_signed(digits[2]));
        running = if item.eval_start {
            digit_row
        } else {
            running * r + digit_row
        };
        acc[row] = running;

        let mut entries = Vec::with_capacity(T1_LOGUP_ENTRIES);
        entries.push((
            one,
            relations.t1.combine(&[
                m31(item.poly as u32),
                m31(item.index as u32),
                m31(lo9),
                m31(hi1),
            ]),
        ));
        entries.push((one, range_denominator(&relations.range, lo9, RcKind::Rc9)));
        for digit in digits {
            entries.push((
                one,
                range_denominator(&relations.range, (digit + 256) as u32, RcKind::Rc9),
            ));
        }
        if item.eval_end {
            evals[item.poly] = running;
            let coords = running.to_m31_array();
            entries.push((
                -one,
                relations.eval.combine(&[
                    m31((T1_EVAL_BASE + item.poly) as u32),
                    coords[0],
                    coords[1],
                    coords[2],
                    coords[3],
                ]),
            ));
        } else {
            entries.push((zero, one));
        }
        assert_eq!(entries.len(), T1_LOGUP_ENTRIES);
        rows[row] = entries;
    }
    let mut trace: Vec<_> = (0..SECURE_EXTENSION_DEGREE)
        .map(|coordinate| {
            col_eval(
                T1_LOG_SIZE,
                acc.iter()
                    .map(|value| value.to_m31_array()[coordinate])
                    .collect(),
            )
        })
        .collect();
    let (logup, claimed_sum) = gen_batched_logup(T1_LOG_SIZE, &rows, T1_LOGUP_ENTRIES);
    trace.extend(logup);
    T1Interaction {
        trace,
        evals,
        claimed_sum,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_key_eval::proof_test::{active_id as test_active_id, OneRowAir};
    use air_core::{Air, AirProver, TreeLayout};
    use stwo::core::air::Component;
    use stwo::core::channel::Blake2sChannel;
    use stwo::core::pcs::PcsConfig;
    use stwo::prover::backend::simd::m31::LOG_N_LANES;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::{ComponentProver, TreeBuilder};
    use stwo_constraint_framework::{FrameworkComponent, TraceLocationAllocator};

    use crate::coeffs::relations::{RangeRelation, SharedRangeRelation};
    use crate::coeffs::tables::SharedRangeTable;

    fn proof_pcs_config() -> PcsConfig {
        PcsConfig {
            fri_config: stwo::core::fri::FriConfig::new(0, 2, 3, 1),
            ..PcsConfig::default()
        }
    }

    #[derive(Clone)]
    struct ScalingFormulaEval {
        digit_adjustment: i64,
    }

    impl FrameworkEval for ScalingFormulaEval {
        fn log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 2
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let fixed_active = eval.get_preprocessed_column(test_active_id());
            let active = eval.next_trace_mask();
            let lo9 = eval.next_trace_mask();
            let hi1 = eval.next_trace_mask();
            let digits = core::array::from_fn(|_| eval.next_trace_mask());
            eval.add_constraint(active.clone() - fixed_active);
            add_scaling_constraints(&mut eval, active, lo9, hi1, &digits, self.digit_adjustment);
            let dummy =
                eval.next_interaction_mask(stwo_constraint_framework::INTERACTION_TRACE_IDX, [0]);
            eval.add_constraint(dummy[0].clone());
            eval
        }
    }

    #[derive(Clone)]
    struct HornerFormulaEval {
        r: SecureField,
        s: SecureField,
    }

    impl FrameworkEval for HornerFormulaEval {
        fn log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 1
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let fixed_active = eval.get_preprocessed_column(test_active_id());
            let active = eval.next_trace_mask();
            let eval_start = eval.next_trace_mask();
            let digits: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
            let acc_prev = E::combine_ef(core::array::from_fn(|_| eval.next_trace_mask()));
            let acc_cur = E::combine_ef(core::array::from_fn(|_| eval.next_trace_mask()));
            eval.add_constraint(active.clone() - fixed_active);

            let mut s_power = SecureField::one();
            let mut digit_row = E::EF::zero();
            for digit in digits {
                digit_row += E::EF::from(digit) * E::EF::from(s_power);
                s_power *= self.s;
            }
            add_horner_constraint(
                &mut eval, active, eval_start, acc_prev, acc_cur, digit_row, self.r,
            );
            let dummy =
                eval.next_interaction_mask(stwo_constraint_framework::INTERACTION_TRACE_IDX, [0]);
            eval.add_constraint(dummy[0].clone());
            eval
        }
    }

    fn assert_boundary_scaling_rejected(label: &str, value: u32, digit_adjustment: i64) {
        let (lo9, hi1) = split_t1(value);
        let mut digits = scaled_digits(value);
        digits[0] += digit_adjustment;
        let trace = [
            m31(1),
            m31(lo9),
            m31(hi1),
            enc_signed(digits[0]),
            enc_signed(digits[1]),
            enc_signed(digits[2]),
        ];
        let forged = ScalingFormulaEval { digit_adjustment };
        let exact = ScalingFormulaEval {
            digit_adjustment: 0,
        };
        let mut prover = OneRowAir::new(forged.clone(), &trace);
        let proof = air_core::prove(&mut [&mut prover], proof_pcs_config())
            .unwrap_or_else(|error| panic!("{label}: forged proving failed: {error:?}"));
        let mut forged_verifier = OneRowAir::new(forged, &trace);
        air_core::verify(&mut [&mut forged_verifier], &proof)
            .unwrap_or_else(|error| panic!("{label}: forged control failed: {error:?}"));
        let mut exact_verifier = OneRowAir::new(exact, &trace);
        assert!(
            air_core::verify(&mut [&mut exact_verifier], &proof).is_err(),
            "{label}: the exact scaling formula must reject the input"
        );
    }

    #[derive(Clone)]
    struct RangeAliasEval {
        relation: RangeRelation,
        require_alias_digit: bool,
    }

    impl FrameworkEval for RangeAliasEval {
        fn log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 2
        }

        fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
            let fixed_active = eval.get_preprocessed_column(test_active_id());
            let active = eval.next_trace_mask();
            let lo9 = eval.next_trace_mask();
            let _hi1 = eval.next_trace_mask();
            let digits: [E::F; 3] = core::array::from_fn(|_| eval.next_trace_mask());
            eval.add_constraint(active.clone() - fixed_active);
            for (numerator, value) in [
                (active.clone(), lo9),
                (
                    active.clone() * E::F::from(m31(u32::from(self.require_alias_digit))),
                    digits[0].clone() + E::F::from(m31(256)),
                ),
                (active.clone(), digits[1].clone() + E::F::from(m31(256))),
                (active, digits[2].clone() + E::F::from(m31(256))),
            ] {
                eval.add_to_relation(RelationEntry::base(
                    &self.relation,
                    numerator,
                    &range_tuple::<E>(value, RcKind::Rc9),
                ));
            }
            eval.finalize_logup_batched(4);
            eval
        }
    }

    struct RangeAliasAir {
        handle: SharedRangeRelation,
        relation: Option<RangeRelation>,
        trace: Option<Vec<ColEval>>,
        lookup_values: [u32; 4],
        require_alias_digit: bool,
        claimed_sum: SecureField,
        component: Option<FrameworkComponent<RangeAliasEval>>,
    }

    impl RangeAliasAir {
        fn prover(value: u32, handle: SharedRangeRelation) -> (Self, RcUses) {
            let (lo9, hi1) = split_t1(value);
            let mut digits = scaled_digits(value);
            digits[0] += B as i64;
            digits[1] -= 1;
            assert_eq!(
                digits[0] + 512 * digits[1] + 512 * 512 * digits[2],
                (value as i64) << D,
                "carry alias must preserve the exact scaled integer"
            );
            let trace_values = [
                m31(1),
                m31(lo9),
                m31(hi1),
                enc_signed(digits[0]),
                enc_signed(digits[1]),
                enc_signed(digits[2]),
            ];
            let trace = trace_values
                .into_iter()
                .map(|value| {
                    let mut column = vec![m31(0); 1usize << LOG_N_LANES];
                    column[0] = value;
                    col_eval(LOG_N_LANES, column)
                })
                .collect();
            let lookup_values = [
                lo9,
                (digits[0] + 256) as u32,
                (digits[1] + 256) as u32,
                (digits[2] + 256) as u32,
            ];
            let mut uses = RcUses::new();
            uses.record(RcKind::Rc9, lookup_values[0]);
            uses.record(RcKind::Rc9, lookup_values[2]);
            uses.record(RcKind::Rc9, lookup_values[3]);
            (
                Self {
                    handle,
                    relation: None,
                    trace: Some(trace),
                    lookup_values,
                    require_alias_digit: false,
                    claimed_sum: SecureField::zero(),
                    component: None,
                },
                uses,
            )
        }

        fn verifier(
            claimed_sum: SecureField,
            handle: SharedRangeRelation,
            lookup_values: [u32; 4],
            require_alias_digit: bool,
        ) -> Self {
            Self {
                handle,
                relation: None,
                trace: None,
                lookup_values,
                require_alias_digit,
                claimed_sum,
                component: None,
            }
        }

        fn relation(&self) -> RangeRelation {
            self.relation.clone().expect("range relation drawn")
        }
    }

    impl Air for RangeAliasAir {
        fn mix_public(&self, _channel: &mut Blake2sChannel) {}

        fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {
            self.relation = Some(self.handle.get());
        }

        fn layout(&self) -> TreeLayout {
            TreeLayout {
                preprocessed: vec![LOG_N_LANES],
                trace: vec![LOG_N_LANES; 6],
                interaction: vec![LOG_N_LANES; SECURE_EXTENSION_DEGREE],
            }
        }

        fn claimed_sums(&self) -> Vec<SecureField> {
            vec![self.claimed_sum]
        }

        fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
            vec![test_active_id()]
        }

        fn canonical_preprocessed_columns(
            &mut self,
        ) -> Result<Vec<ColEval>, stwo::core::verifier::VerificationError> {
            let mut active = vec![m31(0); 1usize << LOG_N_LANES];
            active[0] = m31(1);
            Ok(vec![col_eval(LOG_N_LANES, active)])
        }

        fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
            self.component = Some(FrameworkComponent::new(
                allocator,
                RangeAliasEval {
                    relation: self.relation(),
                    require_alias_digit: self.require_alias_digit,
                },
                self.claimed_sum,
            ));
        }

        fn components(&self) -> Vec<&dyn Component> {
            vec![self.component.as_ref().expect("range alias component")]
        }
    }

    impl AirProver for RangeAliasAir {
        fn max_log_size(&self) -> u32 {
            LOG_N_LANES
        }

        fn max_constraint_log_degree_bound(&self) -> u32 {
            LOG_N_LANES + 2
        }

        fn store_polynomial_coefficients(&self) -> bool {
            true
        }

        fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(
                self.canonical_preprocessed_columns()
                    .expect("range alias preprocessed"),
            );
        }

        fn preprocessed_column_fingerprints(
            &mut self,
        ) -> Vec<air_core::PreprocessedColumnFingerprint> {
            let ids = self.preprocessed_column_ids();
            let columns = self
                .canonical_preprocessed_columns()
                .expect("range alias preprocessed");
            air_core::fingerprint_preprocessed_columns("private_t1_range_alias", &ids, &columns)
        }

        fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            tb.extend_evals(self.trace.take().expect("range alias trace"));
        }

        fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
            let zero = SecureField::zero();
            let one = SecureField::one();
            let mut rows = vec![vec![(zero, one); 4]; 1usize << LOG_N_LANES];
            rows[0] = self
                .lookup_values
                .into_iter()
                .enumerate()
                .map(|(index, value)| {
                    (
                        if index == 1 { zero } else { one },
                        range_denominator(&self.relation(), value, RcKind::Rc9),
                    )
                })
                .collect();
            let (trace, claimed_sum) = gen_batched_logup(LOG_N_LANES, &rows, 4);
            self.claimed_sum = claimed_sum;
            tb.extend_evals(trace);
        }

        fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
            vec![self.component.as_ref().expect("range alias component")]
        }
    }

    fn assert_true_carry_alias_rejected(value: u32) {
        let handle = SharedRangeRelation::new();
        let (mut consumer, uses) = RangeAliasAir::prover(value, handle.clone());
        let lookup_values = consumer.lookup_values;
        let mut table = SharedRangeTable::prover(&[uses], handle);
        let prove_result = air_core::prove(&mut [&mut table, &mut consumer], proof_pcs_config());
        assert_eq!(
            table.claimed_sum() + consumer.claimed_sum,
            SecureField::zero(),
            "t1={value}: forged range claims must cancel"
        );
        let proof = prove_result
            .unwrap_or_else(|error| panic!("t1={value}: alias proving failed: {error:?}"));

        let handle = SharedRangeRelation::new();
        let mut forged_table = SharedRangeTable::verifier(table.claimed_sum(), handle.clone());
        let mut forged_consumer =
            RangeAliasAir::verifier(consumer.claimed_sum, handle, lookup_values, false);
        air_core::verify(&mut [&mut forged_table, &mut forged_consumer], &proof)
            .unwrap_or_else(|error| panic!("t1={value}: forged range control failed: {error:?}"));

        let handle = SharedRangeRelation::new();
        let mut table_verifier = SharedRangeTable::verifier(table.claimed_sum(), handle.clone());
        let mut exact_consumer =
            RangeAliasAir::verifier(consumer.claimed_sum, handle, lookup_values, true);
        assert!(
            air_core::verify(&mut [&mut table_verifier, &mut exact_consumer], &proof).is_err(),
            "t1={value}: the signed Rc9 lookup must reject the carry alias"
        );
    }

    #[test]
    fn malformed_t1_boundary_rows_prove_only_under_forged_formulas() {
        for value in [0, 1023] {
            assert_boundary_scaling_rejected(&format!("t1={value} wrong scaling digit"), value, 1);
            assert_true_carry_alias_rejected(value);
        }
    }

    #[test]
    fn self_consistent_wrong_t1_horner_evaluation_proves_only_under_forged_formula() {
        let exact_r = SecureField::from(m31(17));
        let forged_r = SecureField::from(m31(18));
        let s = SecureField::from(m31(31));
        let digits = [enc_signed(3), enc_signed(-2), enc_signed(1)];
        let acc_prev = SecureField::from(m31(5));
        let digit_row = SecureField::from(digits[0])
            + s * SecureField::from(digits[1])
            + s * s * SecureField::from(digits[2]);
        let acc_cur = acc_prev * forged_r + digit_row;
        assert_ne!(
            acc_cur,
            acc_prev * exact_r + digit_row,
            "forged accumulator must violate the exact recurrence"
        );

        let mut trace = vec![m31(1), m31(0)];
        trace.extend(digits);
        trace.extend(acc_prev.to_m31_array());
        trace.extend(acc_cur.to_m31_array());

        let forged = HornerFormulaEval { r: forged_r, s };
        let exact = HornerFormulaEval { r: exact_r, s };
        let mut prover = OneRowAir::new(forged.clone(), &trace);
        let proof = air_core::prove(&mut [&mut prover], proof_pcs_config())
            .expect("self-consistent forged Horner evaluation must prove under the forged formula");

        let mut forged_verifier = OneRowAir::new(forged, &trace);
        air_core::verify(&mut [&mut forged_verifier], &proof)
            .expect("forged Horner formula control must verify");

        let mut exact_verifier = OneRowAir::new(exact, &trace);
        assert!(
            air_core::verify(&mut [&mut exact_verifier], &proof).is_err(),
            "the exact Horner formula must reject an accumulator built with the wrong r"
        );
    }

    #[test]
    fn every_canonical_t1_has_a_unique_exact_scaled_encoding() {
        let mut seen = std::collections::HashSet::new();
        for value in 0..1 << 10 {
            let (lo9, hi1) = split_t1(value);
            assert!(lo9 < 512);
            assert!(hi1 < 2);
            assert_eq!(lo9 + 512 * hi1, value);
            let digits = scaled_digits(value);
            assert!(digits.iter().all(|digit| (-256..256).contains(digit)));
            assert_eq!(
                digits[0] + 512 * digits[1] + 512 * 512 * digits[2],
                (value as i64) << D
            );
            assert!(seen.insert(digits));
        }
        assert_eq!(scaled_digits(0), [0, 0, 0]);
        assert_eq!(scaled_digits(1023), [0, -16, 32]);
    }

    #[test]
    fn horner_evaluations_match_independent_computation() {
        let mut t1 = [[0u32; N]; K];
        for (poly, coefficients) in t1.iter_mut().enumerate() {
            for (index, value) in coefficients.iter_mut().enumerate() {
                *value = ((poly * 97 + index * 13) & 1023) as u32;
            }
        }
        let r = SecureField::from(m31(17));
        let s = SecureField::from(m31(31));
        let interaction =
            gen_t1_interaction(ML_DSA_65, &t1, r, s, &PrivateKeyEvalRelations::dummy());
        for (poly, coefficients) in t1.iter().enumerate() {
            let mut expected = SecureField::zero();
            for &value in coefficients.iter().rev() {
                let digits = scaled_digits(value);
                let row = SecureField::from(enc_signed(digits[0]))
                    + s * SecureField::from(enc_signed(digits[1]))
                    + s * s * SecureField::from(enc_signed(digits[2]));
                expected = expected * r + row;
            }
            assert_eq!(interaction.evals[poly], expected);
        }
    }

    #[test]
    fn base_range_census_has_exact_lookup_count() {
        let t1 = [[1023u32; N]; K];
        let base = gen_t1_base(ML_DSA_65, &t1);
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc9).iter().sum::<u32>(),
            (4 * T1_ACTIVE_ROWS) as u32
        );
        for kind in [RcKind::Rc13, RcKind::Rc8, RcKind::Rc7, RcKind::Ternary] {
            assert_eq!(base.range_uses.for_kind(kind).iter().sum::<u32>(), 0);
        }
    }
}
