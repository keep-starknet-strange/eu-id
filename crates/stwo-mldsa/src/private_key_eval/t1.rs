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

pub fn t1_preprocessed_ids() -> Vec<PreProcessedColumnId> {
    PRE_NAMES.iter().map(|name| pre_id(name)).collect()
}

pub fn t1_preprocessed_log_sizes() -> Vec<u32> {
    vec![T1_LOG_SIZE; PRE_NAMES.len()]
}

pub fn gen_t1_preprocessed() -> Vec<ColEval> {
    let mut columns = vec![vec![m31(0); 1usize << T1_LOG_SIZE]; PRE_NAMES.len()];
    for (row, item) in schedule().iter().enumerate() {
        columns[0][row] = m31(1);
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

pub fn gen_t1_base(t1: &[T1Poly; K]) -> T1Base {
    let mut columns = vec![vec![m31(0); 1usize << T1_LOG_SIZE]; T1_BASE_COLS];
    let mut range_uses = RcUses::new();
    for (row, item) in schedule().iter().enumerate() {
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
    pub r: SecureField,
    pub s: SecureField,
    pub relations: PrivateKeyEvalRelations,
}

impl FrameworkEval for T1Eval {
    fn log_size(&self) -> u32 {
        T1_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(pre_id("active"));
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

        let one = E::F::one();
        eval.add_constraint(active.clone() * hi1.clone() * (one.clone() - hi1.clone()));
        let t1_value = lo9.clone() + E::F::from(m31(512)) * hi1.clone();
        let scaled = E::F::from(m31(1 << D)) * t1_value;
        let digit_value = digits[0].clone()
            + E::F::from(m31(B as u32)) * digits[1].clone()
            + E::F::from(m31((B * B) as u32)) * digits[2].clone();
        eval.add_constraint(active.clone() * (scaled - digit_value));

        let mut s_power = SecureField::one();
        let mut digit_row = E::EF::zero();
        for digit in &digits {
            digit_row += E::EF::from(digit.clone()) * E::EF::from(s_power);
            s_power *= self.s;
        }
        let expected_acc = E::EF::from(active.clone())
            * (E::EF::from(one - eval_start) * acc_prev * E::EF::from(self.r) + digit_row);
        eval.add_constraint(acc_cur - expected_acc);

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
        let interaction = gen_t1_interaction(&t1, r, s, &PrivateKeyEvalRelations::dummy());
        for poly in 0..K {
            let mut expected = SecureField::zero();
            for &value in t1[poly].iter().rev() {
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
        let base = gen_t1_base(&t1);
        assert_eq!(
            base.range_uses.for_kind(RcKind::Rc9).iter().sum::<u32>(),
            (4 * T1_ACTIVE_ROWS) as u32
        );
        for kind in [RcKind::Rc13, RcKind::Rc8, RcKind::Rc7, RcKind::Ternary] {
            assert_eq!(base.range_uses.for_kind(kind).iter().sum::<u32>(), 0);
        }
    }
}
