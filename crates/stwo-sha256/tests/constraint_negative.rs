use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
use stwo::core::utils::{
    bit_reverse_index, circle_domain_index_to_coset_index, coset_index_to_circle_domain_index,
};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkEval, Relation, RelationEntry, ORIGINAL_TRACE_IDX,
};

use stwo_sha256::components::{is_first_row_column_id, round_cyclic_column_ids};
use stwo_sha256::constraints::Sha256Eval;
use stwo_sha256::relations::Sha256Relations;
use stwo_sha256::trace::{generate_trace, Layout, ROWS_PER_BLOCK};
use stwo_sha256::witness::compute_packed_sha256_witness;

#[derive(Debug, Clone)]
struct Residual {
    natural_row: usize,
    constraint_idx: usize,
    value: SecureField,
}

struct LinearConstraintCollector<'a> {
    trace: &'a [Vec<BaseField>],
    log_size: u32,
    natural_row: usize,
    col_index: usize,
    constraint_idx: usize,
    non_zero: Vec<Residual>,
}

impl<'a> LinearConstraintCollector<'a> {
    fn new(trace: &'a [Vec<BaseField>], log_size: u32, natural_row: usize) -> Self {
        Self {
            trace,
            log_size,
            natural_row,
            col_index: 0,
            constraint_idx: 0,
            non_zero: Vec::new(),
        }
    }
}

impl EvalAtRow for LinearConstraintCollector<'_> {
    type F = BaseField;
    type EF = SecureField;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        assert_eq!(interaction, ORIGINAL_TRACE_IDX);
        let col_index = self.col_index;
        self.col_index += 1;
        let current_slot = Layout::row_slot(self.natural_row, self.log_size);
        let domain_size = 1isize << self.log_size;
        let coset_index = circle_domain_index_to_coset_index(
            bit_reverse_index(current_slot, self.log_size),
            self.log_size,
        ) as isize;
        offsets.map(|offset| {
            let next_coset_index = (coset_index + offset).rem_euclid(domain_size);
            let next_slot = bit_reverse_index(
                coset_index_to_circle_domain_index(next_coset_index as usize, self.log_size),
                self.log_size,
            );
            self.trace[col_index][next_slot]
        })
    }

    fn get_preprocessed_column(&mut self, column: PreProcessedColumnId) -> Self::F {
        if column == is_first_row_column_id() {
            return BaseField::from(u32::from(self.natural_row == 0));
        }
        let t = self.natural_row % stwo_sha256::constants::N_ROUNDS;
        let cyclic = round_cyclic_column_ids();
        let flag = |value: bool| BaseField::from(u32::from(value));
        if column == cyclic[0] {
            BaseField::from(stwo_sha256::constants::K[t] & 0xffff)
        } else if column == cyclic[1] {
            BaseField::from(stwo_sha256::constants::K[t] >> 16)
        } else if column == cyclic[2] {
            flag(t == 0)
        } else if column == cyclic[3] {
            flag(t == 1)
        } else if column == cyclic[4] {
            flag(t == 2)
        } else if column == cyclic[5] {
            flag(t == 3)
        } else if column == cyclic[6] {
            flag(t == 15)
        } else if column == cyclic[7] {
            flag(t == stwo_sha256::constants::N_ROUNDS - 1)
        } else if column == cyclic[8] {
            flag(t >= 16)
        } else {
            panic!("unknown SHA preprocessed column {column:?}");
        }
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        let value = SecureField::from(constraint);
        if !value.is_zero() {
            self.non_zero.push(Residual {
                natural_row: self.natural_row,
                constraint_idx: self.constraint_idx,
                value,
            });
        }
        self.constraint_idx += 1;
    }

    fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        SecureField::from_m31_array(values)
    }

    fn add_to_relation<R: Relation<Self::F, Self::EF>>(
        &mut self,
        _entry: RelationEntry<'_, Self::F, Self::EF, R>,
    ) {
    }

    fn finalize_logup_batched(&mut self, _batch_size: usize) {}
    fn finalize_logup_in_pairs(&mut self) {}
}

fn first_constraint_failure(
    trace: &[Vec<BaseField>],
    log_size: u32,
) -> Option<(usize, usize, SecureField)> {
    for natural_row in 0..(1usize << log_size) {
        let evaluator = Sha256Eval {
            log_size,
            relations: Sha256Relations::dummy(),
            expose_digest: true,
            expose_field: true,
            claim_mask_beta: None,
        };
        let collector =
            evaluator.evaluate(LinearConstraintCollector::new(trace, log_size, natural_row));
        assert_eq!(collector.col_index, Layout::TOTAL_COLS);
        if let Some(residual) = collector.non_zero.first() {
            return Some((
                residual.natural_row,
                residual.constraint_idx,
                residual.value,
            ));
        }
    }
    None
}

fn row_has_constraint_failure(trace: &[Vec<BaseField>], log_size: u32, natural_row: usize) -> bool {
    let evaluator = Sha256Eval {
        log_size,
        relations: Sha256Relations::dummy(),
        expose_digest: true,
        expose_field: true,
        claim_mask_beta: None,
    };
    let collector =
        evaluator.evaluate(LinearConstraintCollector::new(trace, log_size, natural_row));
    assert_eq!(collector.col_index, Layout::TOTAL_COLS);
    !collector.non_zero.is_empty()
}

fn assert_air_accepts(trace: &[Vec<BaseField>], log_size: u32) {
    assert_eq!(
        first_constraint_failure(trace, log_size),
        None,
        "honest packed trace must satisfy every base constraint"
    );
}

fn assert_air_rejects(label: &str, trace: &[Vec<BaseField>], log_size: u32) {
    let residual = first_constraint_failure(trace, log_size);
    assert!(residual.is_some(), "{label} must produce a base residual");
}

fn set_natural(
    trace: &mut [Vec<BaseField>],
    column: usize,
    natural_row: usize,
    value: u32,
    log_size: u32,
) {
    trace[column][Layout::row_slot(natural_row, log_size)] = BaseField::from(value);
}

fn add_one_natural(trace: &mut [Vec<BaseField>], column: usize, natural_row: usize, log_size: u32) {
    let slot = Layout::row_slot(natural_row, log_size);
    trace[column][slot] += BaseField::from(1);
}

fn set_block_column(
    trace: &mut [Vec<BaseField>],
    column: usize,
    block: usize,
    value: u32,
    log_size: u32,
) {
    for t in 0..ROWS_PER_BLOCK {
        set_natural(trace, column, block * ROWS_PER_BLOCK + t, value, log_size);
    }
}

fn honest_fixture() -> (Vec<Vec<BaseField>>, u32) {
    let messages: [&[u8]; 3] = [b"a", &[0x42; 100], b"z"];
    let witness = compute_packed_sha256_witness(&messages).unwrap();
    (generate_trace(&witness, 9), 9)
}

#[test]
fn honest_packed_trace_satisfies_all_base_constraints() {
    let (trace, log_size) = honest_fixture();
    assert_air_accepts(&trace, log_size);
}

#[test]
fn packed_capacity_errors_are_checked() {
    assert!(matches!(
        compute_packed_sha256_witness(&[]),
        Err(stwo_sha256::witness::PackedSha256Error::EmptyMessageSet)
    ));
    let message = vec![0u8; 16_320];
    let witness = compute_packed_sha256_witness(&[message.as_slice()]).unwrap();
    assert!(matches!(
        stwo_sha256::air::Sha256Prover::new(&witness, 14),
        Err(stwo_sha256::witness::PackedSha256Error::TraceTooSmall {
            real_blocks: 256,
            max_real_blocks: 255
        })
    ));
}

#[test]
fn base_trace_mutations_are_rejected() {
    let (honest, log_size) = honest_fixture();

    let mut trace = honest.clone();
    for row in 256..512 {
        set_natural(&mut trace, Layout::COL_ENABLER, row, 1, log_size);
    }
    assert_air_rejects("full circle", &trace, log_size);

    let mut trace = honest.clone();
    for row in 5..512 {
        set_natural(&mut trace, Layout::COL_ENABLER, row, 0, log_size);
    }
    assert_air_rejects("non-R0 cutoff", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(&mut trace, Layout::COL_ENABLER, 511, 1, log_size);
    assert_air_rejects("circle-end re-enable", &trace, log_size);
    assert!(row_has_constraint_failure(&trace, log_size, 511));
    assert!(row_has_constraint_failure(&trace, log_size, 0));

    let mut trace = honest.clone();
    set_natural(&mut trace, Layout::COL_MSG_START, 0, 0, log_size);
    assert_air_rejects("cleared first start", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_MSG_START,
        ROWS_PER_BLOCK + 1,
        1,
        log_size,
    );
    assert_air_rejects("start on wrong round", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_MSG_START,
        4 * ROWS_PER_BLOCK,
        1,
        log_size,
    );
    assert_air_rejects("start while disabled", &trace, log_size);

    let mut trace = honest.clone();
    let (h_in_lo, _) = Layout::h_in_word(0);
    add_one_natural(&mut trace, h_in_lo, ROWS_PER_BLOCK, log_size);
    assert_air_rejects("start without IV", &trace, log_size);

    let mut trace = honest.clone();
    for word in 0..8 {
        let (lo, hi) = Layout::h_in_word(word);
        let value = stwo_sha256::constants::IV[word];
        set_natural(&mut trace, lo, 2 * ROWS_PER_BLOCK, value & 0xffff, log_size);
        set_natural(&mut trace, hi, 2 * ROWS_PER_BLOCK, value >> 16, log_size);
    }
    assert_air_rejects("IV on continuation", &trace, log_size);

    let mut trace = honest.clone();
    add_one_natural(&mut trace, h_in_lo, 2 * ROWS_PER_BLOCK, log_size);
    assert_air_rejects("broken chain", &trace, log_size);

    let mut trace = honest.clone();
    set_block_column(&mut trace, Layout::COL_MSG_ID, 1, 2, log_size);
    set_block_column(&mut trace, Layout::COL_MSG_ID, 2, 2, log_size);
    set_block_column(&mut trace, Layout::COL_MSG_ID, 3, 3, log_size);
    assert_air_rejects("ID skip", &trace, log_size);

    let mut trace = honest.clone();
    set_block_column(&mut trace, Layout::COL_MSG_ID, 1, 0, log_size);
    set_block_column(&mut trace, Layout::COL_MSG_ID, 2, 0, log_size);
    set_block_column(&mut trace, Layout::COL_MSG_ID, 3, 1, log_size);
    assert_air_rejects("ID repeat", &trace, log_size);

    let mut trace = honest.clone();
    set_block_column(&mut trace, Layout::COL_MSG_ID, 3, 0, log_size);
    assert_air_rejects("ID decrement", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_MSG_ID,
        ROWS_PER_BLOCK + 17,
        2,
        log_size,
    );
    assert_air_rejects("ID mid-block", &trace, log_size);

    let mut trace = honest.clone();
    set_block_column(&mut trace, Layout::COL_MSG_BLOCK, 1, 1, log_size);
    set_block_column(&mut trace, Layout::COL_MSG_BLOCK, 2, 2, log_size);
    assert_air_rejects("block not reset", &trace, log_size);

    let mut trace = honest.clone();
    set_block_column(&mut trace, Layout::COL_MSG_BLOCK, 2, 2, log_size);
    assert_air_rejects("block skipped", &trace, log_size);

    let mut trace = honest.clone();
    set_block_column(&mut trace, Layout::COL_MSG_BLOCK, 2, 0, log_size);
    assert_air_rejects("block repeated", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_MSG_BLOCK,
        2 * ROWS_PER_BLOCK + 17,
        2,
        log_size,
    );
    assert_air_rejects("block mid-row", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(&mut trace, Layout::COL_IS_MSG_LAST, 62, 1, log_size);
    assert_air_rejects("terminal forged", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(&mut trace, Layout::COL_IS_MSG_LAST, 63, 0, log_size);
    assert_air_rejects("terminal cleared", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(&mut trace, Layout::COL_IS_MSG_LAST, 63, 0, log_size);
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        ROWS_PER_BLOCK + 63,
        1,
        log_size,
    );
    assert_air_rejects("terminal moved", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        4 * ROWS_PER_BLOCK + 63,
        1,
        log_size,
    );
    assert_air_rejects("disabled digest yield", &trace, log_size);

    let mut trace = honest;
    for t in 0..ROWS_PER_BLOCK {
        set_natural(
            &mut trace,
            Layout::COL_ENABLER,
            4 * ROWS_PER_BLOCK + t,
            1,
            log_size,
        );
    }
    assert_air_rejects("disabled stream yield", &trace, log_size);
}
