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
use stwo_sha256::constants::N_ROUNDS;
use stwo_sha256::constraints::Sha256Eval;
use stwo_sha256::relations::Sha256Relations;
use stwo_sha256::trace::{generate_trace, Layout, ROWS_PER_BLOCK, STATE_SEED_ROWS, WORD_BIT_COLS};
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
        let position = self.natural_row % ROWS_PER_BLOCK;
        let is_round = position >= STATE_SEED_ROWS;
        let t = position.saturating_sub(STATE_SEED_ROWS);
        let cyclic = round_cyclic_column_ids();
        let flag = |value: bool| BaseField::from(u32::from(value));
        if column == cyclic[0] {
            BaseField::from(u32::from(is_round) * (stwo_sha256::constants::K[t] & 0xffff))
        } else if column == cyclic[1] {
            BaseField::from(u32::from(is_round) * (stwo_sha256::constants::K[t] >> 16))
        } else if column == cyclic[2] {
            flag(position == 0)
        } else if column == cyclic[3] {
            flag(is_round && t == 0)
        } else if column == cyclic[4] {
            flag(is_round && t == 15)
        } else if column == cyclic[5] {
            flag(is_round && t == stwo_sha256::constants::N_ROUNDS - 1)
        } else if column == cyclic[6] {
            flag(is_round && t >= 16)
        } else if column == cyclic[7] {
            flag(is_round)
        } else if column == cyclic[8] {
            BaseField::from(u32::from(is_round) * t as u32)
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

fn flip_natural(trace: &mut [Vec<BaseField>], column: usize, natural_row: usize, log_size: u32) {
    let slot = Layout::row_slot(natural_row, log_size);
    trace[column][slot] = BaseField::from(1 - trace[column][slot].0);
}

fn set_seeded_state_word(
    trace: &mut [Vec<BaseField>],
    block: usize,
    word: usize,
    value: u32,
    log_size: u32,
) {
    let lane = usize::from(word >= 4);
    let position = word % 4;
    let natural_row = block * ROWS_PER_BLOCK
        + if position == 0 {
            STATE_SEED_ROWS
        } else {
            STATE_SEED_ROWS - position
        };
    for bit in 0..WORD_BIT_COLS {
        set_natural(
            trace,
            Layout::round_operand_bit(lane, bit),
            natural_row,
            (value >> bit) & 1,
            log_size,
        );
    }
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
fn rejects_aliased_cells_outside_round_15_and_round_63() {
    let (trace, log_size) = honest_fixture();
    assert_air_accepts(&trace, log_size);
    let natural_row = STATE_SEED_ROWS + stwo_sha256::constants::N_ROUNDS - 2;
    for column in Layout::COL_PADDING_START..Layout::COL_PADDING_END {
        let mut mutated = trace.clone();
        add_one_natural(&mut mutated, column, natural_row, log_size);
        assert!(
            row_has_constraint_failure(&mutated, log_size, natural_row),
            "aliased column {column} must be zero outside t=15/t=63"
        );
    }
}

#[test]
fn rejects_padding_value_in_aliased_slot_at_round_63() {
    let (mut trace, log_size) = honest_fixture();
    let natural_row = STATE_SEED_ROWS + stwo_sha256::constants::N_ROUNDS - 1;
    add_one_natural(&mut trace, Layout::COL_PADDING_START, natural_row, log_size);
    assert!(row_has_constraint_failure(&trace, log_size, natural_row));
}

#[test]
fn rejects_marker_flag_on_disabled_round_15() {
    let (mut trace, log_size) = honest_fixture();
    let disabled_t15 = 4 * ROWS_PER_BLOCK + STATE_SEED_ROWS + 15;
    assert_eq!(
        trace[Layout::COL_ENABLER][Layout::row_slot(disabled_t15, log_size)].0,
        0
    );
    set_natural(
        &mut trace,
        Layout::COL_IS_MARKER_BLOCK,
        disabled_t15,
        1,
        log_size,
    );
    assert!(row_has_constraint_failure(&trace, log_size, disabled_t15));
}

#[test]
fn rejects_live_padding_cells_on_disabled_round_15() {
    let (trace, log_size) = honest_fixture();
    let disabled_t15 = 4 * ROWS_PER_BLOCK + STATE_SEED_ROWS + 15;
    let inert_length_cells = [
        Layout::COL_BIT_LENGTH_W14_LO,
        Layout::COL_BIT_LENGTH_W14_HI,
        Layout::COL_BIT_LENGTH_W15_LO,
        Layout::COL_BIT_LENGTH_W15_HI,
    ];
    for column in Layout::COL_PADDING_START..Layout::COL_PADDING_END {
        if inert_length_cells.contains(&column) {
            continue;
        }
        let mut mutated = trace.clone();
        set_natural(&mut mutated, column, disabled_t15, 1, log_size);
        assert!(
            row_has_constraint_failure(&mutated, log_size, disabled_t15),
            "live padding cell {column} must reject on a disabled t=15 row"
        );
    }
}

#[test]
fn honest_packed_trace_satisfies_all_base_constraints() {
    let (trace, log_size) = honest_fixture();
    assert_air_accepts(&trace, log_size);
}

#[test]
fn five_message_active_to_decoy_boundary_satisfies_constraints() {
    let long = [0x42; 100];
    let messages: [&[u8]; 5] = [b"a", &long, b"z", b"q", &long];
    let witness = compute_packed_sha256_witness(&messages).unwrap();
    let log_size = 9;
    let total_blocks = 7;
    let first_disabled = total_blocks * ROWS_PER_BLOCK;
    assert_eq!((1usize << log_size) - first_disabled, 43);

    let trace = generate_trace(&witness, log_size);
    let last_active_slot = Layout::row_slot(first_disabled - 1, log_size);
    let first_disabled_slot = Layout::row_slot(first_disabled, log_size);
    assert_eq!(trace[Layout::COL_ENABLER][last_active_slot].0, 1);
    assert_eq!(trace[Layout::COL_MSG_ID][last_active_slot].0, 4);
    assert_eq!(trace[Layout::COL_MSG_BLOCK][last_active_slot].0, 1);
    assert_eq!(trace[Layout::COL_ENABLER][first_disabled_slot].0, 0);
    assert_eq!(trace[Layout::COL_MSG_ID][first_disabled_slot].0, 0);
    assert_eq!(trace[Layout::COL_MSG_BLOCK][first_disabled_slot].0, 0);
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
            max_real_blocks: 244
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
    assert_air_rejects("mid-block cutoff", &trace, log_size);

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
    assert_air_rejects("start on wrong block row", &trace, log_size);

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
    let a_bit0 = Layout::round_operand_bit(0, 0);
    flip_natural(
        &mut trace,
        a_bit0,
        ROWS_PER_BLOCK + STATE_SEED_ROWS,
        log_size,
    );
    assert_air_rejects("start without IV", &trace, log_size);

    let mut trace = honest.clone();
    for word in 0..8 {
        let value = stwo_sha256::constants::IV[word];
        set_seeded_state_word(&mut trace, 2, word, value, log_size);
    }
    assert_air_rejects("IV on continuation", &trace, log_size);

    let mut trace = honest.clone();
    flip_natural(
        &mut trace,
        a_bit0,
        2 * ROWS_PER_BLOCK + STATE_SEED_ROWS,
        log_size,
    );
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
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        STATE_SEED_ROWS + N_ROUNDS - 2,
        1,
        log_size,
    );
    assert_air_rejects("terminal forged", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        STATE_SEED_ROWS + N_ROUNDS - 1,
        0,
        log_size,
    );
    assert_air_rejects("terminal cleared", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        STATE_SEED_ROWS + N_ROUNDS - 1,
        0,
        log_size,
    );
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        ROWS_PER_BLOCK + STATE_SEED_ROWS + N_ROUNDS - 1,
        1,
        log_size,
    );
    assert_air_rejects("terminal moved", &trace, log_size);

    let mut trace = honest.clone();
    set_natural(
        &mut trace,
        Layout::COL_IS_MSG_LAST,
        4 * ROWS_PER_BLOCK + STATE_SEED_ROWS + N_ROUNDS - 1,
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
