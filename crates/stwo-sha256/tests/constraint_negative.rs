use stwo::core::fields::m31::BaseField;
use stwo_sha256::native::n_blocks_for;
use stwo_sha256::trace::{generate_trace, min_log_size, Layout, ROWS_PER_BLOCK};
use stwo_sha256::witness::compute_packed_sha256_witness;

fn trace_for(messages: &[&[u8]]) -> (Vec<Vec<BaseField>>, u32, usize) {
    let witness = compute_packed_sha256_witness(messages).unwrap();
    let blocks = messages
        .iter()
        .map(|message| n_blocks_for(message.len()))
        .sum();
    let log_size = min_log_size(blocks);
    (generate_trace(&witness, log_size), log_size, blocks)
}

#[test]
fn disabled_tail_contains_at_least_one_complete_block() {
    let (trace, log_size, blocks) = trace_for(&[b"abc"]);
    let rows = 1usize << log_size;
    let enabled = (0..rows)
        .map(|row| trace[Layout::COL_ENABLER][Layout::row_slot(row, log_size)].0)
        .sum::<u32>() as usize;
    assert_eq!(enabled, blocks * ROWS_PER_BLOCK);
    assert!(rows - enabled >= ROWS_PER_BLOCK);
}

#[test]
fn message_start_and_terminal_flags_are_local_to_each_message() {
    let messages: [&[u8]; 2] = [b"short", &[0x55; 100]];
    let (trace, log_size, _) = trace_for(&messages);
    let first_message_last = Layout::round_row_slot(0, 63, log_size);
    let second_message_last = Layout::round_row_slot(2, 63, log_size);
    assert_eq!(trace[Layout::COL_IS_MSG_LAST][first_message_last].0, 1);
    assert_eq!(trace[Layout::COL_IS_MSG_LAST][second_message_last].0, 1);
    assert_eq!(trace[Layout::COL_MSG_START][first_message_last].0, 0);
}

#[test]
fn adjacent_message_stream_indices_reset_at_zero() {
    let messages: [&[u8]; 2] = [b"a", b"b"];
    let (trace, log_size, _) = trace_for(&messages);
    let first = Layout::round_row_slot(0, 15, log_size);
    let second = Layout::round_row_slot(1, 15, log_size);
    assert_eq!(trace[Layout::COL_MSG_BLOCK][first].0, 0);
    assert_eq!(trace[Layout::COL_MSG_BLOCK][second].0, 0);
    assert_eq!(trace[Layout::COL_MSG_ID][first].0, 0);
    assert_eq!(trace[Layout::COL_MSG_ID][second].0, 1);
}
