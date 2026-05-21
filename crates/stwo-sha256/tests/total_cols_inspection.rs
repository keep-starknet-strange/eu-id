//! Pin `Layout::TOTAL_COLS` to the claimed post-3.9.5 number so any
//! future column-count drift fails closed against the test-plan value.

use stwo_sha256::trace::Layout;

#[test]
fn total_cols_equals_9322_after_split_and_pack_refactor() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 9_322);
}
