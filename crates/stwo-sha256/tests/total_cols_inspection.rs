//! Pin `Layout::TOTAL_COLS` to the claimed total so any future
//! column-count drift fails closed against the test-plan value.
//!
//! 9 322 was the pre-padding total after the 3.9.5 split-and-pack
//! refactor. Adding the §10.4 padding-role witness (roadmap 3.9.7) tacks
//! `PADDING_ROW_COLS = 33` cells onto each row, bumping the total to
//! 9 355.

use stwo_sha256::trace::{Layout, PADDING_ROW_COLS};

#[test]
fn total_cols_equals_9355_after_padding_witness() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 9_355);
    // The 33-cell delta corresponds exactly to the padding-role region.
    assert_eq!(PADDING_ROW_COLS, 33);
    assert_eq!(Layout::TOTAL_COLS, 9_322 + PADDING_ROW_COLS);
}
