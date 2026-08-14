use stwo_sha256::constants::DIGEST_BYTES;
use stwo_sha256::trace::{Layout, PADDING_ROW_COLS, ROUND_COLS, SCHEDULE_ENTRY_COLS};

#[test]
fn packed_layout_has_exact_width_and_stable_offsets() {
    assert_eq!(Layout::TOTAL_COLS, 197);
    assert_eq!(ROUND_COLS, 88);
    assert_eq!(SCHEDULE_ENTRY_COLS, 6);
    assert_eq!(PADDING_ROW_COLS, 30);
    assert_eq!(DIGEST_BYTES, 32);
    assert_eq!(Layout::COL_PADDING_START, Layout::COL_FINAL_CARRIES_START);
    assert_eq!(Layout::COL_MSG_ID, Layout::COL_DIGEST_BYTES_END);
    assert_eq!(Layout::COL_MSG_BLOCK, Layout::COL_MSG_ID + 1);
}

#[test]
fn relation_entries_use_typed_constructors() {
    for file in ["components.rs", "constraints.rs"] {
        let source = match file {
            "components.rs" => include_str!("../src/components.rs"),
            _ => include_str!("../src/constraints.rs"),
        };
        assert!(
            !source.contains("RelationEntry::new"),
            "stale constructor in {file}"
        );
    }
}
