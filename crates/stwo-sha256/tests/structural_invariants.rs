//! Structural invariants of the SHA-256 component.
//!
//! Small pin-tests that fail closed if the column layout or per-block
//! lookup-multiplicity counts drift. Kept as integration tests (rather
//! than unit tests) so they exercise the public API surface and don't
//! depend on internal helpers; the assertions themselves are cheap
//! enough to run on every `cargo test`.

use stwo_sha256::constants::DIGEST_BYTES;
use stwo_sha256::trace::{Layout, PADDING_ROW_COLS};

#[test]
fn sha_air_uses_typed_relation_multiplicities() {
    let sources = [
        ("components.rs", include_str!("../src/components.rs")),
        ("constraints.rs", include_str!("../src/constraints.rs")),
    ];
    let mut offenders = Vec::new();
    for (file, source) in sources {
        for (line_idx, line) in source.lines().enumerate() {
            if line.contains("RelationEntry::new") {
                offenders.push(format!("{file}:{}: {}", line_idx + 1, line.trim()));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "SHA relation entries should use unit/neg_unit/base constructors:\n{}",
        offenders.join("\n")
    );
}

/// Pin `Layout::TOTAL_COLS` to the claimed total so any future
/// column-count drift fails closed against the test-plan value.
///
/// Algebraic one-row-per-round layout: enabler (1) + `W` limbs (2) +
/// W bits (32) + round family (216) + schedule family (70) +
/// `is_first_block` (1) + `h_in` (16) + finalization
/// carries (16) + `h_out` (16) + `is_last_block` (1) + digest bytes (32) +
/// padding-role (33) + `enabler_step` (1) = 437.
#[test]
fn total_cols_equals_437() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 437);
    assert_eq!(PADDING_ROW_COLS, 33);
    assert_eq!(DIGEST_BYTES, 32);
}
