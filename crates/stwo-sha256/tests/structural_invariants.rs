//! Structural invariants of the SHA-256 component.
//!
//! Small pin-tests that fail closed if the column layout or per-block
//! lookup-multiplicity counts drift. Kept as integration tests (rather
//! than unit tests) so they exercise the public API surface and do not
//! depend on internal helpers. The assertions themselves are cheap
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
/// Pin the 437-column one-row-per-round layout.
///
/// The total covers control, schedule, bit planes, round values, state,
/// carries, digest bytes, and padding data. The active layout has no
/// split-pack columns.
#[test]
fn total_cols_equals_437() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 437);
    assert_eq!(PADDING_ROW_COLS, 33);
    assert_eq!(DIGEST_BYTES, 32);
}
