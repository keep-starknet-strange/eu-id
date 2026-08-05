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

/// Pin `Layout::TOTAL_COLS` to the documented total.
///
/// Three-seed-row layout: enabler (1) + `W` limbs (2) + W bits (32) +
/// round family (88) + schedule family (6) + finalization carries (16) +
/// `h_out` (16) + `is_last_block` (1) + padding-role (30) = 192.
///
/// Wave A (2026-08-05): deleted the 64 committed schedule-σ output bit
/// columns (schedule family 70→6, ungated recomposition straight from
/// `w_bits`) and 3 padding aux columns (`is_length_only_block`,
/// `is_marker_only_block`, `marker_word_post_strict_15`; padding-role
/// 33→30) — the first two are now inlined AIR expressions, the third is
/// dead code, deleted outright.
#[test]
fn total_cols_equals_192() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 192);
    assert_eq!(PADDING_ROW_COLS, 30);
    assert_eq!(DIGEST_BYTES, 32);
}
