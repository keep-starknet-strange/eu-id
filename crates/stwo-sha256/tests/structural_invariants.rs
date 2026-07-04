//! Structural invariants of the SHA-256 component.
//!
//! Small pin-tests that fail closed if the column layout or per-block
//! lookup-multiplicity counts drift. Kept as integration tests (rather
//! than unit tests) so they exercise the public API surface and don't
//! depend on internal helpers; the assertions themselves are cheap
//! enough to run on every `cargo test`.

use stwo_sha256::constants::DIGEST_BYTES;
use stwo_sha256::trace::{Layout, PADDING_ROW_COLS};
use stwo_sha256::witness::{
    compute_sha256_witness, decode_multiplicities_for_block, maj_ch_xor_multiplicities_for_block,
    split_pack_multiplicities_for_block,
};

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
/// Hybrid one-row-per-round layout at `W = 6`: enabler (1) + `W` limbs (2) +
/// W bits (32) + round family (232) + schedule family (78) +
/// `is_first_block` (1) + `h_in` (16) + aux splits (32) + finalization
/// carries (16) + `h_out` (16) + `is_last_block` (1) + digest bytes (32) +
/// padding-role (33) + `enabler_step` (1) = 493.
#[test]
fn total_cols_equals_493_at_w6_hybrid() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 493);
    assert_eq!(PADDING_ROW_COLS, 33);
    assert_eq!(DIGEST_BYTES, 32);
}

/// Print per-block lookup multiplicities for the `b"abc"` single-block
/// witness and pin them against the design-doc numbers. A drift here
/// indicates the AIR fires a different number of lookups per block than
/// the test plan expects.
#[test]
fn per_block_multiplicities_for_abc_match_plan() {
    let w = compute_sha256_witness(b"abc");
    assert_eq!(w.blocks.len(), 1);
    let block = &w.blocks[0];

    let decode = decode_multiplicities_for_block(block);
    let maj_ch_xor = maj_ch_xor_multiplicities_for_block(block);
    let split_pack = split_pack_multiplicities_for_block(block);

    println!("decode = {decode:?}");
    println!("  total = {}", decode.total());
    println!("maj_ch_xor = {maj_ch_xor:?}");
    println!("  total = {}", maj_ch_xor.total());
    println!("split_pack = {split_pack:?}");
    println!("  total = {}", split_pack.total());
    let grand_total = decode.total() + maj_ch_xor.total() + split_pack.total();
    println!("grand_total = {grand_total}");

    assert_eq!(decode.total(), 448);
    // W=6: maj = ch = 64 rounds × 8 groups = 512 each; xor_8 = 896
    // (unchanged) ⇒ 1920. (Was 1664 at W=7's 6 groups.)
    assert_eq!(maj_ch_xor.total(), 1920);
    assert_eq!(split_pack.total(), 712);
}
