//! Structural invariants of the SHA-256 component.
//!
//! Small pin-tests that fail closed if the column layout or per-block
//! lookup-multiplicity counts drift. Kept as integration tests (rather
//! than unit tests) so they exercise the public API surface and don't
//! depend on internal helpers; the assertions themselves are cheap
//! enough to run on every `cargo test`.

use stwo_sha256::trace::{Layout, PADDING_ROW_COLS};
use stwo_sha256::witness::{
    compute_sha256_witness, decode_multiplicities_for_block, maj_ch_xor_multiplicities_for_block,
    split_pack_multiplicities_for_block,
};

/// Pin `Layout::TOTAL_COLS` to the claimed total so any future
/// column-count drift fails closed against the test-plan value.
///
/// 9 322 was the pre-padding total after the split-and-pack refactor.
/// Adding the §10.4 padding-role witness tacks `PADDING_ROW_COLS = 33`
/// cells onto each row, then the C1-fix aux column `enabler_step` adds
/// 1 more — final total 9 356.
#[test]
fn total_cols_equals_9356_after_c1_aux_column() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 9_356);
    // The 33-cell padding delta and the trailing `enabler_step` cell add
    // up to the post-padding delta over the 9 322-column refactor baseline.
    assert_eq!(PADDING_ROW_COLS, 33);
    assert_eq!(Layout::TOTAL_COLS, 9_322 + PADDING_ROW_COLS + 1);
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
    assert_eq!(maj_ch_xor.total(), 1664);
    assert_eq!(split_pack.total(), 712);
}
