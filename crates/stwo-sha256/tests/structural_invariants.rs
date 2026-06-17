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

/// Pin `Layout::TOTAL_COLS` to the claimed total so any future
/// column-count drift fails closed against the test-plan value.
///
/// 9 842 is the through-`h_out` total at `W = 6`: the round-side Maj/Ch and
/// `H_IN_AUX` packed-group blocks each grew from 6 to 8 groups per
/// operand (+8 cells/round × 64 rounds, +8 for the aux block), i.e.
/// +520 over the `W = 7` baseline of 9 322. The §6.2 digest provider then
/// inserts `1` (`is_last_block` flag) + `DIGEST_BYTES = 32` (the big-endian
/// byte view of `h_out`) after `h_out`; the §10.4 padding-role witness adds
/// `PADDING_ROW_COLS = 33`; and the C1-fix aux column `enabler_step` adds 1
/// more — final total 9 909.
#[test]
fn total_cols_equals_9909_at_w6() {
    println!("Layout::TOTAL_COLS = {}", Layout::TOTAL_COLS);
    assert_eq!(Layout::TOTAL_COLS, 9_909);
    // The digest delta (1 + 32), the 33-cell padding delta, and the trailing
    // `enabler_step` cell add up to the total over the 9 842-column W=6
    // through-`h_out` baseline.
    assert_eq!(PADDING_ROW_COLS, 33);
    assert_eq!(DIGEST_BYTES, 32);
    assert_eq!(
        Layout::TOTAL_COLS,
        9_842 + 1 + DIGEST_BYTES + PADDING_ROW_COLS + 1
    );
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
