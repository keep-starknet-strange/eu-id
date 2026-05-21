//! Integration-level inspection: print per-block multiplicities so the
//! test-plan numbers can be confirmed against the live code, not just
//! against the assertions inside unit tests.

use stwo_sha256::witness::{
    compute_sha256_witness, decode_multiplicities_for_block, maj_ch_xor_multiplicities_for_block,
    split_pack_multiplicities_for_block,
};

#[test]
fn print_per_block_multiplicities_for_abc() {
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

    // Pin against the plan-doc numbers so this test fails if drift sneaks in.
    assert_eq!(decode.total(), 448);
    assert_eq!(maj_ch_xor.total(), 1664);
    assert_eq!(split_pack.total(), 712);
}
