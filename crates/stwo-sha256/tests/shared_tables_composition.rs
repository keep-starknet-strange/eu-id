use stwo_sha256::components::RANGE_TABLES;
use stwo_sha256::shared_tables::ShaTableMultiplicities;
use stwo_sha256::witness::compute_sha256_witness;

#[test]
fn shared_multiplicities_sum_all_packed_messages() {
    let messages = [
        compute_sha256_witness(b"abc"),
        compute_sha256_witness(&[0x42; 200]),
    ];
    let shared = ShaTableMultiplicities::from_messages(&messages);
    assert_eq!(shared.range.len(), RANGE_TABLES.len());
    assert!(shared
        .range
        .iter()
        .all(|multiplicities| multiplicities.iter().any(|&m| m != 0)));
}
