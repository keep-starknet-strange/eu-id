use eu_id_ec_coprocessor::ecdsa::{layout_range, LayoutSlot, LAYOUT_LEN};

#[test]
fn witness_layout_matches_g4_inventory() {
    assert_eq!(LAYOUT_LEN, 1142);
    assert_eq!(layout_range(LayoutSlot::InputLimbs), 0..100);
    assert_eq!(layout_range(LayoutSlot::ScalarInverses), 100..101);
    assert_eq!(layout_range(LayoutSlot::UScalars), 101..103);
    assert_eq!(layout_range(LayoutSlot::ModNQuotients), 103..106);
    assert_eq!(layout_range(LayoutSlot::U1GAccumulators), 106..618);
    assert_eq!(layout_range(LayoutSlot::U2QAccumulators), 618..1130);
    assert_eq!(layout_range(LayoutSlot::CorrectedEndpoints), 1130..1134);
    assert_eq!(
        layout_range(LayoutSlot::FinalAddDenominatorInverse),
        1134..1135
    );
    assert_eq!(layout_range(LayoutSlot::FinalPoint), 1135..1137);
    assert_eq!(layout_range(LayoutSlot::FinalReduction), 1137..1139);
    assert_eq!(layout_range(LayoutSlot::InfinityFlags), 1139..1142);
}

#[test]
fn layout_ranges_are_contiguous() {
    let slots = [
        LayoutSlot::InputLimbs,
        LayoutSlot::ScalarInverses,
        LayoutSlot::UScalars,
        LayoutSlot::ModNQuotients,
        LayoutSlot::U1GAccumulators,
        LayoutSlot::U2QAccumulators,
        LayoutSlot::CorrectedEndpoints,
        LayoutSlot::FinalAddDenominatorInverse,
        LayoutSlot::FinalPoint,
        LayoutSlot::FinalReduction,
        LayoutSlot::InfinityFlags,
    ];
    let mut cursor = 0;
    for slot in slots {
        let range = layout_range(slot);
        assert_eq!(range.start, cursor);
        cursor = range.end;
    }
    assert_eq!(cursor, LAYOUT_LEN);
}
