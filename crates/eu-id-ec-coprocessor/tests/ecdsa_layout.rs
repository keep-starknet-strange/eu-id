use eu_id_ec_coprocessor::ecdsa::{layout_range, LayoutSlot, LAYOUT_LEN};

#[test]
fn witness_layout_matches_g4_inventory() {
    assert_eq!(LAYOUT_LEN, 2680);
    assert_eq!(layout_range(LayoutSlot::InputLimbs), 0..100);
    assert_eq!(layout_range(LayoutSlot::ScalarInverses), 100..101);
    assert_eq!(layout_range(LayoutSlot::UScalars), 101..103);
    assert_eq!(layout_range(LayoutSlot::ModNQuotients), 103..106);
    assert_eq!(layout_range(LayoutSlot::ScalarBits), 106..618);
    assert_eq!(layout_range(LayoutSlot::U1GAccumulators), 618..1130);
    assert_eq!(layout_range(LayoutSlot::U2QAccumulators), 1130..1642);
    assert_eq!(layout_range(LayoutSlot::CorrectedEndpoints), 1642..1646);
    assert_eq!(layout_range(LayoutSlot::U1GDenominatorInverses), 1646..2159);
    assert_eq!(layout_range(LayoutSlot::U2QDenominatorInverses), 2159..2672);
    assert_eq!(
        layout_range(LayoutSlot::FinalAddDenominatorInverse),
        2672..2673
    );
    assert_eq!(layout_range(LayoutSlot::FinalPoint), 2673..2675);
    assert_eq!(layout_range(LayoutSlot::FinalReduction), 2675..2677);
    assert_eq!(layout_range(LayoutSlot::InfinityFlags), 2677..2680);
}

#[test]
fn layout_ranges_are_contiguous() {
    let slots = [
        LayoutSlot::InputLimbs,
        LayoutSlot::ScalarInverses,
        LayoutSlot::UScalars,
        LayoutSlot::ModNQuotients,
        LayoutSlot::ScalarBits,
        LayoutSlot::U1GAccumulators,
        LayoutSlot::U2QAccumulators,
        LayoutSlot::CorrectedEndpoints,
        LayoutSlot::U1GDenominatorInverses,
        LayoutSlot::U2QDenominatorInverses,
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
