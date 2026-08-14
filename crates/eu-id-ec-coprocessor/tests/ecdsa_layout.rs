use eu_id_ec_coprocessor::ecdsa::{layout_range, LayoutSlot, LAYOUT_LEN};

#[test]
fn witness_layout_matches_g4_inventory() {
    assert_eq!(LAYOUT_LEN, 1135);
    assert_eq!(layout_range(LayoutSlot::InputLimbs), 0..100);
    assert_eq!(layout_range(LayoutSlot::UScalars), 100..102);
    assert_eq!(layout_range(LayoutSlot::U1GAccumulators), 102..614);
    assert_eq!(layout_range(LayoutSlot::U2QAccumulators), 614..1126);
    assert_eq!(layout_range(LayoutSlot::CorrectedEndpoints), 1126..1130);
    assert_eq!(
        layout_range(LayoutSlot::FinalAddDenominatorInverse),
        1130..1131
    );
    assert_eq!(layout_range(LayoutSlot::FinalPoint), 1131..1133);
    assert_eq!(layout_range(LayoutSlot::FinalReduction), 1133..1135);
}

#[test]
fn layout_ranges_are_contiguous() {
    let slots = [
        LayoutSlot::InputLimbs,
        LayoutSlot::UScalars,
        LayoutSlot::U1GAccumulators,
        LayoutSlot::U2QAccumulators,
        LayoutSlot::CorrectedEndpoints,
        LayoutSlot::FinalAddDenominatorInverse,
        LayoutSlot::FinalPoint,
        LayoutSlot::FinalReduction,
    ];
    let mut cursor = 0;
    for slot in slots {
        let range = layout_range(slot);
        assert_eq!(range.start, cursor);
        cursor = range.end;
    }
    assert_eq!(cursor, LAYOUT_LEN);
}
