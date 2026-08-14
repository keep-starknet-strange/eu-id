//! In-circuit binding and strict comparison for mdoc validity timestamps.
//!
//! The issuer SHA module exposes the `validFrom` and `validUntil` full-date
//! timestamps from the signed MSO preimage. This component consumes those bytes,
//! parses `YYYY-MM-DDThh:mm:ssZ` in-circuit, and proves:
//!
//! - `validFrom < verifier_time`
//! - `verifier_time < validUntil`

use air_core::claim_mask::{
    add_claim_mask_fraction, ClaimMaskTrace, SharedClaimMaskChallenge, CLAIM_MASK_TRACE_COLUMNS,
};
use air_core::relations::{field_id, FieldBytesRelation, SharedFieldRelation};
use air_core::{
    fingerprint_preprocessed_columns, Air, AirProver, PreprocessedColumnFingerprint, TreeLayout,
};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::{QM31, SECURE_EXTENSION_DEGREE};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    TraceLocationAllocator,
};

use crate::mdoc::{
    gregorian_days_in_month, is_gregorian_leap_year, utc_timestamp_from_epoch_seconds,
    MdocTimestamp,
};

const MDOC_VALIDITY_LOG_SIZE: u32 = 9;
const TIMESTAMP_TEXT_LEN: usize = 20;
const TIMESTAMP_DIGITS: usize = 14;
const DIGIT_BITS: usize = 4;
const DATE_SLACK_BITS: usize = 23;
const SECOND_SLACK_BITS: usize = 17;
const SECOND_LIMB_BASE: u32 = 1 << SECOND_SLACK_BITS;
const DAY_RANGE_BITS: usize = 5;
const HOUR_RANGE_BITS: usize = 5;
const MINUTE_RANGE_BITS: usize = 6;
const SECOND_RANGE_BITS: usize = 6;
const MONTH_SELECTOR_COUNT: usize = 12;
const YEAR_PAIR_QUOTIENT_BITS: usize = 5;
const YEAR_PAIR_REMAINDER_BITS: usize = 2;
const YEAR_PAIR_COUNT: usize = 2;
const ZERO_CHECK_COUNT: usize = 3;
const ZERO_CHECK_COLUMNS: usize = 2;
const CALENDAR_SLACK_BITS: usize = 5;
const MDOC_VALIDITY_PREPROCESSED_COLS: usize = 4;
const MDOC_VALIDITY_TRACE_COLS: usize = TIMESTAMP_TEXT_LEN
    + TIMESTAMP_DIGITS * DIGIT_BITS
    + 1
    + DATE_SLACK_BITS
    + SECOND_SLACK_BITS
    + DAY_RANGE_BITS
    + HOUR_RANGE_BITS
    + MINUTE_RANGE_BITS
    + SECOND_RANGE_BITS
    + MONTH_SELECTOR_COUNT
    + YEAR_PAIR_COUNT * (YEAR_PAIR_QUOTIENT_BITS + YEAR_PAIR_REMAINDER_BITS)
    + ZERO_CHECK_COUNT * ZERO_CHECK_COLUMNS
    + 1
    + CALENDAR_SLACK_BITS;
const MDOC_VALIDITY_LOOKUPS: usize = TIMESTAMP_TEXT_LEN;

type MdocValidityColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type MdocValidityComponent = FrameworkComponent<MdocValidityEval>;

#[derive(Clone, Copy, Debug)]
pub(crate) struct MdocValidityRow {
    field_id: u32,
    valid_from: bool,
    bytes: [u8; TIMESTAMP_TEXT_LEN],
}

impl MdocValidityRow {
    fn new(field_id: u32, valid_from: bool, bytes: [u8; TIMESTAMP_TEXT_LEN]) -> Self {
        Self {
            field_id,
            valid_from,
            bytes,
        }
    }
}

pub(crate) fn mdoc_validity_rows(
    valid_from: [u8; TIMESTAMP_TEXT_LEN],
    valid_until: [u8; TIMESTAMP_TEXT_LEN],
) -> Vec<MdocValidityRow> {
    vec![
        MdocValidityRow::new(field_id::MDOC_VALID_FROM, true, valid_from),
        MdocValidityRow::new(field_id::MDOC_VALID_UNTIL, false, valid_until),
    ]
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct MdocValidityInteractionClaim {
    pub(crate) claimed_sum: QM31,
}

pub(crate) struct MdocValidityBind {
    verification_time_epoch_seconds: u64,
    rows: Vec<MdocValidityRow>,
    issuer_field_handle: SharedFieldRelation,
    claim_mask_trace: Option<ClaimMaskTrace>,
    claim_mask_challenge: Option<SharedClaimMaskChallenge>,
    interaction_claim: Option<MdocValidityInteractionClaim>,
    component: Option<MdocValidityComponent>,
}

impl MdocValidityBind {
    pub(crate) fn new(
        verification_time_epoch_seconds: u64,
        rows: Vec<MdocValidityRow>,
        issuer_field_handle: SharedFieldRelation,
    ) -> Self {
        Self {
            verification_time_epoch_seconds,
            rows,
            issuer_field_handle,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: None,
            component: None,
        }
    }

    pub(crate) fn verifier(
        verification_time_epoch_seconds: u64,
        rows: Vec<MdocValidityRow>,
        issuer_field_handle: SharedFieldRelation,
        interaction_claim: MdocValidityInteractionClaim,
    ) -> Self {
        Self {
            verification_time_epoch_seconds,
            rows,
            issuer_field_handle,
            claim_mask_trace: None,
            claim_mask_challenge: None,
            interaction_claim: Some(interaction_claim),
            component: None,
        }
    }

    pub(crate) fn interaction_claim(&self) -> &MdocValidityInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("mdoc validity interaction claim is set")
    }

    fn issuer_field_relation(&self) -> FieldBytesRelation {
        self.issuer_field_handle.get()
    }

    pub(crate) fn ordered_claim_mask_log_sizes(&self) -> Vec<u32> {
        vec![MDOC_VALIDITY_LOG_SIZE]
    }

    pub(crate) fn with_claim_mask(
        mut self,
        trace: ClaimMaskTrace,
        challenge: SharedClaimMaskChallenge,
    ) -> Self {
        assert_eq!(trace.log_size(), MDOC_VALIDITY_LOG_SIZE);
        self.claim_mask_trace = Some(trace);
        self.claim_mask_challenge = Some(challenge);
        self
    }

    pub(crate) fn with_claim_mask_verifier(mut self, challenge: SharedClaimMaskChallenge) -> Self {
        self.claim_mask_challenge = Some(challenge);
        self
    }

    fn claim_mask_beta(&self) -> Option<QM31> {
        self.claim_mask_challenge
            .as_ref()
            .map(|shared| shared.require().expect("claim-mask anchor drawn first"))
    }
}

#[derive(Clone)]
struct MdocValidityEval {
    verification_time_epoch_seconds: u64,
    issuer_field_relation: FieldBytesRelation,
    claim_mask_beta: Option<QM31>,
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(M31::from_u32_unchecked(value))
}

fn bit_sum<E: EvalAtRow>(bits: &[E::F]) -> E::F {
    bits.iter()
        .enumerate()
        .fold(m31_const::<E>(0), |acc, (bit_idx, bit)| {
            acc + m31_const::<E>(1u32 << bit_idx) * bit.clone()
        })
}

fn date_key(year: u32, month: u32, day: u32) -> u32 {
    year * 512 + month * 32 + day
}

fn timestamp_key(timestamp: MdocTimestamp) -> (u32, u32) {
    (
        date_key(
            u32::from(timestamp.year),
            u32::from(timestamp.month),
            u32::from(timestamp.day),
        ),
        u32::from(timestamp.hour) * 3_600
            + u32::from(timestamp.minute) * 60
            + u32::from(timestamp.second),
    )
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![M31::from_u32_unchecked(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn mdoc_validity_column_eval(log_size: u32, coset_values: Vec<M31>) -> MdocValidityColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(log_size, coset_values)),
    )
}

fn mdoc_validity_col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/validity/{name}"),
    }
}

fn mdoc_validity_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    vec![
        mdoc_validity_col_id("active"),
        mdoc_validity_col_id("field_id"),
        mdoc_validity_col_id("valid_from_active"),
        mdoc_validity_col_id("valid_until_active"),
    ]
}

fn mdoc_validity_preprocessed_columns(rows: &[MdocValidityRow]) -> Vec<MdocValidityColumnEval> {
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); 1 << MDOC_VALIDITY_LOG_SIZE];
        MDOC_VALIDITY_PREPROCESSED_COLS
    ];
    for (row_idx, row) in rows.iter().enumerate() {
        columns[0][row_idx] = M31::from_u32_unchecked(1);
        columns[1][row_idx] = M31::from_u32_unchecked(row.field_id);
        if row.valid_from {
            columns[2][row_idx] = M31::from_u32_unchecked(1);
        } else {
            columns[3][row_idx] = M31::from_u32_unchecked(1);
        }
    }
    columns
        .into_iter()
        .map(|values| mdoc_validity_column_eval(MDOC_VALIDITY_LOG_SIZE, values))
        .collect()
}

fn bits_for(value: u32, bits: usize) -> Vec<u32> {
    (0..bits).map(|bit| (value >> bit) & 1).collect()
}

fn parse_timestamp_text(bytes: &[u8; TIMESTAMP_TEXT_LEN]) -> Option<MdocTimestamp> {
    if bytes[4] != b'-'
        || bytes[7] != b'-'
        || bytes[10] != b'T'
        || bytes[13] != b':'
        || bytes[16] != b':'
        || bytes[19] != b'Z'
    {
        return None;
    }
    for &idx in &[0usize, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18] {
        if !bytes[idx].is_ascii_digit() {
            return None;
        }
    }
    let year = u32::from(bytes[0] - b'0') * 1000
        + u32::from(bytes[1] - b'0') * 100
        + u32::from(bytes[2] - b'0') * 10
        + u32::from(bytes[3] - b'0');
    let month = u32::from(bytes[5] - b'0') * 10 + u32::from(bytes[6] - b'0');
    let day = u32::from(bytes[8] - b'0') * 10 + u32::from(bytes[9] - b'0');
    let hour = u32::from(bytes[11] - b'0') * 10 + u32::from(bytes[12] - b'0');
    let minute = u32::from(bytes[14] - b'0') * 10 + u32::from(bytes[15] - b'0');
    let second = u32::from(bytes[17] - b'0') * 10 + u32::from(bytes[18] - b'0');
    Some(MdocTimestamp {
        year: year.try_into().ok()?,
        month: month.try_into().ok()?,
        day: day.try_into().ok()?,
        hour: hour.try_into().ok()?,
        minute: minute.try_into().ok()?,
        second: second.try_into().ok()?,
    })
}

fn comparison_slack(
    verification_time_epoch_seconds: u64,
    row: &MdocValidityRow,
) -> (u32, u32, u32) {
    let threshold_seconds = if row.valid_from {
        verification_time_epoch_seconds.checked_sub(1)
    } else {
        verification_time_epoch_seconds.checked_add(1)
    };
    let Some(threshold) =
        threshold_seconds.and_then(|seconds| utc_timestamp_from_epoch_seconds(seconds).ok())
    else {
        return (0, 0, 0);
    };
    let Some(signed) = parse_timestamp_text(&row.bytes) else {
        return (0, 0, 0);
    };
    let ((left_date, left_second), (right_date, right_second)) = if row.valid_from {
        (timestamp_key(threshold), timestamp_key(signed))
    } else {
        (timestamp_key(signed), timestamp_key(threshold))
    };
    let (borrow, second_slack) = if left_second >= right_second {
        (0, left_second - right_second)
    } else {
        (1, left_second + SECOND_LIMB_BASE - right_second)
    };
    let date_slack = left_date.saturating_sub(right_date + borrow);
    (borrow, date_slack, second_slack)
}

fn lower_range_slack(value: u32) -> u32 {
    value.saturating_sub(1)
}

fn upper_range_slack(max: u32, value: u32) -> u32 {
    max.saturating_sub(value)
}

fn zero_check_witness(value: u32) -> (u32, M31) {
    if value == 0 {
        (1, M31::from_u32_unchecked(0))
    } else {
        (0, M31::from_u32_unchecked(value).inverse())
    }
}

fn mdoc_validity_base_trace(
    verification_time_epoch_seconds: u64,
    rows: &[MdocValidityRow],
) -> Vec<MdocValidityColumnEval> {
    let mut columns = vec![
        vec![M31::from_u32_unchecked(0); 1 << MDOC_VALIDITY_LOG_SIZE];
        MDOC_VALIDITY_TRACE_COLS
    ];
    for column in &mut columns {
        for value in column.iter_mut().skip(rows.len()) {
            *value = random_m31_cell();
        }
    }
    for (row_idx, row) in rows.iter().enumerate() {
        let mut col_idx = 0usize;
        for byte in row.bytes {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(u32::from(byte));
            col_idx += 1;
        }
        let digits = [
            row.bytes[0],
            row.bytes[1],
            row.bytes[2],
            row.bytes[3],
            row.bytes[5],
            row.bytes[6],
            row.bytes[8],
            row.bytes[9],
            row.bytes[11],
            row.bytes[12],
            row.bytes[14],
            row.bytes[15],
            row.bytes[17],
            row.bytes[18],
        ];
        for byte in digits {
            let digit = byte
                .checked_sub(b'0')
                .filter(|digit| *digit <= 9)
                .unwrap_or(0);
            for bit in bits_for(u32::from(digit), DIGIT_BITS) {
                columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
                col_idx += 1;
            }
        }
        let (borrow, date_slack, second_slack) =
            comparison_slack(verification_time_epoch_seconds, row);
        columns[col_idx][row_idx] = M31::from_u32_unchecked(borrow);
        col_idx += 1;
        for bit in bits_for(date_slack, DATE_SLACK_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(second_slack, SECOND_SLACK_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        let timestamp = parse_timestamp_text(&row.bytes).unwrap_or(MdocTimestamp {
            year: 0,
            month: 0,
            day: 0,
            hour: 0,
            minute: 0,
            second: 0,
        });
        let day = u32::from(timestamp.day);
        for bit in bits_for(lower_range_slack(day), DAY_RANGE_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(
            upper_range_slack(23, u32::from(timestamp.hour)),
            HOUR_RANGE_BITS,
        ) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(
            upper_range_slack(59, u32::from(timestamp.minute)),
            MINUTE_RANGE_BITS,
        ) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        for bit in bits_for(
            upper_range_slack(59, u32::from(timestamp.second)),
            SECOND_RANGE_BITS,
        ) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }

        for month in 1..=MONTH_SELECTOR_COUNT {
            columns[col_idx][row_idx] =
                M31::from_u32_unchecked(u32::from(timestamp.month as usize == month));
            col_idx += 1;
        }

        let year = u32::from(timestamp.year);
        let last_two = year % 100;
        let century = year / 100;
        for (quotient, remainder) in [(last_two / 4, last_two % 4), (century / 4, century % 4)] {
            for bit in bits_for(quotient, YEAR_PAIR_QUOTIENT_BITS) {
                columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
                col_idx += 1;
            }
            for bit in bits_for(remainder, YEAR_PAIR_REMAINDER_BITS) {
                columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
                col_idx += 1;
            }
        }

        for value in [last_two % 4, century % 4, last_two] {
            let (is_zero, inverse) = zero_check_witness(value);
            columns[col_idx][row_idx] = M31::from_u32_unchecked(is_zero);
            col_idx += 1;
            columns[col_idx][row_idx] = inverse;
            col_idx += 1;
        }

        let leap = u32::from(is_gregorian_leap_year(timestamp.year));
        columns[col_idx][row_idx] = M31::from_u32_unchecked(leap);
        col_idx += 1;
        let max_day = gregorian_days_in_month(timestamp.year, timestamp.month)
            .map(u32::from)
            .unwrap_or(0);
        for bit in bits_for(upper_range_slack(max_day, day), CALENDAR_SLACK_BITS) {
            columns[col_idx][row_idx] = M31::from_u32_unchecked(bit);
            col_idx += 1;
        }
        debug_assert_eq!(col_idx, MDOC_VALIDITY_TRACE_COLS);
    }
    columns
        .into_iter()
        .map(|values| mdoc_validity_column_eval(MDOC_VALIDITY_LOG_SIZE, values))
        .collect()
}

fn mdoc_validity_interaction_trace(
    verification_time_epoch_seconds: u64,
    rows: &[MdocValidityRow],
    issuer_field_relation: &FieldBytesRelation,
    claim_mask_trace: Option<&ClaimMaskTrace>,
    claim_mask_beta: Option<QM31>,
) -> (Vec<MdocValidityColumnEval>, QM31) {
    let preprocessed = mdoc_validity_preprocessed_columns(rows);
    let trace = mdoc_validity_base_trace(verification_time_epoch_seconds, rows);
    let n_vec_rows = 1usize << (MDOC_VALIDITY_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> =
        Vec::with_capacity(MDOC_VALIDITY_LOOKUPS + usize::from(claim_mask_trace.is_some()));
    for (byte_idx, trace_col) in trace.iter().enumerate().take(TIMESTAMP_TEXT_LEN) {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    let numerator = PackedQM31::from(preprocessed[0].data[vec_row]);
                    let denominator = issuer_field_relation.combine(&[
                        preprocessed[1].data[vec_row],
                        PackedM31::broadcast(M31::from_u32_unchecked(byte_idx as u32)),
                        trace_col.data[vec_row],
                    ]);
                    (numerator, denominator)
                })
                .collect(),
        );
    }
    // The committed claim mask is emitted last to match the AIR site order.
    match (claim_mask_trace, claim_mask_beta) {
        (Some(mask), Some(beta)) => {
            assert_eq!(mask.log_size(), MDOC_VALIDITY_LOG_SIZE);
            sites.push(
                (0..n_vec_rows)
                    .map(|vec_row| mask.packed_fraction_at(vec_row, beta))
                    .collect(),
            );
        }
        (None, None) => {}
        _ => panic!("mdoc validity claim-mask trace and challenge must be configured together"),
    }
    let mut logup = LogupTraceGenerator::new(MDOC_VALIDITY_LOG_SIZE);
    let mut site_idx = 0usize;
    while site_idx + 1 < sites.len() {
        let left = &sites[site_idx];
        let right = &sites[site_idx + 1];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let (n0, d0) = left[vec_row];
            let (n1, d1) = right[vec_row];
            (n0 * d1 + n1 * d0, d0 * d1)
        }));
        site_idx += 2;
    }
    if site_idx < sites.len() {
        let last = &sites[site_idx];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| last[vec_row]));
    }
    logup.finalize_last()
}

impl FrameworkEval for MdocValidityEval {
    fn log_size(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(mdoc_validity_col_id("active"));
        let field_id = eval.get_preprocessed_column(mdoc_validity_col_id("field_id"));
        let valid_from_active =
            eval.get_preprocessed_column(mdoc_validity_col_id("valid_from_active"));
        let valid_until_active =
            eval.get_preprocessed_column(mdoc_validity_col_id("valid_until_active"));
        let one = m31_const::<E>(1);
        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint(valid_from_active.clone() * (valid_from_active.clone() - one.clone()));
        eval.add_constraint(
            valid_until_active.clone() * (valid_until_active.clone() - one.clone()),
        );
        eval.add_constraint(
            active.clone() * (valid_from_active.clone() + valid_until_active.clone() - one.clone()),
        );

        let bytes: [E::F; TIMESTAMP_TEXT_LEN] = std::array::from_fn(|_| eval.next_trace_mask());
        let digit_bits: [[E::F; DIGIT_BITS]; TIMESTAMP_DIGITS] =
            std::array::from_fn(|_| std::array::from_fn(|_| eval.next_trace_mask()));
        let borrow = eval.next_trace_mask();
        let date_slack_bits: [E::F; DATE_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let second_slack_bits: [E::F; SECOND_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let day_lower_bits: [E::F; DAY_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let hour_upper_bits: [E::F; HOUR_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let minute_upper_bits: [E::F; MINUTE_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let second_upper_bits: [E::F; SECOND_RANGE_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());
        let month_selectors: [E::F; MONTH_SELECTOR_COUNT] =
            std::array::from_fn(|_| eval.next_trace_mask());
        type YearPairBits<F> = ([F; YEAR_PAIR_QUOTIENT_BITS], [F; YEAR_PAIR_REMAINDER_BITS]);
        let year_pair_bits: [YearPairBits<E::F>; YEAR_PAIR_COUNT] = std::array::from_fn(|_| {
            (
                std::array::from_fn(|_| eval.next_trace_mask()),
                std::array::from_fn(|_| eval.next_trace_mask()),
            )
        });
        let zero_checks: [(E::F, E::F); ZERO_CHECK_COUNT] =
            std::array::from_fn(|_| (eval.next_trace_mask(), eval.next_trace_mask()));
        let leap = eval.next_trace_mask();
        let calendar_slack_bits: [E::F; CALENDAR_SLACK_BITS] =
            std::array::from_fn(|_| eval.next_trace_mask());

        for (position, expected) in [
            (4, b'-'),
            (7, b'-'),
            (10, b'T'),
            (13, b':'),
            (16, b':'),
            (19, b'Z'),
        ] {
            eval.add_constraint(
                active.clone() * (bytes[position].clone() - m31_const::<E>(u32::from(expected))),
            );
        }

        let digit_positions = [0usize, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18];
        let mut digits = Vec::with_capacity(TIMESTAMP_DIGITS);
        for (digit_idx, &byte_pos) in digit_positions.iter().enumerate() {
            let bits = &digit_bits[digit_idx];
            for bit in bits {
                eval.add_constraint(active.clone() * bit.clone() * (bit.clone() - one.clone()));
            }
            let digit = bytes[byte_pos].clone() - m31_const::<E>(b'0' as u32);
            let recomposed = bits[0].clone()
                + m31_const::<E>(2) * bits[1].clone()
                + m31_const::<E>(4) * bits[2].clone()
                + m31_const::<E>(8) * bits[3].clone();
            eval.add_constraint(active.clone() * (digit.clone() - recomposed));
            eval.add_constraint(active.clone() * bits[3].clone() * bits[2].clone());
            eval.add_constraint(active.clone() * bits[3].clone() * bits[1].clone());
            digits.push(digit);
        }

        eval.add_constraint(active.clone() * borrow.clone() * (borrow.clone() - one.clone()));
        for bit in date_slack_bits
            .iter()
            .chain(second_slack_bits.iter())
            .chain(day_lower_bits.iter())
            .chain(hour_upper_bits.iter())
            .chain(minute_upper_bits.iter())
            .chain(second_upper_bits.iter())
            .chain(month_selectors.iter())
            .chain(
                year_pair_bits
                    .iter()
                    .flat_map(|(quotient, remainder)| quotient.iter().chain(remainder.iter())),
            )
            .chain(zero_checks.iter().map(|(is_zero, _)| is_zero))
            .chain(std::iter::once(&leap))
            .chain(calendar_slack_bits.iter())
        {
            eval.add_constraint(active.clone() * bit.clone() * (bit.clone() - one.clone()));
        }

        let year = m31_const::<E>(1000) * digits[0].clone()
            + m31_const::<E>(100) * digits[1].clone()
            + m31_const::<E>(10) * digits[2].clone()
            + digits[3].clone();
        let month = m31_const::<E>(10) * digits[4].clone() + digits[5].clone();
        let day = m31_const::<E>(10) * digits[6].clone() + digits[7].clone();
        let hour = m31_const::<E>(10) * digits[8].clone() + digits[9].clone();
        let minute = m31_const::<E>(10) * digits[10].clone() + digits[11].clone();
        let second = m31_const::<E>(10) * digits[12].clone() + digits[13].clone();
        let date_key =
            m31_const::<E>(512) * year + m31_const::<E>(32) * month.clone() + day.clone();
        let second_key = m31_const::<E>(3_600) * hour.clone()
            + m31_const::<E>(60) * minute.clone()
            + second.clone();
        let before = utc_timestamp_from_epoch_seconds(
            self.verification_time_epoch_seconds
                .checked_sub(1)
                .expect("verification time is validated"),
        )
        .expect("verification time minus one is supported");
        let after = utc_timestamp_from_epoch_seconds(
            self.verification_time_epoch_seconds
                .checked_add(1)
                .expect("verification time is validated"),
        )
        .expect("verification time plus one is supported");
        let (before_date, before_second) = timestamp_key(before);
        let (after_date, after_second) = timestamp_key(after);
        let date_slack = bit_sum::<E>(&date_slack_bits);
        let second_slack = bit_sum::<E>(&second_slack_bits);
        let day_lower = bit_sum::<E>(&day_lower_bits);
        let hour_upper = bit_sum::<E>(&hour_upper_bits);
        let minute_upper = bit_sum::<E>(&minute_upper_bits);
        let second_upper = bit_sum::<E>(&second_upper_bits);

        eval.add_constraint(active.clone() * (day.clone() - one.clone() - day_lower));
        eval.add_constraint(active.clone() * (m31_const::<E>(23) - hour - hour_upper));
        eval.add_constraint(active.clone() * (m31_const::<E>(59) - minute - minute_upper));
        eval.add_constraint(active.clone() * (m31_const::<E>(59) - second - second_upper));

        let month_selector_sum = month_selectors
            .iter()
            .cloned()
            .fold(m31_const::<E>(0), |sum, selector| sum + selector);
        let selected_month = month_selectors
            .iter()
            .enumerate()
            .fold(m31_const::<E>(0), |sum, (index, selector)| {
                sum + m31_const::<E>((index + 1) as u32) * selector.clone()
            });
        eval.add_constraint(active.clone() * (month_selector_sum - one.clone()));
        eval.add_constraint(active.clone() * (month.clone() - selected_month));

        let century = m31_const::<E>(10) * digits[0].clone() + digits[1].clone();
        let last_two = m31_const::<E>(10) * digits[2].clone() + digits[3].clone();
        let mut remainders = Vec::with_capacity(YEAR_PAIR_COUNT);
        for (value, (quotient_bits, remainder_bits)) in [
            (last_two.clone(), &year_pair_bits[0]),
            (century, &year_pair_bits[1]),
        ] {
            let quotient = bit_sum::<E>(quotient_bits);
            let remainder = bit_sum::<E>(remainder_bits);
            eval.add_constraint(
                active.clone() * (value - m31_const::<E>(4) * quotient - remainder.clone()),
            );
            remainders.push(remainder);
        }

        for (value, (is_zero, inverse)) in [
            (remainders[0].clone(), &zero_checks[0]),
            (remainders[1].clone(), &zero_checks[1]),
            (last_two, &zero_checks[2]),
        ] {
            eval.add_constraint(active.clone() * value.clone() * is_zero.clone());
            eval.add_constraint(
                active.clone() * (value * inverse.clone() + is_zero.clone() - one.clone()),
            );
            eval.add_constraint(active.clone() * is_zero.clone() * inverse.clone());
        }

        let div4_last = zero_checks[0].0.clone();
        let div4_century = zero_checks[1].0.clone();
        let div100 = zero_checks[2].0.clone();
        eval.add_constraint(
            active.clone()
                * (leap.clone()
                    - div4_last * (one.clone() - div100.clone())
                    - div100 * div4_century),
        );

        let is_february = month_selectors[1].clone();
        let is_thirty_day_month = month_selectors[3].clone()
            + month_selectors[5].clone()
            + month_selectors[8].clone()
            + month_selectors[10].clone();
        let max_day =
            m31_const::<E>(31) - is_thirty_day_month - m31_const::<E>(3) * is_february.clone()
                + leap * is_february;
        let calendar_slack = bit_sum::<E>(&calendar_slack_bits);
        eval.add_constraint(active.clone() * (max_day - day - calendar_slack));
        eval.add_constraint(
            valid_from_active.clone()
                * (m31_const::<E>(before_second)
                    + m31_const::<E>(SECOND_LIMB_BASE) * borrow.clone()
                    - second_key.clone()
                    - second_slack.clone()),
        );
        eval.add_constraint(
            valid_from_active
                * (m31_const::<E>(before_date)
                    - date_key.clone()
                    - borrow.clone()
                    - date_slack.clone()),
        );
        eval.add_constraint(
            valid_until_active.clone()
                * (second_key + m31_const::<E>(SECOND_LIMB_BASE) * borrow.clone()
                    - m31_const::<E>(after_second)
                    - second_slack),
        );
        eval.add_constraint(
            valid_until_active * (date_key - m31_const::<E>(after_date) - borrow - date_slack),
        );

        for (byte_idx, value) in bytes.into_iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.issuer_field_relation,
                E::EF::from(active.clone()),
                &[field_id.clone(), m31_const::<E>(byte_idx as u32), value],
            ));
        }
        // The committed claim mask is emitted last to match the generator.
        if let Some(beta) = self.claim_mask_beta {
            add_claim_mask_fraction(&mut eval, beta);
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

impl Air for MdocValidityBind {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(self.verification_time_epoch_seconds);
        for row in &self.rows {
            channel.mix_u64(u64::from(row.field_id));
            channel.mix_u64(u64::from(!row.valid_from));
        }
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        let mask_enabled = self.claim_mask_challenge.is_some();
        TreeLayout {
            preprocessed: vec![MDOC_VALIDITY_LOG_SIZE; MDOC_VALIDITY_PREPROCESSED_COLS],
            trace: vec![
                MDOC_VALIDITY_LOG_SIZE;
                MDOC_VALIDITY_TRACE_COLS
                    + usize::from(mask_enabled) * CLAIM_MASK_TRACE_COLUMNS
            ],
            interaction: vec![
                MDOC_VALIDITY_LOG_SIZE;
                (MDOC_VALIDITY_LOOKUPS + usize::from(mask_enabled)).div_ceil(2)
                    * SECURE_EXTENSION_DEGREE
            ],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        vec![self.interaction_claim().claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        mdoc_validity_preprocessed_column_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(mdoc_validity_preprocessed_columns(&self.rows))
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        self.component = Some(MdocValidityComponent::new(
            allocator,
            MdocValidityEval {
                verification_time_epoch_seconds: self.verification_time_epoch_seconds,
                issuer_field_relation: self.issuer_field_relation(),
                claim_mask_beta: self.claim_mask_beta(),
            },
            claim.claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc validity component is built")]
    }
}

impl AirProver for MdocValidityBind {
    fn max_log_size(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_VALIDITY_LOG_SIZE + 1
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &mdoc_validity_preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_validity::MdocValidityBind",
            &mdoc_validity_preprocessed_column_ids(),
            &mdoc_validity_preprocessed_columns(&self.rows),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = mdoc_validity_preprocessed_column_ids();
        let all_columns = mdoc_validity_preprocessed_columns(&self.rows);
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected mdoc validity preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(mdoc_validity_base_trace(
            self.verification_time_epoch_seconds,
            &self.rows,
        ));
        if let Some(mask) = &self.claim_mask_trace {
            tb.extend_evals(mask.columns().to_vec());
        }
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let claim_mask_beta = self.claim_mask_beta();
        let (trace, claimed_sum) = mdoc_validity_interaction_trace(
            self.verification_time_epoch_seconds,
            &self.rows,
            &self.issuer_field_relation(),
            self.claim_mask_trace.as_ref(),
            claim_mask_beta,
        );
        tb.extend_evals(trace);
        self.interaction_claim = Some(MdocValidityInteractionClaim { claimed_sum });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![self
            .component
            .as_ref()
            .expect("mdoc validity component is built")]
    }
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let value = rng.next_u32() & 0x7fff_ffff;
        if value < 2_147_483_647 {
            return M31::from_u32_unchecked(value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use air_core::claim_mask::ClaimMaskRing;
    use stwo::prover::backend::simd::m31::N_LANES;
    use stwo_constraint_framework::expr::ExprEvaluator;
    use stwo_constraint_framework::{Multiplicity, PREPROCESSED_TRACE_IDX};

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn inactive_validity_row() -> Self {
            let blind = M31::from_u32_unchecked(2);
            let zero = M31::from_u32_unchecked(0);
            let mut row = Self::default();

            for _ in 0..MDOC_VALIDITY_PREPROCESSED_COLS {
                row.preprocessed.push_back(vec![zero]);
            }
            for _ in 0..MDOC_VALIDITY_TRACE_COLS {
                row.original.push_back(vec![blind]);
            }

            row
        }

        fn nonzero_constraints(&self) -> Vec<(usize, QM31)> {
            self.constraints
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| *value != QM31::from_u32_unchecked(0, 0, 0, 0))
                .collect()
        }

        fn active_validity_row(
            verification_time_epoch_seconds: u64,
            bytes: [u8; TIMESTAMP_TEXT_LEN],
            valid_from: bool,
        ) -> Self {
            let rows = vec![MdocValidityRow::new(
                field_id::MDOC_VALID_FROM,
                valid_from,
                bytes,
            )];
            let preprocessed = mdoc_validity_preprocessed_columns(&rows);
            let trace = mdoc_validity_base_trace(verification_time_epoch_seconds, &rows);
            let row_index = bit_reverse_index(
                coset_index_to_circle_domain_index(0, MDOC_VALIDITY_LOG_SIZE),
                MDOC_VALIDITY_LOG_SIZE,
            );
            let read = |column: &MdocValidityColumnEval| {
                column.data[row_index / N_LANES].to_array()[row_index % N_LANES]
            };
            Self {
                preprocessed: preprocessed
                    .iter()
                    .map(|column| vec![read(column)])
                    .collect(),
                original: trace.iter().map(|column| vec![read(column)]).collect(),
                constraints: Vec::new(),
            }
        }
    }

    impl EvalAtRow for RowEval {
        type F = M31;
        type EF = QM31;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            _offsets: [isize; N],
        ) -> [Self::F; N] {
            let queue = match interaction {
                PREPROCESSED_TRACE_IDX => &mut self.preprocessed,
                stwo_constraint_framework::ORIGINAL_TRACE_IDX => &mut self.original,
                _ => panic!("unexpected interaction index {interaction}"),
            };
            let values = queue
                .pop_front()
                .unwrap_or_else(|| panic!("missing mask for interaction {interaction}"));
            assert_eq!(values.len(), N, "mask arity mismatch");
            std::array::from_fn(|index| values[index])
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.constraints.push(QM31::from(constraint));
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            QM31::from_m31_array(values)
        }

        fn add_to_relation<R: Relation<Self::F, Self::EF>>(
            &mut self,
            _entry: RelationEntry<'_, Self::F, Self::EF, R>,
        ) {
        }

        fn write_logup_frac_typed(
            &mut self,
            _numerator: Multiplicity<Self::F, Self::EF>,
            _denominator: Self::EF,
        ) {
        }

        fn finalize_logup_in_pairs(&mut self) {}
    }

    fn trace_fingerprint(trace: &[MdocValidityColumnEval]) -> Vec<[M31; N_LANES]> {
        trace
            .iter()
            .flat_map(|column| column.data.iter().map(|packed| packed.to_array()))
            .collect()
    }

    fn test_rows() -> Vec<MdocValidityRow> {
        mdoc_validity_rows(*b"2020-01-01T00:00:00Z", *b"2030-12-31T23:59:59Z")
    }

    fn test_verification_time() -> u64 {
        20_642 * 86_400 + 43_200
    }

    fn row_constraints(bytes: [u8; TIMESTAMP_TEXT_LEN], valid_from: bool) -> Vec<(usize, QM31)> {
        let eval = MdocValidityEval {
            verification_time_epoch_seconds: test_verification_time(),
            issuer_field_relation: FieldBytesRelation::dummy(),
            claim_mask_beta: None,
        };
        eval.evaluate(RowEval::active_validity_row(
            test_verification_time(),
            bytes,
            valid_from,
        ))
        .nonzero_constraints()
    }

    #[test]
    fn mdoc_validity_inactive_rows_are_not_zero_or_boolean_pinned() {
        let eval = MdocValidityEval {
            verification_time_epoch_seconds: test_verification_time(),
            issuer_field_relation: FieldBytesRelation::dummy(),
            claim_mask_beta: None,
        };
        let row = eval.evaluate(RowEval::inactive_validity_row());

        let nonzero = row.nonzero_constraints();
        assert!(
            nonzero.is_empty(),
            "inactive validity row still hits constraints: {nonzero:?}"
        );
    }

    #[test]
    fn mdoc_validity_preprocessed_ids_match_columns_and_layout() {
        let ids = mdoc_validity_preprocessed_column_ids();
        let columns = mdoc_validity_preprocessed_columns(&test_rows());
        assert_eq!(ids.len(), MDOC_VALIDITY_PREPROCESSED_COLS);
        assert_eq!(columns.len(), MDOC_VALIDITY_PREPROCESSED_COLS);
        let unique = ids
            .iter()
            .map(|id| id.id.as_str())
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(unique.len(), MDOC_VALIDITY_PREPROCESSED_COLS);
    }

    #[test]
    fn mdoc_validity_enforces_gregorian_calendar_in_both_rows() {
        for valid in [
            *b"2000-02-29T00:00:00Z",
            *b"2004-02-29T00:00:00Z",
            *b"2020-04-30T00:00:00Z",
        ] {
            assert!(
                row_constraints(valid, true).is_empty(),
                "valid Gregorian validFrom date rejected: {:?}",
                String::from_utf8_lossy(&valid)
            );
        }
        assert!(
            row_constraints(*b"2030-12-31T23:59:59Z", false).is_empty(),
            "valid validUntil date rejected"
        );

        for invalid in [
            *b"1900-02-29T00:00:00Z",
            *b"2023-02-29T00:00:00Z",
            *b"2024-02-30T00:00:00Z",
            *b"2024-04-31T00:00:00Z",
            *b"2024-06-31T00:00:00Z",
            *b"2024-09-31T00:00:00Z",
            *b"2024-11-31T00:00:00Z",
        ] {
            assert!(
                !row_constraints(invalid, true).is_empty(),
                "invalid Gregorian validFrom date accepted: {:?}",
                String::from_utf8_lossy(&invalid)
            );
        }
        assert!(
            !row_constraints(*b"2100-02-29T00:00:00Z", false).is_empty(),
            "invalid Gregorian validUntil date accepted"
        );
    }

    #[test]
    fn mdoc_validity_expression_degree_matches_declared_bound() {
        let eval = MdocValidityEval {
            verification_time_epoch_seconds: test_verification_time(),
            issuer_field_relation: FieldBytesRelation::dummy(),
            claim_mask_beta: None,
        };
        let measured = eval
            .clone()
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds()
            .into_iter()
            .max()
            .unwrap_or(0) as u32;
        assert_eq!(measured, 3);
        assert_eq!(
            eval.max_constraint_log_degree_bound(),
            MDOC_VALIDITY_LOG_SIZE + 1
        );
    }

    #[test]
    fn mdoc_validity_class_a_has_256_blind_rows_and_fresh_inactive_cells() {
        assert!(
            (1usize << MDOC_VALIDITY_LOG_SIZE) - test_rows().len() >= 256,
            "mdoc validity Class A needs at least 256 blind rows"
        );

        let rows = test_rows();
        let first = trace_fingerprint(&mdoc_validity_base_trace(test_verification_time(), &rows));
        let second = trace_fingerprint(&mdoc_validity_base_trace(test_verification_time(), &rows));
        let zero = [M31::from_u32_unchecked(0); N_LANES];

        assert!(
            first.iter().any(|value| *value != zero),
            "mdoc validity inactive rows are still all zero"
        );
        assert_ne!(
            first, second,
            "mdoc validity inactive cells must be fresh per trace"
        );
    }

    #[test]
    fn claim_mask_changes_validity_claim_by_beta_times_target_sum() {
        let rows = test_rows();
        let relation = FieldBytesRelation::dummy();
        let (_, unmasked_claim) =
            mdoc_validity_interaction_trace(test_verification_time(), &rows, &relation, None, None);
        let mut ring =
            ClaimMaskRing::new(&[MDOC_VALIDITY_LOG_SIZE, MDOC_VALIDITY_LOG_SIZE]).unwrap();
        let mask = ring.take(MDOC_VALIDITY_LOG_SIZE).unwrap();
        let beta = QM31::from_m31_array([
            M31::from_u32_unchecked(3),
            M31::from_u32_unchecked(5),
            M31::from_u32_unchecked(7),
            M31::from_u32_unchecked(11),
        ]);
        let (_, masked_claim) = mdoc_validity_interaction_trace(
            test_verification_time(),
            &rows,
            &relation,
            Some(&mask),
            Some(beta),
        );

        assert_eq!(masked_claim - unmasked_claim, beta * mask.target_sum());
    }
}
