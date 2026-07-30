//! Exact private MSO validity for the unlinkable TS13 demo profile.
//!
//! The private MSO binder authenticates and yields the two exact 20-byte
//! tag-0 UTC strings through [`MdocMsoValidityBytesRelation`].  This component
//! consumes those bytes, proves their canonical Gregorian interpretation, and
//! proves the strict whole-second inequalities
//!
//! ```text
//! validFrom < timestamp < validUntil.
//! ```
//!
//! Host parsing is only an early-error path.  Every digit, separator, calendar
//! rule, Unix-second conversion limb, and comparison slack is constrained in
//! the AIR.

use std::fmt;

use air_core::relations::SharedRelation;
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
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_mldsa::coeffs::relations::{RangeRelation, SharedRangeRelation};
use stwo_mldsa::coeffs::tables::RcKind;
use stwo_mldsa::coeffs::RcUses;

use crate::claimed_sum_blinder::{
    add_blinder_relation_entry, blinder_counter_interaction, blinder_denominator, random_qm31,
    ClaimedSumBlinderEval, ClaimedSumBlinderRelation,
};

pub(crate) const MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE: u32 = 9;
pub(crate) const MDOC_PRIVATE_MSO_VALIDITY_ROWS: usize =
    1usize << MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE;
pub(crate) const MDOC_PRIVATE_MSO_VALIDITY_ACTIVE_ROWS: usize = 2;
pub(crate) const MDOC_PRIVATE_MSO_VALIDITY_BLIND_ROWS: usize =
    MDOC_PRIVATE_MSO_VALIDITY_ROWS - MDOC_PRIVATE_MSO_VALIDITY_ACTIVE_ROWS;
pub(crate) const MDOC_TDATE_BYTES: usize = 20;

const VALIDITY_VERSION: u64 = 2;
const VALIDITY_DOMAIN: u64 = 0x4d44_4f43_5641_4c32; // "MDOCVAL2"
const PREPROCESSED_COLS: usize = 2;
const DIGIT_COUNT: usize = 14;
const MONTHS: usize = 12;
const UNIX_DAYS_TO_2020: u32 = 18_262;
const SECONDS_PER_DAY: u32 = 86_400;
const TWO_POW_16: u32 = 1 << 16;
const DAY_PRODUCT_LOW_FACTOR: u32 = SECONDS_PER_DAY - TWO_POW_16;
const MAX_YEARS_SINCE_2020: u32 = 79;

const TRACE_BYTES: usize = 0;
const TRACE_DIGITS: usize = TRACE_BYTES + MDOC_TDATE_BYTES;
const TRACE_DIGIT_SLACKS: usize = TRACE_DIGITS + DIGIT_COUNT;
const TRACE_MONTH_SELECTORS: usize = TRACE_DIGIT_SLACKS + DIGIT_COUNT;
const TRACE_YEARS_SINCE_2020: usize = TRACE_MONTH_SELECTORS + MONTHS;
const TRACE_YEAR_UPPER_SLACK: usize = TRACE_YEARS_SINCE_2020 + 1;
const TRACE_LEAP_QUOTIENT: usize = TRACE_YEAR_UPPER_SLACK + 1;
const TRACE_LEAP_REMAINDER_SELECTORS: usize = TRACE_LEAP_QUOTIENT + 1;
const TRACE_DAY_MINUS_ONE: usize = TRACE_LEAP_REMAINDER_SELECTORS + 4;
const TRACE_MONTH_DAY_SLACK: usize = TRACE_DAY_MINUS_ONE + 1;
const TRACE_HOUR_SLACK: usize = TRACE_MONTH_DAY_SLACK + 1;
const TRACE_MINUTE_SLACK: usize = TRACE_HOUR_SLACK + 1;
const TRACE_SECOND_SLACK: usize = TRACE_MINUTE_SLACK + 1;
const TRACE_MUL_LO_LO8: usize = TRACE_SECOND_SLACK + 1;
const TRACE_MUL_LO_HI8: usize = TRACE_MUL_LO_LO8 + 1;
const TRACE_MUL_HI_LO8: usize = TRACE_MUL_LO_HI8 + 1;
const TRACE_MUL_HI_HI7: usize = TRACE_MUL_HI_LO8 + 1;
const TRACE_SECONDS_LO_LO8: usize = TRACE_MUL_HI_HI7 + 1;
const TRACE_SECONDS_LO_HI8: usize = TRACE_SECONDS_LO_LO8 + 1;
const TRACE_SECONDS_HI_LO8: usize = TRACE_SECONDS_LO_HI8 + 1;
const TRACE_SECONDS_HI_HI8: usize = TRACE_SECONDS_HI_LO8 + 1;
const TRACE_CARRY_SELECTORS: usize = TRACE_SECONDS_HI_HI8 + 1;
const TRACE_COMPARE_BORROW: usize = TRACE_CARRY_SELECTORS + 3;
const TRACE_SLACK_LO_LO8: usize = TRACE_COMPARE_BORROW + 1;
const TRACE_SLACK_LO_HI8: usize = TRACE_SLACK_LO_LO8 + 1;
const TRACE_SLACK_HI_LO8: usize = TRACE_SLACK_LO_HI8 + 1;
const TRACE_SLACK_HI_HI8: usize = TRACE_SLACK_HI_LO8 + 1;
const TRACE_COLS: usize = TRACE_SLACK_HI_HI8 + 1;

const PP_ACTIVE: usize = 0;
const PP_IS_VALID_UNTIL: usize = 1;

const DIGIT_POSITIONS: [usize; DIGIT_COUNT] = [0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18];
const COMMON_DAYS_BEFORE_MONTH: [u32; MONTHS] =
    [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
const COMMON_DAYS_IN_MONTH: [u32; MONTHS] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

// `(kind, byte_0, ..., byte_19)`, where `kind=0` is `validFrom` and
// `kind=1` is `validUntil`.
relation!(MdocMsoValidityBytesRelation, 21);

pub(crate) type SharedMdocMsoValidityBytesRelation = SharedRelation<MdocMsoValidityBytesRelation>;

type ValidityColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;
type ValidityComponent = FrameworkComponent<MdocPrivateMsoValidityEval>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoValiditySpec {
    pub(crate) timestamp_epoch_seconds: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoValidityWitness {
    pub(crate) valid_from: [u8; MDOC_TDATE_BYTES],
    pub(crate) valid_until: [u8; MDOC_TDATE_BYTES],
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct MdocPrivateMsoValidityInteractionClaim {
    pub(crate) claimed_sum: QM31,
    pub(crate) blinder_v: QM31,
    pub(crate) blinder_m: QM31,
    pub(crate) blinder_claimed_sum: QM31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MdocPrivateMsoValidityError {
    TimestampOutOfRange {
        timestamp_epoch_seconds: i64,
    },
    MalformedTdate {
        field: &'static str,
    },
    UnsupportedYear {
        field: &'static str,
        year: u32,
    },
    InvalidGregorianDate {
        field: &'static str,
        year: u32,
        month: u32,
        day: u32,
    },
    InvalidTime {
        field: &'static str,
        hour: u32,
        minute: u32,
        second: u32,
    },
    NotYetValid,
    Expired,
}

impl fmt::Display for MdocPrivateMsoValidityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TimestampOutOfRange {
                timestamp_epoch_seconds,
            } => write!(
                f,
                "verification timestamp {timestamp_epoch_seconds} is outside the supported unsigned 32-bit demo range"
            ),
            Self::MalformedTdate { field } => {
                write!(f, "{field} is not canonical YYYY-MM-DDTHH:MM:SSZ")
            }
            Self::UnsupportedYear { field, year } => {
                write!(f, "{field} year {year} is outside 2020..=2099")
            }
            Self::InvalidGregorianDate {
                field,
                year,
                month,
                day,
            } => write!(f, "{field} is not a Gregorian date ({year:04}-{month:02}-{day:02})"),
            Self::InvalidTime {
                field,
                hour,
                minute,
                second,
            } => write!(
                f,
                "{field} is not a UTC whole second ({hour:02}:{minute:02}:{second:02})"
            ),
            Self::NotYetValid => write!(f, "verification timestamp is not after validFrom"),
            Self::Expired => write!(f, "verification timestamp is not before validUntil"),
        }
    }
}

impl std::error::Error for MdocPrivateMsoValidityError {}

#[derive(Clone, Copy, Debug)]
struct ParsedTdate {
    bytes: [u8; MDOC_TDATE_BYTES],
    digits: [u32; DIGIT_COUNT],
    year: u32,
    month: u32,
    day: u32,
    hour: u32,
    minute: u32,
    second: u32,
}

#[derive(Clone)]
struct ValidityRow {
    cells: [u32; TRACE_COLS],
}

impl ValidityRow {
    fn range_cells(&self) -> Vec<(RcKind, u32)> {
        let mut cells = Vec::with_capacity(48);
        for index in 0..DIGIT_COUNT {
            cells.push((RcKind::Rc7, self.cells[TRACE_DIGITS + index]));
        }
        for index in 0..DIGIT_COUNT {
            cells.push((RcKind::Rc7, self.cells[TRACE_DIGIT_SLACKS + index]));
        }
        cells.push((RcKind::Rc7, self.cells[TRACE_YEARS_SINCE_2020]));
        cells.push((RcKind::Rc7, self.cells[TRACE_YEAR_UPPER_SLACK]));
        cells.push((RcKind::Rc7, self.cells[TRACE_LEAP_QUOTIENT]));
        cells.push((RcKind::Rc7, self.cells[TRACE_DAY_MINUS_ONE]));
        cells.push((RcKind::Rc7, self.cells[TRACE_MONTH_DAY_SLACK]));
        cells.push((RcKind::Rc7, self.cells[TRACE_HOUR_SLACK]));
        cells.push((RcKind::Rc7, self.cells[TRACE_MINUTE_SLACK]));
        cells.push((RcKind::Rc7, self.cells[TRACE_SECOND_SLACK]));
        cells.extend([
            (RcKind::Rc8, self.cells[TRACE_MUL_LO_LO8]),
            (RcKind::Rc8, self.cells[TRACE_MUL_LO_HI8]),
            (RcKind::Rc8, self.cells[TRACE_MUL_HI_LO8]),
            (RcKind::Rc7, self.cells[TRACE_MUL_HI_HI7]),
            (RcKind::Rc8, self.cells[TRACE_SECONDS_LO_LO8]),
            (RcKind::Rc8, self.cells[TRACE_SECONDS_LO_HI8]),
            (RcKind::Rc8, self.cells[TRACE_SECONDS_HI_LO8]),
            (RcKind::Rc8, self.cells[TRACE_SECONDS_HI_HI8]),
            (RcKind::Rc8, self.cells[TRACE_SLACK_LO_LO8]),
            (RcKind::Rc8, self.cells[TRACE_SLACK_LO_HI8]),
            (RcKind::Rc8, self.cells[TRACE_SLACK_HI_LO8]),
            (RcKind::Rc8, self.cells[TRACE_SLACK_HI_HI8]),
        ]);
        debug_assert_eq!(cells.len(), 48);
        cells
    }
}

fn parse_digits(bytes: &[u8]) -> Option<u32> {
    bytes.iter().try_fold(0u32, |value, byte| {
        byte.is_ascii_digit()
            .then_some(value * 10 + u32::from(*byte - b'0'))
    })
}

fn is_leap_year(year: u32) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

fn days_in_month(year: u32, month: u32) -> Option<u32> {
    let mut days = *COMMON_DAYS_IN_MONTH.get(month.checked_sub(1)? as usize)?;
    if month == 2 && is_leap_year(year) {
        days += 1;
    }
    Some(days)
}

fn parse_tdate(
    bytes: [u8; MDOC_TDATE_BYTES],
    field: &'static str,
) -> Result<ParsedTdate, MdocPrivateMsoValidityError> {
    for (index, expected) in [
        (4usize, b'-'),
        (7, b'-'),
        (10, b'T'),
        (13, b':'),
        (16, b':'),
        (19, b'Z'),
    ] {
        if bytes[index] != expected {
            return Err(MdocPrivateMsoValidityError::MalformedTdate { field });
        }
    }
    let mut digits = [0u32; DIGIT_COUNT];
    for (digit_index, byte_index) in DIGIT_POSITIONS.into_iter().enumerate() {
        let byte = bytes[byte_index];
        if !byte.is_ascii_digit() {
            return Err(MdocPrivateMsoValidityError::MalformedTdate { field });
        }
        digits[digit_index] = u32::from(byte - b'0');
    }
    let year =
        parse_digits(&bytes[0..4]).ok_or(MdocPrivateMsoValidityError::MalformedTdate { field })?;
    if !(2020..=2099).contains(&year) {
        return Err(MdocPrivateMsoValidityError::UnsupportedYear { field, year });
    }
    let month =
        parse_digits(&bytes[5..7]).ok_or(MdocPrivateMsoValidityError::MalformedTdate { field })?;
    let day =
        parse_digits(&bytes[8..10]).ok_or(MdocPrivateMsoValidityError::MalformedTdate { field })?;
    let Some(max_day) = days_in_month(year, month) else {
        return Err(MdocPrivateMsoValidityError::InvalidGregorianDate {
            field,
            year,
            month,
            day,
        });
    };
    if day == 0 || day > max_day {
        return Err(MdocPrivateMsoValidityError::InvalidGregorianDate {
            field,
            year,
            month,
            day,
        });
    }
    let hour = parse_digits(&bytes[11..13])
        .ok_or(MdocPrivateMsoValidityError::MalformedTdate { field })?;
    let minute = parse_digits(&bytes[14..16])
        .ok_or(MdocPrivateMsoValidityError::MalformedTdate { field })?;
    let second = parse_digits(&bytes[17..19])
        .ok_or(MdocPrivateMsoValidityError::MalformedTdate { field })?;
    if hour >= 24 || minute >= 60 || second >= 60 {
        return Err(MdocPrivateMsoValidityError::InvalidTime {
            field,
            hour,
            minute,
            second,
        });
    }
    Ok(ParsedTdate {
        bytes,
        digits,
        year,
        month,
        day,
        hour,
        minute,
        second,
    })
}

fn unix_days(date: ParsedTdate) -> u32 {
    let years_since_2020 = date.year - 2020;
    let leap_days_before_year = (years_since_2020 + 3) / 4;
    let month_index = (date.month - 1) as usize;
    let leap_day_before_month = u32::from(is_leap_year(date.year) && date.month > 2);
    UNIX_DAYS_TO_2020
        + 365 * years_since_2020
        + leap_days_before_year
        + COMMON_DAYS_BEFORE_MONTH[month_index]
        + leap_day_before_month
        + date.day
        - 1
}

fn unix_seconds(date: ParsedTdate) -> u32 {
    unix_days(date) * SECONDS_PER_DAY + date.hour * 3_600 + date.minute * 60 + date.second
}

fn split_u16(value: u32) -> (u32, u32) {
    (value & 0xff, value >> 8)
}

fn row_for(
    date: ParsedTdate,
    timestamp: u32,
    is_valid_until: bool,
) -> Result<ValidityRow, MdocPrivateMsoValidityError> {
    let seconds = unix_seconds(date);
    let slack = if is_valid_until {
        seconds
            .checked_sub(timestamp)
            .and_then(|delta| delta.checked_sub(1))
            .ok_or(MdocPrivateMsoValidityError::Expired)?
    } else {
        timestamp
            .checked_sub(seconds)
            .and_then(|delta| delta.checked_sub(1))
            .ok_or(MdocPrivateMsoValidityError::NotYetValid)?
    };

    let years_since_2020 = date.year - 2020;
    let leap_quotient = (years_since_2020 + 3) / 4;
    let leap_remainder = (years_since_2020 + 3) % 4;
    let max_day =
        days_in_month(date.year, date.month).expect("parsed tdate has a supported Gregorian month");
    let days = unix_days(date);
    let day_product = days * DAY_PRODUCT_LOW_FACTOR;
    let mul_lo = day_product & 0xffff;
    let mul_hi = day_product >> 16;
    let time_of_day = date.hour * 3_600 + date.minute * 60 + date.second;
    let low_total = mul_lo + time_of_day;
    let low_carry = low_total >> 16;
    let seconds_lo = low_total & 0xffff;
    let seconds_hi = days + mul_hi + low_carry;
    debug_assert_eq!(seconds, seconds_lo + (seconds_hi << 16));

    let (timestamp_lo, timestamp_hi) = (timestamp & 0xffff, timestamp >> 16);
    let (date_lo, date_hi) = (seconds_lo, seconds_hi);
    let (lhs_lo, lhs_hi, rhs_lo, rhs_hi) = if is_valid_until {
        (date_lo, date_hi, timestamp_lo, timestamp_hi)
    } else {
        (timestamp_lo, timestamp_hi, date_lo, date_hi)
    };
    let compare_borrow = u32::from(lhs_lo < rhs_lo + 1);
    let slack_lo = lhs_lo + compare_borrow * TWO_POW_16 - rhs_lo - 1;
    let slack_hi = lhs_hi - rhs_hi - compare_borrow;
    debug_assert_eq!(slack, slack_lo + (slack_hi << 16));

    let mut cells = [0u32; TRACE_COLS];
    for (index, byte) in date.bytes.into_iter().enumerate() {
        cells[TRACE_BYTES + index] = u32::from(byte);
    }
    for (index, digit) in date.digits.into_iter().enumerate() {
        cells[TRACE_DIGITS + index] = digit;
        cells[TRACE_DIGIT_SLACKS + index] = 9 - digit;
    }
    cells[TRACE_MONTH_SELECTORS + (date.month - 1) as usize] = 1;
    cells[TRACE_YEARS_SINCE_2020] = years_since_2020;
    cells[TRACE_YEAR_UPPER_SLACK] = MAX_YEARS_SINCE_2020.saturating_sub(years_since_2020);
    cells[TRACE_LEAP_QUOTIENT] = leap_quotient;
    cells[TRACE_LEAP_REMAINDER_SELECTORS + leap_remainder as usize] = 1;
    cells[TRACE_DAY_MINUS_ONE] = date.day - 1;
    cells[TRACE_MONTH_DAY_SLACK] = max_day - date.day;
    cells[TRACE_HOUR_SLACK] = 23 - date.hour;
    cells[TRACE_MINUTE_SLACK] = 59 - date.minute;
    cells[TRACE_SECOND_SLACK] = 59 - date.second;
    (cells[TRACE_MUL_LO_LO8], cells[TRACE_MUL_LO_HI8]) = split_u16(mul_lo);
    cells[TRACE_MUL_HI_LO8] = mul_hi & 0xff;
    cells[TRACE_MUL_HI_HI7] = mul_hi >> 8;
    (cells[TRACE_SECONDS_LO_LO8], cells[TRACE_SECONDS_LO_HI8]) = split_u16(seconds_lo);
    (cells[TRACE_SECONDS_HI_LO8], cells[TRACE_SECONDS_HI_HI8]) = split_u16(seconds_hi);
    cells[TRACE_CARRY_SELECTORS + low_carry as usize] = 1;
    cells[TRACE_COMPARE_BORROW] = compare_borrow;
    (cells[TRACE_SLACK_LO_LO8], cells[TRACE_SLACK_LO_HI8]) = split_u16(slack_lo);
    (cells[TRACE_SLACK_HI_LO8], cells[TRACE_SLACK_HI_HI8]) = split_u16(slack_hi);
    Ok(ValidityRow { cells })
}

fn build_rows(
    spec: MdocPrivateMsoValiditySpec,
    witness: &MdocPrivateMsoValidityWitness,
) -> Result<[ValidityRow; 2], MdocPrivateMsoValidityError> {
    let timestamp = u32::try_from(spec.timestamp_epoch_seconds).map_err(|_| {
        MdocPrivateMsoValidityError::TimestampOutOfRange {
            timestamp_epoch_seconds: spec.timestamp_epoch_seconds,
        }
    })?;
    let valid_from = parse_tdate(witness.valid_from, "validFrom")?;
    let valid_until = parse_tdate(witness.valid_until, "validUntil")?;
    Ok([
        row_for(valid_from, timestamp, false)?,
        row_for(valid_until, timestamp, true)?,
    ])
}

fn validate_spec(spec: MdocPrivateMsoValiditySpec) -> Result<u32, MdocPrivateMsoValidityError> {
    u32::try_from(spec.timestamp_epoch_seconds).map_err(|_| {
        MdocPrivateMsoValidityError::TimestampOutOfRange {
            timestamp_epoch_seconds: spec.timestamp_epoch_seconds,
        }
    })
}

fn m31(value: u32) -> M31 {
    M31::from_u32_unchecked(value)
}

fn random_m31_cell() -> M31 {
    let mut rng = rand::thread_rng();
    loop {
        let candidate = rng.next_u32() & 0x7fff_ffff;
        if candidate != 0x7fff_ffff {
            return m31(candidate);
        }
    }
}

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![m31(0); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn column_eval(values: Vec<M31>) -> ValidityColumnEval {
    CircleEvaluation::new(
        CanonicCoset::new(MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE).circle_domain(),
        BaseColumn::from_iter(coset_order_to_circle_domain_order(
            MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE,
            values,
        )),
    )
}

fn col_id(name: &str) -> PreProcessedColumnId {
    PreProcessedColumnId {
        id: format!("mdoc/private_mso_validity/v{VALIDITY_VERSION}/{name}"),
    }
}

fn preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    vec![col_id("active"), col_id("is_valid_until")]
}

fn preprocessed_columns() -> Vec<ValidityColumnEval> {
    let mut active = vec![m31(0); MDOC_PRIVATE_MSO_VALIDITY_ROWS];
    let mut is_valid_until = vec![m31(0); MDOC_PRIVATE_MSO_VALIDITY_ROWS];
    active[0] = m31(1);
    active[1] = m31(1);
    is_valid_until[1] = m31(1);
    vec![column_eval(active), column_eval(is_valid_until)]
}

fn base_trace(rows: &[ValidityRow; 2]) -> Vec<ValidityColumnEval> {
    let mut columns = vec![vec![m31(0); MDOC_PRIVATE_MSO_VALIDITY_ROWS]; TRACE_COLS];
    for column in &mut columns {
        for value in column {
            *value = random_m31_cell();
        }
    }
    for (row_index, row) in rows.iter().enumerate() {
        for (column_index, value) in row.cells.iter().copied().enumerate() {
            columns[column_index][row_index] = m31(value);
        }
    }
    columns.into_iter().map(column_eval).collect()
}

fn range_columns() -> Vec<(usize, RcKind)> {
    let mut columns = Vec::with_capacity(48);
    columns.extend((0..DIGIT_COUNT).map(|index| (TRACE_DIGITS + index, RcKind::Rc7)));
    columns.extend((0..DIGIT_COUNT).map(|index| (TRACE_DIGIT_SLACKS + index, RcKind::Rc7)));
    columns.extend([
        (TRACE_YEARS_SINCE_2020, RcKind::Rc7),
        (TRACE_YEAR_UPPER_SLACK, RcKind::Rc7),
        (TRACE_LEAP_QUOTIENT, RcKind::Rc7),
        (TRACE_DAY_MINUS_ONE, RcKind::Rc7),
        (TRACE_MONTH_DAY_SLACK, RcKind::Rc7),
        (TRACE_HOUR_SLACK, RcKind::Rc7),
        (TRACE_MINUTE_SLACK, RcKind::Rc7),
        (TRACE_SECOND_SLACK, RcKind::Rc7),
        (TRACE_MUL_LO_LO8, RcKind::Rc8),
        (TRACE_MUL_LO_HI8, RcKind::Rc8),
        (TRACE_MUL_HI_LO8, RcKind::Rc8),
        (TRACE_MUL_HI_HI7, RcKind::Rc7),
        (TRACE_SECONDS_LO_LO8, RcKind::Rc8),
        (TRACE_SECONDS_LO_HI8, RcKind::Rc8),
        (TRACE_SECONDS_HI_LO8, RcKind::Rc8),
        (TRACE_SECONDS_HI_HI8, RcKind::Rc8),
        (TRACE_SLACK_LO_LO8, RcKind::Rc8),
        (TRACE_SLACK_LO_HI8, RcKind::Rc8),
        (TRACE_SLACK_HI_LO8, RcKind::Rc8),
        (TRACE_SLACK_HI_HI8, RcKind::Rc8),
    ]);
    debug_assert_eq!(columns.len(), 48);
    columns
}

fn range_uses(rows: &[ValidityRow; 2]) -> RcUses {
    let mut uses = RcUses::new();
    for row in rows {
        for (kind, value) in row.range_cells() {
            uses.record(kind, value);
        }
    }
    uses
}

fn interaction_trace(
    rows: &[ValidityRow; 2],
    validity_relation: &MdocMsoValidityBytesRelation,
    range_relation: &RangeRelation,
    blinder_relation: &ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
) -> (Vec<ValidityColumnEval>, QM31) {
    let preprocessed = preprocessed_columns();
    let trace = base_trace(rows);
    let n_vec_rows = 1usize << (MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE - LOG_N_LANES);
    let mut sites: Vec<Vec<(PackedQM31, PackedQM31)>> = Vec::with_capacity(50);

    sites.push(
        (0..n_vec_rows)
            .map(|vec_row| {
                let mut tuple = Vec::with_capacity(1 + MDOC_TDATE_BYTES);
                tuple.push(preprocessed[PP_IS_VALID_UNTIL].data[vec_row]);
                tuple.extend(
                    (0..MDOC_TDATE_BYTES).map(|index| trace[TRACE_BYTES + index].data[vec_row]),
                );
                (
                    PackedQM31::from(preprocessed[PP_ACTIVE].data[vec_row]),
                    validity_relation.combine(&tuple),
                )
            })
            .collect(),
    );
    for (column, kind) in range_columns() {
        sites.push(
            (0..n_vec_rows)
                .map(|vec_row| {
                    (
                        PackedQM31::from(preprocessed[PP_ACTIVE].data[vec_row]),
                        range_relation.combine(&[
                            trace[column].data[vec_row],
                            PackedM31::broadcast(m31(kind.bound_id())),
                        ]),
                    )
                })
                .collect(),
        );
    }
    let blinder_num = PackedQM31::broadcast(blinder_m);
    let blinder_den = blinder_denominator(blinder_relation, blinder_v);
    sites.push(vec![(blinder_num, blinder_den); n_vec_rows]);
    debug_assert_eq!(sites.len(), 50);

    let mut logup = LogupTraceGenerator::new(MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE);
    let mut site_index = 0usize;
    while site_index + 1 < sites.len() {
        let left = &sites[site_index];
        let right = &sites[site_index + 1];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| {
            let (n0, d0) = left[vec_row];
            let (n1, d1) = right[vec_row];
            (n0 * d1 + n1 * d0, d0 * d1)
        }));
        site_index += 2;
    }
    if site_index < sites.len() {
        let last = &sites[site_index];
        logup.col_from_iter((0..n_vec_rows).map(|vec_row| last[vec_row]));
    }
    logup.finalize_last()
}

fn m31_const<E: EvalAtRow>(value: u32) -> E::F {
    E::F::from(m31(value))
}

fn boolean_constraint<E: EvalAtRow>(eval: &mut E, gate: E::F, value: E::F) {
    eval.add_constraint(gate * value.clone() * (value - m31_const::<E>(1)));
}

#[derive(Clone)]
struct MdocPrivateMsoValidityEval {
    timestamp: u32,
    validity_relation: MdocMsoValidityBytesRelation,
    range_relation: RangeRelation,
    blinder_relation: ClaimedSumBlinderRelation,
    blinder_v: QM31,
    blinder_m: QM31,
}

impl FrameworkEval for MdocPrivateMsoValidityEval {
    fn log_size(&self) -> u32 {
        MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        // Gated selector products (month × leap × active) are cubic.
        MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.get_preprocessed_column(col_id("active"));
        let is_valid_until = eval.get_preprocessed_column(col_id("is_valid_until"));
        let values: Vec<E::F> = (0..TRACE_COLS).map(|_| eval.next_trace_mask()).collect();
        let one = m31_const::<E>(1);

        boolean_constraint(&mut eval, one.clone(), active.clone());
        boolean_constraint(&mut eval, active.clone(), is_valid_until.clone());

        let bytes: [E::F; MDOC_TDATE_BYTES] =
            std::array::from_fn(|index| values[TRACE_BYTES + index].clone());
        let digits: [E::F; DIGIT_COUNT] =
            std::array::from_fn(|index| values[TRACE_DIGITS + index].clone());
        let digit_slacks: [E::F; DIGIT_COUNT] =
            std::array::from_fn(|index| values[TRACE_DIGIT_SLACKS + index].clone());
        for index in 0..DIGIT_COUNT {
            eval.add_constraint(
                active.clone()
                    * (digits[index].clone() + digit_slacks[index].clone() - m31_const::<E>(9)),
            );
            eval.add_constraint(
                active.clone()
                    * (bytes[DIGIT_POSITIONS[index]].clone()
                        - m31_const::<E>(u32::from(b'0'))
                        - digits[index].clone()),
            );
        }
        for (index, expected) in [
            (4usize, b'-'),
            (7, b'-'),
            (10, b'T'),
            (13, b':'),
            (16, b':'),
            (19, b'Z'),
        ] {
            eval.add_constraint(
                active.clone() * (bytes[index].clone() - m31_const::<E>(u32::from(expected))),
            );
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

        eval.add_constraint(
            active.clone() * (year - m31_const::<E>(2020) - values[TRACE_YEARS_SINCE_2020].clone()),
        );
        eval.add_constraint(
            active.clone()
                * (values[TRACE_YEARS_SINCE_2020].clone() + values[TRACE_YEAR_UPPER_SLACK].clone()
                    - m31_const::<E>(MAX_YEARS_SINCE_2020)),
        );

        let month_selectors: [E::F; MONTHS] =
            std::array::from_fn(|index| values[TRACE_MONTH_SELECTORS + index].clone());
        let mut month_selector_sum = m31_const::<E>(0);
        let mut selected_month = m31_const::<E>(0);
        let mut days_before_month = m31_const::<E>(0);
        let mut common_days_in_month = m31_const::<E>(0);
        let mut after_february = m31_const::<E>(0);
        for (index, selector) in month_selectors.iter().cloned().enumerate() {
            boolean_constraint(&mut eval, active.clone(), selector.clone());
            month_selector_sum = month_selector_sum + selector.clone();
            selected_month = selected_month + m31_const::<E>((index + 1) as u32) * selector.clone();
            days_before_month = days_before_month
                + m31_const::<E>(COMMON_DAYS_BEFORE_MONTH[index]) * selector.clone();
            common_days_in_month = common_days_in_month
                + m31_const::<E>(COMMON_DAYS_IN_MONTH[index]) * selector.clone();
            if index >= 2 {
                after_february = after_february + selector;
            }
        }
        eval.add_constraint(active.clone() * (month_selector_sum - one.clone()));
        eval.add_constraint(active.clone() * (month - selected_month));

        let remainder_selectors: [E::F; 4] =
            std::array::from_fn(|index| values[TRACE_LEAP_REMAINDER_SELECTORS + index].clone());
        let mut remainder_sum = m31_const::<E>(0);
        let mut remainder = m31_const::<E>(0);
        for (index, selector) in remainder_selectors.iter().cloned().enumerate() {
            boolean_constraint(&mut eval, active.clone(), selector.clone());
            remainder_sum = remainder_sum + selector.clone();
            remainder = remainder + m31_const::<E>(index as u32) * selector;
        }
        eval.add_constraint(active.clone() * (remainder_sum - one.clone()));
        eval.add_constraint(
            active.clone()
                * (values[TRACE_YEARS_SINCE_2020].clone() + m31_const::<E>(3)
                    - m31_const::<E>(4) * values[TRACE_LEAP_QUOTIENT].clone()
                    - remainder),
        );
        let is_leap = remainder_selectors[3].clone();
        let february = month_selectors[1].clone();
        let max_day = common_days_in_month + is_leap.clone() * february;
        eval.add_constraint(
            active.clone() * (day.clone() - one.clone() - values[TRACE_DAY_MINUS_ONE].clone()),
        );
        eval.add_constraint(
            active.clone() * (max_day - day.clone() - values[TRACE_MONTH_DAY_SLACK].clone()),
        );
        eval.add_constraint(
            active.clone() * (m31_const::<E>(23) - hour.clone() - values[TRACE_HOUR_SLACK].clone()),
        );
        eval.add_constraint(
            active.clone()
                * (m31_const::<E>(59) - minute.clone() - values[TRACE_MINUTE_SLACK].clone()),
        );
        eval.add_constraint(
            active.clone()
                * (m31_const::<E>(59) - second.clone() - values[TRACE_SECOND_SLACK].clone()),
        );

        let unix_days = m31_const::<E>(UNIX_DAYS_TO_2020)
            + m31_const::<E>(365) * values[TRACE_YEARS_SINCE_2020].clone()
            + values[TRACE_LEAP_QUOTIENT].clone()
            + days_before_month
            + is_leap * after_february
            + day
            - one.clone();
        let mul_lo = values[TRACE_MUL_LO_LO8].clone()
            + m31_const::<E>(256) * values[TRACE_MUL_LO_HI8].clone();
        let mul_hi = values[TRACE_MUL_HI_LO8].clone()
            + m31_const::<E>(256) * values[TRACE_MUL_HI_HI7].clone();
        eval.add_constraint(
            active.clone()
                * (m31_const::<E>(DAY_PRODUCT_LOW_FACTOR) * unix_days.clone()
                    - mul_lo.clone()
                    - m31_const::<E>(TWO_POW_16) * mul_hi.clone()),
        );
        let time_of_day = m31_const::<E>(3_600) * hour + m31_const::<E>(60) * minute + second;
        let seconds_lo = values[TRACE_SECONDS_LO_LO8].clone()
            + m31_const::<E>(256) * values[TRACE_SECONDS_LO_HI8].clone();
        let seconds_hi = values[TRACE_SECONDS_HI_LO8].clone()
            + m31_const::<E>(256) * values[TRACE_SECONDS_HI_HI8].clone();
        let carry_selectors: [E::F; 3] =
            std::array::from_fn(|index| values[TRACE_CARRY_SELECTORS + index].clone());
        let mut carry_selector_sum = m31_const::<E>(0);
        let mut carry = m31_const::<E>(0);
        for (index, selector) in carry_selectors.iter().cloned().enumerate() {
            boolean_constraint(&mut eval, active.clone(), selector.clone());
            carry_selector_sum = carry_selector_sum + selector.clone();
            carry = carry + m31_const::<E>(index as u32) * selector;
        }
        eval.add_constraint(active.clone() * (carry_selector_sum - one.clone()));
        eval.add_constraint(
            active.clone()
                * (mul_lo + time_of_day
                    - seconds_lo.clone()
                    - m31_const::<E>(TWO_POW_16) * carry.clone()),
        );
        eval.add_constraint(active.clone() * (seconds_hi.clone() - unix_days - mul_hi - carry));

        let compare_borrow = values[TRACE_COMPARE_BORROW].clone();
        boolean_constraint(&mut eval, active.clone(), compare_borrow.clone());
        let slack_lo = values[TRACE_SLACK_LO_LO8].clone()
            + m31_const::<E>(256) * values[TRACE_SLACK_LO_HI8].clone();
        let slack_hi = values[TRACE_SLACK_HI_LO8].clone()
            + m31_const::<E>(256) * values[TRACE_SLACK_HI_HI8].clone();
        let timestamp_lo = m31_const::<E>(self.timestamp & 0xffff);
        let timestamp_hi = m31_const::<E>(self.timestamp >> 16);
        let from_selector = one.clone() - is_valid_until.clone();
        let lhs_lo = from_selector.clone() * timestamp_lo.clone()
            + is_valid_until.clone() * seconds_lo.clone();
        let rhs_lo = from_selector.clone() * seconds_lo + is_valid_until.clone() * timestamp_lo;
        let lhs_hi = from_selector.clone() * timestamp_hi.clone()
            + is_valid_until.clone() * seconds_hi.clone();
        let rhs_hi = from_selector * seconds_hi + is_valid_until.clone() * timestamp_hi;
        eval.add_constraint(
            active.clone()
                * (lhs_lo + m31_const::<E>(TWO_POW_16) * compare_borrow.clone()
                    - rhs_lo
                    - one.clone()
                    - slack_lo),
        );
        eval.add_constraint(active.clone() * (lhs_hi - rhs_hi - compare_borrow - slack_hi));

        let mut validity_tuple = Vec::with_capacity(1 + MDOC_TDATE_BYTES);
        validity_tuple.push(is_valid_until);
        validity_tuple.extend(bytes);
        eval.add_to_relation(RelationEntry::new(
            &self.validity_relation,
            E::EF::from(active.clone()),
            &validity_tuple,
        ));
        for (column, kind) in range_columns() {
            eval.add_to_relation(RelationEntry::new(
                &self.range_relation,
                E::EF::from(active.clone()),
                &[values[column].clone(), m31_const::<E>(kind.bound_id())],
            ));
        }
        add_blinder_relation_entry(
            &mut eval,
            &self.blinder_relation,
            self.blinder_v,
            self.blinder_m,
            false,
        );
        eval.finalize_logup_in_pairs();
        eval
    }
}

pub(crate) struct MdocPrivateMsoValidityV2 {
    spec: MdocPrivateMsoValiditySpec,
    rows: Option<[ValidityRow; 2]>,
    range_handle: SharedRangeRelation,
    validity_handle: SharedMdocMsoValidityBytesRelation,
    blinder_relation: Option<ClaimedSumBlinderRelation>,
    interaction_claim: Option<MdocPrivateMsoValidityInteractionClaim>,
    component: Option<ValidityComponent>,
    blinder_component: Option<FrameworkComponent<ClaimedSumBlinderEval>>,
}

impl MdocPrivateMsoValidityV2 {
    pub(crate) fn prover(
        spec: MdocPrivateMsoValiditySpec,
        witness: MdocPrivateMsoValidityWitness,
        range_handle: SharedRangeRelation,
        validity_handle: SharedMdocMsoValidityBytesRelation,
    ) -> Result<(Self, RcUses), MdocPrivateMsoValidityError> {
        let rows = build_rows(spec, &witness)?;
        let uses = range_uses(&rows);
        Ok((
            Self {
                spec,
                rows: Some(rows),
                range_handle,
                validity_handle,
                blinder_relation: None,
                interaction_claim: None,
                component: None,
                blinder_component: None,
            },
            uses,
        ))
    }

    pub(crate) fn verifier(
        spec: MdocPrivateMsoValiditySpec,
        range_handle: SharedRangeRelation,
        validity_handle: SharedMdocMsoValidityBytesRelation,
        interaction_claim: MdocPrivateMsoValidityInteractionClaim,
    ) -> Result<Self, MdocPrivateMsoValidityError> {
        validate_spec(spec)?;
        Ok(Self {
            spec,
            rows: None,
            range_handle,
            validity_handle,
            blinder_relation: None,
            interaction_claim: Some(interaction_claim),
            component: None,
            blinder_component: None,
        })
    }

    pub(crate) fn interaction_claim(&self) -> &MdocPrivateMsoValidityInteractionClaim {
        self.interaction_claim
            .as_ref()
            .expect("private MSO validity interaction claim is set")
    }

    fn interaction_columns(&self) -> usize {
        // 50 main sites pair into 25 QM31 columns, plus one QM31 blinder
        // counterpart component.
        (50usize.div_ceil(2) + 1) * SECURE_EXTENSION_DEGREE
    }
}

impl Air for MdocPrivateMsoValidityV2 {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        channel.mix_u64(VALIDITY_DOMAIN);
        channel.mix_u64(VALIDITY_VERSION);
        channel.mix_u64(self.spec.timestamp_epoch_seconds as u64);
        channel.mix_u64(PREPROCESSED_COLS as u64);
        channel.mix_u64(TRACE_COLS as u64);
        channel.mix_u64(self.interaction_columns() as u64);
    }

    fn draw_relations(&mut self, channel: &mut Blake2sChannel) {
        self.blinder_relation = Some(ClaimedSumBlinderRelation::draw(channel));
    }

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: vec![MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE; PREPROCESSED_COLS],
            trace: vec![MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE; TRACE_COLS],
            interaction: vec![MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE; self.interaction_columns()],
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        let claim = self.interaction_claim();
        vec![claim.claimed_sum, claim.blinder_claimed_sum]
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids()
    }

    fn canonical_preprocessed_columns(
        &mut self,
    ) -> Result<Vec<air_core::PreprocessedColumnEval>, stwo::core::verifier::VerificationError>
    {
        Ok(preprocessed_columns())
    }

    fn build_components(&mut self, allocator: &mut TraceLocationAllocator) {
        let claim = self.interaction_claim().clone();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private MSO validity blinder relation drawn before components");
        self.component = Some(ValidityComponent::new(
            allocator,
            MdocPrivateMsoValidityEval {
                timestamp: validate_spec(self.spec)
                    .expect("private MSO validity spec validated at construction"),
                validity_relation: self.validity_handle.get(),
                range_relation: self.range_handle.get(),
                blinder_relation: blinder_relation.clone(),
                blinder_v: claim.blinder_v,
                blinder_m: claim.blinder_m,
            },
            claim.claimed_sum,
        ));
        self.blinder_component = Some(FrameworkComponent::new(
            allocator,
            ClaimedSumBlinderEval {
                log_size: MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE,
                relation: blinder_relation,
                v: claim.blinder_v,
                m: claim.blinder_m,
            },
            claim.blinder_claimed_sum,
        ));
    }

    fn components(&self) -> Vec<&dyn Component> {
        vec![
            self.component
                .as_ref()
                .expect("private MSO validity component is built"),
            self.blinder_component
                .as_ref()
                .expect("private MSO validity blinder component is built"),
        ]
    }
}

impl AirProver for MdocPrivateMsoValidityV2 {
    fn max_log_size(&self) -> u32 {
        MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE + 2
    }

    fn write_preprocessed(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        self.write_selected_preprocessed(tb, &preprocessed_column_ids());
    }

    fn preprocessed_column_fingerprints(&mut self) -> Vec<PreprocessedColumnFingerprint> {
        fingerprint_preprocessed_columns(
            "eu_id_prover::mdoc_private_mso_validity::MdocPrivateMsoValidityV2",
            &preprocessed_column_ids(),
            &preprocessed_columns(),
        )
    }

    fn write_selected_preprocessed(
        &mut self,
        tb: &mut TreeBuilder<SimdBackend, air_core::Mc>,
        selected_ids: &[PreProcessedColumnId],
    ) {
        let all_ids = preprocessed_column_ids();
        let all_columns = preprocessed_columns();
        let selected = selected_ids
            .iter()
            .map(|id| {
                all_ids
                    .iter()
                    .position(|candidate| candidate == id)
                    .map(|index| all_columns[index].clone())
                    .expect("unexpected private MSO validity preprocessed selection")
            })
            .collect();
        tb.extend_evals(selected);
    }

    fn write_trace(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        tb.extend_evals(base_trace(
            self.rows
                .as_ref()
                .expect("private MSO validity prover rows are present"),
        ));
    }

    fn write_interaction(&mut self, tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {
        let blinder_v = random_qm31();
        let blinder_m = random_qm31();
        let blinder_relation = self
            .blinder_relation
            .clone()
            .expect("private MSO validity blinder relation drawn before interaction");
        let rows = self
            .rows
            .as_ref()
            .expect("private MSO validity prover rows are present");
        let (trace, claimed_sum) = interaction_trace(
            rows,
            &self.validity_handle.get(),
            &self.range_handle.get(),
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(trace);
        let (blinder_trace, blinder_claimed_sum) = blinder_counter_interaction(
            MDOC_PRIVATE_MSO_VALIDITY_LOG_SIZE,
            &blinder_relation,
            blinder_v,
            blinder_m,
        );
        tb.extend_evals(blinder_trace);
        self.interaction_claim = Some(MdocPrivateMsoValidityInteractionClaim {
            claimed_sum,
            blinder_v,
            blinder_m,
            blinder_claimed_sum,
        });
    }

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            self.component
                .as_ref()
                .expect("private MSO validity component is built"),
            self.blinder_component
                .as_ref()
                .expect("private MSO validity blinder component is built"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    use stwo_constraint_framework::{Multiplicity, ORIGINAL_TRACE_IDX, PREPROCESSED_TRACE_IDX};

    fn tdate(value: &str) -> [u8; MDOC_TDATE_BYTES] {
        value
            .as_bytes()
            .try_into()
            .expect("test tdate has exactly 20 bytes")
    }

    fn spec(timestamp_epoch_seconds: i64) -> MdocPrivateMsoValiditySpec {
        MdocPrivateMsoValiditySpec {
            timestamp_epoch_seconds,
        }
    }

    fn witness(from: &str, until: &str) -> MdocPrivateMsoValidityWitness {
        MdocPrivateMsoValidityWitness {
            valid_from: tdate(from),
            valid_until: tdate(until),
        }
    }

    #[test]
    fn exact_unix_seconds_match_known_vectors() {
        let vectors = [
            ("2020-01-01T00:00:00Z", 1_577_836_800),
            ("2020-02-29T12:34:56Z", 1_582_979_696),
            ("2024-02-29T23:59:59Z", 1_709_251_199),
            ("2099-12-31T23:59:59Z", 4_102_444_799),
        ];
        for (encoded, expected) in vectors {
            let parsed = parse_tdate(tdate(encoded), "test").unwrap();
            assert_eq!(unix_seconds(parsed), expected, "{encoded}");
        }
    }

    #[test]
    fn strict_boundaries_and_one_second_inside_are_exact() {
        let from = "2024-02-29T12:00:00Z";
        let until = "2024-02-29T12:00:02Z";
        let center = i64::from(unix_seconds(
            parse_tdate(tdate("2024-02-29T12:00:01Z"), "center").unwrap(),
        ));
        let handles = || {
            (
                SharedRangeRelation::new(),
                SharedMdocMsoValidityBytesRelation::new(),
            )
        };
        let (range, validity) = handles();
        assert!(MdocPrivateMsoValidityV2::prover(
            spec(center),
            witness(from, until),
            range,
            validity,
        )
        .is_ok());
        let from_second = i64::from(unix_seconds(parse_tdate(tdate(from), "from").unwrap()));
        let until_second = i64::from(unix_seconds(parse_tdate(tdate(until), "until").unwrap()));
        let (range, validity) = handles();
        assert_eq!(
            MdocPrivateMsoValidityV2::prover(
                spec(from_second),
                witness(from, until),
                range,
                validity,
            )
            .err(),
            Some(MdocPrivateMsoValidityError::NotYetValid)
        );
        let (range, validity) = handles();
        assert_eq!(
            MdocPrivateMsoValidityV2::prover(
                spec(until_second),
                witness(from, until),
                range,
                validity,
            )
            .err(),
            Some(MdocPrivateMsoValidityError::Expired)
        );
    }

    #[test]
    fn malformed_and_non_gregorian_tdates_fail_closed() {
        for (value, expected) in [
            (
                "2019-12-31T23:59:59Z",
                MdocPrivateMsoValidityError::UnsupportedYear {
                    field: "test",
                    year: 2019,
                },
            ),
            (
                "2023-02-29T00:00:00Z",
                MdocPrivateMsoValidityError::InvalidGregorianDate {
                    field: "test",
                    year: 2023,
                    month: 2,
                    day: 29,
                },
            ),
            (
                "2024-04-31T00:00:00Z",
                MdocPrivateMsoValidityError::InvalidGregorianDate {
                    field: "test",
                    year: 2024,
                    month: 4,
                    day: 31,
                },
            ),
            (
                "2024-01-01T24:00:00Z",
                MdocPrivateMsoValidityError::InvalidTime {
                    field: "test",
                    hour: 24,
                    minute: 0,
                    second: 0,
                },
            ),
        ] {
            assert_eq!(parse_tdate(tdate(value), "test").unwrap_err(), expected);
        }
        assert_eq!(
            parse_tdate(tdate("2024-01-01 00:00:00Z"), "test").unwrap_err(),
            MdocPrivateMsoValidityError::MalformedTdate { field: "test" }
        );
    }

    #[test]
    fn all_supported_gregorian_dates_round_trip_monotonically() {
        let mut previous = None;
        for year in 2020..=2099 {
            for month in 1..=12 {
                let max_day = days_in_month(year, month).unwrap();
                for day in 1..=max_day {
                    let encoded = format!("{year:04}-{month:02}-{day:02}T00:00:00Z");
                    let parsed = parse_tdate(tdate(&encoded), "test").unwrap();
                    let seconds = unix_seconds(parsed);
                    if let Some(previous) = previous {
                        assert_eq!(seconds - previous, SECONDS_PER_DAY, "{encoded}");
                    }
                    previous = Some(seconds);
                }
            }
        }
    }

    #[derive(Default)]
    struct RowEval {
        preprocessed: VecDeque<Vec<M31>>,
        original: VecDeque<Vec<M31>>,
        constraints: Vec<QM31>,
    }

    impl RowEval {
        fn from_row(row: &ValidityRow, is_valid_until: bool) -> Self {
            Self {
                preprocessed: VecDeque::from([vec![m31(1)], vec![m31(u32::from(is_valid_until))]]),
                original: row.cells.iter().map(|value| vec![m31(*value)]).collect(),
                constraints: Vec::new(),
            }
        }

        fn nonzero_constraints(&self) -> Vec<(usize, QM31)> {
            self.constraints
                .iter()
                .copied()
                .enumerate()
                .filter(|(_, value)| *value != QM31::from_u32_unchecked(0, 0, 0, 0))
                .collect()
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
                ORIGINAL_TRACE_IDX => &mut self.original,
                _ => panic!("unexpected interaction {interaction}"),
            };
            let values = queue.pop_front().expect("row mask is present");
            assert_eq!(values.len(), N);
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

    fn test_eval(timestamp: u32) -> MdocPrivateMsoValidityEval {
        MdocPrivateMsoValidityEval {
            timestamp,
            validity_relation: MdocMsoValidityBytesRelation::dummy(),
            range_relation: RangeRelation::dummy(),
            blinder_relation: ClaimedSumBlinderRelation::dummy(),
            blinder_v: QM31::from_u32_unchecked(1, 2, 3, 4),
            blinder_m: QM31::from_u32_unchecked(5, 6, 7, 8),
        }
    }

    #[test]
    fn honest_rows_satisfy_every_air_constraint_and_mutations_do_not() {
        let timestamp =
            unix_seconds(parse_tdate(tdate("2024-03-01T00:00:00Z"), "timestamp").unwrap());
        let rows = build_rows(
            spec(i64::from(timestamp)),
            &witness("2024-02-29T23:59:59Z", "2024-03-01T00:00:01Z"),
        )
        .unwrap();
        for (index, row) in rows.iter().enumerate() {
            let evaluated = test_eval(timestamp).evaluate(RowEval::from_row(row, index == 1));
            assert!(
                evaluated.nonzero_constraints().is_empty(),
                "honest row {index}: {:?}",
                evaluated.nonzero_constraints()
            );
        }

        for column in [
            TRACE_BYTES,
            TRACE_DIGITS,
            TRACE_DIGIT_SLACKS,
            TRACE_MONTH_SELECTORS,
            TRACE_YEARS_SINCE_2020,
            TRACE_YEAR_UPPER_SLACK,
            TRACE_LEAP_QUOTIENT,
            TRACE_LEAP_REMAINDER_SELECTORS,
            TRACE_DAY_MINUS_ONE,
            TRACE_MONTH_DAY_SLACK,
            TRACE_MUL_LO_LO8,
            TRACE_MUL_HI_LO8,
            TRACE_SECONDS_LO_LO8,
            TRACE_SECONDS_HI_LO8,
            TRACE_CARRY_SELECTORS,
            TRACE_COMPARE_BORROW,
            TRACE_SLACK_LO_LO8,
            TRACE_SLACK_HI_LO8,
        ] {
            let mut attacked = rows[0].clone();
            attacked.cells[column] = attacked.cells[column].wrapping_add(1);
            let evaluated = test_eval(timestamp).evaluate(RowEval::from_row(&attacked, false));
            assert!(
                !evaluated.nonzero_constraints().is_empty(),
                "column {column} mutation escaped"
            );
        }
    }

    #[test]
    fn air_enforces_2020_through_2099_year_window() {
        for year in 2020..=2099 {
            let encoded = format!("{year:04}-01-01T00:00:00Z");
            let parsed = parse_tdate(tdate(&encoded), "test").unwrap();
            let timestamp = unix_seconds(parsed) + 1;
            let row = row_for(parsed, timestamp, false).unwrap();
            let evaluated = test_eval(timestamp).evaluate(RowEval::from_row(&row, false));
            assert!(
                evaluated.nonzero_constraints().is_empty(),
                "supported year {year}: {:?}",
                evaluated.nonzero_constraints()
            );
        }

        let bytes = tdate("2100-01-01T00:00:00Z");
        let mut digits = [0u32; DIGIT_COUNT];
        for (digit_index, byte_index) in DIGIT_POSITIONS.into_iter().enumerate() {
            digits[digit_index] = u32::from(bytes[byte_index] - b'0');
        }
        let forged = ParsedTdate {
            bytes,
            digits,
            year: 2100,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
        };
        let timestamp = unix_seconds(forged) - 1;
        let row = row_for(forged, timestamp, true).unwrap();
        let evaluated = test_eval(timestamp).evaluate(RowEval::from_row(&row, true));
        assert_eq!(
            evaluated.nonzero_constraints().len(),
            1,
            "forged 2100 row must fail only the supported-year AIR constraint: {:?}",
            evaluated.nonzero_constraints()
        );
    }

    #[test]
    fn range_census_is_exact_and_blind_rows_exceed_requirement() {
        let timestamp =
            unix_seconds(parse_tdate(tdate("2024-03-01T00:00:00Z"), "timestamp").unwrap());
        let rows = build_rows(
            spec(i64::from(timestamp)),
            &witness("2024-02-29T23:59:59Z", "2024-03-01T00:00:01Z"),
        )
        .unwrap();
        let uses = range_uses(&rows);
        assert_eq!(uses.rc7.iter().sum::<u32>(), 74);
        assert_eq!(uses.rc8.iter().sum::<u32>(), 22);
        assert_eq!(uses.rc9.iter().sum::<u32>(), 0);
        assert_eq!(uses.rc13.iter().sum::<u32>(), 0);
        assert_eq!(uses.ternary.iter().sum::<u32>(), 0);
        assert_eq!(MDOC_PRIVATE_MSO_VALIDITY_BLIND_ROWS, 510);
    }
}
