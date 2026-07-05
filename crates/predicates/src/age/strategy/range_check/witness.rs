use crate::age::calendar::{max_days_at, valid_day_row_index};
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::types::Trace;
use crate::utils::push_repeated_column;
use crate::Witness;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

const LOG_SIZE: u32 = 5;
pub(crate) const DOB_TEXT_LEN: usize = 10;
pub(crate) const DOB_TEXT_DIGITS: usize = 8;
pub(crate) const DOB_TEXT_DIGIT_BITS: usize = 4;

/// How the credential DOB is exposed to the age module: packed 4-byte
/// `[year_hi, year_lo, month, day]` or a 10-byte `YYYY-MM-DD` text window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DobBindingMode {
    Packed,
    Text,
}

impl DobBindingMode {
    /// Extra witness trace columns the binding contributes (after the 9 base).
    pub fn trace_columns(self) -> usize {
        match self {
            Self::Packed => 3,
            Self::Text => 1 + DOB_TEXT_LEN + DOB_TEXT_DIGITS * DOB_TEXT_DIGIT_BITS,
        }
    }

    /// Exposed DOB byte requires the binding emits on the shared field channel.
    pub fn field_bytes(self) -> usize {
        match self {
            Self::Packed => 4,
            Self::Text => DOB_TEXT_LEN,
        }
    }
}

pub struct WitnessData {
    pub witness_trace: Trace,
    pub cal_mult_trace: Trace,
    pub valid_day_mult_trace: Trace,
    pub day_delta_mult_trace: Trace,
    pub month_delta_mult_trace: Trace,
    pub year_delta_mult_trace: Trace,
    // Lookup argument values reused when building the interaction traces.
    pub table_index: u32,
    pub dob_max_days: u32,
    pub dob_day: u32,
    pub day_delta_val: u32,
    pub month_delta_val: u32,
    pub year_delta_val: u32,
    /// Credential DOB byte values when the credential binding is wired (`Some`)
    /// — either four packed bytes `[year_hi, year_lo, month, day]` or ten text
    /// bytes `YYYY-MM-DD`. These are the require tuples the interaction trace
    /// emits against the shared `Sha256Field` channel. `None` for a standalone
    /// age proof, where [`witness_trace`](Self::witness_trace) holds only the
    /// nine base columns.
    pub dob_bytes: Option<Vec<u32>>,
}

/// Trace column index of the single-row binding selector `bind_active` (the
/// tenth column, after the nine base witness columns). Only present when the
/// DOB binding is wired; the interaction trace reads it as the require numerator.
pub const BIND_ACTIVE_COL: usize = 9;

impl WitnessData {
    pub fn new(
        witness: &Witness,
        preprocessed: &Preprocessed,
        dob_binding_mode: Option<DobBindingMode>,
    ) -> Self {
        let dob_max_days = max_days_at(witness.dob.month, witness.dob.year);
        let table_index = (witness.dob.year - witness.public.bounds.min_supported_year) * 12
            + witness.dob.month
            - 1;
        let valid_day_row = valid_day_row_index(dob_max_days, witness.dob.day);

        let day_borrow = u32::from(witness.cutoff.day < witness.dob.day);
        let day_delta_val = witness.cutoff.day + 32 * day_borrow - witness.dob.day;
        let month_borrow = u32::from(witness.cutoff.month < witness.dob.month + day_borrow);
        let month_delta_val =
            witness.cutoff.month + 16 * month_borrow - witness.dob.month - day_borrow;
        let year_delta_val =
            (witness.cutoff.year as i32 - witness.dob.year as i32 - month_borrow as i32) as u32;

        let cal_log_size = preprocessed.cal_trace[0].domain.log_size();
        let valid_day_log_size = preprocessed.valid_day_trace[0].domain.log_size();

        let mut cal_mult_data = vec![M31::zero(); 1 << cal_log_size];
        cal_mult_data[table_index as usize] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let cal_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(cal_log_size).circle_domain(),
            BaseColumn::from_iter(cal_mult_data),
        )];

        let mut valid_day_mult_data = vec![M31::zero(); 1 << valid_day_log_size];
        valid_day_mult_data[valid_day_row] = M31::from_u32_unchecked(1 << LOG_SIZE);
        let valid_day_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(valid_day_log_size).circle_domain(),
            BaseColumn::from_iter(valid_day_mult_data),
        )];

        let repeated = |val: u32| vec![M31::from_u32_unchecked(val); 1 << LOG_SIZE];
        let day_delta_mult_trace = vec![Preprocessed::day_range()
            .claim()
            .gen_multiplicity_col(&[repeated(day_delta_val)])];
        let month_delta_mult_trace = vec![Preprocessed::month_range()
            .claim()
            .gen_multiplicity_col(&[repeated(month_delta_val)])];
        let year_delta_mult_trace = vec![Preprocessed::year_range(&witness.public.bounds)
            .claim()
            .gen_multiplicity_col(&[repeated(year_delta_val)])];

        // Big-endian recomposition matches `Credential::encode` (`year` is the
        // u16 birth year): byte 0 is the high byte, byte 1 the low byte, then the
        // single month/day bytes — the same four bytes SHA yields for the DOB
        // window (`docs/credential-format.md`).
        let dob_bytes = dob_binding_mode.map(|mode| dob_field_bytes(witness, mode));

        Self {
            witness_trace: gen_trace(witness, dob_binding_mode),
            cal_mult_trace,
            valid_day_mult_trace,
            day_delta_mult_trace,
            month_delta_mult_trace,
            year_delta_mult_trace,
            table_index,
            dob_max_days,
            dob_day: witness.dob.day,
            day_delta_val,
            month_delta_val,
            year_delta_val,
            dob_bytes,
        }
    }

    pub fn log_size() -> u32 {
        LOG_SIZE
    }

    pub fn extend_evals(
        &self,
        witness_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
        witness_tree_builder.extend_evals(self.witness_trace.clone());
        witness_tree_builder.extend_evals(self.cal_mult_trace.clone());
        witness_tree_builder.extend_evals(self.valid_day_mult_trace.clone());
        witness_tree_builder.extend_evals(self.day_delta_mult_trace.clone());
        witness_tree_builder.extend_evals(self.month_delta_mult_trace.clone());
        witness_tree_builder.extend_evals(self.year_delta_mult_trace.clone());
    }
}

fn gen_trace(witness: &Witness, dob_binding_mode: Option<DobBindingMode>) -> Trace {
    let mut cols = Vec::with_capacity(
        9 + dob_binding_mode
            .map(DobBindingMode::trace_columns)
            .unwrap_or(0),
    );
    push_repeated_column(&mut cols, witness.dob.day, LOG_SIZE);
    push_repeated_column(&mut cols, witness.dob.month, LOG_SIZE);
    push_repeated_column(&mut cols, witness.dob.year, LOG_SIZE);
    push_repeated_column(
        &mut cols,
        max_days_at(witness.dob.month, witness.dob.year),
        LOG_SIZE,
    );

    let day_borrow = u32::from(witness.cutoff.day < witness.dob.day);
    let day_delta = witness.cutoff.day + 32 * day_borrow - witness.dob.day;

    let month_borrow = u32::from(witness.cutoff.month < witness.dob.month + day_borrow);
    let month_delta = witness.cutoff.month + 16 * month_borrow - witness.dob.month - day_borrow;

    let year_delta = witness.cutoff.year as i32 - witness.dob.year as i32 - month_borrow as i32;

    push_repeated_column(&mut cols, day_delta, LOG_SIZE);
    push_repeated_column(&mut cols, month_delta, LOG_SIZE);
    push_repeated_column(&mut cols, year_delta as u32, LOG_SIZE);
    push_repeated_column(&mut cols, day_borrow, LOG_SIZE);
    push_repeated_column(&mut cols, month_borrow, LOG_SIZE);

    // The credential-field binding columns (slots 9..12). `bind_active` selects
    // the single row whose DOB-byte requires fire; `year_hi`/`year_lo` are the
    // big-endian birth-year bytes the reconciliation constraint ties to the
    // packed `birth_year`. Repeated so the always-on reconciliation holds on
    // every row; the global LogUp balance forces the selected row's bytes to the
    // credential's signed bytes.
    if let Some(mode) = dob_binding_mode {
        push_single_active(&mut cols, LOG_SIZE);
        match mode {
            DobBindingMode::Packed => {
                push_repeated_column(&mut cols, witness.dob.year >> 8, LOG_SIZE);
                push_repeated_column(&mut cols, witness.dob.year & 0xFF, LOG_SIZE);
            }
            DobBindingMode::Text => {
                let text = dob_text_bytes(witness);
                for &byte in &text {
                    push_repeated_column(&mut cols, u32::from(byte), LOG_SIZE);
                }
                // Per-digit 4-bit decomposition: the eval reconstructs each ASCII
                // digit from these bits and caps it at 9, replacing a dedicated
                // range table for the 4-bit check.
                for (i, &byte) in text_digit_bytes(&text).iter().enumerate() {
                    let digit = byte - b'0';
                    debug_assert!(digit <= 9, "generated DOB digit {i} must be decimal");
                    for bit in 0..DOB_TEXT_DIGIT_BITS {
                        push_repeated_column(&mut cols, u32::from((digit >> bit) & 1), LOG_SIZE);
                    }
                }
            }
        }
    }

    cols
}

/// The exposed DOB bytes for `mode`: packed big-endian `[year_hi, year_lo,
/// month, day]` or the ten `YYYY-MM-DD` text bytes.
pub fn dob_field_bytes(witness: &Witness, mode: DobBindingMode) -> Vec<u32> {
    match mode {
        DobBindingMode::Packed => vec![
            witness.dob.year >> 8,
            witness.dob.year & 0xFF,
            witness.dob.month,
            witness.dob.day,
        ],
        DobBindingMode::Text => dob_text_bytes(witness).into_iter().map(u32::from).collect(),
    }
}

fn dob_text_bytes(witness: &Witness) -> [u8; DOB_TEXT_LEN] {
    format!(
        "{:04}-{:02}-{:02}",
        witness.dob.year, witness.dob.month, witness.dob.day
    )
    .as_bytes()
    .try_into()
    .expect("formatted DOB text has YYYY-MM-DD length")
}

/// The eight digit bytes of a `YYYY-MM-DD` window, skipping the two `-`
/// separators at positions 4 and 7.
fn text_digit_bytes(text: &[u8; DOB_TEXT_LEN]) -> [u8; DOB_TEXT_DIGITS] {
    [
        text[0], text[1], text[2], text[3], text[5], text[6], text[8], text[9],
    ]
}

/// A column that is `1` on exactly one row and `0` on the rest — the
/// credential-field binding single-row require selector. Any single fixed row
/// works: the age witness repeats its columns across all rows, and the boolean
/// constraint plus the cross-module balance force this column to fire once with
/// the credential's bytes.
fn push_single_active(
    columns: &mut Vec<CircleEvaluation<SimdBackend, M31, stwo::prover::poly::BitReversedOrder>>,
    log_size: u32,
) {
    let domain = CanonicCoset::new(log_size).circle_domain();
    let mut data = vec![M31::zero(); 1 << log_size];
    data[0] = M31::from_u32_unchecked(1);
    columns.push(CircleEvaluation::new(domain, BaseColumn::from_iter(data)));
}
