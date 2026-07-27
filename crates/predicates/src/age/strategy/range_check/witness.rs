use crate::age::calendar::{max_days_at, valid_day_row_index, VALID_DAY_REAL_ROWS};
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::types::Trace;
use crate::utils::random_m31_cell;
use crate::Witness;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::TreeBuilder;

/// Class-C rewrite (Q-015 / p4c): the age component is a single-active-row
/// trace with a preprocessed selector. Row 0 (the active row) holds the real
/// witness; every constraint and lookup use in [`super::eval`] is gated by the
/// preprocessed `active` selector, so the remaining `2^LOG_SIZE − 1` rows are
/// free blind rows filled with fresh random field cells. `LOG_SIZE = 9` gives
/// `511 ≥ 256` blind rows (the Q-015 blind budget).
const LOG_SIZE: u32 = 9;
/// The single active (witness-bearing) row; every other row is a blind row.
const ACTIVE_ROW: usize = 0;
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
    /// The single-row require selector is now the preprocessed `active` column,
    /// so binding no longer contributes a `bind_active` trace column.
    pub fn trace_columns(self) -> usize {
        match self {
            Self::Packed => 2,
            Self::Text => DOB_TEXT_LEN + DOB_TEXT_DIGITS * DOB_TEXT_DIGIT_BITS,
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

        // The active row now uses each table exactly once, so table
        // multiplicities are 1 (not `1 << LOG_SIZE`).
        let mut cal_mult_data = vec![M31::zero(); 1 << cal_log_size];
        cal_mult_data[table_index as usize] = M31::from_u32_unchecked(1);
        let cal_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(cal_log_size).circle_domain(),
            BaseColumn::from_iter(cal_mult_data),
        )];

        let mut valid_day_mult_data = vec![M31::zero(); 1 << valid_day_log_size];
        valid_day_mult_data[valid_day_row] = M31::from_u32_unchecked(1);
        for value in valid_day_mult_data.iter_mut().skip(VALID_DAY_REAL_ROWS) {
            *value = random_m31_cell();
        }
        let valid_day_mult_trace = vec![CircleEvaluation::new(
            CanonicCoset::new(valid_day_log_size).circle_domain(),
            BaseColumn::from_iter(valid_day_mult_data),
        )];

        // Class-D blinded multiplicity columns for the three delta range tables:
        // real count (1) on the value row, fresh random on the reserved dummy
        // reserved dummy suffix.
        let single = |val: u32| vec![M31::from_u32_unchecked(val)];
        let day_delta_mult_trace = vec![Preprocessed::day_range()
            .claim()
            .gen_blind_multiplicity_col(&[single(day_delta_val)])];
        let month_delta_mult_trace = vec![Preprocessed::month_range()
            .claim()
            .gen_blind_multiplicity_col(&[single(month_delta_val)])];
        let year_delta_mult_trace = vec![Preprocessed::year_range(&witness.public.bounds)
            .claim()
            .gen_blind_multiplicity_col(&[single(year_delta_val)])];

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

/// The base witness column values for the active row, in eval-read order. Blind
/// rows overwrite these with fresh randomness; the active row keeps them.
fn base_active_values(witness: &Witness) -> Vec<u32> {
    let day_borrow = u32::from(witness.cutoff.day < witness.dob.day);
    let day_delta = witness.cutoff.day + 32 * day_borrow - witness.dob.day;
    let month_borrow = u32::from(witness.cutoff.month < witness.dob.month + day_borrow);
    let month_delta = witness.cutoff.month + 16 * month_borrow - witness.dob.month - day_borrow;
    let year_delta = witness.cutoff.year as i32 - witness.dob.year as i32 - month_borrow as i32;

    vec![
        witness.dob.day,
        witness.dob.month,
        witness.dob.year,
        max_days_at(witness.dob.month, witness.dob.year),
        day_delta,
        month_delta,
        year_delta as u32,
        day_borrow,
        month_borrow,
    ]
}

fn gen_trace(witness: &Witness, dob_binding_mode: Option<DobBindingMode>) -> Trace {
    let mut active_values = base_active_values(witness);

    // The credential-field binding columns (after the 9 base). `year_hi`/
    // `year_lo` are the big-endian birth-year bytes the reconciliation
    // constraint ties to the packed `birth_year`; text mode exposes the ten
    // ASCII bytes plus the per-digit 4-bit decomposition. The single-row require
    // selector is the preprocessed `active` column, so no `bind_active` trace
    // column is needed. On the active row the always-on-when-active
    // reconciliation holds; the global LogUp balance forces the active row's
    // bytes to the credential's signed bytes.
    if let Some(mode) = dob_binding_mode {
        match mode {
            DobBindingMode::Packed => {
                active_values.push(witness.dob.year >> 8);
                active_values.push(witness.dob.year & 0xFF);
            }
            DobBindingMode::Text => {
                let text = dob_text_bytes(witness);
                for &byte in &text {
                    active_values.push(u32::from(byte));
                }
                // Per-digit 4-bit decomposition: the eval reconstructs each
                // ASCII digit from these bits and caps it at 9, replacing a
                // dedicated range table for the 4-bit check.
                for (i, &byte) in text_digit_bytes(&text).iter().enumerate() {
                    let digit = byte - b'0';
                    debug_assert!(digit <= 9, "generated DOB digit {i} must be decimal");
                    for bit in 0..DOB_TEXT_DIGIT_BITS {
                        active_values.push(u32::from((digit >> bit) & 1));
                    }
                }
            }
        }
    }

    active_values.into_iter().map(active_column).collect()
}

/// A column that holds `active_value` on [`ACTIVE_ROW`] and a fresh uniform
/// random field cell on every other row. The random inactive cells are the
/// Class-C blind rows: the eval gates every witness-touching constraint off the
/// preprocessed `active` selector, so those rows are unconstrained and mask the
/// column's proof-side openings.
fn active_column(
    active_value: u32,
) -> CircleEvaluation<SimdBackend, M31, stwo::prover::poly::BitReversedOrder> {
    let domain = CanonicCoset::new(LOG_SIZE).circle_domain();
    let mut data: Vec<M31> = (0..1usize << LOG_SIZE).map(|_| random_m31_cell()).collect();
    data[ACTIVE_ROW] = M31::from_u32_unchecked(active_value);
    CircleEvaluation::new(domain, BaseColumn::from_iter(data))
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

#[cfg(test)]
mod class_c_tests {
    use super::*;
    use crate::age::types::{Date, PublicInput};
    use air_core::claim_mask::CLAIM_MASK_MIN_LOG_SIZE;
    use stwo::prover::backend::simd::m31::N_LANES;
    use stwo::prover::backend::Column as _;

    fn test_witness() -> Witness {
        let public = PublicInput::new(
            Date {
                year: 2026,
                month: 5,
                day: 19,
            },
            18,
        );
        let dob = Date {
            year: 2000,
            month: 3,
            day: 15,
        };
        Witness {
            public,
            dob,
            cutoff: public.cutoff_date(),
            age_slack: 0,
        }
    }

    fn trace_fingerprint(trace: &Trace) -> Vec<[M31; N_LANES]> {
        trace
            .iter()
            .flat_map(|column| column.values.data.iter().map(|packed| packed.to_array()))
            .collect()
    }

    /// Class-C: `LOG_SIZE = 9` leaves `511 ≥ 256` blind rows past the single
    /// active row (the Q-015 blind budget).
    #[test]
    fn age_class_c_has_at_least_256_blind_rows() {
        let blind_rows = (1usize << WitnessData::log_size()) - 1;
        assert!(
            blind_rows >= 256,
            "age Class-C needs ≥256 blind rows, got {blind_rows}"
        );
    }

    /// Class-C: the inactive (blind) rows carry fresh randomness — non-zero and
    /// different across two witness generations of the same witness.
    #[test]
    fn age_class_c_inactive_cells_are_fresh_per_trace() {
        let witness = test_witness();
        let preprocessed = Preprocessed::new(&witness.public.bounds);
        let first =
            trace_fingerprint(&WitnessData::new(&witness, &preprocessed, None).witness_trace);
        let second =
            trace_fingerprint(&WitnessData::new(&witness, &preprocessed, None).witness_trace);
        let zero = [M31::from_u32_unchecked(0); N_LANES];

        assert!(
            first.iter().any(|value| *value != zero),
            "age blind rows are still all zero"
        );
        assert_ne!(
            first, second,
            "age inactive cells must be fresh per trace (differ across two generations)"
        );
    }

    #[test]
    fn valid_day_dummy_multiplicities_are_fresh() {
        let witness = test_witness();
        let preprocessed = Preprocessed::new(&witness.public.bounds);
        let first = WitnessData::new(&witness, &preprocessed, None);
        let second = WitnessData::new(&witness, &preprocessed, None);
        let dummy_range = VALID_DAY_REAL_ROWS..1 << CLAIM_MASK_MIN_LOG_SIZE;
        let first_dummy: Vec<u32> = dummy_range
            .clone()
            .map(|row| first.valid_day_mult_trace[0].values.at(row).0)
            .collect();
        let second_dummy: Vec<u32> = dummy_range
            .map(|row| second.valid_day_mult_trace[0].values.at(row).0)
            .collect();
        assert_ne!(first_dummy, second_dummy);
    }
}
