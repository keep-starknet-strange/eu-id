use crate::age::strategy::range_check::lookup_elements::LookupElements;
use crate::age::strategy::range_check::preprocessed::Preprocessed;
use crate::age::strategy::range_check::witness::WitnessData;
use crate::types::Trace;
use air_core::claim_mask::ClaimMaskTrace;
use air_core::relations::{field_id, FieldBytesRelation};
use num_traits::One;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::TreeBuilder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};

type LogupEntry = (Vec<PackedQM31>, Vec<PackedQM31>);

fn append_entry(
    entries: &mut Vec<LogupEntry>,
    n_packed: usize,
    fraction: impl Fn(usize) -> (PackedQM31, PackedQM31),
) {
    let mut numerators = Vec::with_capacity(n_packed);
    let mut denominators = Vec::with_capacity(n_packed);
    for packed_row in 0..n_packed {
        let (numerator, denominator) = fraction(packed_row);
        numerators.push(numerator);
        denominators.push(denominator);
    }
    entries.push((numerators, denominators));
}

fn write_paired_entries(logup: &mut LogupTraceGenerator, entries: &[LogupEntry]) {
    for chunk in entries.chunks(2) {
        logup.col_from_fn(|packed_row| {
            let mut numerator = chunk[0].0[packed_row];
            let mut denominator = chunk[0].1[packed_row];
            if let Some((next_numerators, next_denominators)) = chunk.get(1) {
                let n = next_numerators[packed_row];
                let d = next_denominators[packed_row];
                numerator = numerator * d + n * denominator;
                denominator *= d;
            }
            (numerator, denominator)
        });
    }
}

/// Build a Class-D blinded delta-table interaction column mirroring
/// [`crate::range_check::BlindEval`]'s SINGLE gated entry: numerator
/// `-(1 − is_dummy)·mult` over one column (`finalize_logup`). `-mult` on real
/// rows and `0` on dummy rows regardless of the random `m` committed there — the
/// claimed sum is identical to the unblinded table's over the same real uses.
fn blind_delta_interaction(
    log_size: u32,
    value_col: &crate::types::Column,
    dummy_col: &crate::types::Column,
    mult_col: &crate::types::Column,
    relation: &crate::range_check::RangeCheckLookupElements,
    claim_mask: Option<&ClaimMaskTrace>,
    claim_mask_beta: Option<QM31>,
) -> (Trace, QM31) {
    let one = PackedQM31::broadcast(QM31::from(1));
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    logup_gen.col_from_fn(|vec_row| {
        let value: PackedM31 = value_col.values.data[vec_row];
        let dummy: PackedM31 = dummy_col.values.data[vec_row];
        let mult: PackedM31 = mult_col.values.data[vec_row];
        let denom: PackedQM31 = relation.combine(&[value]);
        let numerator = -((one - PackedQM31::from(dummy)) * PackedQM31::from(mult));
        (numerator, denom)
    });
    if let (Some(mask), Some(beta)) = (claim_mask, claim_mask_beta) {
        logup_gen.col_from_fn(|vec_row| mask.packed_fraction_at(vec_row, beta));
    }
    logup_gen.finalize_last()
}

pub struct InteractionTraces {
    pub age_interaction: Trace,
    pub cal_interaction: Trace,
    pub valid_day_interaction: Trace,
    pub day_delta_interaction: Trace,
    pub month_delta_interaction: Trace,
    pub year_delta_interaction: Trace,
    pub age_claimed_sum: QM31,
    pub cal_claimed_sum: QM31,
    pub valid_day_claimed_sum: QM31,
    pub day_delta_claimed_sum: QM31,
    pub month_delta_claimed_sum: QM31,
    pub year_delta_claimed_sum: QM31,
}

impl InteractionTraces {
    pub fn new(
        witness_data: &WitnessData,
        preprocessed: &Preprocessed,
        lookup_elements: &LookupElements,
        dob_field: Option<&FieldBytesRelation>,
        claim_masks: Option<&[ClaimMaskTrace]>,
        claim_mask_beta: Option<QM31>,
    ) -> Self {
        assert_eq!(
            claim_masks.map(|masks| masks.len()),
            claim_mask_beta.map(|_| 6),
            "age claim masks and challenge must be enabled together"
        );
        let cal_log_size = preprocessed.cal_trace[0].domain.log_size();
        let valid_day_log_size = preprocessed.valid_day_trace[0].domain.log_size();
        let n_packed = 1 << (WitnessData::log_size() - LOG_N_LANES);

        // Class-C: the age-component lookup uses fire only on the active row.
        // Their numerator is the preprocessed `active` selector (1 on row 0, 0 on
        // the blind rows), matching `E::EF::from(active)` in the eval.
        let active = &preprocessed.active_trace[0];

        // Age component: 5 logical logup fractions (calendar, valid-day,
        // day_delta, month_delta, year_delta), plus optional DOB-byte binding
        // requires. The AIR uses `finalize_logup_in_pairs`, so write the same
        // ordered entry stream in consecutive pairs.
        let mut age_entries = Vec::new();
        append_entry(&mut age_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row]),
                lookup_elements.calendar.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.table_index)),
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_max_days)),
                ]),
            )
        });
        append_entry(&mut age_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row]),
                lookup_elements.valid_day.combine(&[
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_max_days)),
                    PackedM31::broadcast(M31::from_u32_unchecked(witness_data.dob_day)),
                ]),
            )
        });
        append_entry(&mut age_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row]),
                lookup_elements.day_delta.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.day_delta_val),
                )]),
            )
        });
        append_entry(&mut age_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row]),
                lookup_elements.month_delta.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.month_delta_val),
                )]),
            )
        });
        append_entry(&mut age_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row]),
                lookup_elements.year_delta.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.year_delta_val),
                )]),
            )
        });

        // The credential-field binding: require the packed DOB bytes or the ten
        // text DOB bytes on the shared `Sha256Field` channel, one solo column per
        // byte. The numerator is the preprocessed `active` selector (1 on a single
        // row), so each byte is required exactly once — matching SHA's single
        // `−is_first_block` yield. Appended after the statement's own five
        // fractions so those columns are unchanged; the eval emits the same order
        // before paired finalization.
        if let (Some(field), Some(bytes)) = (dob_field, witness_data.dob_bytes.as_ref()) {
            for (byte_index, &value) in bytes.iter().enumerate() {
                append_entry(&mut age_entries, n_packed, |packed_row| {
                    (
                        PackedQM31::from(active.values.data[packed_row]),
                        field.combine(&[
                            PackedM31::broadcast(M31::from_u32_unchecked(field_id::DOB)),
                            PackedM31::broadcast(M31::from_u32_unchecked(byte_index as u32)),
                            PackedM31::broadcast(M31::from_u32_unchecked(value)),
                        ]),
                    )
                });
            }
        }
        if let (Some(masks), Some(beta)) = (claim_masks, claim_mask_beta) {
            append_entry(&mut age_entries, n_packed, |packed_row| {
                masks[0].packed_fraction_at(packed_row, beta)
            });
        }

        let mut logup_gen = LogupTraceGenerator::new(WitnessData::log_size());
        write_paired_entries(&mut logup_gen, &age_entries);
        let (age_interaction, age_claimed_sum) = logup_gen.finalize_last();

        // Calendar table (single-fraction `-mult`, not blinded).
        let mut logup_gen = LogupTraceGenerator::new(cal_log_size);
        logup_gen.col_from_fn(|vec_row| {
            let max_days_val: PackedM31 = preprocessed.cal_trace[0].values.data[vec_row];
            let index_val: PackedM31 = preprocessed.cal_trace[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.cal_mult_trace[0].values.data[vec_row];
            (
                PackedQM31::from(-mult_val),
                lookup_elements.calendar.combine(&[index_val, max_days_val]),
            )
        });
        if let (Some(masks), Some(beta)) = (claim_masks, claim_mask_beta) {
            logup_gen.col_from_fn(|vec_row| masks[1].packed_fraction_at(vec_row, beta));
        }
        let (cal_interaction, cal_claimed_sum) = logup_gen.finalize_last();

        // Valid-day table: real rows emit `-mult`; reserved dummy rows are
        // gated out while their multiplicities remain fresh committed blinds.
        let mut logup_gen = LogupTraceGenerator::new(valid_day_log_size);
        logup_gen.col_from_fn(|vec_row| {
            let max_days_val: PackedM31 = preprocessed.valid_day_trace[0].values.data[vec_row];
            let day_val: PackedM31 = preprocessed.valid_day_trace[1].values.data[vec_row];
            let dummy_val: PackedM31 = preprocessed.valid_day_trace[2].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.valid_day_mult_trace[0].values.data[vec_row];
            (
                -((PackedQM31::one() - PackedQM31::from(dummy_val)) * PackedQM31::from(mult_val)),
                lookup_elements.valid_day.combine(&[max_days_val, day_val]),
            )
        });
        if let (Some(masks), Some(beta)) = (claim_masks, claim_mask_beta) {
            logup_gen.col_from_fn(|vec_row| masks[2].packed_fraction_at(vec_row, beta));
        }
        let (valid_day_interaction, valid_day_claimed_sum) = logup_gen.finalize_last();

        // Class-D blinded delta tables: one gated fraction per row,
        // `-(1-is_dummy)·mult`. The padded domain size is read straight off the
        // committed value column.
        let (day_delta_interaction, day_delta_claimed_sum) = blind_delta_interaction(
            preprocessed.day_delta_table[0].domain.log_size(),
            &preprocessed.day_delta_table[0],
            &preprocessed.day_delta_table[1],
            &witness_data.day_delta_mult_trace[0],
            &lookup_elements.day_delta,
            claim_masks.map(|masks| &masks[3]),
            claim_mask_beta,
        );
        let (month_delta_interaction, month_delta_claimed_sum) = blind_delta_interaction(
            preprocessed.month_delta_table[0].domain.log_size(),
            &preprocessed.month_delta_table[0],
            &preprocessed.month_delta_table[1],
            &witness_data.month_delta_mult_trace[0],
            &lookup_elements.month_delta,
            claim_masks.map(|masks| &masks[4]),
            claim_mask_beta,
        );
        let (year_delta_interaction, year_delta_claimed_sum) = blind_delta_interaction(
            preprocessed.year_delta_table[0].domain.log_size(),
            &preprocessed.year_delta_table[0],
            &preprocessed.year_delta_table[1],
            &witness_data.year_delta_mult_trace[0],
            &lookup_elements.year_delta,
            claim_masks.map(|masks| &masks[5]),
            claim_mask_beta,
        );

        Self {
            age_interaction,
            cal_interaction,
            valid_day_interaction,
            day_delta_interaction,
            month_delta_interaction,
            year_delta_interaction,
            age_claimed_sum,
            cal_claimed_sum,
            valid_day_claimed_sum,
            day_delta_claimed_sum,
            month_delta_claimed_sum,
            year_delta_claimed_sum,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[
            self.age_claimed_sum,
            self.cal_claimed_sum,
            self.valid_day_claimed_sum,
            self.day_delta_claimed_sum,
            self.month_delta_claimed_sum,
            self.year_delta_claimed_sum,
        ]);
    }

    pub fn extend_evals(
        &self,
        interaction_tree_builder: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>,
    ) {
        interaction_tree_builder.extend_evals(self.age_interaction.clone());
        interaction_tree_builder.extend_evals(self.cal_interaction.clone());
        interaction_tree_builder.extend_evals(self.valid_day_interaction.clone());
        interaction_tree_builder.extend_evals(self.day_delta_interaction.clone());
        interaction_tree_builder.extend_evals(self.month_delta_interaction.clone());
        interaction_tree_builder.extend_evals(self.year_delta_interaction.clone());
    }
}
