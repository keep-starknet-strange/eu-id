use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::Preprocessed;
use crate::nat::witness::WitnessData;
use crate::types::Trace;
use air_core::claim_mask::ClaimMaskTrace;
use air_core::relations::{field_id, FieldBytesRelation};
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

pub struct InteractionTraces {
    pub nat_interaction: Trace,
    pub table_interaction: Trace,
    pub nat_claimed_sum: QM31,
    pub table_claimed_sum: QM31,
}

impl InteractionTraces {
    pub fn new(
        witness_data: &WitnessData,
        preprocessed: &Preprocessed,
        lookup_elements: &LookupElements,
        nat_field: Option<&FieldBytesRelation>,
        claim_masks: Option<&[ClaimMaskTrace]>,
        claim_mask_beta: Option<QM31>,
    ) -> Self {
        assert_eq!(
            claim_masks.map(|masks| masks.len()),
            claim_mask_beta.map(|_| 2),
            "nationality claim masks and challenge must be enabled together"
        );
        let n_packed = 1 << (WitnessData::log_size() - LOG_N_LANES);

        let row_index = &preprocessed.prefix[1];
        let first = &preprocessed.prefix[2];
        let active = &witness_data.witness_trace[0];
        let last = &witness_data.witness_trace[1];
        let nationality = &witness_data.witness_trace[2];
        let accepted = &witness_data.witness_trace[3];
        let seen_before = &witness_data.witness_trace[4];
        let seen_after = &witness_data.witness_trace[5];
        let one_m31 = PackedM31::broadcast(M31::from_u32_unchecked(1));

        let mut nat_entries = Vec::new();
        append_entry(&mut nat_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row] * accepted.values.data[packed_row]),
                lookup_elements
                    .nat_table
                    .combine(&[nationality.values.data[packed_row]]),
            )
        });
        append_entry(&mut nat_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row]),
                lookup_elements
                    .signed_valid
                    .combine(&[nationality.values.data[packed_row]]),
            )
        });

        append_entry(&mut nat_entries, n_packed, |packed_row| {
            (
                PackedQM31::from(active.values.data[packed_row] - first.values.data[packed_row]),
                lookup_elements.prefix_transition.combine(&[
                    row_index.values.data[packed_row],
                    seen_before.values.data[packed_row],
                ]),
            )
        });
        append_entry(&mut nat_entries, n_packed, |packed_row| {
            (
                -PackedQM31::from(active.values.data[packed_row] - last.values.data[packed_row]),
                lookup_elements.prefix_transition.combine(&[
                    row_index.values.data[packed_row] + one_m31,
                    seen_after.values.data[packed_row],
                ]),
            )
        });

        if nat_field.is_some() {
            assert!(
                witness_data.nat_bytes.is_some(),
                "bound nationality witness must include byte columns"
            );
        }
        if let Some(field) = nat_field {
            let code_hi = &witness_data.witness_trace[6];
            let code_lo = &witness_data.witness_trace[7];
            let field_id = PackedM31::broadcast(M31::from_u32_unchecked(field_id::NATIONALITY));
            let two = PackedM31::broadcast(M31::from_u32_unchecked(2));
            for (byte_offset, value) in [(0u32, code_hi), (1, code_lo)] {
                let offset = PackedM31::broadcast(M31::from_u32_unchecked(byte_offset));
                append_entry(&mut nat_entries, n_packed, |packed_row| {
                    (
                        PackedQM31::from(active.values.data[packed_row]),
                        field.combine(&[
                            field_id,
                            row_index.values.data[packed_row] * two + offset,
                            value.values.data[packed_row],
                        ]),
                    )
                });
            }
        }
        if let (Some(masks), Some(beta)) = (claim_masks, claim_mask_beta) {
            append_entry(&mut nat_entries, n_packed, |packed_row| {
                masks[0].packed_fraction_at(packed_row, beta)
            });
        }

        let mut logup_gen = LogupTraceGenerator::new(WitnessData::log_size());
        write_paired_entries(&mut logup_gen, &nat_entries);
        let (nat_interaction, nat_claimed_sum) = logup_gen.finalize_last();

        // The accepted-policy and fixed signed-validity providers share a
        // component but use independent relations.
        let table_log_size = preprocessed.acceptable[0].domain.log_size();
        let one = PackedQM31::broadcast(QM31::from(1));
        let table_n_packed = 1 << (table_log_size - LOG_N_LANES);
        let mut table_entries = Vec::new();
        append_entry(&mut table_entries, table_n_packed, |vec_row| {
            let nat_val: PackedM31 = preprocessed.acceptable[0].values.data[vec_row];
            let dummy_val: PackedM31 = preprocessed.acceptable[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.table_mult_trace[0].values.data[vec_row];
            (
                -((one - PackedQM31::from(dummy_val)) * PackedQM31::from(mult_val)),
                lookup_elements.nat_table.combine(&[nat_val]),
            )
        });
        append_entry(&mut table_entries, table_n_packed, |vec_row| {
            let nat_val: PackedM31 = preprocessed.signed_valid[0].values.data[vec_row];
            let dummy_val: PackedM31 = preprocessed.signed_valid[1].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.table_mult_trace[1].values.data[vec_row];
            (
                -((one - PackedQM31::from(dummy_val)) * PackedQM31::from(mult_val)),
                lookup_elements.signed_valid.combine(&[nat_val]),
            )
        });
        if let (Some(masks), Some(beta)) = (claim_masks, claim_mask_beta) {
            append_entry(&mut table_entries, table_n_packed, |vec_row| {
                masks[1].packed_fraction_at(vec_row, beta)
            });
        }
        let mut logup_gen = LogupTraceGenerator::new(table_log_size);
        write_paired_entries(&mut logup_gen, &table_entries);
        let (table_interaction, table_claimed_sum) = logup_gen.finalize_last();

        Self {
            nat_interaction,
            table_interaction,
            nat_claimed_sum,
            table_claimed_sum,
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.nat_claimed_sum, self.table_claimed_sum]);
    }

    pub fn extend_evals(&self, tb: &mut TreeBuilder<SimdBackend, Blake2sMerkleChannel>) {
        tb.extend_evals(self.nat_interaction.clone());
        tb.extend_evals(self.table_interaction.clone());
    }
}
