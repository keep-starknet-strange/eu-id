use crate::nat::lookup_elements::LookupElements;
use crate::nat::preprocessed::Preprocessed;
use crate::nat::witness::{WitnessData, BIND_ACTIVE_COL};
use crate::types::Trace;
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
        let n_packed = chunk[0].0.len();
        let mut col_gen = logup.new_col();
        for packed_row in 0..n_packed {
            let mut numerator = chunk[0].0[packed_row];
            let mut denominator = chunk[0].1[packed_row];
            if let Some((next_numerators, next_denominators)) = chunk.get(1) {
                let n = next_numerators[packed_row];
                let d = next_denominators[packed_row];
                numerator = numerator * d + n * denominator;
                denominator *= d;
            }
            col_gen.write_frac(packed_row, numerator, denominator);
        }
        col_gen.finalize_col();
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
    ) -> Self {
        let acceptable_nat_log_size = preprocessed.acceptable[0].domain.log_size();
        let n_packed = 1 << (WitnessData::log_size() - LOG_N_LANES);

        let mut nat_entries = Vec::new();
        append_entry(&mut nat_entries, n_packed, |_| {
            (
                PackedQM31::one(),
                lookup_elements.nat_table.combine(&[PackedM31::broadcast(
                    M31::from_u32_unchecked(witness_data.nationality),
                )]),
            )
        });

        // The credential-field binding: require the two nationality bytes on the
        // shared `Sha256Field` channel, one solo column per byte. The numerator
        // is the `bind_active` selector (1 on a single row), so each byte is
        // required exactly once — matching SHA's single `−is_first_block` yield.
        // Appended after the membership fraction so that column is unchanged; the
        // eval emits the same order before `finalize_logup`.
        if let (Some(field), Some(bytes)) = (nat_field, witness_data.nat_bytes) {
            let bind_active = &witness_data.witness_trace[BIND_ACTIVE_COL];
            for (byte_index, &value) in bytes.iter().enumerate() {
                append_entry(&mut nat_entries, n_packed, |packed_row| {
                    (
                        PackedQM31::from(bind_active.values.data[packed_row]),
                        field.combine(&[
                            PackedM31::broadcast(M31::from_u32_unchecked(field_id::NATIONALITY)),
                            PackedM31::broadcast(M31::from_u32_unchecked(byte_index as u32)),
                            PackedM31::broadcast(M31::from_u32_unchecked(value)),
                        ]),
                    )
                });
            }
        }

        let mut logup_gen = LogupTraceGenerator::new(WitnessData::log_size());
        write_paired_entries(&mut logup_gen, &nat_entries);
        let (nat_interaction, nat_claimed_sum) = logup_gen.finalize_last();

        let mut logup_gen = LogupTraceGenerator::new(acceptable_nat_log_size);
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (acceptable_nat_log_size - LOG_N_LANES)) {
            let nat_val: PackedM31 = preprocessed.acceptable[0].values.data[vec_row];
            let mult_val: PackedM31 = witness_data.table_mult_trace[0].values.data[vec_row];
            col_gen.write_frac(
                vec_row,
                PackedQM31::from(-mult_val),
                lookup_elements.nat_table.combine(&[nat_val]),
            );
        }
        col_gen.finalize_col();
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
