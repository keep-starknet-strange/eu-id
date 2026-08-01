//! Canonical byte bridge for the final SHA-256 state.

use num_traits::One;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo_constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::components::digest_bridge_active_column_id_ns;
use crate::constants::{DIGEST_BYTES, N_STATE_WORDS};
use crate::constraints::LOGUP_BATCH;
use crate::relations::Sha256Relations;
use crate::trace::h_out_digest_bytes;
use crate::types::Sha256Witness;

/// The SIMD backend's minimum 16-row domain.
pub const DIGEST_BRIDGE_LOG_SIZE: u32 = 4;
pub const DIGEST_BRIDGE_BASE_COLS: usize = DIGEST_BYTES;
pub const DIGEST_BRIDGE_LOOKUPS_BASE: usize = DIGEST_BYTES + 1;

#[inline]
pub const fn digest_bridge_lookups(expose_digest: bool) -> usize {
    DIGEST_BRIDGE_LOOKUPS_BASE + expose_digest as usize
}

#[inline]
const fn limb_byte_indices(index: usize) -> (usize, usize) {
    let word_byte = 4 * (index / 2);
    if index.is_multiple_of(2) {
        (word_byte + 2, word_byte + 3)
    } else {
        (word_byte, word_byte + 1)
    }
}

/// One active row converts the final 16-bit state limbs to canonical bytes.
#[derive(Clone)]
pub struct DigestBridgeEval {
    pub relations: Sha256Relations,
    pub expose_digest: bool,
    pub instance_namespace: String,
}

impl FrameworkEval for DigestBridgeEval {
    fn log_size(&self) -> u32 {
        DIGEST_BRIDGE_LOG_SIZE
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        DIGEST_BRIDGE_LOG_SIZE + 2
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval
            .get_preprocessed_column(digest_bridge_active_column_id_ns(&self.instance_namespace));
        let bytes: [E::F; DIGEST_BYTES] = std::array::from_fn(|_| eval.next_trace_mask());

        for byte in &bytes {
            eval.add_constraint((E::F::one() - active.clone()) * byte.clone());
            eval.add_to_relation(RelationEntry::base(
                &self.relations.range.range_8,
                active.clone(),
                std::slice::from_ref(byte),
            ));
        }

        let radix = E::F::from(M31::from(1u32 << 8));
        let limbs: [E::F; 2 * N_STATE_WORDS] = std::array::from_fn(|index| {
            let (high_byte, low_byte) = limb_byte_indices(index);
            radix.clone() * bytes[high_byte].clone() + bytes[low_byte].clone()
        });
        eval.add_to_relation(RelationEntry::base(
            &self.relations.digest.limbs,
            active.clone(),
            &limbs,
        ));

        if self.expose_digest {
            eval.add_to_relation(RelationEntry::base(
                &self.relations.digest.digest,
                -active,
                &bytes,
            ));
        }

        eval.finalize_logup_batched(LOGUP_BATCH);
        eval
    }
}

pub(crate) fn generate_digest_bridge_trace(witness: &Sha256Witness) -> Vec<BaseColumn> {
    let digest = h_out_digest_bytes(
        &witness
            .blocks
            .last()
            .expect("SHA witness contains at least one block")
            .h_out,
    );
    digest
        .into_iter()
        .map(|byte| {
            let mut column = vec![BaseField::from(0u32); 1 << DIGEST_BRIDGE_LOG_SIZE];
            column[0] = BaseField::from(byte);
            column.into_iter().collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::compute_sha256_witness;
    use num_traits::Zero;
    use stwo::core::fields::qm31::{SecureField, SECURE_EXTENSION_DEGREE};
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
    use stwo_constraint_framework::{Relation, ORIGINAL_TRACE_IDX};

    struct ConstraintCollector<'a> {
        trace: &'a [Vec<BaseField>],
        row: usize,
        column: usize,
        rejected: bool,
    }

    impl EvalAtRow for ConstraintCollector<'_> {
        type F = BaseField;
        type EF = SecureField;

        fn next_interaction_mask<const N: usize>(
            &mut self,
            interaction: usize,
            offsets: [isize; N],
        ) -> [Self::F; N] {
            assert_eq!(interaction, ORIGINAL_TRACE_IDX);
            assert!(offsets.iter().all(|offset| *offset == 0));
            let value = self.trace[self.column][self.row];
            self.column += 1;
            [value; N]
        }

        fn get_preprocessed_column(&mut self, _column: PreProcessedColumnId) -> Self::F {
            BaseField::from(u32::from(self.row == 0))
        }

        fn add_constraint<G>(&mut self, constraint: G)
        where
            Self::EF: std::ops::Mul<G, Output = Self::EF> + From<G>,
        {
            self.rejected |= !SecureField::from(constraint).is_zero();
        }

        fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
            SecureField::from_m31_array(values)
        }

        fn add_to_relation<R: Relation<Self::F, Self::EF>>(
            &mut self,
            _entry: RelationEntry<'_, Self::F, Self::EF, R>,
        ) {
        }

        fn finalize_logup_batched(&mut self, _batch_size: usize) {}
    }

    #[test]
    fn bridge_trace_contains_only_the_final_digest() {
        let witness = compute_sha256_witness(&[0x5a; 200]);
        let expected = h_out_digest_bytes(&witness.blocks.last().unwrap().h_out);
        let trace = generate_digest_bridge_trace(&witness);
        assert_eq!(trace.len(), DIGEST_BYTES);
        for (index, column) in trace.iter().enumerate() {
            assert_eq!(column.at(0).0, expected[index]);
            for row in 1..(1usize << DIGEST_BRIDGE_LOG_SIZE) {
                assert_eq!(column.at(row).0, 0, "byte {index}, row {row}");
            }
        }
    }

    #[test]
    fn bridge_byte_order_reconstructs_low_then_high_limbs() {
        let witness = compute_sha256_witness(b"abc");
        let block = witness.blocks.last().unwrap();
        let bytes = h_out_digest_bytes(&block.h_out);

        for index in 0..2 * N_STATE_WORDS {
            let (high_byte, low_byte) = limb_byte_indices(index);
            let reconstructed = 256 * bytes[high_byte] + bytes[low_byte];
            let word = index / 2;
            let expected = if index.is_multiple_of(2) {
                block.h_out[word].lo
            } else {
                block.h_out[word].hi
            };
            assert_eq!(reconstructed, expected, "digest limb {index}");
        }
    }

    #[test]
    fn bridge_rejects_nonzero_inactive_byte() {
        let witness = compute_sha256_witness(b"abc");
        let mut trace: Vec<_> = generate_digest_bridge_trace(&witness)
            .into_iter()
            .map(BaseColumn::into_cpu_vec)
            .collect();
        trace[7][9] = BaseField::from(1u32);
        let component = DigestBridgeEval {
            relations: Sha256Relations::dummy(),
            expose_digest: false,
            instance_namespace: String::new(),
        };
        let collector = component.evaluate(ConstraintCollector {
            trace: &trace,
            row: 9,
            column: 0,
            rejected: false,
        });
        assert!(collector.rejected);
    }
}
