//! Prover-side trace + interaction generation for the digest-bind bridge.
//!
//! The base trace holds, per signature row, `(active, sig_id, z[20], bytes[32],
//! carries[31])` (see [`super`] `COL_*`). The interaction trace replays the
//! bridge's LogUp consumes — range8 bytes, range13 carries, the `(sig_id, z)`
//! binding, then the optional cross-module digest — in the **same order** the
//! eval emits them, paired into LogUp columns.

use num_traits::{One, Zero};
use rand::RngCore;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::{bit_reverse_index, coset_index_to_circle_domain_index};
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::{PackedM31, LOG_N_LANES};
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::poly::BitReversedOrder;
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_p256_utils::constants::N_LIMBS;

use air_core::relations::DigestBytesRelation;

use crate::field::limbs::P256M31BigInt;
use crate::range_checks::{write_batched_logup_columns, RangeCheckRelation};

use super::{
    z_digest_byte_witness, ScalarZRelation, COL_BYTES_START, COL_CARRIES_START, COL_SIG_ID,
    COL_Z_START, DIGEST_BYTES, N_CARRIES, SCALAR_Z_RELATION_ARITY, TOTAL_COLS,
};

/// One `(sig_id, z)` signature the bridge binds. `z` is the message hash in
/// limb form, exactly the value `scalar_setup` runs the ECDSA math over.
#[derive(Clone, Debug)]
pub struct DigestBindRow {
    pub sig_id: M31,
    pub z: P256M31BigInt,
}

pub type ColumnEval = CircleEvaluation<SimdBackend, M31, BitReversedOrder>;

fn coset_order_to_circle_domain_order(log_size: u32, values: Vec<M31>) -> Vec<M31> {
    let mut ordered = vec![M31::zero(); 1usize << log_size];
    for (coset_index, value) in values.into_iter().enumerate() {
        let row = bit_reverse_index(
            coset_index_to_circle_domain_index(coset_index, log_size),
            log_size,
        );
        ordered[row] = value;
    }
    ordered
}

fn column_eval(log_size: u32, coset_values: Vec<M31>) -> ColumnEval {
    let values = coset_order_to_circle_domain_order(log_size, coset_values);
    CircleEvaluation::new(
        CanonicCoset::new(log_size).circle_domain(),
        BaseColumn::from_iter(values),
    )
}

pub fn active_preprocessed_column(log_size: u32, active_rows: usize) -> ColumnEval {
    let n_rows = 1usize << log_size;
    assert!(
        active_rows <= n_rows,
        "{active_rows} active rows exceed 2^{log_size} trace rows",
    );
    let mut values = vec![M31::zero(); n_rows];
    for value in values.iter_mut().take(active_rows) {
        *value = M31::one();
    }
    column_eval(log_size, values)
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

/// Build the bridge's base trace: one active row per signature, padding rows
/// blinded. Columns are returned in committed order ([`TOTAL_COLS`] of them).
pub fn gen_base_trace(rows: &[DigestBindRow], log_size: u32) -> Vec<ColumnEval> {
    let n_rows = 1usize << log_size;
    assert!(
        rows.len() <= n_rows,
        "{} signatures exceed 2^{log_size} trace rows",
        rows.len(),
    );
    let mut cols = vec![vec![M31::zero(); n_rows]; TOTAL_COLS];
    for col in &mut cols {
        for value in col.iter_mut().skip(rows.len()) {
            *value = random_m31_cell();
        }
    }
    for (row, sig) in rows.iter().enumerate() {
        let (bytes, carries) = z_digest_byte_witness(&sig.z);
        cols[COL_SIG_ID][row] = sig.sig_id;
        for (i, limb) in sig.z.limbs().iter().enumerate() {
            cols[COL_Z_START + i][row] = *limb;
        }
        for (j, &b) in bytes.iter().enumerate() {
            cols[COL_BYTES_START + j][row] = M31::from_u32_unchecked(u32::from(b));
        }
        for (m, &c) in carries.iter().enumerate() {
            cols[COL_CARRIES_START + m][row] = M31::from_u32_unchecked(c);
        }
    }
    cols.into_iter()
        .map(|col| column_eval(log_size, col))
        .collect()
}

/// The byte / carry values the bridge looks up, for feeding the range-check
/// providers' multiplicity columns. `(bytes, carries)` flattened across all
/// active rows, each as a `0..2^k` table index.
pub fn range_uses(rows: &[DigestBindRow]) -> (Vec<M31>, Vec<M31>) {
    let mut byte_uses = Vec::with_capacity(rows.len() * DIGEST_BYTES);
    let mut carry_uses = Vec::with_capacity(rows.len() * N_CARRIES);
    for sig in rows {
        let (bytes, carries) = z_digest_byte_witness(&sig.z);
        byte_uses.extend(bytes.iter().map(|&b| M31::from_u32_unchecked(u32::from(b))));
        carry_uses.extend(carries.iter().map(|&c| M31::from_u32_unchecked(c)));
    }
    (byte_uses, carry_uses)
}

/// The relations the bridge consumes. `digest` is the shared cross-module
/// channel; the rest are P256-internal.
pub struct DigestBindRelations<'a> {
    pub range8: &'a RangeCheckRelation,
    pub range13: &'a RangeCheckRelation,
    pub scalar_z: &'a ScalarZRelation,
    pub digest: &'a DigestBytesRelation,
}

/// Build the bridge's LogUp interaction trace and its claimed sum. Lookups are
/// emitted in the canonical order (range8 bytes, range13 carries, `(sig_id, z)`,
/// then the optional digest), paired by consecutive entries to match the
/// eval's `finalize_logup_in_pairs`.
pub fn gen_interaction_trace(
    active: &ColumnEval,
    base: &[ColumnEval],
    relations: &DigestBindRelations<'_>,
    expose_digest: bool,
) -> (Vec<ColumnEval>, SecureField) {
    assert_eq!(base.len(), TOTAL_COLS);
    let log_size = active.domain.log_size();
    let n_vec_rows = 1usize << (log_size - LOG_N_LANES);
    assert_eq!(base[0].domain.log_size(), log_size);

    let numerators: Vec<PackedQM31> = (0..n_vec_rows)
        .map(|r| PackedQM31::from(active.data[r]))
        .collect();

    let mut entries: Vec<(Vec<PackedQM31>, Vec<PackedQM31>)> = Vec::new();

    // range8: each digest byte to [0, 256).
    for j in 0..DIGEST_BYTES {
        let col = &base[COL_BYTES_START + j];
        let denoms = (0..n_vec_rows)
            .map(|r| relations.range8.combine(&[col.data[r]]))
            .collect();
        entries.push((numerators.clone(), denoms));
    }
    // range13: each base-256 carry to [0, 2^13).
    for m in 0..N_CARRIES {
        let col = &base[COL_CARRIES_START + m];
        let denoms = (0..n_vec_rows)
            .map(|r| relations.range13.combine(&[col.data[r]]))
            .collect();
        entries.push((numerators.clone(), denoms));
    }
    // scalar_z: the (sig_id, z[20]) binding.
    {
        let denoms = (0..n_vec_rows)
            .map(|r| {
                let mut values = [PackedM31::broadcast(M31::zero()); SCALAR_Z_RELATION_ARITY];
                values[0] = base[COL_SIG_ID].data[r];
                for i in 0..N_LIMBS {
                    values[1 + i] = base[COL_Z_START + i].data[r];
                }
                relations.scalar_z.combine(&values)
            })
            .collect();
        entries.push((numerators.clone(), denoms));
    }
    // digest: the cross-module require of the 32 bytes (optional).
    if expose_digest {
        let denoms = (0..n_vec_rows)
            .map(|r| {
                let mut values = [PackedM31::broadcast(M31::zero()); DIGEST_BYTES];
                for j in 0..DIGEST_BYTES {
                    values[j] = base[COL_BYTES_START + j].data[r];
                }
                relations.digest.combine(&values)
            })
            .collect();
        entries.push((numerators.clone(), denoms));
    }

    let mut logup = LogupTraceGenerator::new(log_size);
    write_batched_logup_columns(&mut logup, &entries, 2);
    let (trace, claimed_sum) = logup.finalize_last();
    (trace, claimed_sum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::components::digest_bind::air::{active_col_id, DigestBindComponent, DigestBindEval};
    use crate::debug::MockCommitmentScheme;
    use crate::range_checks::RangeCheckInteractionClaim;
    use crate::range_checks::{ColumnEval as RcColumnEval, RangeCheckClaim};
    use crate::types::U256;
    use itertools::Itertools;
    use std::ops::Deref;
    use stwo::core::channel::Blake2sChannel;
    use stwo_constraint_framework::{
        assert_constraints_on_trace, FrameworkEval, Relation, TraceLocationAllocator,
        PREPROCESSED_TRACE_IDX,
    };

    const RANGE8_BITS: u32 = 8;
    const RANGE13_BITS: u32 = 13;

    fn sample_rows() -> Vec<DigestBindRow> {
        let z = P256M31BigInt::from_u256(&U256::from_le_u64s(&[
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0xA5A5_5A5A_F0F0_0F0F,
            0x0000_DEAD_BEEF_1234,
        ]));
        vec![DigestBindRow {
            sig_id: M31::from_u32_unchecked(1),
            z,
        }]
    }

    /// The whole bridge balances against synthetic providers for every channel
    /// it consumes — range8, range13, the `(sig_id, z)` binding, and the
    /// cross-module digest. The total over consumer + providers is exactly zero,
    /// which is what the global LogUp identity checks in a real proof.
    #[test]
    fn base_trace_inactive_rows_are_fresh_blind_cells() {
        let rows = sample_rows();
        let first = gen_base_trace(&rows, 9);
        let second = gen_base_trace(&rows, 9);

        let first_fingerprint = first
            .iter()
            .flat_map(|column| column.data.iter().map(|packed| packed.to_array()))
            .collect_vec();
        let second_fingerprint = second
            .iter()
            .flat_map(|column| column.data.iter().map(|packed| packed.to_array()))
            .collect_vec();

        assert_ne!(
            first_fingerprint, second_fingerprint,
            "digest bridge inactive trace cells must be fresh per trace"
        );
    }

    #[test]
    fn bridge_balances_against_all_providers() {
        let log_size = LOG_N_LANES; // 16 rows: 1 active signature + padding.
        let rows = sample_rows();

        // Draw all four channels from one transcript so consumer and providers
        // combine over identical LookupElements.
        let mut channel = Blake2sChannel::default();
        let range8 = RangeCheckRelation::draw(&mut channel);
        let range13 = RangeCheckRelation::draw(&mut channel);
        let scalar_z = ScalarZRelation::draw(&mut channel);
        let digest = DigestBytesRelation::draw(&mut channel);

        let active = active_preprocessed_column(log_size, rows.len());
        let base = gen_base_trace(&rows, log_size);
        let relations = DigestBindRelations {
            range8: &range8,
            range13: &range13,
            scalar_z: &scalar_z,
            digest: &digest,
        };
        let (_trace, consumer_sum) = gen_interaction_trace(&active, &base, &relations, true);
        assert_ne!(
            consumer_sum,
            SecureField::zero(),
            "an unbalanced consumer must have a non-zero claimed sum",
        );

        // Range-check providers: multiplicities = the bridge's uses.
        let (byte_uses, carry_uses) = range_uses(&rows);
        let range8_provider = provider_sum(RANGE8_BITS, byte_uses, &range8);
        let range13_provider = provider_sum(RANGE13_BITS, carry_uses, &range13);

        // Synthetic single-yield providers for the two cross-binding channels.
        let row = &rows[0];
        let mut scalar_z_values = vec![row.sig_id];
        scalar_z_values.extend(row.z.limbs().iter().copied());
        let scalar_z_provider = -SecureField::one()
            / <ScalarZRelation as Relation<M31, SecureField>>::combine(&scalar_z, &scalar_z_values);
        let (bytes, _carries) = z_digest_byte_witness(&row.z);
        let digest_values: Vec<M31> = bytes
            .iter()
            .map(|&b| M31::from_u32_unchecked(u32::from(b)))
            .collect();
        let digest_provider = -SecureField::one()
            / <DigestBytesRelation as Relation<M31, SecureField>>::combine(&digest, &digest_values);

        let total =
            consumer_sum + range8_provider + range13_provider + scalar_z_provider + digest_provider;
        assert_eq!(
            total,
            SecureField::zero(),
            "bridge consume must cancel against every provider",
        );
    }

    /// A consumer requiring a *different* digest (one bit flipped) cannot be
    /// balanced by the honest providers — the binding fails closed.
    #[test]
    fn mismatched_digest_does_not_balance() {
        let log_size = LOG_N_LANES;
        let rows = sample_rows();
        let mut channel = Blake2sChannel::default();
        let range8 = RangeCheckRelation::draw(&mut channel);
        let range13 = RangeCheckRelation::draw(&mut channel);
        let scalar_z = ScalarZRelation::draw(&mut channel);
        let digest = DigestBytesRelation::draw(&mut channel);

        let active = active_preprocessed_column(log_size, rows.len());
        let base = gen_base_trace(&rows, log_size);
        let relations = DigestBindRelations {
            range8: &range8,
            range13: &range13,
            scalar_z: &scalar_z,
            digest: &digest,
        };
        let (_trace, consumer_sum) = gen_interaction_trace(&active, &base, &relations, true);

        let (byte_uses, carry_uses) = range_uses(&rows);
        let range8_provider = provider_sum(RANGE8_BITS, byte_uses, &range8);
        let range13_provider = provider_sum(RANGE13_BITS, carry_uses, &range13);
        let row = &rows[0];
        let mut scalar_z_values = vec![row.sig_id];
        scalar_z_values.extend(row.z.limbs().iter().copied());
        let scalar_z_provider = -SecureField::one()
            / <ScalarZRelation as Relation<M31, SecureField>>::combine(&scalar_z, &scalar_z_values);
        // Provider yields a digest with one byte flipped — a different message.
        let (mut bytes, _carries) = z_digest_byte_witness(&row.z);
        bytes[0] ^= 1;
        let digest_values: Vec<M31> = bytes
            .iter()
            .map(|&b| M31::from_u32_unchecked(u32::from(b)))
            .collect();
        let digest_provider = -SecureField::one()
            / <DigestBytesRelation as Relation<M31, SecureField>>::combine(&digest, &digest_values);

        let total =
            consumer_sum + range8_provider + range13_provider + scalar_z_provider + digest_provider;
        assert_ne!(
            total,
            SecureField::zero(),
            "a mismatched digest must break the balance",
        );
    }

    /// The eval's constraints (boolean `active`, the 32 base-256 recomposition
    /// equations, and the LogUp interaction column) all hold on an honest
    /// trace, and the claimed sum matches the interaction trace. This pins the
    /// eval ⟷ witness agreement: the eval must read the 85 columns in exactly
    /// the order the trace generator writes them, and emit its lookups in the
    /// order the interaction generator pairs them.
    #[test]
    fn honest_trace_satisfies_constraints() {
        let log_size = LOG_N_LANES;
        let rows = sample_rows();
        let mut channel = Blake2sChannel::default();
        let range8 = RangeCheckRelation::draw(&mut channel);
        let range13 = RangeCheckRelation::draw(&mut channel);
        let scalar_z = ScalarZRelation::draw(&mut channel);
        let digest = DigestBytesRelation::draw(&mut channel);

        let active = active_preprocessed_column(log_size, rows.len());
        let base = gen_base_trace(&rows, log_size);
        let relations = DigestBindRelations {
            range8: &range8,
            range13: &range13,
            scalar_z: &scalar_z,
            digest: &digest,
        };
        let (interaction, claimed_sum) = gen_interaction_trace(&active, &base, &relations, true);

        // Build the three
        // commitment trees the constraint evaluator expects.
        let mut commitment_scheme = MockCommitmentScheme::default();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(vec![active]);
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(base);
        tree_builder.finalize_interaction();
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction);
        tree_builder.finalize_interaction();

        let mut allocator =
            TraceLocationAllocator::new_with_preprocessed_columns(&[active_col_id(
                log_size,
                rows.len(),
            )]);
        let component = DigestBindComponent::new(
            &mut allocator,
            DigestBindEval {
                log_size,
                active_rows: rows.len(),
                range8,
                range13,
                scalar_z,
                digest,
                expose_digest: true,
            },
            claimed_sum,
        );

        let trace = commitment_scheme.trace_domain_evaluations();
        let mut component_trace = trace
            .sub_tree(component.trace_locations())
            .map(|tree| tree.into_iter().cloned().collect_vec());
        component_trace[PREPROCESSED_TRACE_IDX] = component
            .preprocessed_column_indices()
            .iter()
            .map(|index| trace[PREPROCESSED_TRACE_IDX][*index])
            .collect();
        let component_eval = component.deref();
        assert_constraints_on_trace(
            &component_trace,
            log_size,
            |eval| {
                let _ = component_eval.evaluate(eval);
            },
            component.claimed_sum(),
        );
    }

    /// Sum of a range-check provider built with `uses` as its multiplicities,
    /// over the same relation the bridge consumes — its `−Σ mult/combine` part
    /// of the LogUp identity.
    fn provider_sum(bits: u32, uses: Vec<M31>, relation: &RangeCheckRelation) -> SecureField {
        let claim = RangeCheckClaim::new(bits);
        let value: RcColumnEval = claim.gen_preprocessed_column();
        let multiplicity: RcColumnEval = claim.gen_multiplicity_trace(uses);
        let (_trace, claim) =
            RangeCheckInteractionClaim::gen_interaction_trace(&multiplicity, &value, relation);
        claim.claimed_sum
    }
}
