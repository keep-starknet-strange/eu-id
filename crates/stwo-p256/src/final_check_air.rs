//! FinalEcdsaCheck AIR — increment 6.1 (write-back scaffolding).
//!
//! This binds the verifier-facing proof to the public signature `r` using the
//! same pattern as stwo-cairo's `public_data.logup_sum`: the public input
//! provides `(sig_id, r)` on [`EcdsaResultRelation`] as an initial LogUp claim,
//! and this component consumes `(sig_id, r_check)` from its committed trace.
//! Balance (`provider + consumer == 0`) forces `r_check == r`.
//!
//! SCAFFOLDING: `r_check` is currently a free witness equal to the public `r`,
//! so this increment is verifier-meaningless on its own. Increment 6.2 replaces
//! `r_check` with the reduced x-coordinate `x(u1·G + u2·Q) mod n` proven in
//! circuit (EC tripling to undo the fake-GLV factor, the H1+H2 addition, and the
//! `x mod n` reduction), at which point the balance becomes the ECDSA verdict.

use stwo::core::{
    air::Component,
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
    pcs::TreeVec,
    ColumnVec,
};
use stwo::prover::{
    backend::simd::{
        m31::{PackedM31, LOG_N_LANES},
        qm31::PackedQM31,
        SimdBackend,
    },
    ComponentProver,
};
use stwo_constraint_framework::{
    relation, EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation,
    RelationEntry, TraceLocationAllocator,
};
use stwo_p256_utils::constants::N_LIMBS;

use crate::limbs::P256BigInt;
use crate::public_inputs::{PublicEcdsaInputClaim, PublicEcdsaInstance};
use crate::scalar::scalar_mod_mul::columns::{m31_column_eval, padded_log_size, M31ColumnEval};

/// `(sig_id, r[N_LIMBS])`.
pub const ECDSA_RESULT_RELATION_ARITY: usize = 1 + N_LIMBS;

relation!(EcdsaResultRelation, ECDSA_RESULT_RELATION_ARITY);

const FINAL_CHECK_TRACE_COLUMNS: usize = 1 + 1 + N_LIMBS;

pub type FinalCheckAirComponent = FrameworkComponent<FinalCheckAirEval>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalCheckAirProofClaim {
    pub log_size: u32,
}

impl FinalCheckAirProofClaim {
    pub fn from_claim(claim: &PublicEcdsaInputClaim) -> Self {
        Self {
            log_size: padded_log_size(claim.instances.len()),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalCheckAirInteractionClaim {
    pub claimed_sum: SecureField,
    pub result_consumer_claimed_sum: SecureField,
}

impl FinalCheckAirInteractionClaim {
    pub fn zero() -> Self {
        Self {
            claimed_sum: secure_zero(),
            result_consumer_claimed_sum: secure_zero(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub struct FinalCheckAirComponents {
    pub check: FinalCheckAirComponent,
}

impl FinalCheckAirComponents {
    pub(crate) fn new(
        allocator: &mut TraceLocationAllocator,
        claim: FinalCheckAirProofClaim,
        interaction_claim: &FinalCheckAirInteractionClaim,
        result_relation: &EcdsaResultRelation,
    ) -> Self {
        Self {
            check: FinalCheckAirComponent::new(
                allocator,
                FinalCheckAirEval {
                    log_size: claim.log_size,
                    result_relation: result_relation.clone(),
                },
                interaction_claim.claimed_sum,
            ),
        }
    }

    pub fn components(&self) -> Vec<&dyn Component> {
        vec![&self.check as &dyn Component]
    }

    pub fn component_provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![&self.check as &dyn ComponentProver<SimdBackend>]
    }

    pub fn trace_log_degree_bounds(&self) -> TreeVec<ColumnVec<u32>> {
        self.check.trace_log_degree_bounds()
    }

    pub fn max_constraint_log_degree_bound(&self) -> u32 {
        self.check.max_constraint_log_degree_bound()
    }
}

#[derive(Clone)]
pub struct FinalCheckAirEval {
    pub log_size: u32,
    pub result_relation: EcdsaResultRelation,
}

impl FrameworkEval for FinalCheckAirEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let active = eval.next_trace_mask();
        let sig_id = eval.next_trace_mask();
        let r_check = P256BigInt::from_limbs(core::array::from_fn(|_| eval.next_trace_mask()));
        let one = E::F::from(M31::from_u32_unchecked(1));

        eval.add_constraint(active.clone() * (active.clone() - one.clone()));
        eval.add_constraint((one.clone() - active.clone()) * sig_id.clone());
        for limb in r_check.limbs() {
            eval.add_constraint((one.clone() - active.clone()) * limb.clone());
        }

        let mut values = Vec::with_capacity(ECDSA_RESULT_RELATION_ARITY);
        values.push(sig_id);
        values.extend(r_check.limbs().iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.result_relation,
            E::EF::from(active),
            &values,
        ));
        eval.finalize_logup();
        eval
    }
}

/// Public-input side: provide `(sig_id, r)` per instance as an initial LogUp
/// claim (no trace), mirroring `public_ecdsa_provider_claimed_sum`.
pub fn ecdsa_result_provider_claimed_sum(
    instances: &[PublicEcdsaInstance<M31>],
    relation: &EcdsaResultRelation,
) -> SecureField {
    instances
        .iter()
        .map(|instance| {
            let denominator: SecureField = relation.combine(&result_values(instance));
            -SecureField::from(M31::from_u32_unchecked(1)) / denominator
        })
        .sum()
}

pub fn gen_final_check_air_base_trace(
    public_claim: &PublicEcdsaInputClaim,
    proof_claim: FinalCheckAirProofClaim,
) -> ColumnVec<M31ColumnEval> {
    let row_count = 1usize << proof_claim.log_size;
    assert!(public_claim.instances.len() <= row_count);
    let mut columns =
        vec![vec![M31::from_u32_unchecked(0); row_count]; FINAL_CHECK_TRACE_COLUMNS];
    for (row, instance) in public_claim.instances.iter().enumerate() {
        columns[0][row] = M31::from_u32_unchecked(1);
        columns[1][row] = instance.sig_id;
        for (limb_index, limb) in instance.r.limbs().iter().enumerate() {
            columns[2 + limb_index][row] = *limb;
        }
    }
    columns
        .into_iter()
        .map(|values| m31_column_eval(proof_claim.log_size, values))
        .collect()
}

pub(crate) fn gen_final_check_air_interaction_trace(
    base: &[M31ColumnEval],
    relation: &EcdsaResultRelation,
) -> (ColumnVec<M31ColumnEval>, FinalCheckAirInteractionClaim) {
    assert_eq!(base.len(), FINAL_CHECK_TRACE_COLUMNS);
    let log_size = base[0].domain.log_size();
    let mut logup = LogupTraceGenerator::new(log_size);
    let mut col = logup.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        col.write_frac(
            vec_row,
            PackedQM31::from(base[0].data[vec_row]),
            relation.combine(&result_packed_values_from_base(base, vec_row)),
        );
    }
    col.finalize_col();
    let (trace, claimed_sum) = logup.finalize_last();
    let result_consumer_claimed_sum: SecureField = storage_rows(base)
        .filter(|row| row[0] != M31::from_u32_unchecked(0))
        .map(|row| -> SecureField {
            let denominator: SecureField = relation.combine(&result_values_from_base(&row));
            SecureField::from(row[0]) / denominator
        })
        .sum();
    (
        trace,
        FinalCheckAirInteractionClaim {
            claimed_sum,
            result_consumer_claimed_sum,
        },
    )
}

fn result_values(instance: &PublicEcdsaInstance<M31>) -> [M31; ECDSA_RESULT_RELATION_ARITY] {
    core::array::from_fn(|index| {
        if index == 0 {
            instance.sig_id
        } else {
            instance.r.limbs()[index - 1]
        }
    })
}

fn result_packed_values_from_base(
    base: &[M31ColumnEval],
    vec_row: usize,
) -> [PackedM31; ECDSA_RESULT_RELATION_ARITY] {
    core::array::from_fn(|index| base[1 + index].data[vec_row])
}

fn result_values_from_base(row: &[M31]) -> [M31; ECDSA_RESULT_RELATION_ARITY] {
    core::array::from_fn(|index| row[1 + index])
}

fn storage_rows(base: &[M31ColumnEval]) -> impl Iterator<Item = Vec<M31>> + '_ {
    let row_count = base[0].domain.size();
    (0..row_count).map(|row| {
        let vec_row = row / (1 << LOG_N_LANES);
        let lane = row % (1 << LOG_N_LANES);
        base.iter()
            .map(|column| column.data[vec_row].to_array()[lane])
            .collect::<Vec<_>>()
    })
}

fn secure_zero() -> SecureField {
    SecureField::from(M31::from_u32_unchecked(0))
}
