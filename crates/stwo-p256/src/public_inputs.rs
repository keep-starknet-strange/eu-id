use std::{array, collections::BTreeMap};

use stwo::core::{
    channel::Channel,
    fields::{m31::M31, qm31::SecureField},
};
use stwo_constraint_framework::{relation, EvalAtRow, Relation, RelationEntry};
use stwo_p256_utils::constants::N_LIMBS;

use crate::limbs::{P256BigInt, P256M31BigInt};
use crate::types::EcdsaVerifyInput;

relation!(PublicEcdsaInstanceRelation, 101);

/// Relation key shape:
/// `(sig_id, z[20], r[20], s[20], pub_x[20], pub_y[20])`.
pub const PUBLIC_ECDSA_INSTANCE_ARITY: usize = 1 + 5 * N_LIMBS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicEcdsaInstance<F> {
    pub sig_id: F,
    pub z: P256BigInt<F>,
    pub r: P256BigInt<F>,
    pub s: P256BigInt<F>,
    pub pub_x: P256BigInt<F>,
    pub pub_y: P256BigInt<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicEcdsaInputClaim {
    pub instances: Vec<PublicEcdsaInstance<M31>>,
}

impl PublicEcdsaInputClaim {
    pub fn from_inputs(inputs: &[EcdsaVerifyInput]) -> Self {
        Self {
            instances: inputs
                .iter()
                .enumerate()
                .map(|(sig_id, input)| PublicEcdsaInstance::from_input(sig_id as u32, input))
                .collect(),
        }
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.instances.len() as u64);
        for instance in &self.instances {
            let values = instance.relation_values().map(SecureField::from);
            channel.mix_felts(&values);
        }
    }

    pub fn initial_logup_claim(
        &self,
        relation: &PublicEcdsaInstanceRelation,
    ) -> PublicEcdsaInputInteractionClaim {
        PublicEcdsaInputInteractionClaim {
            claimed_sum: public_ecdsa_provider_claimed_sum(&self.instances, relation),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicEcdsaInputInteractionClaim {
    pub claimed_sum: SecureField,
}

impl PublicEcdsaInputInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

impl PublicEcdsaInstance<M31> {
    pub fn from_input(sig_id: u32, input: &EcdsaVerifyInput) -> Self {
        Self {
            sig_id: M31::from_u32_unchecked(sig_id),
            z: P256M31BigInt::from_u256(&input.message_hash),
            r: P256M31BigInt::from_u256(&input.signature.r),
            s: P256M31BigInt::from_u256(&input.signature.s),
            pub_x: P256M31BigInt::from_u256(&input.public_key.x),
            pub_y: P256M31BigInt::from_u256(&input.public_key.y),
        }
    }
}

pub fn public_ecdsa_provider_claimed_sum(
    instances: &[PublicEcdsaInstance<M31>],
    relation: &PublicEcdsaInstanceRelation,
) -> SecureField {
    public_ecdsa_claimed_sum(instances, relation, -1)
}

pub fn public_ecdsa_consumer_claimed_sum(
    instances: &[PublicEcdsaInstance<M31>],
    relation: &PublicEcdsaInstanceRelation,
) -> SecureField {
    public_ecdsa_claimed_sum(instances, relation, 1)
}

fn public_ecdsa_claimed_sum(
    instances: &[PublicEcdsaInstance<M31>],
    relation: &PublicEcdsaInstanceRelation,
    numerator: i64,
) -> SecureField {
    instances
        .iter()
        .map(|instance| public_ecdsa_fraction(instance, relation, numerator))
        .sum()
}

fn public_ecdsa_fraction(
    instance: &PublicEcdsaInstance<M31>,
    relation: &PublicEcdsaInstanceRelation,
    numerator: i64,
) -> SecureField {
    let values = instance.relation_values();
    let denominator: SecureField = relation.combine(&values);
    secure_from_i64(numerator) / denominator
}

fn secure_from_i64(value: i64) -> SecureField {
    const MODULUS: i64 = (1i64 << 31) - 1;
    SecureField::from(M31::from_u32_unchecked(value.rem_euclid(MODULUS) as u32))
}

impl<F: Clone> PublicEcdsaInstance<F> {
    pub fn relation_values(&self) -> [F; PUBLIC_ECDSA_INSTANCE_ARITY] {
        array::from_fn(|index| self.relation_value(index))
    }

    fn relation_value(&self, index: usize) -> F {
        if index == 0 {
            return self.sig_id.clone();
        }

        let limb_index = (index - 1) % N_LIMBS;
        match (index - 1) / N_LIMBS {
            0 => self.z.limbs()[limb_index].clone(),
            1 => self.r.limbs()[limb_index].clone(),
            2 => self.s.limbs()[limb_index].clone(),
            3 => self.pub_x.limbs()[limb_index].clone(),
            4 => self.pub_y.limbs()[limb_index].clone(),
            _ => panic!("public ECDSA instance relation index {index} out of range"),
        }
    }
}

/// Public-data side of the relation: `-1 * PublicEcdsaInstance(...)`.
pub fn add_public_ecdsa_instance_provider<E: EvalAtRow>(
    eval: &mut E,
    relation: &PublicEcdsaInstanceRelation,
    gate: E::F,
    instance: &PublicEcdsaInstance<E::F>,
) {
    add_public_ecdsa_instance_relation(eval, relation, -E::EF::from(gate), instance);
}

/// ECDSA VM side of the relation: `+sig_active * PublicEcdsaInstance(...)`.
pub fn add_public_ecdsa_instance_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &PublicEcdsaInstanceRelation,
    gate: E::F,
    instance: &PublicEcdsaInstance<E::F>,
) {
    add_public_ecdsa_instance_relation(eval, relation, E::EF::from(gate), instance);
}

fn add_public_ecdsa_instance_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &PublicEcdsaInstanceRelation,
    numerator: E::EF,
    instance: &PublicEcdsaInstance<E::F>,
) {
    let values = instance.relation_values();
    eval.add_to_relation(RelationEntry::new(relation, numerator, &values));
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PublicEcdsaInstanceAudit {
    entries: BTreeMap<Vec<u32>, i64>,
}

impl PublicEcdsaInstanceAudit {
    pub fn add_provider(&mut self, instance: &PublicEcdsaInstance<M31>) {
        self.add(instance, -1);
    }

    pub fn add_consumer(&mut self, instance: &PublicEcdsaInstance<M31>) {
        self.add(instance, 1);
    }

    pub fn is_balanced(&self) -> bool {
        self.entries.values().all(|&multiplicity| multiplicity == 0)
    }

    pub fn nonzero_entries(&self) -> usize {
        self.entries
            .values()
            .filter(|&&multiplicity| multiplicity != 0)
            .count()
    }

    fn add(&mut self, instance: &PublicEcdsaInstance<M31>, multiplicity: i64) {
        let key = instance
            .relation_values()
            .into_iter()
            .map(|value| value.0)
            .collect::<Vec<_>>();
        *self.entries.entry(key).or_default() += multiplicity;
    }
}

#[cfg(test)]
mod tests {
    use stwo::core::channel::Blake2sM31Channel;

    use crate::constants::{P256_GX, P256_GY};
    use crate::types::{AffinePoint, Signature, U256};

    use super::*;

    fn test_input(r: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: scalar(42),
            signature: Signature {
                r: scalar(r),
                s: scalar(11),
            },
            public_key: AffinePoint {
                x: U256::from_le_u64s(&P256_GX),
                y: U256::from_le_u64s(&P256_GY),
            },
        }
    }

    fn scalar(value: u64) -> U256 {
        U256::from_le_u64s(&[value, 0, 0, 0])
    }

    fn zero() -> SecureField {
        SecureField::from(M31::from_u32_unchecked(0))
    }

    #[test]
    fn public_ecdsa_instance_relation_has_expected_arity() {
        assert_eq!(PUBLIC_ECDSA_INSTANCE_ARITY, 101);
    }

    #[test]
    fn public_ecdsa_instance_flattens_in_spec_order() {
        let instance = PublicEcdsaInstance::from_input(7, &test_input(77));
        let values = instance.relation_values();

        assert_eq!(values[0], M31::from_u32_unchecked(7));
        assert_eq!(values[1], instance.z.limbs()[0]);
        assert_eq!(values[1 + N_LIMBS], instance.r.limbs()[0]);
        assert_eq!(values[1 + 2 * N_LIMBS], instance.s.limbs()[0]);
        assert_eq!(values[1 + 3 * N_LIMBS], instance.pub_x.limbs()[0]);
        assert_eq!(values[1 + 4 * N_LIMBS], instance.pub_y.limbs()[0]);
    }

    #[test]
    fn public_ecdsa_audit_balances_matching_provider_and_consumer() {
        let instance = PublicEcdsaInstance::from_input(0, &test_input(77));
        let mut audit = PublicEcdsaInstanceAudit::default();

        audit.add_provider(&instance);
        audit.add_consumer(&instance);

        assert!(audit.is_balanced());
        assert_eq!(audit.nonzero_entries(), 0);
    }

    #[test]
    fn public_ecdsa_audit_allows_duplicate_tuple_at_different_sig_ids() {
        let input = test_input(77);
        let first = PublicEcdsaInstance::from_input(0, &input);
        let second = PublicEcdsaInstance::from_input(1, &input);
        let mut audit = PublicEcdsaInstanceAudit::default();

        audit.add_provider(&first);
        audit.add_provider(&second);
        audit.add_consumer(&first);
        audit.add_consumer(&second);

        assert!(audit.is_balanced());
    }

    #[test]
    fn public_ecdsa_audit_rejects_wrong_sig_id_consumer() {
        let input = test_input(77);
        let provider = PublicEcdsaInstance::from_input(0, &input);
        let consumer = PublicEcdsaInstance::from_input(1, &input);
        let mut audit = PublicEcdsaInstanceAudit::default();

        audit.add_provider(&provider);
        audit.add_consumer(&consumer);

        assert!(!audit.is_balanced());
        assert_eq!(audit.nonzero_entries(), 2);
    }

    #[test]
    fn public_ecdsa_audit_rejects_mutated_public_tuple() {
        let provider = PublicEcdsaInstance::from_input(0, &test_input(77));
        let consumer = PublicEcdsaInstance::from_input(0, &test_input(78));
        let mut audit = PublicEcdsaInstanceAudit::default();

        audit.add_provider(&provider);
        audit.add_consumer(&consumer);

        assert!(!audit.is_balanced());
        assert_eq!(audit.nonzero_entries(), 2);
    }

    #[test]
    fn public_ecdsa_claim_assigns_ordered_sig_ids() {
        let claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77), test_input(78)]);

        assert_eq!(claim.instances[0].sig_id, M31::from_u32_unchecked(0));
        assert_eq!(claim.instances[1].sig_id, M31::from_u32_unchecked(1));
        assert_ne!(
            claim.instances[0].relation_values(),
            claim.instances[1].relation_values()
        );
    }

    #[test]
    fn public_ecdsa_initial_logup_claim_balances_vm_consumers() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77), test_input(78)]);

        let public_data = claim.initial_logup_claim(&relation);
        let vm_consumers = public_ecdsa_consumer_claimed_sum(&claim.instances, &relation);

        assert_eq!(public_data.claimed_sum + vm_consumers, zero());
    }

    #[test]
    fn public_ecdsa_initial_logup_claim_detects_wrong_sig_id_consumer() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let provider_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77)]);
        let wrong_consumer = PublicEcdsaInstance::from_input(1, &test_input(77));

        let public_data = provider_claim.initial_logup_claim(&relation);
        let vm_consumers = public_ecdsa_consumer_claimed_sum(&[wrong_consumer], &relation);

        assert_ne!(public_data.claimed_sum + vm_consumers, zero());
    }

    #[test]
    fn public_ecdsa_initial_logup_claim_detects_mutated_consumer_tuple() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let provider_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77)]);
        let wrong_consumer = PublicEcdsaInstance::from_input(0, &test_input(78));

        let public_data = provider_claim.initial_logup_claim(&relation);
        let vm_consumers = public_ecdsa_consumer_claimed_sum(&[wrong_consumer], &relation);

        assert_ne!(public_data.claimed_sum + vm_consumers, zero());
    }

    #[test]
    fn public_ecdsa_claims_mix_into_transcript() {
        let claim = PublicEcdsaInputClaim::from_inputs(&[test_input(77)]);
        let interaction_claim = claim.initial_logup_claim(&PublicEcdsaInstanceRelation::dummy());
        let mut channel = Blake2sM31Channel::default();

        claim.mix_into(&mut channel);
        interaction_claim.mix_into(&mut channel);
    }
}
