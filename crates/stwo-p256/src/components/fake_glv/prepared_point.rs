use std::collections::BTreeMap;

use stwo::core::fields::{m31::M31, qm31::SecureField};
use stwo_constraint_framework::{relation, EvalAtRow, Relation, RelationEntry};
use stwo_p256_utils::constants::N_LIMBS;

use crate::limbs::{P256BigInt, P256M31BigInt};
use crate::range_checks::{add_range_check, RangeCheckRelation};

use crate::scalar::fake_glv_selector::{FakeGlvSelectorClaim, FakeGlvSelectorRow};
use crate::scalar::fake_glv_selector_lookup::Selector16DecodeEntry;

relation!(PreparedPointRelation, 44);

pub const PREPARED_POINT_ARITY: usize = 3 + 2 * N_LIMBS + 1;
pub const PREPARED_BASE_COUNT: usize = 8;
pub const TABLE16_INDEX: u32 = 16;
pub const MAX_PREPARED_POINT_USE_COUNT: u32 = 127;

#[derive(Clone, Debug)]
pub struct PreparedPointUseCountClaim {
    pub certs: Vec<PreparedPointUseCounts>,
}

impl PreparedPointUseCountClaim {
    pub fn from_selector_claim(
        selectors: &FakeGlvSelectorClaim,
    ) -> Result<Self, PreparedPointError> {
        let certs = selectors
            .rows
            .iter()
            .map(PreparedPointUseCounts::from_selector_row)
            .collect::<Result<Vec<_>, _>>()?;
        let claim = Self { certs };
        claim.verify()?;
        Ok(claim)
    }

    pub fn verify(&self) -> Result<(), PreparedPointError> {
        for cert in &self.certs {
            cert.verify()?;
        }
        Ok(())
    }

    pub fn total_use_count(&self) -> u32 {
        self.certs
            .iter()
            .map(PreparedPointUseCounts::total_use_count)
            .sum()
    }

    pub fn range7_use_count_values(&self) -> Vec<M31> {
        self.certs
            .iter()
            .filter(|cert| cert.cert_active.0 == 1)
            .flat_map(PreparedPointUseCounts::range7_use_count_values)
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPointUseCounts {
    pub sig_id: M31,
    pub cert_id: M31,
    pub cert_active: M31,
    pub base_counts: [M31; PREPARED_BASE_COUNT],
    pub table16_count: M31,
    pub lsb00_active: M31,
}

impl PreparedPointUseCounts {
    pub fn from_selector_row(row: &FakeGlvSelectorRow) -> Result<Self, PreparedPointError> {
        if row.cert_active.0 == 0 {
            return Ok(Self {
                sig_id: row.sig_id,
                cert_id: row.cert_id,
                cert_active: row.cert_active,
                base_counts: [M31::from_u32_unchecked(0); PREPARED_BASE_COUNT],
                table16_count: M31::from_u32_unchecked(0),
                lsb00_active: M31::from_u32_unchecked(0),
            });
        }

        let mut base_counts = [0u32; PREPARED_BASE_COUNT];

        let init_base_index = row.init_base_index.0 as usize;
        add_base_count(&mut base_counts, init_base_index)?;

        let selector0_base_index = Selector16DecodeEntry::from_selector(row.selectors[0])
            .map_err(|_| PreparedPointError::InvalidSelector {
                selector: row.selectors[0].0,
            })?
            .base_index
            .0 as usize;
        add_base_count(&mut base_counts, selector0_base_index)?;

        for selector in row.selectors.iter().skip(1) {
            let base_index = Selector16DecodeEntry::from_selector(*selector)
                .map_err(|_| PreparedPointError::InvalidSelector {
                    selector: selector.0,
                })?
                .base_index
                .0 as usize;
            add_base_count(&mut base_counts, base_index)?;
        }

        let lsb00_active = u32::from(row.s1_lsb.0 == 0 && row.s2_lsb.0 == 0);
        if lsb00_active == 1 {
            add_base_count(&mut base_counts, 2)?;
        }

        Ok(Self {
            sig_id: row.sig_id,
            cert_id: row.cert_id,
            cert_active: row.cert_active,
            base_counts: base_counts.map(M31::from_u32_unchecked),
            table16_count: M31::from_u32_unchecked(1),
            lsb00_active: M31::from_u32_unchecked(lsb00_active),
        })
    }

    pub fn verify(&self) -> Result<(), PreparedPointError> {
        require_bool("cert_active", self.cert_active)?;
        require_bool("lsb00_active", self.lsb00_active)?;
        let expected_table16 = self.cert_active.0;
        require_eq("table16_count", self.table16_count.0, expected_table16)?;
        if self.cert_active.0 == 0 {
            for (index, count) in self.base_counts.iter().enumerate() {
                if count.0 != 0 {
                    return Err(PreparedPointError::InactiveUseCountNonZero {
                        table_index: index as u32,
                        count: count.0,
                    });
                }
            }
            require_eq("inactive lsb00_active", self.lsb00_active.0, 0)?;
        }
        for (index, count) in self.base_counts.iter().enumerate() {
            if count.0 > MAX_PREPARED_POINT_USE_COUNT {
                return Err(PreparedPointError::UseCountOutOfRange {
                    table_index: index as u32,
                    count: count.0,
                });
            }
        }
        if self.table16_count.0 > MAX_PREPARED_POINT_USE_COUNT {
            return Err(PreparedPointError::UseCountOutOfRange {
                table_index: TABLE16_INDEX,
                count: self.table16_count.0,
            });
        }
        Ok(())
    }

    pub fn total_use_count(&self) -> u32 {
        self.base_counts.iter().map(|count| count.0).sum::<u32>() + self.table16_count.0
    }

    pub fn range7_use_count_values(&self) -> [M31; PREPARED_BASE_COUNT + 1] {
        let mut values = [M31::from_u32_unchecked(0); PREPARED_BASE_COUNT + 1];
        values[..PREPARED_BASE_COUNT].copy_from_slice(&self.base_counts);
        values[PREPARED_BASE_COUNT] = self.table16_count;
        values
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPointInstance<F> {
    pub sig_id: F,
    pub cert_id: F,
    pub table_index: F,
    pub x: P256BigInt<F>,
    pub y: P256BigInt<F>,
    pub inf: F,
}

impl PreparedPointInstance<M31> {
    pub fn dummy(sig_id: M31, cert_id: M31, table_index: u32) -> Self {
        Self {
            sig_id,
            cert_id,
            table_index: M31::from_u32_unchecked(table_index),
            x: deterministic_point_limb(table_index, 11),
            y: deterministic_point_limb(table_index, 29),
            inf: M31::from_u32_unchecked(0),
        }
    }
}

impl<F: Clone> PreparedPointInstance<F> {
    pub fn relation_values(&self) -> [F; PREPARED_POINT_ARITY] {
        core::array::from_fn(|index| self.relation_value(index))
    }

    fn relation_value(&self, index: usize) -> F {
        match index {
            0 => self.sig_id.clone(),
            1 => self.cert_id.clone(),
            2 => self.table_index.clone(),
            3..=22 => self.x.limbs()[index - 3].clone(),
            23..=42 => self.y.limbs()[index - 23].clone(),
            43 => self.inf.clone(),
            _ => panic!("PreparedPoint relation index {index} out of range"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPointProvider {
    pub instance: PreparedPointInstance<M31>,
    pub use_count: M31,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPointTraceClaim {
    pub providers: Vec<PreparedPointProvider>,
}

impl PreparedPointTraceClaim {
    pub fn from_use_counts_with_dummy_points(use_counts: &PreparedPointUseCountClaim) -> Self {
        Self::from_use_counts(use_counts, PreparedPointInstance::dummy)
    }

    pub fn from_use_counts(
        use_counts: &PreparedPointUseCountClaim,
        mut point: impl FnMut(M31, M31, u32) -> PreparedPointInstance<M31>,
    ) -> Self {
        let mut providers = Vec::new();
        for cert in &use_counts.certs {
            for (table_index, count) in cert.base_counts.iter().enumerate() {
                providers.push(PreparedPointProvider {
                    instance: point(cert.sig_id, cert.cert_id, table_index as u32),
                    use_count: *count,
                });
            }
            providers.push(PreparedPointProvider {
                instance: point(cert.sig_id, cert.cert_id, TABLE16_INDEX),
                use_count: cert.table16_count,
            });
        }
        Self { providers }
    }

    pub fn consumer_instances(&self) -> Vec<PreparedPointInstance<M31>> {
        let mut consumers = Vec::new();
        for provider in &self.providers {
            for _ in 0..provider.use_count.0 {
                consumers.push(provider.instance.clone());
            }
        }
        consumers
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PreparedPointAudit {
    entries: BTreeMap<Vec<u32>, i64>,
}

impl PreparedPointAudit {
    pub fn balanced_for_claim(claim: &PreparedPointTraceClaim) -> Self {
        let mut audit = Self::default();
        for provider in &claim.providers {
            audit.add_provider(provider);
        }
        for consumer in claim.consumer_instances() {
            audit.add_consumer(&consumer);
        }
        audit
    }

    pub fn add_provider(&mut self, provider: &PreparedPointProvider) {
        self.add(&provider.instance, -(provider.use_count.0 as i64));
    }

    pub fn add_consumer(&mut self, instance: &PreparedPointInstance<M31>) {
        self.add(instance, 1);
    }

    pub fn is_balanced(&self) -> bool {
        self.entries.values().all(|count| *count == 0)
    }

    fn add(&mut self, instance: &PreparedPointInstance<M31>, multiplicity: i64) {
        let key = instance
            .relation_values()
            .into_iter()
            .map(|value| value.0)
            .collect::<Vec<_>>();
        *self.entries.entry(key).or_default() += multiplicity;
    }
}

pub fn prepared_point_provider_claimed_sum(
    providers: &[PreparedPointProvider],
    relation: &PreparedPointRelation,
) -> SecureField {
    providers
        .iter()
        .map(|provider| {
            prepared_point_fraction(&provider.instance, relation, -(provider.use_count.0 as i64))
        })
        .sum()
}

pub fn prepared_point_consumer_claimed_sum(
    consumers: &[PreparedPointInstance<M31>],
    relation: &PreparedPointRelation,
) -> SecureField {
    consumers
        .iter()
        .map(|consumer| prepared_point_fraction(consumer, relation, 1))
        .sum()
}

pub fn prepared_point_range7_consumer_claimed_sum(
    use_counts: &PreparedPointUseCountClaim,
    range7: &RangeCheckRelation,
) -> SecureField {
    use_counts
        .range7_use_count_values()
        .iter()
        .map(|value| range7_fraction(*value, range7, 1))
        .sum()
}

pub fn add_prepared_point_provider<E: EvalAtRow>(
    eval: &mut E,
    relation: &PreparedPointRelation,
    use_count: E::F,
    instance: &PreparedPointInstance<E::F>,
) {
    add_prepared_point_relation(eval, relation, -use_count, instance);
}

pub fn add_prepared_point_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &PreparedPointRelation,
    gate: E::F,
    instance: &PreparedPointInstance<E::F>,
) {
    add_prepared_point_relation(eval, relation, gate, instance);
}

pub fn add_prepared_point_use_count_range_checks<E: EvalAtRow>(
    eval: &mut E,
    range7: &RangeCheckRelation,
    cert_active: E::F,
    base_counts: &[E::F; PREPARED_BASE_COUNT],
    table16_count: E::F,
) {
    for use_count in base_counts {
        add_range_check(eval, range7, cert_active.clone(), use_count.clone());
    }
    add_range_check(eval, range7, cert_active, table16_count);
}

fn add_prepared_point_relation<E: EvalAtRow>(
    eval: &mut E,
    relation: &PreparedPointRelation,
    numerator: E::F,
    instance: &PreparedPointInstance<E::F>,
) {
    let values = instance.relation_values();
    eval.add_to_relation(RelationEntry::base(relation, numerator, &values));
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedPointError {
    InvalidSelector {
        selector: u32,
    },
    NonBooleanFlag {
        field: &'static str,
        actual: u32,
    },
    FieldMismatch {
        field: &'static str,
        expected: u32,
        actual: u32,
    },
    UseCountOutOfRange {
        table_index: u32,
        count: u32,
    },
    InactiveUseCountNonZero {
        table_index: u32,
        count: u32,
    },
}

fn prepared_point_fraction(
    instance: &PreparedPointInstance<M31>,
    relation: &PreparedPointRelation,
    numerator: i64,
) -> SecureField {
    let values = instance.relation_values();
    let denominator: SecureField = relation.combine(&values);
    secure_from_i64(numerator) / denominator
}

fn range7_fraction(value: M31, relation: &RangeCheckRelation, numerator: i64) -> SecureField {
    let denominator: SecureField = relation.combine(&[value]);
    secure_from_i64(numerator) / denominator
}

fn add_base_count(
    counts: &mut [u32; PREPARED_BASE_COUNT],
    index: usize,
) -> Result<(), PreparedPointError> {
    if index >= PREPARED_BASE_COUNT {
        return Err(PreparedPointError::UseCountOutOfRange {
            table_index: index as u32,
            count: 1,
        });
    }
    counts[index] += 1;
    Ok(())
}

fn deterministic_point_limb(table_index: u32, offset: u32) -> P256M31BigInt {
    P256M31BigInt::from_limbs(core::array::from_fn(|i| {
        M31::from_u32_unchecked(table_index * 100 + offset + i as u32)
    }))
}

fn require_bool(field: &'static str, value: M31) -> Result<(), PreparedPointError> {
    if value.0 <= 1 {
        return Ok(());
    }
    Err(PreparedPointError::NonBooleanFlag {
        field,
        actual: value.0,
    })
}

fn require_eq(field: &'static str, actual: u32, expected: u32) -> Result<(), PreparedPointError> {
    if actual == expected {
        return Ok(());
    }
    Err(PreparedPointError::FieldMismatch {
        field,
        expected,
        actual,
    })
}

fn secure_from_i64(value: i64) -> SecureField {
    const MODULUS: i64 = (1i64 << 31) - 1;
    SecureField::from(M31::from_u32_unchecked(value.rem_euclid(MODULUS) as u32))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{P256_GX, P256_GY};
    use crate::public_inputs::{
        public_ecdsa_consumer_claimed_sum, PublicEcdsaInputClaim, PublicEcdsaInstanceRelation,
    };
    use crate::range_checks::{
        RangeCheckClaim, RangeCheckInteractionClaim, RangeCheckRelation, RANGE7_BITS,
    };
    use crate::scalar::cert_bind::CertScalarInputClaim;
    use crate::scalar::fake_glv_scalar::{FakeGlvScalarHint, FakeGlvScalarHintClaim};
    use crate::scalar::fake_glv_selector::FakeGlvSelectorClaim;
    use crate::scalar::setup_air::ScalarSetupClaim;
    use crate::types::{AffinePoint, EcdsaVerifyInput, Signature, U256};

    fn test_input(message_hash: u64, r: u64, s: u64) -> EcdsaVerifyInput {
        EcdsaVerifyInput {
            message_hash: scalar(message_hash),
            signature: Signature {
                r: scalar(r),
                s: scalar(s),
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

    fn build_selectors(
        message_hash: u64,
    ) -> (
        PublicEcdsaInputClaim,
        ScalarSetupClaim,
        FakeGlvSelectorClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(message_hash, 77, 1)]);
        let scalar_setup =
            ScalarSetupClaim::from_public_inputs(&public_claim).expect("valid scalar setup");
        let certs =
            CertScalarInputClaim::from_scalar_setup(&scalar_setup).expect("valid cert inputs");
        let hints = certs
            .rows
            .iter()
            .map(|row| FakeGlvScalarHint::trivial_for_small_scalar(&row.scalar).unwrap())
            .collect();
        let fake_glv =
            FakeGlvScalarHintClaim::from_cert_inputs(&certs, hints).expect("valid hints");
        let selectors =
            FakeGlvSelectorClaim::from_scalar_hints(&fake_glv).expect("valid selectors");
        (public_claim, scalar_setup, selectors)
    }

    #[test]
    fn prepared_point_relation_has_expected_arity() {
        assert_eq!(PREPARED_POINT_ARITY, 44);
    }

    #[test]
    fn prepared_point_use_counts_match_selector_flow() {
        let (_, _, selectors) = build_selectors(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");

        assert_eq!(use_counts.certs.len(), 2);
        assert_eq!(use_counts.certs[0].table16_count.0, 1);
        assert_eq!(use_counts.certs[0].total_use_count(), 65);
        assert_eq!(use_counts.certs[1].total_use_count(), 65);
        use_counts.verify().expect("use counts verify");
    }

    #[test]
    fn prepared_point_zero_branch_has_zero_counts() {
        let (_, _, selectors) = build_selectors(0);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");

        assert_eq!(use_counts.certs[0].cert_active.0, 0);
        assert_eq!(use_counts.certs[0].total_use_count(), 0);
        assert_eq!(use_counts.certs[1].cert_active.0, 1);
        assert_eq!(use_counts.certs[1].total_use_count(), 65);
    }

    #[test]
    fn prepared_point_provider_and_consumers_balance() {
        let (_, _, selectors) = build_selectors(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let claim = PreparedPointTraceClaim::from_use_counts_with_dummy_points(&use_counts);
        let audit = PreparedPointAudit::balanced_for_claim(&claim);

        assert_eq!(
            claim.consumer_instances().len() as u32,
            use_counts.total_use_count()
        );
        assert!(audit.is_balanced());
    }

    #[test]
    fn prepared_point_logup_sums_balance() {
        let (_, _, selectors) = build_selectors(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let claim = PreparedPointTraceClaim::from_use_counts_with_dummy_points(&use_counts);
        let relation = PreparedPointRelation::dummy();
        let providers = prepared_point_provider_claimed_sum(&claim.providers, &relation);
        let consumers = prepared_point_consumer_claimed_sum(&claim.consumer_instances(), &relation);

        assert_eq!(
            providers + consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn prepared_point_range7_consumers_skip_inactive_certs() {
        let (_, _, selectors) = build_selectors(0);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let range7_uses = use_counts.range7_use_count_values();

        assert_eq!(use_counts.certs[0].cert_active.0, 0);
        assert_eq!(use_counts.certs[1].cert_active.0, 1);
        assert_eq!(range7_uses.len(), PREPARED_BASE_COUNT + 1);
        assert_eq!(
            range7_uses.iter().map(|value| value.0).sum::<u32>(),
            use_counts.certs[1].total_use_count()
        );
    }

    #[test]
    fn prepared_point_range7_logup_sums_balance() {
        let (_, _, selectors) = build_selectors(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let relation = RangeCheckRelation::dummy();
        let range7 = RangeCheckClaim::new(RANGE7_BITS);
        let values = range7.gen_preprocessed_column();
        let multiplicity = range7.gen_multiplicity_trace(use_counts.range7_use_count_values());
        let (_, provider) =
            RangeCheckInteractionClaim::gen_interaction_trace(&multiplicity, &values, &relation);
        let consumers = prepared_point_range7_consumer_claimed_sum(&use_counts, &relation);

        assert_eq!(
            provider.claimed_sum + consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn prepared_point_range7_rejects_field_sized_use_count() {
        let (_, _, selectors) = build_selectors(42);
        let mut use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        use_counts.certs[0].base_counts[0] = M31::from_u32_unchecked(128);

        let err = use_counts
            .verify()
            .expect_err("field-sized use count must fail");

        assert!(matches!(
            err,
            PreparedPointError::UseCountOutOfRange {
                table_index: 0,
                count: 128,
            }
        ));
    }

    #[test]
    fn prepared_point_e2e_preserves_public_balance() {
        let public_relation = PublicEcdsaInstanceRelation::dummy();
        let (public_claim, scalar_setup, selectors) = build_selectors(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let prepared_claim =
            PreparedPointTraceClaim::from_use_counts_with_dummy_points(&use_counts);
        let prepared_audit = PreparedPointAudit::balanced_for_claim(&prepared_claim);
        let public_interaction = public_claim.initial_logup_claim(&public_relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &public_relation);
        let range7_relation = RangeCheckRelation::dummy();
        let range7 = RangeCheckClaim::new(RANGE7_BITS);
        let range7_values = range7.gen_preprocessed_column();
        let range7_multiplicity =
            range7.gen_multiplicity_trace(use_counts.range7_use_count_values());
        let (_, range7_provider) = RangeCheckInteractionClaim::gen_interaction_trace(
            &range7_multiplicity,
            &range7_values,
            &range7_relation,
        );
        let range7_consumers =
            prepared_point_range7_consumer_claimed_sum(&use_counts, &range7_relation);

        assert!(prepared_audit.is_balanced());
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
        assert_eq!(
            range7_provider.claimed_sum + range7_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn prepared_point_detects_mutated_use_count() {
        let (_, _, selectors) = build_selectors(42);
        let mut use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        use_counts.certs[0].table16_count = M31::from_u32_unchecked(2);

        let err = use_counts
            .verify()
            .expect_err("bad table16 count must fail");

        assert!(matches!(
            err,
            PreparedPointError::FieldMismatch {
                field: "table16_count",
                ..
            }
        ));
    }

    #[test]
    fn prepared_point_audit_detects_mutated_consumer_point() {
        let (_, _, selectors) = build_selectors(42);
        let use_counts =
            PreparedPointUseCountClaim::from_selector_claim(&selectors).expect("valid counts");
        let claim = PreparedPointTraceClaim::from_use_counts_with_dummy_points(&use_counts);
        let mut consumers = claim.consumer_instances();
        consumers[0].table_index = M31::from_u32_unchecked(99);
        let mut audit = PreparedPointAudit::default();
        for provider in &claim.providers {
            audit.add_provider(provider);
        }
        for consumer in &consumers {
            audit.add_consumer(consumer);
        }

        assert!(!audit.is_balanced());
    }
}
