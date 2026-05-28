use std::collections::BTreeMap;

use stwo::core::fields::{m31::M31, qm31::SecureField};
use stwo_constraint_framework::{relation, EvalAtRow, Relation, RelationEntry};

use super::fake_glv_selector::{FakeGlvSelectorClaim, FAKE_GLV_SELECTOR_CHUNKS};

relation!(Selector4x4Relation, 3);
relation!(Selector16DecodeRelation, 3);
relation!(FinalSelectorRelation, 4);

#[derive(Clone, Debug)]
pub struct FakeGlvSelectorLookupRelations {
    pub selector4x4: Selector4x4Relation,
    pub selector16_decode: Selector16DecodeRelation,
    pub final_selector: FinalSelectorRelation,
}

impl FakeGlvSelectorLookupRelations {
    pub fn dummy() -> Self {
        Self {
            selector4x4: Selector4x4Relation::dummy(),
            selector16_decode: Selector16DecodeRelation::dummy(),
            final_selector: FinalSelectorRelation::dummy(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Selector4x4Entry {
    pub a: M31,
    pub b: M31,
    pub selector: M31,
}

impl Selector4x4Entry {
    pub fn new(a: u32, b: u32) -> Self {
        Self {
            a: M31::from_u32_unchecked(a),
            b: M31::from_u32_unchecked(b),
            selector: M31::from_u32_unchecked(a + 4 * b),
        }
    }

    pub fn values(self) -> [M31; 3] {
        [self.a, self.b, self.selector]
    }

    pub fn verify(self) -> Result<(), SelectorLookupError> {
        if self.a.0 >= 4 || self.b.0 >= 4 || self.selector.0 != self.a.0 + 4 * self.b.0 {
            return Err(SelectorLookupError::InvalidSelector4x4(self));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Selector16DecodeEntry {
    pub selector: M31,
    pub base_index: M31,
    pub neg_bit: M31,
}

impl Selector16DecodeEntry {
    pub fn from_selector(selector: M31) -> Result<Self, SelectorLookupError> {
        let (base_index, neg_bit) = decode_selector16(selector.0)
            .ok_or(SelectorLookupError::Selector16OutOfRange { selector })?;
        Ok(Self {
            selector,
            base_index: M31::from_u32_unchecked(base_index),
            neg_bit: M31::from_u32_unchecked(neg_bit),
        })
    }

    pub fn values(self) -> [M31; 3] {
        [self.selector, self.base_index, self.neg_bit]
    }

    pub fn verify(self) -> Result<(), SelectorLookupError> {
        let expected = Self::from_selector(self.selector)?;
        if self != expected {
            return Err(SelectorLookupError::InvalidSelector16Decode {
                actual: self,
                expected,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FinalSelectorEntry {
    pub s1_msb: M31,
    pub s2_msb: M31,
    pub selector_final: M31,
    pub init_base_index: M31,
}

impl FinalSelectorEntry {
    pub fn new(s1_msb: M31, s2_msb: M31) -> Self {
        Self {
            s1_msb,
            s2_msb,
            selector_final: M31::from_u32_unchecked(5 + s1_msb.0 + 4 * s2_msb.0),
            init_base_index: M31::from_u32_unchecked(2 + s1_msb.0 + 4 * s2_msb.0),
        }
    }

    pub fn values(self) -> [M31; 4] {
        [
            self.s1_msb,
            self.s2_msb,
            self.selector_final,
            self.init_base_index,
        ]
    }

    pub fn verify(self) -> Result<(), SelectorLookupError> {
        if self.s1_msb.0 > 1 || self.s2_msb.0 > 1 {
            return Err(SelectorLookupError::InvalidFinalSelector(self));
        }
        let expected = Self::new(self.s1_msb, self.s2_msb);
        if self != expected {
            return Err(SelectorLookupError::InvalidFinalSelector(self));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SelectorLookupRequests {
    pub selector4x4: Vec<Selector4x4Entry>,
    pub selector16_decode: Vec<Selector16DecodeEntry>,
    pub final_selector: Vec<FinalSelectorEntry>,
}

impl SelectorLookupRequests {
    pub fn from_selector_claim(claim: &FakeGlvSelectorClaim) -> Result<Self, SelectorLookupError> {
        let mut requests = Self::default();
        for row in &claim.rows {
            if row.cert_active.0 == 0 {
                continue;
            }

            for selector in row.selectors {
                let a = selector.0 % 4;
                let b = selector.0 / 4;
                let selector4x4 = Selector4x4Entry {
                    a: M31::from_u32_unchecked(a),
                    b: M31::from_u32_unchecked(b),
                    selector,
                };
                selector4x4.verify()?;
                requests.selector4x4.push(selector4x4);
                requests
                    .selector16_decode
                    .push(Selector16DecodeEntry::from_selector(selector)?);
            }

            let final_selector = FinalSelectorEntry {
                s1_msb: row.s1_msb,
                s2_msb: row.s2_msb,
                selector_final: row.selector_final,
                init_base_index: row.init_base_index,
            };
            final_selector.verify()?;
            requests.final_selector.push(final_selector);
        }
        Ok(requests)
    }

    pub fn verify(&self) -> Result<(), SelectorLookupError> {
        for entry in &self.selector4x4 {
            entry.verify()?;
        }
        for entry in &self.selector16_decode {
            entry.verify()?;
        }
        for entry in &self.final_selector {
            entry.verify()?;
        }
        Ok(())
    }

    pub fn expected_selector4x4_uses(&self) -> usize {
        self.final_selector.len() * FAKE_GLV_SELECTOR_CHUNKS
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SelectorLookupAudit {
    selector4x4: BTreeMap<[u32; 3], i64>,
    selector16_decode: BTreeMap<[u32; 3], i64>,
    final_selector: BTreeMap<[u32; 4], i64>,
}

impl SelectorLookupAudit {
    pub fn balanced_for_requests(
        requests: &SelectorLookupRequests,
    ) -> Result<Self, SelectorLookupError> {
        requests.verify()?;
        let mut audit = Self::default();
        audit.add_consumers(requests);
        audit.add_multiplicity_providers(requests);
        Ok(audit)
    }

    pub fn add_consumers(&mut self, requests: &SelectorLookupRequests) {
        for entry in &requests.selector4x4 {
            *self
                .selector4x4
                .entry(entry.values().map(|value| value.0))
                .or_default() += 1;
        }
        for entry in &requests.selector16_decode {
            *self
                .selector16_decode
                .entry(entry.values().map(|value| value.0))
                .or_default() += 1;
        }
        for entry in &requests.final_selector {
            *self
                .final_selector
                .entry(entry.values().map(|value| value.0))
                .or_default() += 1;
        }
    }

    pub fn add_multiplicity_providers(&mut self, requests: &SelectorLookupRequests) {
        for entry in &requests.selector4x4 {
            *self
                .selector4x4
                .entry(entry.values().map(|value| value.0))
                .or_default() -= 1;
        }
        for entry in &requests.selector16_decode {
            *self
                .selector16_decode
                .entry(entry.values().map(|value| value.0))
                .or_default() -= 1;
        }
        for entry in &requests.final_selector {
            *self
                .final_selector
                .entry(entry.values().map(|value| value.0))
                .or_default() -= 1;
        }
    }

    pub fn is_balanced(&self) -> bool {
        self.selector4x4.values().all(|count| *count == 0)
            && self.selector16_decode.values().all(|count| *count == 0)
            && self.final_selector.values().all(|count| *count == 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelectorLookupInteractionClaim {
    pub claimed_sum: SecureField,
}

pub fn selector_lookup_consumer_claimed_sum(
    requests: &SelectorLookupRequests,
    relations: &FakeGlvSelectorLookupRelations,
) -> SecureField {
    selector_lookup_claimed_sum(requests, relations, 1)
}

pub fn selector_lookup_provider_claimed_sum(
    requests: &SelectorLookupRequests,
    relations: &FakeGlvSelectorLookupRelations,
) -> SecureField {
    selector_lookup_claimed_sum(requests, relations, -1)
}

fn selector_lookup_claimed_sum(
    requests: &SelectorLookupRequests,
    relations: &FakeGlvSelectorLookupRelations,
    numerator: i64,
) -> SecureField {
    requests
        .selector4x4
        .iter()
        .map(|entry| selector_fraction(&relations.selector4x4, &entry.values(), numerator))
        .sum::<SecureField>()
        + requests
            .selector16_decode
            .iter()
            .map(|entry| {
                selector_fraction(&relations.selector16_decode, &entry.values(), numerator)
            })
            .sum::<SecureField>()
        + requests
            .final_selector
            .iter()
            .map(|entry| selector_fraction(&relations.final_selector, &entry.values(), numerator))
            .sum::<SecureField>()
}

fn selector_fraction<R, const N: usize>(
    relation: &R,
    values: &[M31; N],
    numerator: i64,
) -> SecureField
where
    R: Relation<M31, SecureField>,
{
    let denominator: SecureField = relation.combine(values);
    secure_from_i64(numerator) / denominator
}

pub fn add_selector4x4_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &Selector4x4Relation,
    gate: E::F,
    entry: &[E::F; 3],
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), entry));
}

pub fn add_selector16_decode_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &Selector16DecodeRelation,
    gate: E::F,
    entry: &[E::F; 3],
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), entry));
}

pub fn add_final_selector_consumer<E: EvalAtRow>(
    eval: &mut E,
    relation: &FinalSelectorRelation,
    gate: E::F,
    entry: &[E::F; 4],
) {
    eval.add_to_relation(RelationEntry::new(relation, E::EF::from(gate), entry));
}

pub fn selector4x4_table() -> [Selector4x4Entry; 16] {
    core::array::from_fn(|selector| {
        let selector = selector as u32;
        Selector4x4Entry {
            a: M31::from_u32_unchecked(selector % 4),
            b: M31::from_u32_unchecked(selector / 4),
            selector: M31::from_u32_unchecked(selector),
        }
    })
}

pub fn selector16_decode_table() -> [Selector16DecodeEntry; 16] {
    core::array::from_fn(|selector| {
        Selector16DecodeEntry::from_selector(M31::from_u32_unchecked(selector as u32))
            .expect("selector table entry is valid")
    })
}

pub fn final_selector_table() -> [FinalSelectorEntry; 4] {
    [
        FinalSelectorEntry::new(M31::from_u32_unchecked(0), M31::from_u32_unchecked(0)),
        FinalSelectorEntry::new(M31::from_u32_unchecked(1), M31::from_u32_unchecked(0)),
        FinalSelectorEntry::new(M31::from_u32_unchecked(0), M31::from_u32_unchecked(1)),
        FinalSelectorEntry::new(M31::from_u32_unchecked(1), M31::from_u32_unchecked(1)),
    ]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelectorLookupError {
    InvalidSelector4x4(Selector4x4Entry),
    Selector16OutOfRange {
        selector: M31,
    },
    InvalidSelector16Decode {
        actual: Selector16DecodeEntry,
        expected: Selector16DecodeEntry,
    },
    InvalidFinalSelector(FinalSelectorEntry),
}

fn decode_selector16(selector: u32) -> Option<(u32, u32)> {
    Some(match selector {
        0 => (7, 1),
        1 => (6, 1),
        2 => (5, 0),
        3 => (4, 0),
        4 => (3, 1),
        5 => (2, 1),
        6 => (1, 0),
        7 => (0, 0),
        8 => (0, 1),
        9 => (1, 1),
        10 => (2, 0),
        11 => (3, 0),
        12 => (4, 1),
        13 => (5, 1),
        14 => (6, 0),
        15 => (7, 0),
        _ => return None,
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

    fn build_selectors() -> (
        PublicEcdsaInputClaim,
        ScalarSetupClaim,
        FakeGlvSelectorClaim,
    ) {
        let public_claim = PublicEcdsaInputClaim::from_inputs(&[test_input(42, 77, 1)]);
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
    fn selector_tables_have_expected_shapes() {
        assert_eq!(selector4x4_table().len(), 16);
        assert_eq!(selector16_decode_table().len(), 16);
        assert_eq!(final_selector_table().len(), 4);
        assert_eq!(selector16_decode_table()[0].base_index.0, 7);
        assert_eq!(selector16_decode_table()[0].neg_bit.0, 1);
        assert_eq!(selector16_decode_table()[15].base_index.0, 7);
        assert_eq!(selector16_decode_table()[15].neg_bit.0, 0);
        assert_eq!(final_selector_table()[3].selector_final.0, 10);
        assert_eq!(final_selector_table()[3].init_base_index.0, 7);
    }

    #[test]
    fn selector_requests_from_reconstruction_balance_provider_multiplicities() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let audit = SelectorLookupAudit::balanced_for_requests(&requests).expect("valid audit");

        assert_eq!(requests.final_selector.len(), 2);
        assert_eq!(
            requests.expected_selector4x4_uses(),
            2 * FAKE_GLV_SELECTOR_CHUNKS
        );
        assert_eq!(requests.selector4x4.len(), 2 * FAKE_GLV_SELECTOR_CHUNKS);
        assert_eq!(
            requests.selector16_decode.len(),
            2 * FAKE_GLV_SELECTOR_CHUNKS
        );
        assert!(audit.is_balanced());
    }

    #[test]
    fn selector_lookup_logup_sums_balance() {
        let (_, _, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let relations = FakeGlvSelectorLookupRelations::dummy();
        let providers = selector_lookup_provider_claimed_sum(&requests, &relations);
        let consumers = selector_lookup_consumer_claimed_sum(&requests, &relations);

        assert_eq!(
            providers + consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn selector_lookup_e2e_preserves_public_balance() {
        let relation = PublicEcdsaInstanceRelation::dummy();
        let (public_claim, scalar_setup, selectors) = build_selectors();
        let requests =
            SelectorLookupRequests::from_selector_claim(&selectors).expect("valid requests");
        let audit = SelectorLookupAudit::balanced_for_requests(&requests).expect("valid audit");
        let public_interaction = public_claim.initial_logup_claim(&relation);
        let vm_consumers =
            public_ecdsa_consumer_claimed_sum(&scalar_setup.public_consumers(), &relation);

        scalar_setup.verify().expect("scalar setup verifies");
        assert!(audit.is_balanced());
        assert_eq!(
            public_interaction.claimed_sum + vm_consumers,
            SecureField::from(M31::from_u32_unchecked(0))
        );
    }

    #[test]
    fn selector_lookup_rejects_invalid_decode_entry() {
        let actual = Selector16DecodeEntry {
            selector: M31::from_u32_unchecked(10),
            base_index: M31::from_u32_unchecked(7),
            neg_bit: M31::from_u32_unchecked(0),
        };

        let err = actual.verify().expect_err("wrong decode must fail");

        assert!(matches!(
            err,
            SelectorLookupError::InvalidSelector16Decode { .. }
        ));
    }

    #[test]
    fn selector_lookup_rejects_invalid_final_selector_entry() {
        let entry = FinalSelectorEntry {
            s1_msb: M31::from_u32_unchecked(1),
            s2_msb: M31::from_u32_unchecked(1),
            selector_final: M31::from_u32_unchecked(9),
            init_base_index: M31::from_u32_unchecked(7),
        };

        let err = entry.verify().expect_err("wrong final selector must fail");

        assert!(matches!(err, SelectorLookupError::InvalidFinalSelector(_)));
    }
}
