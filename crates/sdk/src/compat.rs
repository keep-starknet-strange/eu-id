//! Wallet-facing UniFFI compatibility types and pure contract helpers.

const SYSTEM_NAME: &str = "stwo-euid-v1";
const SPEC_ID_PID: &str = "stwo-euid-pid-v1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum PredicateMode {
    Age,
    Nat,
    And,
    Or,
}

impl PredicateMode {
    pub(crate) fn as_token(self) -> &'static str {
        match self {
            Self::Age => "age",
            Self::Nat => "nat",
            Self::And => "and",
            Self::Or => "or",
        }
    }

    pub(crate) fn from_token(token: &str) -> Option<Self> {
        match token {
            "age" => Some(Self::Age),
            "nat" => Some(Self::Nat),
            "and" => Some(Self::And),
            "or" => Some(Self::Or),
            _ => None,
        }
    }

    pub(crate) fn uses_age(self) -> bool {
        matches!(self, Self::Age | Self::And | Self::Or)
    }

    pub(crate) fn uses_nat(self) -> bool {
        matches!(self, Self::Nat | Self::And | Self::Or)
    }
}

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum NatMode {
    Any,
}

#[derive(uniffi::Enum, Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkSystemKind {
    P256,
    MlDsa,
}

#[derive(uniffi::Enum, Clone, Debug, PartialEq, Eq)]
pub enum IssuerKey {
    P256 { x: Vec<u8>, y: Vec<u8> },
    MlDsa { pk_hash: Vec<u8> },
}

#[derive(uniffi::Enum, Clone, Debug)]
pub enum TrustedIssuers {
    Certificates(Vec<Vec<u8>>),
    PublicKeys(Vec<Vec<u8>>),
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct ProductPublicStatementV1 {
    pub spec_id: String,
    pub version: u32,
    pub doctype: String,
    pub namespace: String,
    pub issuer_key: IssuerKey,
    pub today_epoch_day: i32,
    pub nonce: Vec<u8>,
    pub predicate_mode: PredicateMode,
    pub age_threshold_years: Option<u32>,
    pub accepted_numeric_countries: Option<Vec<u32>>,
    pub nat_mode: NatMode,
}

#[derive(uniffi::Record, Clone, Debug)]
pub struct ProductMdocWitnessV1 {
    pub document: Vec<u8>,
    pub trusted_issuers: TrustedIssuers,
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct IdentityStatement {
    pub circuit_hash: Vec<u8>,
    pub zk_system_id: String,
    pub document_type: String,
    pub namespace: String,
    pub element_identifier: String,
    pub expected_value_cbor: Vec<u8>,
    pub timestamp_epoch_seconds: i64,
    pub session_transcript: Vec<u8>,
    pub trusted_issuer_public_key: Vec<u8>,
    pub revocation_public_key: Vec<u8>,
    pub revocation_epoch: u32,
}

#[derive(uniffi::Record, Clone)]
pub struct IdentityWitness {
    pub document: Vec<u8>,
    pub revocation_id_lo: u64,
    pub revocation_id_hi: u64,
    pub revocation_signature: Vec<u8>,
}

#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct DemoRevocationWitness {
    pub id_lo: u64,
    pub id_hi: u64,
    pub signature: Vec<u8>,
}

#[derive(uniffi::Record, Clone, Debug)]
pub struct ZkContract {
    pub system_name: String,
    pub spec_id_pid: String,
    pub pid_namespace: String,
    pub doctype_pid: String,
    pub element_birth_date: String,
    pub element_nationality: String,
    pub param_predicate_mode: String,
    pub param_min_age: String,
    pub param_accepted_countries: String,
    pub param_nat_mode: String,
    pub param_version: String,
    pub param_num_attributes: String,
    pub param_circuit_hash: String,
    pub result_nat_in_set: String,
}

#[derive(uniffi::Enum, Clone, Debug)]
pub enum ZkPublicStatement {
    ProductV1(ProductPublicStatementV1),
    Ts13DemoV1(IdentityStatement),
    ProductV2(crate::ProductPublicStatementV2),
}

#[derive(uniffi::Enum, Clone)]
pub enum ZkMdocWitness {
    ProductV1(ProductMdocWitnessV1),
    Ts13DemoV1(IdentityWitness),
    ProductV2(crate::ProductMdocWitnessV2),
}

#[uniffi::export]
pub fn zk_contract_v1() -> ZkContract {
    ZkContract {
        system_name: SYSTEM_NAME.to_string(),
        spec_id_pid: SPEC_ID_PID.to_string(),
        pid_namespace: PID_NAMESPACE.to_string(),
        doctype_pid: PID_DOCTYPE.to_string(),
        element_birth_date: "birth_date".to_string(),
        element_nationality: "nationality".to_string(),
        param_predicate_mode: "predicate_mode".to_string(),
        param_min_age: "min_age".to_string(),
        param_accepted_countries: "accepted_countries".to_string(),
        param_nat_mode: "nat_mode".to_string(),
        param_version: "version".to_string(),
        param_num_attributes: "num_attributes".to_string(),
        param_circuit_hash: "circuit_hash".to_string(),
        result_nat_in_set: "nationality_in_set".to_string(),
    }
}

#[uniffi::export]
pub fn result_age_over(min_age: u32) -> String {
    format!("age_over_{min_age}")
}

#[uniffi::export]
pub fn predicate_mode_from_token(token: String) -> Option<PredicateMode> {
    PredicateMode::from_token(&token)
}

#[uniffi::export]
pub fn predicate_mode_token(mode: PredicateMode) -> String {
    mode.as_token().to_string()
}

#[uniffi::export]
pub fn predicate_mode_uses_age(mode: PredicateMode) -> bool {
    mode.uses_age()
}

#[uniffi::export]
pub fn predicate_mode_uses_nat(mode: PredicateMode) -> bool {
    mode.uses_nat()
}

#[uniffi::export]
pub fn nat_mode_token(mode: NatMode) -> String {
    match mode {
        NatMode::Any => "any".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contract_and_helpers_match_the_wallet_abi() {
        let contract = zk_contract_v1();
        assert_eq!(
            [
                contract.system_name.as_str(),
                contract.spec_id_pid.as_str(),
                contract.pid_namespace.as_str(),
                contract.doctype_pid.as_str(),
                contract.element_birth_date.as_str(),
                contract.element_nationality.as_str(),
                contract.param_predicate_mode.as_str(),
                contract.param_min_age.as_str(),
                contract.param_accepted_countries.as_str(),
                contract.param_nat_mode.as_str(),
                contract.param_version.as_str(),
                contract.param_num_attributes.as_str(),
                contract.param_circuit_hash.as_str(),
                contract.result_nat_in_set.as_str(),
            ],
            [
                "stwo-euid-v1",
                "stwo-euid-pid-v1",
                "eu.europa.ec.eudi.pid.1",
                "eu.europa.ec.eudi.pid.1",
                "birth_date",
                "nationality",
                "predicate_mode",
                "min_age",
                "accepted_countries",
                "nat_mode",
                "version",
                "num_attributes",
                "circuit_hash",
                "nationality_in_set",
            ]
        );

        for (mode, token, uses_age, uses_nat) in [
            (PredicateMode::Age, "age", true, false),
            (PredicateMode::Nat, "nat", false, true),
            (PredicateMode::And, "and", true, true),
            (PredicateMode::Or, "or", true, true),
        ] {
            assert_eq!(predicate_mode_from_token(token.to_string()), Some(mode));
            assert_eq!(predicate_mode_token(mode), token);
            assert_eq!(predicate_mode_uses_age(mode), uses_age);
            assert_eq!(predicate_mode_uses_nat(mode), uses_nat);
        }
        assert_eq!(predicate_mode_from_token("unknown".to_string()), None);
        assert_eq!(nat_mode_token(NatMode::Any), "any");
        assert_eq!(result_age_over(18), "age_over_18");
    }

    #[test]
    fn tagged_variants_preserve_the_wallet_payload_shapes() {
        let product_statement = ProductPublicStatementV1 {
            spec_id: SPEC_ID_PID.to_string(),
            version: 1,
            doctype: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            issuer_key: IssuerKey::P256 {
                x: vec![1],
                y: vec![2],
            },
            today_epoch_day: 20_000,
            nonce: vec![3],
            predicate_mode: PredicateMode::Age,
            age_threshold_years: Some(18),
            accepted_numeric_countries: None,
            nat_mode: NatMode::Any,
        };
        let product_witness = ProductMdocWitnessV1 {
            document: vec![4],
            trusted_issuers: TrustedIssuers::Certificates(vec![vec![5]]),
        };
        let identity_statement = IdentityStatement {
            circuit_hash: vec![6],
            zk_system_id: SYSTEM_NAME.to_string(),
            document_type: PID_DOCTYPE.to_string(),
            namespace: PID_NAMESPACE.to_string(),
            element_identifier: result_age_over(18),
            expected_value_cbor: vec![0xf5],
            timestamp_epoch_seconds: 1,
            session_transcript: vec![7],
            trusted_issuer_public_key: vec![8],
            revocation_public_key: vec![9],
            revocation_epoch: 17,
        };
        let identity_witness = IdentityWitness {
            document: vec![10],
            revocation_id_lo: 11,
            revocation_id_hi: 12,
            revocation_signature: vec![13],
        };

        assert!(matches!(
            ZkPublicStatement::ProductV1(product_statement),
            ZkPublicStatement::ProductV1(ProductPublicStatementV1 { version: 1, .. })
        ));
        assert!(matches!(
            ZkMdocWitness::ProductV1(product_witness),
            ZkMdocWitness::ProductV1(ProductMdocWitnessV1 { document, .. }) if document == [4]
        ));
        assert!(matches!(
            ZkPublicStatement::Ts13DemoV1(identity_statement),
            ZkPublicStatement::Ts13DemoV1(IdentityStatement {
                revocation_epoch: 17,
                ..
            })
        ));
        assert!(matches!(
            ZkMdocWitness::Ts13DemoV1(identity_witness),
            ZkMdocWitness::Ts13DemoV1(IdentityWitness {
                revocation_id_lo: 11,
                revocation_id_hi: 12,
                ..
            })
        ));

        let revocation = DemoRevocationWitness {
            id_lo: 14,
            id_hi: 15,
            signature: vec![16],
        };
        assert_eq!((revocation.id_lo, revocation.id_hi), (14, 15));
        let IssuerKey::MlDsa { pk_hash } = (IssuerKey::MlDsa { pk_hash: vec![17] }) else {
            unreachable!()
        };
        assert_eq!(pk_hash, [17]);

        let TrustedIssuers::PublicKeys(keys) = TrustedIssuers::PublicKeys(vec![vec![18]]) else {
            unreachable!()
        };
        assert_eq!(keys, [vec![18]]);
    }
}
