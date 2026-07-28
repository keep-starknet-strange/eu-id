//! Product SDK prove->verify regression for the real ML-DSA mdoc path.

use euid_zk_sdk::{
    prove_identity, verify_identity, IssuerKey, NatMode, PredicateMode, TrustedIssuers,
    ZkMdocWitness, ZkPublicStatement, ZkVerifyResult,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const PRODUCT_SPEC_ID: &str = "stwo-euid-pid-v1";
const PRODUCT_EPOCH_DAY: i32 = 20_637;

#[derive(Serialize, Deserialize)]
struct ProductProofEnvelopeForTest {
    envelope_format: u16,
    statement_bytes: Vec<u8>,
    mdoc_statement: eu_id_prover::MdocStatement,
    stark_proof: Vec<u8>,
}

fn product_statement(session_transcript: Vec<u8>, issuer_pk: &[u8]) -> ZkPublicStatement {
    ZkPublicStatement {
        spec_id: PRODUCT_SPEC_ID.to_string(),
        version: 1,
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        issuer_key: IssuerKey::MlDsa {
            pk_hash: Sha256::digest(issuer_pk).to_vec(),
        },
        today_epoch_day: PRODUCT_EPOCH_DAY,
        nonce: session_transcript,
        predicate_mode: PredicateMode::And,
        age_threshold_years: Some(18),
        accepted_numeric_countries: Some(vec![276, 250]),
        nat_mode: NatMode::Any,
    }
}

fn tamper_product_stark_proof(proof: &[u8]) -> Vec<u8> {
    let mut envelope: ProductProofEnvelopeForTest =
        bincode::deserialize(proof).expect("product proof envelope decodes in test");
    assert!(
        !envelope.stark_proof.is_empty(),
        "product envelope carries an inner STARK proof"
    );
    let tamper_index = envelope.stark_proof.len() / 2;
    envelope.stark_proof[tamper_index] ^= 0x01;
    bincode::serialize(&envelope).expect("tampered product proof envelope serializes")
}

fn add_ts13_revocation_to_product_statement(
    proof: &[u8],
    revocation_pk: Vec<u8>,
    revocation_signature: Vec<u8>,
) -> Vec<u8> {
    let mut envelope: ProductProofEnvelopeForTest =
        bincode::deserialize(proof).expect("product proof envelope decodes in test");
    envelope.mdoc_statement.ts13_revocation =
        Some(eu_id_prover::mdoc::MdocRevocationPublicInputs {
            revocation_public_key: eu_id_prover::mdoc::MdocRevocationKey::MlDsa(revocation_pk),
            epoch: 7,
        });
    envelope.mdoc_statement.ts13_revocation_signature = Some(
        eu_id_prover::mdoc::MdocRevocationSignature::MlDsa(revocation_signature),
    );
    bincode::serialize(&envelope).expect("revocation product envelope serializes")
}

fn assert_rejects(result: Result<ZkVerifyResult, euid_zk_sdk::ZkError>, context: &str) {
    if let Ok(result) = result {
        assert!(!result.ok, "{context}");
    }
}

#[test]
fn product_identity_real_proof_verifies_and_rejects_relabels_and_stark_tamper() {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-product-identity-session");
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
    let statement = product_statement(session_transcript, &fixture.issuer_pk);
    let (revocation_pk, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(1, 2, 7);
    assert_eq!(revocation_pk, fixture.revocation_pk);
    let witness = ZkMdocWitness {
        document: fixture.document,
        trusted_issuers: TrustedIssuers::PublicKeys(vec![fixture.issuer_pk]),
    };

    let proof = prove_identity(statement.clone(), witness).expect("product proof builds");
    assert!(
        verify_identity(statement.clone(), proof.clone())
            .expect("product verification runs")
            .ok,
        "real product proof must verify"
    );

    let mut relabeled = statement.clone();
    relabeled.spec_id.push_str("-relabeled");
    assert_rejects(
        verify_identity(relabeled, proof.clone()),
        "relabeled spec_id must reject",
    );

    let mut relabeled = statement.clone();
    relabeled.version += 1;
    assert_rejects(
        verify_identity(relabeled, proof.clone()),
        "relabeled version must reject",
    );

    let mut relabeled = statement.clone();
    relabeled.namespace.push_str(".relabeled");
    assert_rejects(
        verify_identity(relabeled, proof.clone()),
        "relabeled namespace must reject",
    );

    let revocation_bearing_product_envelope =
        add_ts13_revocation_to_product_statement(&proof, revocation_pk, revocation_signature);
    assert_rejects(
        verify_identity(statement.clone(), revocation_bearing_product_envelope),
        "product verifier must reject revocation-bearing TS13 statements",
    );

    let tampered = tamper_product_stark_proof(&proof);
    assert!(
        !verify_identity(statement, tampered)
            .expect("tampered product proof verification runs")
            .ok,
        "tampered product STARK proof must reject"
    );
}
