mod mldsa_fixture;

use eu_id_prover::mdoc::{
    MdocDeviceAuthenticationProfile, MdocDisclosureMode, MdocRequestedAttribute, MdocRevocationKey,
    MdocRevocationPublicInputs, MdocRevocationSignature,
};
use eu_id_prover::ts13_demo::{
    derive_public_context, Ts13DemoPublicContextInput, ML_DSA_65_PUBLIC_KEY_BYTES,
};
use eu_id_prover::{
    prove_mdoc_ts13_demo, verify_mdoc_ts13_demo, MdocPidRequest, MdocTs13DemoCircuitPublicInput,
};

const VERIFY_AT: i64 = 1_798_761_600; // 2027-01-01T00:00:00Z
const REVOCATION_EPOCH: u32 = 17;

fn request(transcript: Vec<u8>, issuer_public_key: Vec<u8>) -> MdocPidRequest {
    MdocPidRequest {
        doctype: "eu.europa.ec.eudi.pid.1".to_string(),
        namespace: "eu.europa.ec.eudi.pid.1".to_string(),
        attributes: vec![MdocRequestedAttribute {
            element_identifier: "age_over_18".to_string(),
            mode: MdocDisclosureMode::ValueEquality(vec![0xf5]),
        }],
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: transcript,
        trusted_mldsa_issuer_public_keys: vec![issuer_public_key],
        device_authentication_profile: MdocDeviceAuthenticationProfile::Iso180135,
    }
}

fn public_input(
    transcript: &[u8],
    issuer_public_key: &[u8],
    revocation_public_key: &[u8],
    zk_system_id: &str,
) -> MdocTs13DemoCircuitPublicInput {
    let circuit_hash = [0x42; 32];
    let derived = derive_public_context(Ts13DemoPublicContextInput {
        circuit_hash: &circuit_hash,
        zk_system_id,
        document_type: "eu.europa.ec.eudi.pid.1",
        namespace: "eu.europa.ec.eudi.pid.1",
        element_identifier: "age_over_18",
        expected_value_cbor: &[0xf5],
        timestamp_epoch_seconds: VERIFY_AT,
        session_transcript: transcript,
        trusted_issuer_public_key: issuer_public_key,
        revocation_public_key,
        revocation_epoch: REVOCATION_EPOCH,
    })
    .expect("public request context derives");
    MdocTs13DemoCircuitPublicInput {
        circuit_hash,
        request_context_digest: derived.request_context_digest,
        timestamp_epoch_seconds: VERIFY_AT,
        trusted_issuer_public_key: issuer_public_key.to_vec(),
        device_cose_sig_structure: derived.device_cose_sig_structure,
        revocation: MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(revocation_public_key.to_vec()),
            epoch: REVOCATION_EPOCH,
        },
    }
}

#[test]
fn ts13_unlinkable_demo_composed_proof_verifies_without_public_device_key() {
    std::thread::Builder::new()
        .name("ts13-demo-composed-test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let transcript =
                eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-demo-composed-proof");
            let fixture =
                mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript);
            assert_eq!(fixture.issuer_pk.len(), ML_DSA_65_PUBLIC_KEY_BYTES);
            assert_eq!(fixture.device_pk.len(), ML_DSA_65_PUBLIC_KEY_BYTES);
            let public = public_input(
                &transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                "rp-local-demo-a",
            );
            let request = request(transcript, fixture.issuer_pk);
            let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
            let id_lo = id.checked_sub(1).expect("fixture revocation id is nonzero");
            let id_hi = id.checked_add(1).expect("fixture revocation id is not max");
            let (_, revocation_signature) =
                mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, REVOCATION_EPOCH);

            let proof = prove_mdoc_ts13_demo(
                &fixture.document,
                &request,
                &public,
                id_lo,
                id_hi,
                MdocRevocationSignature::MlDsa(revocation_signature),
            )
            .expect("TS13 demo proves");
            assert!(proof.has_ts13_demo_shape());
            verify_mdoc_ts13_demo(&proof, &public).expect("TS13 demo verifies");
        })
        .expect("large-stack TS13 test thread starts")
        .join()
        .expect("large-stack TS13 test thread succeeds");
}
