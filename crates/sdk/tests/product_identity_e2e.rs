//! Product SDK prove->verify regression for the real ML-DSA mdoc path.

use bzip2::read::BzDecoder;
use ciborium::value::Value;
use euid_zk_sdk::{
    prove_identity, verify_identity, IssuerKey, NatMode, PredicateMode, TrustedIssuers,
    ZkMdocWitness, ZkPublicStatement, ZkVerifyResult,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::io::Read;

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const PRODUCT_SPEC_ID: &str = "stwo-euid-pid-v1";
const PRODUCT_EPOCH_DAY: i32 = 20_637;
const PRODUCT_ENVELOPE_FORMAT_V7: u16 = 7;
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1_952;
const HIGH_BIRTH_DATE_DIGEST_ID: u64 = 0x1234;
const HIGH_NATIONALITY_DIGEST_ID: u64 = 0x4321;
const ISSUER_SIG_STRUCTURE_FRAGMENT_BYTES: usize = 64;
const PRIVATE_SIGNATURE_FRAGMENT_BYTES: usize = 64;
const PREPROCESSED_TREE_INDEX: usize = 0;
const PHASE2_MIN_STABLE_DEVICE_KEY_RUN_BYTES: usize = 32;

#[derive(Serialize, Deserialize)]
struct ProductProofEnvelopeForTest {
    envelope_format: u16,
    statement_bytes: Vec<u8>,
    mdoc_statement: eu_id_prover::MdocStatement,
    stark_proof: Vec<u8>,
}

fn encode_cbor(value: &Value) -> Vec<u8> {
    let mut encoded = Vec::new();
    ciborium::ser::into_writer(value, &mut encoded).expect("test CBOR serializes");
    encoded
}

fn exact_occurrence_count(haystack: &[u8], needle: &[u8]) -> usize {
    assert!(
        !needle.is_empty(),
        "exact stable/private region is non-empty"
    );
    haystack
        .windows(needle.len())
        .filter(|window| *window == needle)
        .count()
}

fn map_text_entry<'a>(entries: &'a [(Value, Value)], key: &str) -> &'a Value {
    entries
        .iter()
        .find_map(|(candidate, value)| match candidate {
            Value::Text(candidate) if candidate == key => Some(value),
            _ => None,
        })
        .unwrap_or_else(|| panic!("fixture CBOR map contains {key}"))
}

fn issuer_mso(issuer_sig_structure: &[u8]) -> Vec<u8> {
    let value: Value = ciborium::de::from_reader(issuer_sig_structure)
        .expect("issuer Sig_structure is canonical CBOR");
    let Value::Array(parts) = value else {
        panic!("issuer Sig_structure is a CBOR array");
    };
    let Some(Value::Bytes(mso)) = parts.get(3) else {
        panic!("issuer Sig_structure carries an MSO byte string");
    };
    mso.clone()
}

fn high_digest_id_context(mso: &[u8], digest_id: u64) -> Vec<u8> {
    let value: Value = ciborium::de::from_reader(mso).expect("fixture MSO is canonical CBOR");
    let Value::Map(mso_entries) = value else {
        panic!("fixture MSO is a CBOR map");
    };
    let Value::Map(value_digest_namespaces) = map_text_entry(&mso_entries, "valueDigests") else {
        panic!("fixture valueDigests is a CBOR map");
    };
    let Value::Map(pid_value_digests) = map_text_entry(value_digest_namespaces, PID_NAMESPACE)
    else {
        panic!("fixture PID valueDigests namespace is a CBOR map");
    };
    let digest = pid_value_digests
        .iter()
        .find_map(|(candidate, digest)| {
            let Value::Integer(candidate) = candidate else {
                return None;
            };
            (i128::from(*candidate) == i128::from(digest_id)).then_some(digest)
        })
        .unwrap_or_else(|| panic!("fixture contains high digest ID {digest_id:#x}"));
    let Value::Bytes(digest) = digest else {
        panic!("fixture valueDigest is a byte string");
    };
    assert_eq!(digest.len(), 32, "fixture valueDigest is SHA-256");

    let mut context = encode_cbor(&Value::from(digest_id));
    context.extend(encode_cbor(&Value::Bytes(digest.clone())));
    assert_eq!(
        exact_occurrence_count(mso, &context),
        1,
        "high digest-ID key and its selected digest form one exact MSO context"
    );
    context
}

fn decode_inner_proof(
    envelope: &ProductProofEnvelopeForTest,
) -> (Vec<u8>, eu_id_prover::MdocProof) {
    let mut decoder = BzDecoder::new(envelope.stark_proof.as_slice());
    let mut raw_bincode = Vec::new();
    decoder
        .read_to_end(&mut raw_bincode)
        .expect("inner product proof decompresses");
    let proof =
        bincode::deserialize(&raw_bincode).expect("decompressed product STARK proof decodes");
    (raw_bincode, proof)
}

fn assert_exact_envelope_segmentation(wire: &[u8], envelope: &ProductProofEnvelopeForTest) {
    let mut segmented =
        bincode::serialize(&envelope.envelope_format).expect("envelope format serializes");
    segmented.extend(
        bincode::serialize(&envelope.statement_bytes).expect("public statement bytes serialize"),
    );
    segmented
        .extend(bincode::serialize(&envelope.mdoc_statement).expect("mdoc statement serializes"));
    segmented.extend(
        bincode::serialize(&envelope.stark_proof).expect("compressed STARK proof serializes"),
    );
    assert_eq!(
        wire, segmented,
        "fingerprint analysis covers every serialized envelope byte"
    );
}

fn zero_unique_region(bytes: &[u8], region: &[u8], name: &str) -> Vec<u8> {
    assert_eq!(
        exact_occurrence_count(bytes, region),
        1,
        "{name} must occupy one exact serialized region"
    );
    let offset = bytes
        .windows(region.len())
        .position(|window| window == region)
        .expect("unique region offset exists");
    let mut normalized = bytes.to_vec();
    normalized[offset..offset + region.len()].fill(0);
    normalized
}

fn normalized_public_regions(
    envelope: &ProductProofEnvelopeForTest,
    session_transcript: &[u8],
    device_sig_structure: &[u8],
) -> (Vec<u8>, Vec<u8>) {
    let statement_bytes = zero_unique_region(
        &envelope.statement_bytes,
        session_transcript,
        "verifier nonce",
    );
    let serialized_mdoc_statement =
        bincode::serialize(&envelope.mdoc_statement).expect("mdoc statement serializes");
    let mdoc_statement = zero_unique_region(
        &serialized_mdoc_statement,
        device_sig_structure,
        "public DeviceAuthentication Sig_structure",
    );
    (statement_bytes, mdoc_statement)
}

fn serialized<T: Serialize>(value: &T, name: &str) -> Vec<u8> {
    bincode::serialize(value).unwrap_or_else(|error| panic!("{name} serializes: {error}"))
}

fn assert_same_credential_stability_rule<T: Serialize>(
    name: &str,
    same_credential_a: &T,
    same_credential_b: &T,
    different_credential: &T,
) {
    let a = serialized(same_credential_a, name);
    let b = serialized(same_credential_b, name);
    if a == b {
        assert_eq!(
            a,
            serialized(different_credential, name),
            "{name} is stable across nonce changes but identifies the credential"
        );
    }
}

fn assert_inner_proof_stability(
    same_credential_a: &eu_id_prover::MdocProof,
    same_credential_b: &eu_id_prover::MdocProof,
    different_credential: &eu_id_prover::MdocProof,
) {
    let a = &same_credential_a.stark_proof.0;
    let b = &same_credential_b.stark_proof.0;
    let different = &different_credential.stark_proof.0;
    assert_eq!(a.commitments.len(), b.commitments.len());
    assert_eq!(a.commitments.len(), different.commitments.len());
    assert!(
        a.commitments.len() > PREPROCESSED_TREE_INDEX,
        "product proof has a tree-0 preprocessing commitment"
    );

    let tree_zero_a = serialized(
        &a.commitments[PREPROCESSED_TREE_INDEX],
        "same-credential tree zero A",
    );
    assert_eq!(
        tree_zero_a,
        serialized(
            &b.commitments[PREPROCESSED_TREE_INDEX],
            "same-credential tree zero B"
        ),
        "tree zero is independent of the verifier nonce"
    );
    assert_eq!(
        tree_zero_a,
        serialized(
            &different.commitments[PREPROCESSED_TREE_INDEX],
            "different-credential tree zero"
        ),
        "tree zero depends only on public resource shape, never credential facts"
    );

    for index in 0..a.commitments.len() {
        assert_same_credential_stability_rule(
            &format!("STARK commitment tree {index}"),
            &a.commitments[index],
            &b.commitments[index],
            &different.commitments[index],
        );
    }
    for (role, a_claims, b_claims, different_claims) in [
        (
            "issuer ML-DSA claims",
            &same_credential_a.mldsa,
            &same_credential_b.mldsa,
            &different_credential.mldsa,
        ),
        (
            "device ML-DSA claims",
            &same_credential_a.device_mldsa,
            &same_credential_b.device_mldsa,
            &different_credential.device_mldsa,
        ),
        (
            "revocation ML-DSA claims",
            &same_credential_a.revocation_mldsa,
            &same_credential_b.revocation_mldsa,
            &different_credential.revocation_mldsa,
        ),
    ] {
        assert_same_credential_stability_rule(role, a_claims, b_claims, different_claims);
    }
    assert_same_credential_stability_rule(
        "Keccak service claimed sums",
        &same_credential_a.keccak_service_claimed_sums,
        &same_credential_b.keccak_service_claimed_sums,
        &different_credential.keccak_service_claimed_sums,
    );
    assert_eq!(
        same_credential_a.post_interaction_payloads.len(),
        same_credential_b.post_interaction_payloads.len()
    );
    assert_eq!(
        same_credential_a.post_interaction_payloads.len(),
        different_credential.post_interaction_payloads.len()
    );
    for index in 0..same_credential_a.post_interaction_payloads.len() {
        assert_same_credential_stability_rule(
            &format!("post-interaction payload {index}"),
            &same_credential_a.post_interaction_payloads[index],
            &same_credential_b.post_interaction_payloads[index],
            &different_credential.post_interaction_payloads[index],
        );
    }
}

fn assert_phase1_stable_region_whitelist(
    envelopes: &[&[u8]],
    fixture: &mldsa_fixture::MldsaFullPqFixture,
) {
    let phase1_stable_region_whitelist: [(&str, &[u8]); 2] = [
        // U7/U9: the full device public key remains public in Phase 1. This
        // exact entry is removed when private device-key binding lands.
        ("1,952-byte device public key", fixture.device_pk.as_slice()),
        // Permanent: verifier trust selection requires the issuer trust key.
        ("issuer trust key", fixture.issuer_pk.as_slice()),
    ];
    assert_eq!(
        phase1_stable_region_whitelist.len(),
        2,
        "Phase-1 stable regions are an exact, source-enumerated list"
    );
    assert_eq!(
        phase1_stable_region_whitelist[0].1.len(),
        ML_DSA_65_PUBLIC_KEY_BYTES
    );
    assert_eq!(
        phase1_stable_region_whitelist[1].1.len(),
        ML_DSA_65_PUBLIC_KEY_BYTES
    );

    for (presentation_index, envelope) in envelopes.iter().enumerate() {
        for (name, exact_region) in phase1_stable_region_whitelist {
            assert_eq!(
                exact_occurrence_count(envelope, exact_region),
                1,
                "presentation {presentation_index} must serialize exactly one explicitly \
                 whitelisted {name}"
            );
        }
    }
}

fn assert_private_markers_absent(
    wire: &[u8],
    decompressed_inner_proof: &[u8],
    fixture: &mldsa_fixture::MldsaFullPqFixture,
    private_birth_date: &[u8],
    private_nationality_item_fragment: &[u8],
    private_random: &[u8],
) {
    let mso = issuer_mso(&fixture.issuer_sig_structure);
    let high_birth_date_digest_context = high_digest_id_context(&mso, HIGH_BIRTH_DATE_DIGEST_ID);
    let high_nationality_digest_context = high_digest_id_context(&mso, HIGH_NATIONALITY_DIGEST_ID);
    let issuer_sig_structure_fragment =
        &fixture.issuer_sig_structure[..ISSUER_SIG_STRUCTURE_FRAGMENT_BYTES];
    let issuer_signature_fragment = &fixture.issuer_signature[..PRIVATE_SIGNATURE_FRAGMENT_BYTES];
    let device_signature_fragment = &fixture.device_signature[..PRIVATE_SIGNATURE_FRAGMENT_BYTES];

    for (name, marker) in [
        ("full MSO run", mso.as_slice()),
        (
            "credential-selected high birth-date digest-ID context",
            high_birth_date_digest_context.as_slice(),
        ),
        (
            "credential-selected high nationality digest-ID context",
            high_nationality_digest_context.as_slice(),
        ),
        (
            "issuer Sig_structure fragment",
            issuer_sig_structure_fragment,
        ),
        ("issuer signature fragment", issuer_signature_fragment),
        ("device signature fragment", device_signature_fragment),
        ("private birth date", private_birth_date),
        (
            "private nationality item fragment",
            private_nationality_item_fragment,
        ),
        ("private IssuerSignedItem randomizer", private_random),
        ("validFrom timestamp", b"2026-01-01T00:00:00Z"),
        ("validUntil timestamp", b"2030-01-01T00:00:00Z"),
        ("serialized validity result field", b"valid_today"),
    ] {
        assert!(
            !wire.windows(marker.len()).any(|window| window == marker),
            "product wire envelope must not contain {name}"
        );
        assert!(
            !decompressed_inner_proof
                .windows(marker.len())
                .any(|window| window == marker),
            "decompressed inner proof must not contain {name}"
        );
    }
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
        ts13_request: None,
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

fn signature_witness_markers(
    role: &str,
    input: &stwo_mldsa::MlDsaVerifyInput,
) -> Vec<(String, Vec<u8>)> {
    let z = input.z.iter().flatten().copied().collect::<Vec<_>>();
    let hint = input.hint.iter().flatten().copied().collect::<Vec<_>>();
    vec![
        (
            format!("{role} c_tilde"),
            bincode::serialize(input.c_tilde.as_slice()).expect("c_tilde marker serializes"),
        ),
        (
            format!("{role} z"),
            bincode::serialize(&z).expect("z marker serializes"),
        ),
        (
            format!("{role} hint"),
            bincode::serialize(&hint).expect("hint marker serializes"),
        ),
    ]
}

#[test]
fn product_identity_real_proof_verifies_and_rejects_relabels_and_stark_tamper() {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-product-identity-session");
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
    let extraction_request = eu_id_prover::MdocPidRequest {
        doctype: PID_DOCTYPE.to_string(),
        namespace: PID_NAMESPACE.to_string(),
        attributes: vec![
            eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: "birth_date".to_string(),
                mode: eu_id_prover::mdoc::MdocDisclosureMode::AgeOver,
            },
            eu_id_prover::mdoc::MdocRequestedAttribute {
                element_identifier: "nationality".to_string(),
                mode: eu_id_prover::mdoc::MdocDisclosureMode::Alpha2Set,
            },
        ],
        birth_date_element: "birth_date".to_string(),
        nationality_element: "nationality".to_string(),
        session_transcript: session_transcript.clone(),
        trusted_mldsa_issuer_public_keys: vec![fixture.issuer_pk.clone()],
        device_authentication_profile:
            eu_id_prover::mdoc::MdocDeviceAuthenticationProfile::Iso180135,
    };
    let extracted = eu_id_prover::mdoc::extract_pid_mdoc(&fixture.document, &extraction_request)
        .expect("product fixture extracts");
    let signature_witness_markers = [
        (
            "issuer",
            extracted
                .issuer_auth_input
                .as_mldsa()
                .expect("ML-DSA issuer"),
        ),
        (
            "device",
            extracted
                .device_auth_input
                .as_mldsa()
                .expect("ML-DSA device"),
        ),
    ]
    .into_iter()
    .flat_map(|(role, input)| signature_witness_markers(role, input))
    .collect::<Vec<_>>();
    let private_issuer_input = extracted.issuer_auth_input;
    let private_device_input = extracted.device_auth_input;
    let statement = product_statement(session_transcript, &fixture.issuer_pk);
    let (revocation_pk, revocation_signature) = mldsa_fixture::mldsa_revocation_fixture(1, 2, 7);
    assert_eq!(revocation_pk, fixture.revocation_pk);
    let issuer_signature = fixture.issuer_signature.clone();
    let device_signature = fixture.device_signature.clone();
    let witness = ZkMdocWitness {
        document: fixture.document,
        trusted_issuers: TrustedIssuers::PublicKeys(vec![fixture.issuer_pk]),
        ts13_trusted_issuer_public_keys: None,
        ts13_revocation_id_lo: None,
        ts13_revocation_id_hi: None,
        ts13_revocation_signature: None,
    };

    let proof = prove_identity(statement.clone(), witness).expect("product proof builds");
    let product_envelope: ProductProofEnvelopeForTest =
        bincode::deserialize(&proof).expect("product proof envelope decodes");
    assert_eq!(
        product_envelope.envelope_format, PRODUCT_ENVELOPE_FORMAT_V7,
        "product envelope tag must remain byte-compatible"
    );
    assert!(
        verify_identity(statement.clone(), proof.clone())
            .expect("product verification runs")
            .ok,
        "real product proof must verify"
    );

    // The age/nationality predicates prove facts ABOUT the birth date and
    // nationality; neither value may travel to the verifier. `prove_mdoc`
    // ships `MdocCircuitStatement::public_view()` for exactly this reason.
    for (name, secret) in [
        ("birth_date", b"1990-07-15".as_slice()),
        ("nationality", b"cDE".as_slice()),
    ] {
        assert!(
            !proof.windows(secret.len()).any(|window| window == secret),
            "product identity envelope must not contain the credential's {name}"
        );
    }
    for (name, signature) in [
        ("issuer", issuer_signature.as_slice()),
        ("device", device_signature.as_slice()),
    ] {
        assert!(
            !proof
                .windows(signature.len())
                .any(|window| window == signature),
            "product identity envelope must not contain the raw {name} signature"
        );
        assert!(
            !proof
                .windows(stwo_mldsa::constants::C_TILDE_BYTES)
                .any(|window| window == &signature[..stwo_mldsa::constants::C_TILDE_BYTES]),
            "product identity envelope must not contain the {name} c_tilde witness"
        );
    }
    for (name, marker) in &signature_witness_markers {
        assert!(
            !proof
                .windows(marker.len())
                .any(|window| window == marker.as_slice()),
            "product identity envelope must not contain the serialized {name} witness"
        );
    }

    let public_envelope: ProductProofEnvelopeForTest =
        bincode::deserialize(&proof).expect("product proof envelope decodes");
    for (name, input) in [
        ("issuer", &public_envelope.mdoc_statement.issuer_input),
        ("device", &public_envelope.mdoc_statement.device_input),
    ] {
        let input = input.as_mldsa().expect("product role is ML-DSA");
        assert!(
            input.c_tilde.iter().all(|&value| value == 0)
                && input.z.iter().flatten().all(|&value| value == 0)
                && input.hint.iter().flatten().all(|&value| value == 0),
            "product verifier statement must zero the {name} signature witness"
        );
    }
    let private_inputs = [
        ("issuer", &private_issuer_input),
        ("device", &private_device_input),
    ];
    for (name, marker) in &signature_witness_markers {
        assert!(
            private_inputs.iter().any(|(_, input)| {
                let serialized = bincode::serialize(input).expect("private auth input serializes");
                serialized
                    .windows(marker.len())
                    .any(|window| window == marker.as_slice())
            }),
            "pre-scrub control envelope must contain the serialized {name} witness"
        );
    }
    let d2_envelope_bytes_delta = private_inputs
        .iter()
        .map(|(_, input)| {
            let input = input.as_mldsa().expect("ML-DSA private auth input");
            let public_input = (input.encode_pk(), input.message.clone());
            bincode::serialized_size(input).expect("private auth input size") as usize
                - bincode::serialized_size(&public_input).expect("public auth input size") as usize
        })
        .sum::<usize>();
    eprintln!("d2_envelope_bytes_delta={d2_envelope_bytes_delta}");
    assert!(
        d2_envelope_bytes_delta >= 7 * 1024,
        "signature scrub must save at least the expected ~7 KiB"
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

#[test]
#[ignore = "U9 Phase-2 gate: the device public key is intentionally public in Phase 1"]
fn product_phase2_u9_device_key_whitelist_is_empty_and_envelope_has_no_stable_run() {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"sdk-product-phase2-u9-gate");
    let fixture = mldsa_fixture::mldsa_high_digest_id_fixture_with_transcript(&session_transcript);
    let statement = product_statement(session_transcript, &fixture.issuer_pk);
    let device_public_key = fixture.device_pk.clone();
    let proof = prove_identity(
        statement,
        ZkMdocWitness {
            document: fixture.document,
            trusted_issuers: TrustedIssuers::PublicKeys(vec![fixture.issuer_pk]),
            ts13_trusted_issuer_public_keys: None,
            ts13_revocation_id_lo: None,
            ts13_revocation_id_hi: None,
            ts13_revocation_signature: None,
        },
    )
    .expect("U9 product gate proof builds");

    let phase2_device_key_stable_region_whitelist = Vec::<&[u8]>::new();
    assert!(
        phase2_device_key_stable_region_whitelist.is_empty(),
        "Phase-2 device-key stable-region whitelist must be empty"
    );
    let leaked_device_key_offset = device_public_key
        .windows(PHASE2_MIN_STABLE_DEVICE_KEY_RUN_BYTES)
        .position(|run| proof.windows(run.len()).any(|window| window == run));
    assert!(
        leaked_device_key_offset.is_none(),
        "serialized product envelope contains a device-key run of at least \
         {PHASE2_MIN_STABLE_DEVICE_KEY_RUN_BYTES} bytes beginning at device-key offset {}",
        leaked_device_key_offset.unwrap_or_default()
    );
}
