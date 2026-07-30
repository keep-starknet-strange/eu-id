#[allow(dead_code)]
mod mldsa_fixture;

use ciborium::value::Value;
use eu_id_prover::mdoc::{
    extract_pid_mdoc, MdocCircuitStatement, MdocDeviceAuthenticationProfile, MdocDisclosureMode,
    MdocError, MdocPidRequest, MdocRequestedAttribute, MdocRevocationKey,
    MdocRevocationPublicInputs, MdocRevocationRangeWitness, MdocRevocationSignature,
    MdocTs13PublicStatement, TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY,
};
use eu_id_prover::ts13_demo::{
    derive_device_authentication, derive_public_context, ensure_device_cose_sig_structure_capacity,
    Ts13DemoContextError, Ts13DemoPublicContextInput, ML_DSA_65_PUBLIC_KEY_BYTES,
};
use eu_id_prover::{
    prove_mdoc_ts13_demo, verify_mdoc, verify_mdoc_ts13_demo, MdocTs13DemoCircuitPublicInput,
    Policy,
};
use ml_dsa::signature::Signer;
use ml_dsa::{EncodedSignature, MlDsa65, SigningKey};

const VERIFY_AT: i64 = 1_798_761_600; // 2027-01-01T00:00:00Z
const REVOCATION_EPOCH: u32 = 17;
const CIRCUIT_HASH: [u8; 32] = eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH;
const PID_SCOPE: &str = "eu.europa.ec.eudi.pid.1";
const AGE_OVER_18: &str = "age_over_18";

fn request(transcript: Vec<u8>, issuer_public_key: Vec<u8>) -> MdocPidRequest {
    MdocPidRequest {
        doctype: PID_SCOPE.to_string(),
        namespace: PID_SCOPE.to_string(),
        attributes: vec![MdocRequestedAttribute {
            element_identifier: AGE_OVER_18.to_string(),
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
    timestamp_epoch_seconds: i64,
) -> MdocTs13DemoCircuitPublicInput {
    let derived = derive_public_context(Ts13DemoPublicContextInput {
        circuit_hash: &CIRCUIT_HASH,
        zk_system_id,
        document_type: PID_SCOPE,
        namespace: PID_SCOPE,
        element_identifier: AGE_OVER_18,
        expected_value_cbor: &[0xf5],
        timestamp_epoch_seconds,
        session_transcript: transcript,
        trusted_issuer_public_key: issuer_public_key,
        revocation_public_key,
        revocation_epoch: REVOCATION_EPOCH,
    })
    .expect("public request context derives");
    MdocTs13DemoCircuitPublicInput {
        circuit_hash: CIRCUIT_HASH,
        request_context_digest: derived.request_context_digest,
        timestamp_epoch_seconds,
        verification_timestamp_rfc3339_utc: derived.verification_timestamp_rfc3339_utc,
        trusted_issuer_public_key: issuer_public_key.to_vec(),
        device_cose_sig_structure: derived.device_cose_sig_structure,
        revocation: MdocRevocationPublicInputs {
            revocation_public_key: MdocRevocationKey::MlDsa(revocation_public_key.to_vec()),
            epoch: REVOCATION_EPOCH,
        },
    }
}

fn demo_policy() -> Policy {
    Policy {
        current_date: predicates::Date {
            year: 2027,
            month: 1,
            day: 1,
        },
        min_age_years: 18,
        accepted_nationalities: Vec::new(),
    }
}

fn revocation_witness(mso: &[u8]) -> (u64, u64, MdocRevocationSignature) {
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(mso);
    let id_lo = id.checked_sub(1).expect("fixture revocation id is nonzero");
    let id_hi = id.checked_add(1).expect("fixture revocation id is not max");
    let (_, signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, REVOCATION_EPOCH);
    (id_lo, id_hi, MdocRevocationSignature::MlDsa(signature))
}

fn encode_value(value: &Value) -> Vec<u8> {
    let mut encoded = Vec::new();
    ciborium::ser::into_writer(value, &mut encoded).expect("test CBOR encodes");
    encoded
}

fn text_map_value_mut<'a>(value: &'a mut Value, key: &str) -> &'a mut Value {
    let Value::Map(entries) = value else {
        panic!("test fixture node is a map");
    };
    entries
        .iter_mut()
        .find_map(|(entry_key, value)| {
            (entry_key == &Value::Text(key.to_string())).then_some(value)
        })
        .unwrap_or_else(|| panic!("test fixture contains {key}"))
}

fn rewrite_validity(
    mut fixture: mldsa_fixture::MldsaFullPqFixture,
    valid_from: &str,
    valid_until: &str,
) -> mldsa_fixture::MldsaFullPqFixture {
    let original_mso_len = fixture.mso.len();
    let original_document_len = fixture.document.len();
    let mut mso: Value =
        ciborium::de::from_reader(fixture.mso.as_slice()).expect("fixture MSO decodes");
    let validity = text_map_value_mut(&mut mso, "validityInfo");
    *text_map_value_mut(validity, "validFrom") =
        Value::Tag(0, Box::new(Value::Text(valid_from.to_string())));
    *text_map_value_mut(validity, "validUntil") =
        Value::Tag(0, Box::new(Value::Text(valid_until.to_string())));
    let mso = encode_value(&mso);
    assert_eq!(mso.len(), original_mso_len, "fixed MSO shape is retained");

    let protected = vec![0xa1, 0x01, 0x38, 0x30];
    let issuer_sig_structure = encode_value(&Value::Array(vec![
        Value::Text("Signature1".to_string()),
        Value::Bytes(protected),
        Value::Bytes(Vec::new()),
        Value::Bytes(mso.clone()),
    ]));
    let issuer_key = SigningKey::<MlDsa65>::from_seed(&[0x5a; 32].into());
    let issuer_signature: EncodedSignature<MlDsa65> =
        issuer_key.sign(&issuer_sig_structure).encode();

    let mut document: Value =
        ciborium::de::from_reader(fixture.document.as_slice()).expect("fixture document decodes");
    let issuer_signed = text_map_value_mut(&mut document, "issuerSigned");
    let issuer_auth = text_map_value_mut(issuer_signed, "issuerAuth");
    let Value::Array(parts) = issuer_auth else {
        panic!("fixture issuerAuth is COSE_Sign1");
    };
    parts[2] = Value::Bytes(mso.clone());
    parts[3] = Value::Bytes(issuer_signature.to_vec());

    fixture.document = encode_value(&document);
    fixture.mso = mso;
    fixture.issuer_sig_structure = issuer_sig_structure;
    fixture.issuer_signature = issuer_signature.to_vec();
    assert_eq!(
        fixture.document.len(),
        original_document_len,
        "fixed document shape is retained"
    );
    fixture
}

fn transcript_for_device_message_len(target: usize) -> Vec<u8> {
    (0..=target)
        .find_map(|payload_len| {
            let transcript = encode_value(&Value::Array(vec![
                Value::Null,
                Value::Null,
                Value::Bytes(vec![0x5a; payload_len]),
            ]));
            (derive_device_authentication(&transcript)
                .ok()?
                .device_cose_sig_structure
                .len()
                == target)
                .then_some(transcript)
        })
        .unwrap_or_else(|| panic!("canonical transcript yielding {target} message bytes exists"))
}

#[test]
fn composed_demo_binds_every_context_role_and_profile_at_capacity() {
    std::thread::Builder::new()
        .name("ts13-demo-composed-test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let transcript =
                transcript_for_device_message_len(TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY);
            let fixture = rewrite_validity(
                mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript),
                "2026-12-31T23:59:59Z",
                "2027-01-01T00:00:01Z",
            );
            assert_eq!(fixture.issuer_pk.len(), ML_DSA_65_PUBLIC_KEY_BYTES);
            assert_eq!(fixture.device_pk.len(), ML_DSA_65_PUBLIC_KEY_BYTES);
            let public = public_input(
                &transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                "rp-local-demo-a",
                VERIFY_AT,
            );
            assert_eq!(
                public.device_cose_sig_structure.len(),
                TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY
            );
            let request = request(transcript.clone(), fixture.issuer_pk.clone());
            let (id_lo, id_hi, revocation_signature) = revocation_witness(&fixture.mso);

            let proof = prove_mdoc_ts13_demo(
                &fixture.document,
                &request,
                &public,
                id_lo,
                id_hi,
                revocation_signature.clone(),
            )
            .expect("TS13 demo proves");
            assert!(proof.has_ts13_demo_shape());
            let shape = proof.ts13_demo_proof_shape();
            let geometry = proof
                .ts13_demo_circuit_geometry()
                .expect("live circuit geometry is captured");
            let artifact_input =
                include_bytes!("../../../artifacts/ts13-demo-v1/generation-input-v1.json");
            eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                artifact_input,
                &geometry,
                &shape,
            )
            .expect("checked-in artifact input matches the live composed circuit");
            let mut drifted_geometry = geometry.clone();
            assert_ne!(
                drifted_geometry.air_instances[0].preprocessed_log_sizes[5],
                drifted_geometry.air_instances[0].preprocessed_log_sizes[6],
                "fixture must exercise an order-only column-schema mutation"
            );
            drifted_geometry.air_instances[0]
                .preprocessed_log_sizes
                .swap(5, 6);
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &drifted_geometry,
                    &shape,
                )
                .is_err(),
                "physical column-order drift must reject even when its histogram is unchanged"
            );
            let mut drifted = shape.clone();
            drifted.queried_values[0][0] -= 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "per-column query-count drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.decommitment_hash_counts[0] = 36 * 19 + 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "Merkle decommitment-bound drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.fri_first_layer_witness_count = 109;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "FRI witness-bound drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.sampled_values[0][0] += 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "sampled-field-count drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.sampled_values[0][0] += 1;
            drifted.sampled_values[0][1] -= 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "balanced sampled-value histogram drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.fri_last_layer_coefficient_count += 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "FRI last-layer coefficient drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.proof_bytes = 1_755_051;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    artifact_input,
                    &geometry,
                    &drifted,
                )
                .is_err(),
                "a proof beyond the deterministic worst-case bound must reject"
            );
            let mut committed_histogram = std::collections::BTreeMap::new();
            for &log_size in &geometry.committed_preprocessed_log_sizes {
                *committed_histogram.entry(log_size).or_insert(0usize) += 1;
            }
            assert_eq!(
                committed_histogram.into_iter().collect::<Vec<_>>(),
                [
                    (4, 3),
                    (5, 8),
                    (6, 14),
                    (7, 15),
                    (8, 35),
                    (9, 689),
                    (10, 104),
                    (11, 8),
                    (12, 4),
                    (13, 46),
                    (14, 10),
                    (15, 8),
                    (16, 3),
                ]
            );
            assert_eq!(shape.commitment_count, 5);
            assert_eq!(
                shape
                    .sampled_values
                    .iter()
                    .map(Vec::len)
                    .collect::<Vec<_>>(),
                [947, 5_000, 2_416, 8, 32]
            );
            assert_eq!(
                shape
                    .queried_values
                    .iter()
                    .map(Vec::len)
                    .collect::<Vec<_>>(),
                [947, 5_000, 2_416, 8, 32]
            );
            assert!(shape
                .queried_values
                .iter()
                .flatten()
                .all(|&query_count| query_count == 36));
            let mut expected_post_payloads = vec![0; 20];
            expected_post_payloads[2] = 20_128;
            assert_eq!(shape.post_interaction_payload_bytes, expected_post_payloads);
            assert_eq!(shape.fri_last_layer_coefficient_count, 2);
            assert_eq!(shape.sha_table_pair_claim_count, 3);
            assert_eq!(shape.attribute_sha_range_claim_counts, [0]);
            assert_eq!(shape.mso_sha_range_claim_count, Some(0));
            assert_eq!(
                (
                    shape.issuer_mldsa_group_eval_count,
                    shape.issuer_mldsa_claimed_sum_count,
                    shape.device_mldsa_group_eval_count,
                    shape.device_mldsa_claimed_sum_count,
                    shape.revocation_mldsa_group_eval_count,
                    shape.revocation_mldsa_claimed_sum_count,
                    shape.keccak_service_claimed_sum_count,
                ),
                (
                    Some(30),
                    Some(18),
                    Some(66),
                    Some(23),
                    Some(30),
                    Some(18),
                    Some(12),
                )
            );
            assert_eq!(shape.private_item_claim_count, 1);
            assert_eq!(shape.cbor_parser_claim_count, 2);

            let column_counts = geometry
                .air_instances
                .iter()
                .map(|air| {
                    (
                        air.preprocessed_log_sizes.len(),
                        air.trace_log_sizes.len(),
                        air.interaction_log_sizes.len(),
                        air.post_interaction_log_sizes.len(),
                    )
                })
                .collect::<Vec<_>>();
            assert_eq!(
                column_counts,
                [
                    (8, 4, 12, 0),
                    (2, 1, 4, 0),
                    (555, 2_368, 892, 8),
                    (0, 0, 0, 0),
                    (2, 2, 8, 0),
                    (71, 99, 160, 0),
                    (10, 438, 124, 0),
                    (10, 438, 124, 0),
                    (3, 117, 4, 0),
                    (3, 117, 4, 0),
                    (6, 154, 140, 0),
                    (142, 203, 144, 0),
                    (2, 88, 104, 0),
                    (4, 324, 108, 0),
                    (16, 13, 16, 0),
                    (12, 34, 52, 0),
                    (94, 165, 312, 0),
                    (1, 336, 48, 0),
                    (71, 99, 160, 0),
                    (0, 0, 0, 0),
                ]
            );
            assert_eq!(
                geometry
                    .air_instances
                    .iter()
                    .map(|air| air.components.len())
                    .collect::<Vec<_>>(),
                [3, 1, 13, 0, 2, 18, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 23, 2, 18, 0]
            );
            assert_eq!(
                geometry.air_instances[2].post_interaction_log_sizes,
                [13; 8]
            );
            assert!(geometry
                .air_instances
                .iter()
                .enumerate()
                .all(|(index, air)| index == 2 || air.post_interaction_log_sizes.is_empty()));
            assert_eq!(geometry.committed_preprocessed_log_sizes.len(), 947);
            assert_eq!(
                column_counts.iter().fold(
                    [0usize; 3],
                    |[trace, interaction, post], &(_, air_trace, air_interaction, air_post)| [
                        trace + air_trace,
                        interaction + air_interaction,
                        post + air_post,
                    ]
                ),
                [5_000, 2_416, 8]
            );
            verify_mdoc_ts13_demo(&proof, &public).expect("TS13 demo verifies");

            let derive = |circuit_hash: &[u8; 32],
                          zk_system_id: &str,
                          document_type: &str,
                          namespace: &str,
                          element_identifier: &str,
                          expected_value_cbor: &[u8],
                          timestamp_epoch_seconds: i64,
                          session_transcript: &[u8],
                          issuer_key: &[u8],
                          revocation_key: &[u8],
                          epoch: u32| {
                derive_public_context(Ts13DemoPublicContextInput {
                    circuit_hash,
                    zk_system_id,
                    document_type,
                    namespace,
                    element_identifier,
                    expected_value_cbor,
                    timestamp_epoch_seconds,
                    session_transcript,
                    trusted_issuer_public_key: issuer_key,
                    revocation_public_key: revocation_key,
                    revocation_epoch: epoch,
                })
            };
            let relabeled = |label: &str, public: MdocTs13DemoCircuitPublicInput| {
                assert!(
                    verify_mdoc_ts13_demo(&proof, &public).is_err(),
                    "{label} relabel must reject"
                );
            };

            let mut changed = public.clone();
            changed.request_context_digest[0] ^= 1;
            relabeled("request digest", changed);

            let mut changed = public.clone();
            changed.verification_timestamp_rfc3339_utc[0] ^= 1;
            relabeled("caller-supplied timestamp rendering", changed);

            let changed_circuit_hash = [0x43; 32];
            let derived = derive(
                &changed_circuit_hash,
                "rp-local-demo-a",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT,
                &transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed circuit context derives");
            let mut changed = public.clone();
            changed.circuit_hash = changed_circuit_hash;
            changed.request_context_digest = derived.request_context_digest;
            relabeled("circuit hash", changed);

            let derived = derive(
                &CIRCUIT_HASH,
                "rp-local-demo-b",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT,
                &transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed RP context derives");
            let mut changed = public.clone();
            changed.request_context_digest = derived.request_context_digest;
            relabeled("zk system id", changed);

            let changed_transcript =
                eu_id_prover::mdoc::openid4vp_session_transcript(b"relabel-session");
            let derived = derive(
                &CIRCUIT_HASH,
                "rp-local-demo-a",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT,
                &changed_transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed transcript context derives");
            let mut changed = public.clone();
            changed.request_context_digest = derived.request_context_digest;
            changed.device_cose_sig_structure = derived.device_cose_sig_structure;
            relabeled("session transcript", changed);

            let derived = derive(
                &CIRCUIT_HASH,
                "rp-local-demo-a",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT + 1,
                &transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed timestamp context derives");
            let mut changed = public.clone();
            changed.timestamp_epoch_seconds = VERIFY_AT + 1;
            changed.request_context_digest = derived.request_context_digest;
            changed.verification_timestamp_rfc3339_utc = derived.verification_timestamp_rfc3339_utc;
            relabeled("timestamp", changed);

            let derived = derive(
                &CIRCUIT_HASH,
                "rp-local-demo-a",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT,
                &transcript,
                &fixture.device_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed issuer context derives");
            let mut changed = public.clone();
            changed.trusted_issuer_public_key = fixture.device_pk.clone();
            changed.request_context_digest = derived.request_context_digest;
            relabeled("issuer key", changed);

            let derived = derive(
                &CIRCUIT_HASH,
                "rp-local-demo-a",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT,
                &transcript,
                &fixture.issuer_pk,
                &fixture.device_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed revocation context derives");
            let mut changed = public.clone();
            changed.revocation.revocation_public_key =
                MdocRevocationKey::MlDsa(fixture.device_pk.clone());
            changed.request_context_digest = derived.request_context_digest;
            relabeled("revocation key", changed);

            let derived = derive(
                &CIRCUIT_HASH,
                "rp-local-demo-a",
                PID_SCOPE,
                PID_SCOPE,
                AGE_OVER_18,
                &[0xf5],
                VERIFY_AT,
                &transcript,
                &fixture.issuer_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH + 1,
            )
            .expect("changed epoch context derives");
            let mut changed = public.clone();
            changed.revocation.epoch = REVOCATION_EPOCH + 1;
            changed.request_context_digest = derived.request_context_digest;
            relabeled("revocation epoch", changed);

            for (label, result) in [
                (
                    "document type",
                    derive(
                        &CIRCUIT_HASH,
                        "rp-local-demo-a",
                        "org.example.other",
                        PID_SCOPE,
                        AGE_OVER_18,
                        &[0xf5],
                        VERIFY_AT,
                        &transcript,
                        &fixture.issuer_pk,
                        &fixture.revocation_pk,
                        REVOCATION_EPOCH,
                    ),
                ),
                (
                    "namespace",
                    derive(
                        &CIRCUIT_HASH,
                        "rp-local-demo-a",
                        PID_SCOPE,
                        "org.example.other",
                        AGE_OVER_18,
                        &[0xf5],
                        VERIFY_AT,
                        &transcript,
                        &fixture.issuer_pk,
                        &fixture.revocation_pk,
                        REVOCATION_EPOCH,
                    ),
                ),
                (
                    "element identifier",
                    derive(
                        &CIRCUIT_HASH,
                        "rp-local-demo-a",
                        PID_SCOPE,
                        PID_SCOPE,
                        "birth_date",
                        &[0xf5],
                        VERIFY_AT,
                        &transcript,
                        &fixture.issuer_pk,
                        &fixture.revocation_pk,
                        REVOCATION_EPOCH,
                    ),
                ),
                (
                    "expected value",
                    derive(
                        &CIRCUIT_HASH,
                        "rp-local-demo-a",
                        PID_SCOPE,
                        PID_SCOPE,
                        AGE_OVER_18,
                        &[0xf4],
                        VERIFY_AT,
                        &transcript,
                        &fixture.issuer_pk,
                        &fixture.revocation_pk,
                        REVOCATION_EPOCH,
                    ),
                ),
            ] {
                assert_eq!(
                    result,
                    Err(Ts13DemoContextError::InvalidPublicContext),
                    "{label} profile relabel must reject"
                );
            }

            for (label, mut swapped) in [
                ("issuer/device", proof.clone()),
                ("issuer/revocation", proof.clone()),
                ("device/revocation", proof.clone()),
            ] {
                match label {
                    "issuer/device" => {
                        std::mem::swap(&mut swapped.mldsa, &mut swapped.device_mldsa)
                    }
                    "issuer/revocation" => {
                        std::mem::swap(&mut swapped.mldsa, &mut swapped.revocation_mldsa)
                    }
                    "device/revocation" => {
                        std::mem::swap(&mut swapped.device_mldsa, &mut swapped.revocation_mldsa)
                    }
                    _ => unreachable!(),
                }
                assert!(
                    verify_mdoc_ts13_demo(&swapped, &public).is_err(),
                    "{label} role replay must reject"
                );
            }

            let one = stwo::core::fields::qm31::SecureField::from(
                stwo::core::fields::m31::M31::from_u32_unchecked(1),
            );
            let mut changed = proof.clone();
            changed
                .ts13_expand_a_claim_mut_for_test()
                .expect("TS13 demo carries the U5 ExpandA claim")
                .absorb_claimed_sum += one;
            verify_mdoc_ts13_demo(&changed, &public)
                .expect_err("changed U5 claim must reject in the final composition");

            let mut changed = proof.clone();
            assert!(
                changed.tamper_ts13_device_key_bind_claimed_sum_for_test(),
                "TS13 demo carries the U9 device-key/MSO claim"
            );
            verify_mdoc_ts13_demo(&changed, &public)
                .expect_err("changed U9 claim must reject in the final composition");

            let mut changed = proof.clone();
            changed
                .device_mldsa
                .as_mut()
                .expect("TS13 demo carries private-key device ML-DSA claims")
                .group_evals[0] += one;
            verify_mdoc_ts13_demo(&changed, &public)
                .expect_err("changed U6/U7 device ML-DSA claim must reject in composition");

            let extracted =
                extract_pid_mdoc(&fixture.document, &request).expect("fixture extracts");
            let product_statement = MdocCircuitStatement::from_extracted(&extracted, demo_policy())
                .expect("product statement builds");
            verify_mdoc(&proof, &product_statement.into_public_view())
                .expect_err("demo proof must not verify as product");

            let legacy_statement = MdocCircuitStatement::from_extracted(&extracted, demo_policy())
                .expect("legacy statement builds")
                .with_ts13_revocation(public.revocation.clone())
                .with_ts13_revocation_range(MdocRevocationRangeWitness {
                    id: eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso),
                    id_lo,
                    id_hi,
                })
                .with_ts13_revocation_signature(revocation_signature);
            let legacy_public = MdocTs13PublicStatement::from_circuit(&legacy_statement)
                .expect("legacy public statement builds");
            eu_id_prover::mdoc::verify_mdoc_ts13_public_statement(&proof, &legacy_public)
                .expect_err("demo proof must not verify as legacy TS13");
        })
        .expect("large-stack TS13 test thread starts")
        .join()
        .expect("large-stack TS13 test thread succeeds");
}

#[test]
fn composed_k1_mso_k2_device_substitution_rejects() {
    std::thread::Builder::new()
        .name("ts13-demo-k1-k2-test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let transcript = eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-demo-k1-k2");
            let credential_a =
                mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript);
            let credential_b =
                mldsa_fixture::mldsa_ts13_unlinkable_credential_b_with_transcript(&transcript);
            assert_ne!(credential_a.device_pk, credential_b.device_pk);
            assert_eq!(
                credential_a.device_sig_structure,
                credential_b.device_sig_structure
            );

            let request_a = request(transcript.clone(), credential_a.issuer_pk.clone());
            let request_b = request(transcript.clone(), credential_b.issuer_pk.clone());
            let mut hybrid =
                extract_pid_mdoc(&credential_a.document, &request_a).expect("K1 fixture extracts");
            let extracted_b =
                extract_pid_mdoc(&credential_b.document, &request_b).expect("K2 fixture extracts");
            stwo_mldsa::witness::generate_witness(
                extracted_b
                    .device_auth_input
                    .as_mldsa()
                    .expect("K2 device authentication is ML-DSA"),
            )
            .expect("K2 device signature and complete ML-DSA witness are internally valid");
            hybrid.device_auth_input = extracted_b.device_auth_input;

            let public = public_input(
                &transcript,
                &credential_a.issuer_pk,
                &credential_a.revocation_pk,
                "rp-local-demo-k1-k2",
                VERIFY_AT,
            );
            let (id_lo, id_hi, signature) = revocation_witness(&credential_a.mso);
            let statement = MdocCircuitStatement::from_extracted(&hybrid, demo_policy())
                .expect("hybrid statement builds")
                .with_ts13_revocation(public.revocation.clone())
                .with_ts13_revocation_range(MdocRevocationRangeWitness {
                    id: eu_id_prover::ts13::ts13_mso_derived_revocation_id(&credential_a.mso),
                    id_lo,
                    id_hi,
                })
                .with_ts13_revocation_signature(signature);

            let proof =
                eu_id_prover::mdoc::prove_mdoc_ts13_demo_circuit(&hybrid, &statement, &public)
                    .expect("the internally valid K2 witness builds an adversarial proof");
            verify_mdoc_ts13_demo(&proof, &public)
                .expect_err("K1-in-MSO/K2 device proof must fail in the composed relation system");
        })
        .expect("large-stack K1/K2 test thread starts")
        .join()
        .expect("large-stack K1/K2 test thread succeeds");
}

#[test]
fn composed_wrong_mso_revocation_id_with_resigned_endpoints_rejects() {
    std::thread::Builder::new()
        .name("ts13-demo-wrong-revocation-id-test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let transcript =
                eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-wrong-revocation-id");
            let fixture =
                mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript);
            let extracted = extract_pid_mdoc(
                &fixture.document,
                &request(transcript.clone(), fixture.issuer_pk.clone()),
            )
            .expect("fixture extracts");
            let actual_id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&fixture.mso);
            let wrong_id = if actual_id <= u64::MAX - 3 {
                actual_id + 2
            } else {
                actual_id - 2
            };
            let wrong_id_lo = wrong_id - 1;
            let wrong_id_hi = wrong_id + 1;
            assert!(wrong_id_lo < wrong_id && wrong_id < wrong_id_hi);
            assert!(
                !(wrong_id_lo < actual_id && actual_id < wrong_id_hi),
                "honest MSO-derived ID is outside the forged interval"
            );

            let (revocation_pk, signature) =
                mldsa_fixture::mldsa_revocation_fixture(wrong_id_lo, wrong_id_hi, REVOCATION_EPOCH);
            assert_eq!(revocation_pk, fixture.revocation_pk);
            let signed_message =
                mldsa_fixture::revocation_message(wrong_id_lo, wrong_id_hi, REVOCATION_EPOCH);
            let signature_trace =
                stwo_mldsa::verify_internals(&revocation_pk, &signed_message, &signature)
                    .expect("re-signed forged endpoints decode");
            assert!(
                signature_trace.accepted,
                "re-signed forged endpoints are internally valid: {:?}",
                signature_trace.reason
            );

            let public = public_input(
                &transcript,
                &fixture.issuer_pk,
                &revocation_pk,
                "rp-local-demo-wrong-revocation-id",
                VERIFY_AT,
            );
            let statement = MdocCircuitStatement::from_extracted(&extracted, demo_policy())
                .expect("statement builds")
                .with_ts13_revocation(public.revocation.clone())
                .with_ts13_revocation_range(MdocRevocationRangeWitness {
                    id: wrong_id,
                    id_lo: wrong_id_lo,
                    id_hi: wrong_id_hi,
                })
                .with_ts13_revocation_signature(MdocRevocationSignature::MlDsa(signature));

            let proof =
                eu_id_prover::mdoc::prove_mdoc_ts13_demo_circuit(&extracted, &statement, &public)
                    .expect("internally valid forged revocation inputs build an adversarial proof");
            let error = verify_mdoc_ts13_demo(&proof, &public)
                .expect_err("wrong MSO-derived revocation ID must fail composition");
            assert!(
                matches!(error, eu_id_prover::Error::Verify(_)),
                "adversarial proof must reach and fail STARK verification, got {error:?}"
            );
        })
        .expect("large-stack wrong-revocation-ID test thread starts")
        .join()
        .expect("large-stack wrong-revocation-ID test thread succeeds");
}

#[test]
fn validity_and_capacity_boundaries_fail_closed_before_proving() {
    let transcript = eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-validity");
    let tight = rewrite_validity(
        mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript),
        "2026-12-31T23:59:59Z",
        "2027-01-01T00:00:01Z",
    );
    let (id_lo, id_hi, signature) = revocation_witness(&tight.mso);
    for (label, timestamp, expected) in [
        (
            "one second before validFrom",
            VERIFY_AT - 2,
            "not after validFrom",
        ),
        ("validFrom equality", VERIFY_AT - 1, "not after validFrom"),
        (
            "validUntil equality",
            VERIFY_AT + 1,
            "not before validUntil",
        ),
        (
            "one second after validUntil",
            VERIFY_AT + 2,
            "not before validUntil",
        ),
    ] {
        let public = public_input(
            &transcript,
            &tight.issuer_pk,
            &tight.revocation_pk,
            "rp-local-demo-validity",
            timestamp,
        );
        let error = match prove_mdoc_ts13_demo(
            &tight.document,
            &request(transcript.clone(), tight.issuer_pk.clone()),
            &public,
            id_lo,
            id_hi,
            signature.clone(),
        ) {
            Err(error) => error,
            Ok(_) => panic!("strict validity boundary must reject"),
        };
        assert!(
            format!("{error:?}").contains(expected),
            "{label} returned {error:?}"
        );
    }

    for (label, fixture, expected) in [
        (
            "invalid Gregorian date",
            rewrite_validity(
                mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript),
                "2026-02-30T00:00:00Z",
                "2030-01-01T00:00:00Z",
            ),
            "Gregorian date",
        ),
        (
            "unsupported validity year",
            rewrite_validity(
                mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript),
                "2026-01-01T00:00:00Z",
                "2100-01-01T00:00:00Z",
            ),
            "outside 2020..=2099",
        ),
    ] {
        let public = public_input(
            &transcript,
            &fixture.issuer_pk,
            &fixture.revocation_pk,
            "rp-local-demo-validity",
            VERIFY_AT,
        );
        let (id_lo, id_hi, signature) = revocation_witness(&fixture.mso);
        let error = match prove_mdoc_ts13_demo(
            &fixture.document,
            &request(transcript.clone(), fixture.issuer_pk),
            &public,
            id_lo,
            id_hi,
            signature,
        ) {
            Err(error) => error,
            Ok(_) => panic!("invalid private validity must reject"),
        };
        assert!(
            format!("{error:?}").contains(expected),
            "{label} returned {error:?}"
        );
    }

    let malformed = rewrite_validity(
        mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript),
        "2026-01-01T00:00:0xZ",
        "2030-01-01T00:00:00Z",
    );
    let public = public_input(
        &transcript,
        &malformed.issuer_pk,
        &malformed.revocation_pk,
        "rp-local-demo-validity",
        VERIFY_AT,
    );
    let (id_lo, id_hi, signature) = revocation_witness(&malformed.mso);
    assert!(matches!(
        prove_mdoc_ts13_demo(
            &malformed.document,
            &request(transcript.clone(), malformed.issuer_pk),
            &public,
            id_lo,
            id_hi,
            signature,
        ),
        Err(eu_id_prover::Error::Mdoc(MdocError::InvalidTdate(
            "validityInfo.validFrom"
        )))
    ));

    let revocation_fixture =
        mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&transcript);
    let revocation_id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(&revocation_fixture.mso);
    let revocation_public = public_input(
        &transcript,
        &revocation_fixture.issuer_pk,
        &revocation_fixture.revocation_pk,
        "rp-local-demo-revocation-strictness",
        VERIFY_AT,
    );
    let below_revocation_id = revocation_id.checked_sub(1).expect("fixture ID is nonzero");
    let above_revocation_id = revocation_id
        .checked_add(1)
        .expect("fixture ID is below u64::MAX");
    for (label, id_lo, id_hi) in [
        (
            "lower endpoint equality",
            revocation_id,
            above_revocation_id,
        ),
        (
            "upper endpoint equality",
            below_revocation_id,
            revocation_id,
        ),
    ] {
        let (_, signature) =
            mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, REVOCATION_EPOCH);
        assert!(
            prove_mdoc_ts13_demo(
                &revocation_fixture.document,
                &request(transcript.clone(), revocation_fixture.issuer_pk.clone(),),
                &revocation_public,
                id_lo,
                id_hi,
                MdocRevocationSignature::MlDsa(signature),
            )
            .is_err(),
            "{label} must violate the strict private revocation interval"
        );
    }

    let at_capacity = transcript_for_device_message_len(TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY);
    let overflow = transcript_for_device_message_len(TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY + 1);
    let at_capacity_message = derive_device_authentication(&at_capacity)
        .expect("capacity transcript derives")
        .device_cose_sig_structure;
    let overflow_message = derive_device_authentication(&overflow)
        .expect("overflow transcript derives")
        .device_cose_sig_structure;
    assert_eq!(
        ensure_device_cose_sig_structure_capacity(
            &at_capacity_message,
            TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY as u32,
        ),
        Ok(())
    );
    assert_eq!(
        ensure_device_cose_sig_structure_capacity(
            &overflow_message,
            TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY as u32,
        ),
        Err(Ts13DemoContextError::InvalidPublicContext)
    );

    let overflow_fixture =
        mldsa_fixture::mldsa_ts13_unlinkable_credential_a_with_transcript(&overflow);
    let overflow_public = public_input(
        &overflow,
        &overflow_fixture.issuer_pk,
        &overflow_fixture.revocation_pk,
        "rp-local-demo-overflow",
        VERIFY_AT,
    );
    let (id_lo, id_hi, signature) = revocation_witness(&overflow_fixture.mso);
    let error = match prove_mdoc_ts13_demo(
        &overflow_fixture.document,
        &request(overflow, overflow_fixture.issuer_pk),
        &overflow_public,
        id_lo,
        id_hi,
        signature,
    ) {
        Err(error) => error,
        Ok(_) => panic!("capacity overflow must reject"),
    };
    assert!(
        format!("{error:?}").contains("outside 1..=1024"),
        "unexpected capacity overflow error: {error:?}"
    );
}
