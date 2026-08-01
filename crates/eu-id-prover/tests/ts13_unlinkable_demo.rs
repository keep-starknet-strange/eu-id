#[allow(dead_code)]
#[path = "support/mldsa_fixture.rs"]
mod mldsa_fixture;

use ciborium::value::Value;
use eu_id_prover::mdoc::{
    MdocError, MdocPidRequest, MdocRevocationKey, MdocRevocationPublicInputs,
    MdocRevocationSignature, TS13_DEMO_DEVICE_SIG_STRUCTURE_CAPACITY,
};
use eu_id_prover::ts13_demo::{
    derive_device_authentication, derive_public_context, ensure_device_cose_sig_structure_capacity,
    Ts13DemoContextError, Ts13DemoPublicContextInput, ML_DSA_65_PUBLIC_KEY_BYTES,
};
use eu_id_prover::{prove_mdoc_ts13_demo, verify_mdoc_ts13_demo, MdocTs13DemoCircuitPublicInput};
use ml_dsa::signature::Signer;
use ml_dsa::{EncodedSignature, MlDsa65, SigningKey};
use stwo_mldsa::profile::ML_DSA_44;

const VERIFY_AT: i64 = 1_798_761_600; // 2027-01-01T00:00:00Z
const REVOCATION_EPOCH: u32 = 17;
const CIRCUIT_HASH: [u8; 32] = eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_CIRCUIT_HASH;
const PID_SCOPE: &str = "eu.europa.ec.eudi.pid.1";
const AGE_OVER_18: &str = "age_over_18";

fn request(transcript: Vec<u8>) -> MdocPidRequest {
    MdocPidRequest::age_over_18(transcript)
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
            revocation_public_key: MdocRevocationKey(revocation_public_key.to_vec()),
            epoch: REVOCATION_EPOCH,
        },
    }
}

fn revocation_witness(mso: &[u8]) -> (u64, u64, MdocRevocationSignature) {
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(mso);
    let id_lo = id.checked_sub(1).expect("fixture revocation id is nonzero");
    let id_hi = id.checked_add(1).expect("fixture revocation id is not max");
    let (_, signature) = mldsa_fixture::mldsa_revocation_fixture(id_lo, id_hi, REVOCATION_EPOCH);
    (id_lo, id_hi, MdocRevocationSignature(signature))
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
    mut fixture: mldsa_fixture::MldsaIdentityFixture,
    valid_from: &str,
    valid_until: &str,
) -> mldsa_fixture::MldsaIdentityFixture {
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
fn public_issuer_trust_mismatch_rejects_before_proving() {
    let transcript = eu_id_prover::mdoc::openid4vp_session_transcript(b"issuer-trust-mismatch");
    let fixture = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
    let public = public_input(
        &transcript,
        &fixture.device_pk,
        &fixture.revocation_pk,
        "rp-local-demo-issuer-trust",
        VERIFY_AT,
    );
    let (id_lo, id_hi, signature) = revocation_witness(&fixture.mso);

    match prove_mdoc_ts13_demo(
        &fixture.document,
        &request(transcript),
        &public,
        id_lo,
        id_hi,
        signature,
    ) {
        Err(eu_id_prover::Error::Prove(message)) => {
            assert_eq!(
                message,
                "TS13 demo private witness does not match the public theorem"
            );
        }
        Err(error) => panic!("unexpected issuer trust error: {error:?}"),
        Ok(_) => panic!("an untrusted issuer key must reject"),
    }
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
                mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript),
                "2026-12-31T23:59:59Z",
                "2027-01-01T00:00:01Z",
            );
            assert_eq!(fixture.issuer_pk.len(), ML_DSA_65_PUBLIC_KEY_BYTES);
            assert_eq!(fixture.device_pk.len(), ML_DSA_44.pk_bytes());
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
            let request = request(transcript.clone());
            let (id_lo, id_hi, revocation_signature) = revocation_witness(&fixture.mso);

            let proof = prove_mdoc_ts13_demo(
                &fixture.document,
                &request,
                &public,
                id_lo,
                id_hi,
                revocation_signature,
            )
            .expect("TS13 demo proves");
            let shape = proof.ts13_demo_proof_shape();
            let geometry = proof
                .ts13_demo_circuit_geometry()
                .expect("live circuit geometry is captured");
            let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            let artifact_input_path =
                workspace.join(eu_id_prover::ts13_artifact::GENERATION_INPUT_PATH);
            let artifact_input =
                std::fs::read(&artifact_input_path).expect("generation input is readable");
            if std::env::var("TS13_REFRESH_GENERATION_INPUT").as_deref() == Ok("1") {
                verify_mdoc_ts13_demo(&proof, &public)
                    .expect("the proof used to refresh the artifact input verifies");
                eu_id_prover::ts13_artifact::refresh_live_ts13_demo_generation_input(
                    &workspace, geometry, &shape,
                )
                .expect("live generation input refreshes atomically");
                return;
            }
            assert!(proof.has_ts13_demo_shape());
            eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                &artifact_input,
                geometry,
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
                    &artifact_input,
                    &drifted_geometry,
                    &shape,
                )
                .is_err(),
                "physical column-order drift must reject even when its histogram is unchanged"
            );
            let mut drifted = shape.clone();
            let common_query_count = drifted.queried_values[0][0];
            drifted.queried_values[0][0] = if common_query_count == 1 {
                2
            } else {
                common_query_count - 1
            };
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
                    &drifted,
                )
                .is_err(),
                "an in-cap per-column queried-value count mismatch must reject"
            );
            let mut drifted = shape.clone();
            drifted.queried_values[0][0] =
                eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_QUERY_COUNT + 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
                    &drifted,
                )
                .is_err(),
                "a per-column queried-value count above the configured cap must reject"
            );
            let mut drifted = shape.clone();
            drifted.decommitment_hash_counts[0] =
                eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_TREE_MERKLE_HASH_CAPS[0] + 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
                    &drifted,
                )
                .is_err(),
                "Merkle decommitment-bound drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.fri_first_layer_witness_count =
                eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_FRI_FIRST_WITNESS_CAP + 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
                    &drifted,
                )
                .is_err(),
                "FRI witness-bound drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.sampled_values[0][0] += 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
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
                    &artifact_input,
                    geometry,
                    &drifted,
                )
                .is_err(),
                "balanced sampled-value histogram drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.fri_last_layer_coefficient_count += 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
                    &drifted,
                )
                .is_err(),
                "FRI last-layer coefficient drift must reject"
            );
            let mut drifted = shape.clone();
            drifted.proof_bytes =
                eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_PROOF_BODY_CAPACITY as usize
                    + 1;
            assert!(
                eu_id_prover::ts13_artifact::validate_live_ts13_demo_profile(
                    &artifact_input,
                    geometry,
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
                    (4, 5),
                    (5, 20),
                    (6, 3),
                    (7, 7),
                    (8, 46),
                    (9, 95),
                    (10, 92),
                    (11, 20),
                    (12, 2),
                    (13, 31),
                    (14, 2),
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
                [334, 4_285, 2_380, 8, 16]
            );
            assert_eq!(
                shape
                    .queried_values
                    .iter()
                    .map(Vec::len)
                    .collect::<Vec<_>>(),
                [334, 4_285, 2_380, 8, 16]
            );
            let common_query_count = shape.queried_values[0][0];
            assert!(common_query_count > 0);
            assert!(
                common_query_count
                    <= eu_id_prover::ts13_demo_artifact_constants::TS13_DEMO_QUERY_COUNT
            );
            assert!(shape
                .queried_values
                .iter()
                .flatten()
                .all(|&query_count| query_count == common_query_count));
            let mut expected_post_payloads = vec![0; 20];
            expected_post_payloads[2] = 18_464;
            assert_eq!(shape.post_interaction_payload_bytes, expected_post_payloads);
            assert_eq!(shape.fri_last_layer_coefficient_count, 2);
            assert_eq!(shape.sha_table_pair_claim_count, 3);
            assert_eq!(shape.attribute_sha_range_claim_count, 0);
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
                    (58, 1_963, 888, 8),
                    (0, 0, 0, 0),
                    (2, 2, 8, 0),
                    (63, 125, 192, 0),
                    (11, 292, 68, 0),
                    (11, 292, 68, 0),
                    (3, 117, 4, 0),
                    (3, 117, 4, 0),
                    (5, 80, 140, 0),
                    (67, 202, 144, 0),
                    (2, 88, 104, 0),
                    (4, 305, 92, 0),
                    (11, 13, 16, 0),
                    (5, 34, 52, 0),
                    (84, 189, 344, 0),
                    (1, 336, 48, 0),
                    (63, 125, 192, 0),
                    (0, 0, 0, 0),
                ]
            );
            assert_eq!(
                geometry
                    .air_instances
                    .iter()
                    .map(|air| air.components.len())
                    .collect::<Vec<_>>(),
                [3, 1, 13, 0, 2, 18, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 23, 2, 18, 0]
            );
            assert_eq!(
                geometry
                    .air_instances
                    .iter()
                    .map(|air| air.claimed_sum_count)
                    .collect::<Vec<_>>(),
                [3, 1, 12, 0, 2, 18, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 23, 2, 18, 0]
            );
            assert_eq!(
                geometry.air_instances[2].post_interaction_log_sizes,
                [12; 8]
            );
            assert!(geometry
                .air_instances
                .iter()
                .enumerate()
                .all(|(index, air)| index == 2 || air.post_interaction_log_sizes.is_empty()));
            assert_eq!(geometry.committed_preprocessed_log_sizes.len(), 334);
            assert_eq!(
                column_counts.iter().fold(
                    [0usize; 3],
                    |[trace, interaction, post], &(_, air_trace, air_interaction, air_post)| [
                        trace + air_trace,
                        interaction + air_interaction,
                        post + air_post,
                    ]
                ),
                [4_285, 2_380, 8]
            );
            let reject_proof_without_panic = |label: &str, candidate: &eu_id_prover::MdocProof| {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    verify_mdoc_ts13_demo(candidate, &public)
                }));
                match result {
                    Ok(Err(_)) => {}
                    Ok(Ok(())) => panic!("{label} must reject"),
                    Err(_) => panic!("{label} must return an error without panicking"),
                }
            };

            let mut forged_root = proof.clone();
            forged_root.stark_proof.0.commitments[0].0[0] ^= 1;
            reject_proof_without_panic("forged tree-zero root", &forged_root);
            verify_mdoc_ts13_demo(&proof, &public).expect("canonical proof verifies");
            reject_proof_without_panic("forged tree-zero root after verification", &forged_root);
            verify_mdoc_ts13_demo(&proof, &public).expect("canonical proof verifies again");

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
                &fixture.revocation_pk,
                &fixture.revocation_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed issuer context derives");
            let mut changed = public.clone();
            changed.trusted_issuer_public_key = fixture.revocation_pk.clone();
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
                &fixture.issuer_pk,
                REVOCATION_EPOCH,
            )
            .expect("changed revocation context derives");
            let mut changed = public.clone();
            changed.revocation.revocation_public_key = MdocRevocationKey(fixture.issuer_pk.clone());
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
            changed.device_mldsa.group_evals[0] += one;
            verify_mdoc_ts13_demo(&changed, &public)
                .expect_err("changed private device ML-DSA claim must reject in composition");

            fn role_claims_mut<'a>(
                proof: &'a mut eu_id_prover::MdocProof,
                role: &str,
            ) -> &'a mut eu_id_prover::mdoc::MdocMlDsaClaims {
                match role {
                    "issuer" => &mut proof.mldsa,
                    "device" => &mut proof.device_mldsa,
                    "revocation" => &mut proof.revocation_mldsa,
                    _ => unreachable!("test role is fixed"),
                }
            }

            for role in ["issuer", "device", "revocation"] {
                let mut short_group_evals = proof.clone();
                role_claims_mut(&mut short_group_evals, role)
                    .group_evals
                    .pop()
                    .expect("role has group evaluations");
                reject_proof_without_panic(
                    &format!("short {role} group-evaluation vector"),
                    &short_group_evals,
                );

                let mut long_group_evals = proof.clone();
                let extra = *role_claims_mut(&mut long_group_evals, role)
                    .group_evals
                    .last()
                    .expect("role has group evaluations");
                role_claims_mut(&mut long_group_evals, role)
                    .group_evals
                    .push(extra);
                reject_proof_without_panic(
                    &format!("long {role} group-evaluation vector"),
                    &long_group_evals,
                );

                let mut short_claimed_sums = proof.clone();
                role_claims_mut(&mut short_claimed_sums, role)
                    .claimed_sums
                    .pop()
                    .expect("role has claimed sums");
                reject_proof_without_panic(
                    &format!("short {role} claimed-sum vector"),
                    &short_claimed_sums,
                );

                let mut long_claimed_sums = proof.clone();
                let extra = *role_claims_mut(&mut long_claimed_sums, role)
                    .claimed_sums
                    .last()
                    .expect("role has claimed sums");
                role_claims_mut(&mut long_claimed_sums, role)
                    .claimed_sums
                    .push(extra);
                reject_proof_without_panic(
                    &format!("long {role} claimed-sum vector"),
                    &long_claimed_sums,
                );
            }

            let mut changed = proof.clone();
            changed.mldsa.claimed_sums[0] += one;
            reject_proof_without_panic("changed issuer claimed sum", &changed);

            let mut short_service_claims = proof.clone();
            short_service_claims
                .keccak_service_claimed_sums
                .pop()
                .expect("Keccak service claim vector is not empty");
            reject_proof_without_panic("short Keccak service claim vector", &short_service_claims);

            let mut changed_service_claim = proof.clone();
            changed_service_claim.keccak_service_claimed_sums[0] += one;
            reject_proof_without_panic("changed Keccak service claim", &changed_service_claim);
        })
        .expect("large-stack TS13 test thread starts")
        .join()
        .expect("large-stack TS13 test thread succeeds");
}

#[test]
fn validity_and_capacity_boundaries_fail_closed_before_proving() {
    let transcript = eu_id_prover::mdoc::openid4vp_session_transcript(b"ts13-validity");
    let tight = rewrite_validity(
        mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript),
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
            &request(transcript.clone()),
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
                mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript),
                "2026-02-30T00:00:00Z",
                "2030-01-01T00:00:00Z",
            ),
            "Gregorian date",
        ),
        (
            "unsupported validity year",
            rewrite_validity(
                mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript),
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
            &request(transcript.clone()),
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
        mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript),
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
            &request(transcript.clone()),
            &public,
            id_lo,
            id_hi,
            signature,
        ),
        Err(eu_id_prover::Error::Mdoc(MdocError::InvalidTdate(
            "validityInfo.validFrom"
        )))
    ));

    let revocation_fixture = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&transcript);
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
                &request(transcript.clone()),
                &revocation_public,
                id_lo,
                id_hi,
                MdocRevocationSignature(signature),
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

    let overflow_fixture = mldsa_fixture::mldsa_ts13_credential_a_with_transcript(&overflow);
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
        &request(overflow),
        &overflow_public,
        id_lo,
        id_hi,
        signature,
    ) {
        Err(error) => error,
        Ok(_) => panic!("capacity overflow must reject"),
    };
    match error {
        eu_id_prover::Error::Prove(message) => assert_eq!(
            message,
            "mdoc public shape: public input does not match the fixed TS13 profile"
        ),
        error => panic!("unexpected capacity overflow error: {error:?}"),
    }
}
