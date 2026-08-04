//! Current mdoc 2.0 grammar, validity, digest, and mandatory revocation tests.

use super::decode;
use ciborium::value::Value;
use ecdsa::signature::Signer;
use eu_id_prover::mdoc::{self, MdocCircuitStatement, MdocError, MdocTimestamp};
use eu_id_prover::ts13::{
    ts13_mso_derived_revocation_id, Ts13RevocationError, Ts13RevocationStatement,
    Ts13RevocationWitness,
};
use eu_id_prover::{prove_mdoc, Date, Error, Policy};
use p256::ecdsa::{Signature as P256Signature, SigningKey};
use sha2::{Digest as _, Sha256};

const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";

fn encode(value: Value) -> Vec<u8> {
    let mut bytes = Vec::new();
    ciborium::ser::into_writer(&value, &mut bytes).expect("fixture CBOR encodes");
    bytes
}

fn value_map_mut<'a>(value: &'a mut Value, label: &str) -> &'a mut Vec<(Value, Value)> {
    let Value::Map(map) = value else {
        panic!("{label} must be a map");
    };
    map
}

fn value_array_mut<'a>(value: &'a mut Value, label: &str) -> &'a mut Vec<Value> {
    let Value::Array(array) = value else {
        panic!("{label} must be an array");
    };
    array
}

fn text_value_mut<'a>(map: &'a mut [(Value, Value)], key: &str) -> &'a mut Value {
    map.iter_mut()
        .find_map(|(candidate, value)| {
            (candidate == &Value::Text(key.to_string())).then_some(value)
        })
        .unwrap_or_else(|| panic!("missing map key {key}"))
}

fn issuer_auth_mut(document: &mut Value) -> &mut Vec<Value> {
    let document = value_map_mut(document, "document");
    let issuer_signed = value_map_mut(text_value_mut(document, "issuerSigned"), "issuerSigned");
    value_array_mut(text_value_mut(issuer_signed, "issuerAuth"), "issuerAuth")
}

fn issuer_items_mut(document: &mut Value) -> &mut Vec<Value> {
    let document = value_map_mut(document, "document");
    let issuer_signed = value_map_mut(text_value_mut(document, "issuerSigned"), "issuerSigned");
    let namespaces = value_map_mut(
        text_value_mut(issuer_signed, "nameSpaces"),
        "issuerSigned.nameSpaces",
    );
    let namespace = namespaces
        .iter_mut()
        .find_map(|(key, value)| (key == &Value::Text(PID_NAMESPACE.to_string())).then_some(value))
        .expect("PID namespace exists");
    value_array_mut(namespace, "PID namespace items")
}

fn mutate_mso_and_resign(document: &mut Value, mutate: impl FnOnce(&mut Vec<(Value, Value)>)) {
    let issuer_auth = issuer_auth_mut(document);
    let Value::Bytes(protected) = &issuer_auth[0] else {
        panic!("issuerAuth protected header must be bytes");
    };
    let protected = protected.clone();
    let Value::Bytes(payload) = &issuer_auth[2] else {
        panic!("issuerAuth payload must be bytes");
    };
    let Value::Tag(24, wrapped_mso) = decode(payload) else {
        panic!("issuerAuth payload must wrap the MSO with tag 24");
    };
    let Value::Bytes(mso_bytes) = *wrapped_mso else {
        panic!("MSO tag must contain bytes");
    };
    let Value::Map(mut mso) = decode(&mso_bytes) else {
        panic!("MSO must be a map");
    };
    mutate(&mut mso);

    let payload = encode(Value::Tag(
        24,
        Box::new(Value::Bytes(encode(Value::Map(mso)))),
    ));
    let sig_structure = encode(Value::Array(vec![
        Value::Text("Signature1".to_string()),
        Value::Bytes(protected),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.clone()),
    ]));
    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("demo issuer key");
    let signature: P256Signature = signing_key.sign(&sig_structure);
    issuer_auth[2] = Value::Bytes(payload);
    issuer_auth[3] = Value::Bytes(signature.to_bytes().to_vec());
}

fn mutate_selected_value_and_bind_digest(
    document: &mut Value,
    item_index: usize,
    digest_id: u64,
    replacement: Value,
) {
    let item_bytes = {
        let items = issuer_items_mut(document);
        let Value::Tag(24, encoded_item) = &mut items[item_index] else {
            panic!("IssuerSignedItemBytes must use tag 24");
        };
        let Value::Bytes(item_bytes) = encoded_item.as_mut() else {
            panic!("IssuerSignedItemBytes tag must contain bytes");
        };
        let Value::Map(mut item) = decode(item_bytes) else {
            panic!("IssuerSignedItem must be a map");
        };
        *text_value_mut(&mut item, "elementValue") = replacement;
        *item_bytes = encode(Value::Map(item));
        encode(items[item_index].clone())
    };
    let digest = Sha256::digest(item_bytes).to_vec();

    mutate_mso_and_resign(document, |mso| {
        let value_digests = value_map_mut(text_value_mut(mso, "valueDigests"), "valueDigests");
        let namespace_digests = value_map_mut(
            text_value_mut(value_digests, PID_NAMESPACE),
            "PID valueDigests",
        );
        let digest_value = namespace_digests
            .iter_mut()
            .find_map(|(key, value)| (key == &Value::from(digest_id)).then_some(value))
            .expect("selected digest ID exists");
        *digest_value = Value::Bytes(digest);
    });
}

fn policy_on(base: &Policy, year: u32, month: u32, day: u32) -> Policy {
    let mut policy = base.clone();
    policy.current_date = Date { year, month, day };
    policy
}

#[test]
fn deterministic_fixture_is_only_current_mdoc_2_text_date_alpha2_profile() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    mdoc::validate_product_mdoc_cbor_structure(&fixture.document)
        .expect("current product document has bounded deterministic CBOR");

    assert_eq!(fixture.request.doctype, PID_NAMESPACE);
    assert_eq!(fixture.request.namespace, PID_NAMESPACE);
    assert_eq!(fixture.extracted.birth_date_binding.0, *b"1990-07-15");
    assert_eq!(fixture.extracted.nationality_binding.0, *b"DE");
    assert_eq!(
        fixture.extracted.valid_from_timestamp,
        MdocTimestamp {
            year: 2026,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
        }
    );
    assert_eq!(
        fixture.extracted.valid_until_timestamp,
        MdocTimestamp {
            year: 2030,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
        }
    );

    let digest_ids = fixture
        .extracted
        .extracted_attributes
        .iter()
        .map(|attribute| attribute.digest_id)
        .collect::<Vec<_>>();
    assert_eq!(digest_ids, vec![7, 9]);
    assert_ne!(digest_ids[0], digest_ids[1]);
    assert_eq!(fixture.statement.age_attribute_index, Some(0));
    assert_eq!(fixture.statement.nationality_attribute_index, Some(1));
}

#[test]
fn product_cbor_rejects_malformed_and_noncanonical_encodings() {
    for (label, bytes) in [
        ("indefinite container", vec![0x9f, 0xff]),
        ("trailing root", vec![0xf6, 0xf6]),
        ("non-minimal integer", vec![0x18, 0x01]),
    ] {
        assert!(
            matches!(
                mdoc::validate_product_mdoc_cbor_structure(&bytes),
                Err(MdocError::Cbor(_))
            ),
            "{label} must be rejected"
        );
    }

    let mut too_deep = vec![0xc0; 8];
    too_deep.push(0xf6);
    assert!(matches!(
        mdoc::validate_product_mdoc_cbor_structure(&too_deep),
        Err(MdocError::Cbor(message)) if message.contains("nesting exceeds 8")
    ));

    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut document = decode(&fixture.document);
    let items = issuer_items_mut(&mut document);
    let Value::Tag(24, encoded_item) = &mut items[0] else {
        panic!("IssuerSignedItemBytes must use tag 24");
    };
    let Value::Bytes(item_bytes) = encoded_item.as_mut() else {
        panic!("IssuerSignedItemBytes tag must contain bytes");
    };
    let Value::Map(mut item) = decode(item_bytes) else {
        panic!("IssuerSignedItem must be a map");
    };
    item.swap(0, 1);
    *item_bytes = encode(Value::Map(item));
    assert!(matches!(
        prove_mdoc(
            &encode(document),
            &fixture.request,
            fixture.statement.policy
        ),
        Err(Error::Mdoc(MdocError::UnsupportedCircuitValue(
            "IssuerSignedItem canonical key order"
        )))
    ));
}

#[test]
fn product_rejects_duplicate_digest_ids_and_unsupported_value_encodings() {
    let duplicate_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut duplicate = decode(&duplicate_fixture.document);
    mutate_mso_and_resign(&mut duplicate, |mso| {
        let value_digests = value_map_mut(text_value_mut(mso, "valueDigests"), "valueDigests");
        let namespace_digests = value_map_mut(
            text_value_mut(value_digests, PID_NAMESPACE),
            "PID valueDigests",
        );
        let first = namespace_digests[0].clone();
        namespace_digests.push(first);
    });
    assert!(matches!(
        prove_mdoc(
            &encode(duplicate),
            &duplicate_fixture.request,
            duplicate_fixture.statement.policy
        ),
        Err(Error::Mdoc(MdocError::InvalidProductDocumentShape(
            "duplicate valueDigests digestID"
        )))
    ));

    let birth_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut packed_birth = decode(&birth_fixture.document);
    mutate_selected_value_and_bind_digest(
        &mut packed_birth,
        0,
        7,
        Value::Bytes(vec![0x07, 0xc6, 7, 15]),
    );
    assert!(matches!(
        prove_mdoc(
            &encode(packed_birth),
            &birth_fixture.request,
            birth_fixture.statement.policy
        ),
        Err(Error::Mdoc(MdocError::WrongType("birth_date elementValue")))
    ));

    let nationality_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut numeric_nationality = decode(&nationality_fixture.document);
    mutate_selected_value_and_bind_digest(
        &mut numeric_nationality,
        1,
        9,
        Value::Array(vec![Value::from(276)]),
    );
    assert!(matches!(
        prove_mdoc(
            &encode(numeric_nationality),
            &nationality_fixture.request,
            nationality_fixture.statement.policy
        ),
        Err(Error::Mdoc(MdocError::WrongType(
            "nationality elementValue"
        )))
    ));

    let version_fixture = mdoc::demo_mdoc_circuit_fixture();
    let mut version_one = decode(&version_fixture.document);
    mutate_mso_and_resign(&mut version_one, |mso| {
        *text_value_mut(mso, "version") = Value::Text("1.0".to_string());
    });
    assert!(matches!(
        prove_mdoc(
            &encode(version_one),
            &version_fixture.request,
            version_fixture.statement.policy
        ),
        Err(Error::Mdoc(MdocError::UnsupportedMsoVersion(version))) if version == "1.0"
    ));
}

#[test]
fn verifier_time_uses_strict_second_boundaries() {
    const VALID_FROM: u64 = 1_767_225_600;
    const VALID_UNTIL: u64 = 1_893_456_000;

    let fixture = mdoc::demo_mdoc_circuit_fixture();
    assert_eq!(
        MdocCircuitStatement::from_extracted_at(
            &fixture.extracted,
            policy_on(&fixture.statement.policy, 2026, 1, 1),
            VALID_FROM,
        )
        .unwrap_err(),
        MdocError::CredentialNotYetValid
    );
    MdocCircuitStatement::from_extracted_at(
        &fixture.extracted,
        policy_on(&fixture.statement.policy, 2026, 1, 1),
        VALID_FROM + 1,
    )
    .expect("one second after validFrom is accepted");
    MdocCircuitStatement::from_extracted_at(
        &fixture.extracted,
        policy_on(&fixture.statement.policy, 2029, 12, 31),
        VALID_UNTIL - 1,
    )
    .expect("one second before validUntil is accepted");
    assert_eq!(
        MdocCircuitStatement::from_extracted_at(
            &fixture.extracted,
            policy_on(&fixture.statement.policy, 2030, 1, 1),
            VALID_UNTIL,
        )
        .unwrap_err(),
        MdocError::CredentialExpired
    );
}

#[test]
fn mandatory_revocation_binds_mso_range_epoch_key_and_signature() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let public = Ts13RevocationStatement {
        revocation_public_key: fixture
            .request
            .revocation
            .public_inputs
            .revocation_public_key
            .clone(),
        epoch: fixture.request.revocation.public_inputs.epoch,
    };
    let witness = Ts13RevocationWitness {
        id: fixture.statement.ts13_revocation_range.id,
        id_lo: fixture.request.revocation.id_lo,
        id_hi: fixture.request.revocation.id_hi,
        epoch: fixture.request.revocation.public_inputs.epoch,
        signature: fixture.request.revocation.signature.clone(),
    };

    assert_eq!(
        witness.id,
        ts13_mso_derived_revocation_id(&fixture.extracted.mso)
    );
    assert_eq!(
        fixture.statement.ts13_revocation,
        fixture.request.revocation.public_inputs
    );
    assert_eq!(
        fixture.statement.ts13_revocation_range.id_lo,
        fixture.request.revocation.id_lo
    );
    assert_eq!(
        fixture.statement.ts13_revocation_range.id_hi,
        fixture.request.revocation.id_hi
    );
    assert_eq!(
        fixture.statement.ts13_revocation_signature,
        fixture.request.revocation.signature
    );
    public
        .verify_witness(&fixture.extracted, &witness)
        .expect("current mandatory revocation witness verifies");

    let mut wrong_id = witness.clone();
    wrong_id.id ^= 1;
    assert_eq!(
        public.verify_witness(&fixture.extracted, &wrong_id),
        Err(Ts13RevocationError::DerivedIdMismatch)
    );

    let mut equal_lower = witness.clone();
    equal_lower.id_lo = equal_lower.id;
    assert_eq!(
        public.verify_witness(&fixture.extracted, &equal_lower),
        Err(Ts13RevocationError::Range)
    );

    let mut equal_upper = witness.clone();
    equal_upper.id_hi = equal_upper.id;
    assert_eq!(
        public.verify_witness(&fixture.extracted, &equal_upper),
        Err(Ts13RevocationError::Range)
    );

    let mut stale_epoch = witness.clone();
    stale_epoch.epoch += 1;
    assert_eq!(
        public.verify_witness(&fixture.extracted, &stale_epoch),
        Err(Ts13RevocationError::Epoch)
    );

    let mut forged = witness;
    forged.signature.s.0[31] ^= 1;
    assert_eq!(
        public.verify_witness(&fixture.extracted, &forged),
        Err(Ts13RevocationError::InvalidSignature)
    );
}
