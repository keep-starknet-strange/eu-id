//! Demo-only ML-DSA-65 issuance helpers exported over UniFFI.
//!
//! ## Status
//!
//! This module is NOT a production capability. No post-quantum PID issuer or
//! PKI exists yet. For end-to-end demos, a fixed deterministic "demo issuer"
//! re-signs an existing (P-256) PID mdoc under ML-DSA-65. The wallet mints
//! such a document. The verifier pins `sha256(demo_issuer_public_key())` as
//! its trust anchor.
//!
//! ## Keys
//!
//! This module owns the issuer key: the module is the single source of truth
//! for the pin. The device key is a caller-supplied parameter, because holder
//! binding is per-wallet. The deterministic seeds mirror `eu-id-prover`'s
//! `mldsa_fixture`, so the reference and the demo agree.

use ciborium::value::Value;
use eu_id_prover::ts13_demo::{ML_DSA_65_PUBLIC_KEY_BYTES, ML_DSA_65_SIGNATURE_BYTES};
use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};

use crate::ZkError;

/// CBOR tag 24 (`encoded-cbor`), wrapping `MobileSecurityObjectBytes`.
const CBOR_TAG_ENCODED_CBOR: u64 = 24;
/// COSE alg id for ML-DSA-65 (`stwo_mldsa::constants::COSE_ALG_ML_DSA_65`).
const COSE_ALG_ML_DSA_65: i64 = -49;
/// COSE key type "AKP" (`stwo_mldsa::constants::COSE_KTY_AKP`).
const COSE_KTY_AKP: i64 = 7;
/// Deterministic ML-DSA-65 demo issuer seed (mirrors the eu-id-prover fixture).
const MLDSA_ISSUER_SEED: [u8; 32] = [0x5au8; 32];
/// Deterministic ML-DSA-65 demo revocation-authority seed.
const MLDSA_REVOCATION_SEED: [u8; 32] = [0x7eu8; 32];
/// Epoch used by the demo revocation authority.
const DEMO_REVOCATION_EPOCH: u32 = 17;

fn issuer_signing_key() -> SigningKey<MlDsa65> {
    SigningKey::<MlDsa65>::from_seed(&MLDSA_ISSUER_SEED.into())
}

fn revocation_signing_key() -> SigningKey<MlDsa65> {
    SigningKey::<MlDsa65>::from_seed(&MLDSA_REVOCATION_SEED.into())
}

fn encode_value(value: &Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(value, &mut out).expect("CBOR serialization is infallible");
    out
}

fn decode_value(bytes: &[u8]) -> Result<Value, ZkError> {
    ciborium::de::from_reader(bytes)
        .map_err(|e| ZkError::InvalidInput(format!("invalid CBOR: {e}")))
}

/// Serializes the COSE `protected` header `{1: -49}` to a bstr.
fn mldsa_protected_header() -> Vec<u8> {
    encode_value(&Value::Map(vec![(
        Value::from(1),
        Value::from(COSE_ALG_ML_DSA_65),
    )]))
}

/// COSE `Sig_structure` (RFC 9052 §4.4) for a COSE_Sign1 with empty external AAD.
fn sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    encode_value(&Value::Array(vec![
        Value::Text("Signature1".to_string()),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.to_vec()),
    ]))
}

/// Builds an ML-DSA-65 AKP COSE_Key: `{1: AKP, 3: -49, -1: pkEncode}`.
fn mldsa_cose_key(pk: &[u8]) -> Value {
    Value::Map(vec![
        (Value::from(1), Value::from(COSE_KTY_AKP)),
        (Value::from(3), Value::from(COSE_ALG_ML_DSA_65)),
        (Value::from(-1), Value::Bytes(pk.to_vec())),
    ])
}

fn as_map(value: &Value, ctx: &str) -> Result<Vec<(Value, Value)>, ZkError> {
    match value {
        Value::Map(entries) => Ok(entries.clone()),
        _ => Err(ZkError::InvalidInput(format!(
            "expected a CBOR map for {ctx}"
        ))),
    }
}

fn map_get<'a>(entries: &'a [(Value, Value)], key: &str) -> Result<&'a Value, ZkError> {
    entries
        .iter()
        .find(|(k, _)| matches!(k, Value::Text(t) if t == key))
        .map(|(_, v)| v)
        .ok_or_else(|| ZkError::InvalidInput(format!("missing field '{key}'")))
}

/// Lifts the `MobileSecurityObject` map out of a COSE_Sign1 payload, accepting
/// both the standard `#6.24(bstr .cbor MSO)` wrapping and a bare MSO map.
fn lift_mso(payload: &[u8]) -> Result<Value, ZkError> {
    match decode_value(payload)? {
        Value::Tag(CBOR_TAG_ENCODED_CBOR, inner) => match *inner {
            Value::Bytes(bytes) => decode_value(&bytes),
            _ => Err(ZkError::InvalidInput(
                "MobileSecurityObjectBytes is not a bstr".to_string(),
            )),
        },
        other => Ok(other),
    }
}

/// Returns a copy of `mso` with `deviceKeyInfo.deviceKey` replaced by
/// `device_key`.
fn replace_device_key(mso: &Value, device_key: Value) -> Result<Value, ZkError> {
    let mut out = mso.clone();
    let Value::Map(entries) = &mut out else {
        return Err(ZkError::InvalidInput(
            "expected a CBOR map for MobileSecurityObject".to_string(),
        ));
    };
    let mut replaced = false;
    for (key, value) in entries {
        if matches!(key, Value::Text(text) if text == "deviceKeyInfo") {
            let Value::Map(device_key_info) = value else {
                return Err(ZkError::InvalidInput(
                    "expected a CBOR map for deviceKeyInfo".to_string(),
                ));
            };
            for (key, value) in device_key_info {
                if matches!(key, Value::Text(text) if text == "deviceKey") {
                    *value = device_key.clone();
                    replaced = true;
                }
            }
        }
    }
    if !replaced {
        return Err(ZkError::InvalidInput(
            "MSO has no deviceKeyInfo.deviceKey to replace".to_string(),
        ));
    }
    Ok(out)
}

/// The demo issuer's ML-DSA-65 public key (`pkEncode`). The verifier pins
/// `sha256` of this as its trusted issuer key.
#[uniffi::export]
pub fn demo_issuer_public_key() -> Vec<u8> {
    let vk: EncodedVerifyingKey<MlDsa65> = issuer_signing_key().verifying_key().encode();
    vk.to_vec()
}

/// A signed open interval that contains the MSO-derived revocation ID.
#[derive(uniffi::Record, Clone, Debug, PartialEq, Eq)]
pub struct DemoRevocationWitness {
    pub id_lo: u64,
    pub id_hi: u64,
    pub signature: Vec<u8>,
}

/// The demo revocation authority's ML-DSA-65 public key (`pkEncode`).
#[uniffi::export]
pub fn demo_revocation_public_key() -> Vec<u8> {
    let vk: EncodedVerifyingKey<MlDsa65> = revocation_signing_key().verifying_key().encode();
    vk.to_vec()
}

/// The epoch signed by the demo revocation authority.
#[uniffi::export]
pub fn demo_revocation_epoch() -> u32 {
    DEMO_REVOCATION_EPOCH
}

/// Builds the demo revocation witness for an assembled ML-DSA mdoc `Document`.
#[uniffi::export]
pub fn demo_revocation_witness(document: Vec<u8>) -> Result<DemoRevocationWitness, ZkError> {
    let document = as_map(&decode_value(&document)?, "Document")?;
    let issuer_signed = as_map(map_get(&document, "issuerSigned")?, "issuerSigned")?;
    let issuer_auth = match map_get(&issuer_signed, "issuerAuth")? {
        Value::Array(items) if items.len() == 4 => items,
        _ => {
            return Err(ZkError::InvalidInput(
                "issuerAuth is not a 4-element COSE_Sign1 array".to_string(),
            ))
        }
    };
    let mso_payload = match &issuer_auth[2] {
        Value::Bytes(bytes) => bytes,
        _ => {
            return Err(ZkError::InvalidInput(
                "issuerAuth payload is not a bstr".to_string(),
            ))
        }
    };
    let id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(mso_payload);
    let id_lo = id.checked_sub(1).ok_or_else(|| {
        ZkError::InvalidInput("demo revocation ID has no lower endpoint".to_string())
    })?;
    let id_hi = id.checked_add(1).ok_or_else(|| {
        ZkError::InvalidInput("demo revocation ID has no upper endpoint".to_string())
    })?;
    let message = eu_id_prover::ts13::ts13_revocation_message(id_lo, id_hi, DEMO_REVOCATION_EPOCH);
    let signature: EncodedSignature<MlDsa65> = revocation_signing_key().sign(&message).encode();
    Ok(DemoRevocationWitness {
        id_lo,
        id_hi,
        signature: signature.to_vec(),
    })
}

/// Re-issues a P-256 PID mdoc under the demo ML-DSA-65 issuer.
///
/// Takes the wallet's real `IssuerSigned` CBOR (`{nameSpaces, issuerAuth}`).
/// Keeps the namespaces, and thus the `valueDigests`, verbatim. Replaces the
/// MSO `deviceKey` with `device_public_key` (an ML-DSA-65 `pkEncode`).
/// Re-signs `issuerAuth` with the demo issuer key. Returns the new ML-DSA
/// `IssuerSigned` CBOR.
///
/// This function does not verify the incoming P-256 signature. It reads only
/// the CBOR.
#[uniffi::export]
pub fn demo_mint_ml_dsa_signed_pid_mdoc(
    p256_issuer_signed: Vec<u8>,
    device_public_key: Vec<u8>,
) -> Result<Vec<u8>, ZkError> {
    if device_public_key.len() != ML_DSA_65_PUBLIC_KEY_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "device_public_key must be a {ML_DSA_65_PUBLIC_KEY_BYTES}-byte ML-DSA-65 pkEncode, got {}",
            device_public_key.len()
        )));
    }

    let issuer_signed = as_map(&decode_value(&p256_issuer_signed)?, "IssuerSigned")?;
    let name_spaces = map_get(&issuer_signed, "nameSpaces")?.clone();
    let issuer_auth = match map_get(&issuer_signed, "issuerAuth")? {
        Value::Array(items) if items.len() == 4 => items.clone(),
        _ => {
            return Err(ZkError::InvalidInput(
                "issuerAuth is not a 4-element COSE_Sign1 array".to_string(),
            ))
        }
    };
    let payload = match &issuer_auth[2] {
        Value::Bytes(bytes) => bytes.clone(),
        _ => {
            return Err(ZkError::InvalidInput(
                "issuerAuth payload is not a bstr".to_string(),
            ))
        }
    };

    let mso = lift_mso(&payload)?;
    let new_mso = replace_device_key(&mso, mldsa_cose_key(&device_public_key))?;
    // Standard MobileSecurityObjectBytes: #6.24(bstr .cbor MSO).
    let new_payload = encode_value(&Value::Tag(
        CBOR_TAG_ENCODED_CBOR,
        Box::new(Value::Bytes(encode_value(&new_mso))),
    ));

    let protected = mldsa_protected_header();
    let signature: Vec<u8> = {
        let sig = issuer_signing_key().sign(&sig_structure(&protected, &new_payload));
        let encoded: EncodedSignature<MlDsa65> = sig.encode();
        encoded.to_vec()
    };

    let new_issuer_auth = Value::Array(vec![
        Value::Bytes(protected),
        Value::Map(vec![(
            Value::Text("issuerKey".to_string()),
            mldsa_cose_key(&demo_issuer_public_key()),
        )]),
        Value::Bytes(new_payload),
        Value::Bytes(signature),
    ]);

    Ok(encode_value(&Value::Map(vec![
        (Value::Text("nameSpaces".to_string()), name_spaces),
        (Value::Text("issuerAuth".to_string()), new_issuer_auth),
    ])))
}

/// Returns the COSE `Sig_structure` that the device signs for the
/// presentation. The structure covers the `DeviceAuthentication` derived from
/// `session_transcript` and `doctype`.
///
/// For the in-memory re-sign path, the caller signs these bytes with its own
/// ML-DSA-65 key (for example, a hardware-backed Android Keystore device key)
/// and passes the resulting signature to [demo_build_ml_dsa_witness]. Signing
/// on the caller side lets the real hardware device key do the signing.
#[uniffi::export]
pub fn demo_device_auth_sig_structure(
    session_transcript: Vec<u8>,
    doctype: String,
) -> Result<Vec<u8>, ZkError> {
    let device_payload =
        eu_id_prover::mdoc::device_authentication_bytes(&session_transcript, &doctype).map_err(
            |e| ZkError::InvalidInput(format!("invalid DeviceAuthentication input: {e:?}")),
        )?;
    Ok(sig_structure(&mldsa_protected_header(), &device_payload))
}

/// Assembles the full ISO 18013-5 `Document` CBOR that the prover consumes as
/// the witness.
///
/// Combines an ML-DSA `IssuerSigned` (from [demo_mint_ml_dsa_signed_pid_mdoc])
/// with a `deviceSigned`. The `deviceSignature` carries `device_signature`:
/// the caller's raw FIPS 204 `sigEncode` over the
/// [demo_device_auth_sig_structure] bytes. Keeps all CBOR/COSE assembly in
/// Rust, so the wallet only signs and calls.
#[uniffi::export]
pub fn demo_build_ml_dsa_witness(
    ml_dsa_issuer_signed: Vec<u8>,
    session_transcript: Vec<u8>,
    doctype: String,
    device_signature: Vec<u8>,
) -> Result<Vec<u8>, ZkError> {
    if device_signature.len() != ML_DSA_65_SIGNATURE_BYTES {
        return Err(ZkError::InvalidInput(format!(
            "device_signature must be a {ML_DSA_65_SIGNATURE_BYTES}-byte ML-DSA-65 sigEncode, got {}",
            device_signature.len()
        )));
    }
    let issuer_signed = decode_value(&ml_dsa_issuer_signed)?;
    let device_payload =
        eu_id_prover::mdoc::device_authentication_bytes(&session_transcript, &doctype).map_err(
            |e| ZkError::InvalidInput(format!("invalid DeviceAuthentication input: {e:?}")),
        )?;

    // deviceSignature COSE_Sign1 [protected {1:-49}, {}, payload, signature].
    let device_signature_cose = Value::Array(vec![
        Value::Bytes(mldsa_protected_header()),
        Value::Map(Vec::new()),
        Value::Bytes(device_payload),
        Value::Bytes(device_signature),
    ]);

    // Document { docType, issuerSigned, deviceSigned { deviceAuth { deviceSignature } } }.
    let document = Value::Map(vec![
        (Value::Text("docType".to_string()), Value::Text(doctype)),
        (Value::Text("issuerSigned".to_string()), issuer_signed),
        (
            Value::Text("deviceSigned".to_string()),
            Value::Map(vec![(
                Value::Text("deviceAuth".to_string()),
                Value::Map(vec![(
                    Value::Text("deviceSignature".to_string()),
                    device_signature_cose,
                )]),
            )]),
        ),
    ]);
    Ok(encode_value(&document))
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo_mldsa::profile::MlDsaProfile;
    use stwo_mldsa::reference::verify::verify_internals;

    const PID_NS: &str = "eu.europa.ec.eudi.pid.1";
    /// Deterministic ML-DSA-65 demo device seed (mirrors the eu-id-prover fixture).
    const MLDSA_DEVICE_SEED: [u8; 32] = [0x6du8; 32];

    fn device_signing_key() -> SigningKey<MlDsa65> {
        SigningKey::<MlDsa65>::from_seed(&MLDSA_DEVICE_SEED.into())
    }

    /// The demo device's ML-DSA-65 `pkEncode`. This key is a convenient valid
    /// device key for the mint and build-witness tests. The production device
    /// key is the wallet's Keystore key.
    fn device_public_key() -> Vec<u8> {
        let vk: EncodedVerifyingKey<MlDsa65> = device_signing_key().verifying_key().encode();
        vk.to_vec()
    }

    /// Builds a minimal P-256-style `IssuerSigned`. Only the CBOR shape
    /// matters, because the mint never verifies the incoming signature. The
    /// MSO carries a placeholder deviceKey and a `valueDigests` entry that the
    /// mint must preserve verbatim.
    fn dummy_p256_issuer_signed() -> Vec<u8> {
        let mso = Value::Map(vec![
            ("version".into(), "1.0".into()),
            ("docType".into(), PID_NS.into()),
            ("digestAlgorithm".into(), "SHA-256".into()),
            (
                "valueDigests".into(),
                Value::Map(vec![(
                    PID_NS.into(),
                    Value::Map(vec![(Value::from(7), Value::Bytes(vec![0xAB; 32]))]),
                )]),
            ),
            (
                "deviceKeyInfo".into(),
                Value::Map(vec![(
                    "deviceKey".into(),
                    Value::Text("p256-placeholder".into()),
                )]),
            ),
            (
                "validityInfo".into(),
                Value::Map(vec![(
                    "signed".into(),
                    Value::Tag(0, Box::new("2026-01-01T00:00:00Z".into())),
                )]),
            ),
        ]);
        let payload = encode_value(&Value::Tag(
            CBOR_TAG_ENCODED_CBOR,
            Box::new(Value::Bytes(encode_value(&mso))),
        ));
        let issuer_auth = Value::Array(vec![
            Value::Bytes(vec![0xA0]), // dummy protected header
            Value::Map(Vec::new()),   // dummy unprotected (x5chain for a real P-256 mdoc)
            Value::Bytes(payload),
            Value::Bytes(vec![0u8; 64]), // dummy P-256 signature
        ]);
        let name_spaces = Value::Map(vec![(
            PID_NS.into(),
            Value::Array(vec![Value::Bytes(vec![1, 2, 3])]),
        )]);
        encode_value(&Value::Map(vec![
            ("nameSpaces".into(), name_spaces),
            ("issuerAuth".into(), issuer_auth),
        ]))
    }

    #[test]
    fn device_key_replacement_updates_duplicates_and_preserves_map_errors() {
        let replacement = Value::Bytes(vec![7]);
        let device_key_info = || {
            Value::Map(vec![
                ("deviceKey".into(), "first".into()),
                ("deviceKey".into(), "second".into()),
            ])
        };
        let mso = Value::Map(vec![
            ("deviceKeyInfo".into(), device_key_info()),
            ("deviceKeyInfo".into(), device_key_info()),
        ]);

        let replaced = replace_device_key(&mso, replacement.clone()).expect("replace keys");
        let replaced_entries = as_map(&replaced, "MobileSecurityObject").expect("MSO map");
        let replaced_keys = replaced_entries
            .iter()
            .filter(|(key, _)| matches!(key, Value::Text(text) if text == "deviceKeyInfo"))
            .flat_map(|(_, value)| as_map(value, "deviceKeyInfo").expect("device key map"))
            .filter(|(key, _)| matches!(key, Value::Text(text) if text == "deviceKey"))
            .collect::<Vec<_>>();
        assert_eq!(replaced_keys.len(), 4);
        assert!(replaced_keys.iter().all(|(_, value)| value == &replacement));

        for (malformed, message) in [
            (Value::Null, "expected a CBOR map for MobileSecurityObject"),
            (
                Value::Map(vec![("deviceKeyInfo".into(), Value::Null)]),
                "expected a CBOR map for deviceKeyInfo",
            ),
            (
                Value::Map(vec![("deviceKeyInfo".into(), Value::Map(Vec::new()))]),
                "MSO has no deviceKeyInfo.deviceKey to replace",
            ),
        ] {
            assert_eq!(
                replace_device_key(&malformed, replacement.clone()),
                Err(ZkError::InvalidInput(message.to_string()))
            );
        }
    }

    #[test]
    fn mint_rebinds_device_key_and_signs_with_demo_issuer() {
        let input = dummy_p256_issuer_signed();
        let device_pk = device_public_key();
        let minted = demo_mint_ml_dsa_signed_pid_mdoc(input.clone(), device_pk.clone())
            .expect("mint succeeds");

        let issuer_signed = as_map(&decode_value(&minted).unwrap(), "IssuerSigned").unwrap();
        let issuer_auth = match map_get(&issuer_signed, "issuerAuth").unwrap() {
            Value::Array(items) => items.clone(),
            _ => panic!("issuerAuth not an array"),
        };

        // Protected header is ML-DSA-65.
        assert_eq!(issuer_auth[0], Value::Bytes(mldsa_protected_header()));

        // Unprotected header carries the demo issuer's AKP key.
        let unprotected = as_map(&issuer_auth[1], "unprotected").unwrap();
        assert_eq!(
            map_get(&unprotected, "issuerKey").unwrap(),
            &mldsa_cose_key(&demo_issuer_public_key()),
        );

        // MSO deviceKey rebound to the supplied device key; valueDigests preserved.
        let payload = match &issuer_auth[2] {
            Value::Bytes(bytes) => bytes.clone(),
            _ => panic!("payload not a bstr"),
        };
        let mso = as_map(&lift_mso(&payload).unwrap(), "MSO").unwrap();
        let device_key_info = as_map(map_get(&mso, "deviceKeyInfo").unwrap(), "dki").unwrap();
        assert_eq!(
            map_get(&device_key_info, "deviceKey").unwrap(),
            &mldsa_cose_key(&device_pk),
        );
        let value_digests = as_map(map_get(&mso, "valueDigests").unwrap(), "vd").unwrap();
        let ns_digests = as_map(map_get(&value_digests, PID_NS).unwrap(), "ns").unwrap();
        assert_eq!(ns_digests[0].1, Value::Bytes(vec![0xAB; 32]));

        // nameSpaces preserved verbatim.
        let input_ns = map_get(
            &as_map(&decode_value(&input).unwrap(), "in").unwrap(),
            "nameSpaces",
        )
        .unwrap()
        .clone();
        assert_eq!(map_get(&issuer_signed, "nameSpaces").unwrap(), &input_ns);

        // The signature verifies under the demo issuer key. The check uses the
        // prover's own reference verifier, so proving accepts the signature.
        let signature = match &issuer_auth[3] {
            Value::Bytes(bytes) => bytes.clone(),
            _ => panic!("signature not a bstr"),
        };
        let trace = verify_internals(
            MlDsaProfile::MlDsa65,
            &demo_issuer_public_key(),
            &sig_structure(&mldsa_protected_header(), &payload),
            &signature,
        )
        .expect("verify runs");
        assert!(trace.accepted, "minted issuerAuth signature must verify");
    }

    #[test]
    fn mint_rejects_wrong_length_device_key() {
        let err = demo_mint_ml_dsa_signed_pid_mdoc(dummy_p256_issuer_signed(), vec![0u8; 10]);
        assert!(matches!(err, Err(ZkError::InvalidInput(_))));
    }

    #[test]
    fn build_witness_assembles_document_with_verifiable_device_signature() {
        let transcript = eu_id_prover::mdoc::openid4vp_session_transcript(b"witness-probe");
        let issuer_signed =
            demo_mint_ml_dsa_signed_pid_mdoc(dummy_p256_issuer_signed(), device_public_key())
                .expect("mint");

        // Real path: the caller signs the sig_structure with its own key. In
        // this test the demo device key stands in for the Keystore key.
        let sig_struct = demo_device_auth_sig_structure(transcript.clone(), PID_NS.to_string())
            .expect("sig_structure");
        let device_signature = {
            let sig = device_signing_key().sign(&sig_struct);
            let encoded: EncodedSignature<MlDsa65> = sig.encode();
            encoded.to_vec()
        };

        let witness = demo_build_ml_dsa_witness(
            issuer_signed,
            transcript,
            PID_NS.to_string(),
            device_signature.clone(),
        )
        .expect("build witness");

        // Structure: { docType, issuerSigned, deviceSigned { deviceAuth { deviceSignature } } }.
        let doc = as_map(&decode_value(&witness).unwrap(), "Document").unwrap();
        assert_eq!(
            map_get(&doc, "docType").unwrap(),
            &Value::Text(PID_NS.to_string())
        );
        assert!(map_get(&doc, "issuerSigned").is_ok());
        let device_signed = as_map(map_get(&doc, "deviceSigned").unwrap(), "deviceSigned").unwrap();
        let device_auth =
            as_map(map_get(&device_signed, "deviceAuth").unwrap(), "deviceAuth").unwrap();
        let device_sig_cose = match map_get(&device_auth, "deviceSignature").unwrap() {
            Value::Array(items) => items.clone(),
            _ => panic!("deviceSignature not a COSE_Sign1 array"),
        };
        let embedded_sig = match &device_sig_cose[3] {
            Value::Bytes(bytes) => bytes.clone(),
            _ => panic!("signature not a bstr"),
        };

        // The embedded device signature verifies against the sig_structure the caller signed.
        let trace = verify_internals(
            MlDsaProfile::MlDsa65,
            &device_public_key(),
            &sig_struct,
            &embedded_sig,
        )
        .expect("verify");
        assert!(trace.accepted, "assembled deviceSignature must verify");
    }

    #[test]
    fn build_witness_rejects_wrong_length_device_signature() {
        let err = demo_build_ml_dsa_witness(
            vec![0xA0],
            eu_id_prover::mdoc::openid4vp_session_transcript(b"x"),
            PID_NS.to_string(),
            vec![0u8; 10],
        );
        assert!(matches!(err, Err(ZkError::InvalidInput(_))));
    }

    #[test]
    fn revocation_helpers_sign_the_mso_derived_open_interval() {
        let issuer_signed =
            demo_mint_ml_dsa_signed_pid_mdoc(dummy_p256_issuer_signed(), device_public_key())
                .expect("mint");
        let issuer_signed_value = decode_value(&issuer_signed).expect("decode issuerSigned");
        let issuer_signed_map = as_map(&issuer_signed_value, "IssuerSigned").expect("map");
        let issuer_auth = match map_get(&issuer_signed_map, "issuerAuth").expect("issuerAuth") {
            Value::Array(items) => items,
            _ => panic!("issuerAuth not an array"),
        };
        let mso_payload = match &issuer_auth[2] {
            Value::Bytes(bytes) => bytes,
            _ => panic!("payload not a bstr"),
        };
        let expected_id = eu_id_prover::ts13::ts13_mso_derived_revocation_id(mso_payload);
        let document = demo_build_ml_dsa_witness(
            issuer_signed,
            eu_id_prover::mdoc::openid4vp_session_transcript(b"revocation-probe"),
            PID_NS.to_string(),
            vec![0u8; ML_DSA_65_SIGNATURE_BYTES],
        )
        .expect("build document");

        let witness = demo_revocation_witness(document).expect("build revocation witness");
        assert_eq!(witness.id_lo + 1, expected_id);
        assert_eq!(witness.id_hi - 1, expected_id);
        assert_eq!(demo_revocation_epoch(), DEMO_REVOCATION_EPOCH);
        assert_eq!(
            demo_revocation_public_key().len(),
            ML_DSA_65_PUBLIC_KEY_BYTES
        );

        let message = eu_id_prover::ts13::ts13_revocation_message(
            witness.id_lo,
            witness.id_hi,
            demo_revocation_epoch(),
        );
        let trace = verify_internals(
            MlDsaProfile::MlDsa65,
            &demo_revocation_public_key(),
            &message,
            &witness.signature,
        )
        .expect("verify revocation signature");
        assert!(trace.accepted, "demo revocation signature must verify");
    }

    #[test]
    fn revocation_witness_rejects_a_document_without_issuer_auth() {
        let err = demo_revocation_witness(vec![0xa0]);
        assert!(matches!(err, Err(ZkError::InvalidInput(_))));
    }
}
