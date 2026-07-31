//! ML-DSA-65 mdoc test fixture.
//!
//! The issuer, device, and revocation authority use deterministic ML-DSA-65 keys.
//! Issuer and device authentication sign the standard COSE `Sig_structure`.
//! Revocation signs the raw 20-byte message.

use ciborium::value::Value;
use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use sha2::{Digest, Sha256};

use stwo_mldsa::constants::{COSE_ALG_ML_DSA_65, COSE_KTY_AKP};
const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const EXTRA_VALUE_DIGESTS_NAMESPACE: &str = "org.example.issuer.metadata";
const EXTRA_VALUE_DIGESTS_ID: u64 = 0;
const EXTRA_VALUE_DIGEST: [u8; 32] = [0xa5; 32];
const MDOC_PROFILE_VERSION: &str = "1.0";
const CBOR_TAG_ENCODED_CBOR: u64 = 24;

/// Deterministic ML-DSA-65 issuer seed.
const MLDSA_ISSUER_SEED: [u8; 32] = [0x5au8; 32];
/// Deterministic ML-DSA-65 device seed.
const MLDSA_DEVICE_SEED: [u8; 32] = [0x6du8; 32];
/// Independent deterministic device key for credential B.
const MLDSA_DEVICE_B_SEED: [u8; 32] = [0x6eu8; 32];
/// Deterministic ML-DSA-65 revocation-authority seed.
const MLDSA_REVOCATION_SEED: [u8; 32] = [0x7eu8; 32];

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization");
    out
}

/// COSE `protected` header for ML-DSA-65: `{1: alg}` serialized to a bstr.
fn mldsa_protected_header() -> Vec<u8> {
    encode_value(Value::Map(vec![(
        Value::from(1),
        Value::from(COSE_ALG_ML_DSA_65),
    )]))
}

/// COSE `Sig_structure` (RFC 9052 §4.4).
fn sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    encode_value(Value::Array(vec![
        Value::Text("Signature1".to_string()),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.to_vec()),
    ]))
}

/// ML-DSA COSE_Key with an AKP key type and raw public key.
/// `kty` is `COSE_KTY_AKP`.
/// `alg` is `COSE_ALG_ML_DSA_65`.
/// Label `-1` contains the public key.
/// Issuer and device keys use this form.
fn mldsa_cose_key(pk: &[u8]) -> Value {
    Value::Map(vec![
        (Value::from(1), Value::from(COSE_KTY_AKP)),
        (Value::from(3), Value::from(COSE_ALG_ML_DSA_65)),
        (Value::from(-1), Value::Bytes(pk.to_vec())),
    ])
}

/// Build an ISO `IssuerSignedItemBytes` value.
fn issuer_signed_item(digest_id: u64, element: &str, value: Value, random: Vec<u8>) -> Vec<u8> {
    let item = Value::Map(vec![
        (Value::Text("digestID".into()), Value::from(digest_id)),
        (Value::Text("random".into()), Value::Bytes(random)),
        (Value::Text("elementIdentifier".into()), element.into()),
        (Value::Text("elementValue".into()), value),
    ]);
    encode_value(Value::Tag(
        CBOR_TAG_ENCODED_CBOR,
        Box::new(Value::Bytes(encode_value(item))),
    ))
}

fn tdate(text: &str) -> Value {
    Value::Tag(0, Box::new(text.into()))
}

/// Issuer-signed data and device authentication data.
struct IssuerSignedDocument {
    document: Vec<u8>,
    mso: Vec<u8>,
    issuer_pk: Vec<u8>,
    issuer_sig_structure: Vec<u8>,
    issuer_signature: Vec<u8>,
}

/// Build a PID mdoc with caller-selected issuer-signed items.
fn build_pid_document_with_attributes(
    device_key: Value,
    device_cose_sign1: Value,
    attributes: Vec<(u64, &str, Value, Vec<u8>)>,
    signed: &str,
    valid_from: &str,
    valid_until: &str,
) -> IssuerSignedDocument {
    // A deterministic seed makes the issuer key pair reproducible.
    let issuer_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_ISSUER_SEED.into());
    let issuer_vk = issuer_sk.verifying_key();
    let issuer_pk_bytes: EncodedVerifyingKey<MlDsa65> = issuer_vk.encode();
    let issuer_pk = issuer_pk_bytes.to_vec();

    let attributes: Vec<(u64, Vec<u8>, [u8; 32])> = attributes
        .into_iter()
        .map(|(digest_id, element, value, random)| {
            let item = issuer_signed_item(digest_id, element, value, random);
            let digest = Sha256::digest(&item).into();
            (digest_id, item, digest)
        })
        .collect();
    assert!(
        !attributes.is_empty(),
        "fixture needs at least one attribute"
    );
    let value_digests = attributes
        .iter()
        .map(|(digest_id, _, digest)| (Value::from(*digest_id), Value::Bytes(digest.to_vec())))
        .collect();
    let namespace_items = attributes
        .iter()
        .map(|(_, item, _)| Value::Bytes(item.clone()))
        .collect();

    let mso = encode_value(Value::Map(vec![
        ("version".into(), MDOC_PROFILE_VERSION.into()),
        ("docType".into(), PID_DOCTYPE.into()),
        ("digestAlgorithm".into(), "SHA-256".into()),
        (
            "valueDigests".into(),
            Value::Map(vec![
                // Add an extra namespace to exercise the valueDigests scanner.
                (
                    EXTRA_VALUE_DIGESTS_NAMESPACE.into(),
                    Value::Map(vec![(
                        Value::from(EXTRA_VALUE_DIGESTS_ID),
                        Value::Bytes(EXTRA_VALUE_DIGEST.to_vec()),
                    )]),
                ),
                (PID_NAMESPACE.into(), Value::Map(value_digests)),
            ]),
        ),
        (
            "deviceKeyInfo".into(),
            Value::Map(vec![("deviceKey".into(), device_key)]),
        ),
        (
            "validityInfo".into(),
            Value::Map(vec![
                ("signed".into(), tdate(signed)),
                ("validFrom".into(), tdate(valid_from)),
                ("validUntil".into(), tdate(valid_until)),
            ]),
        ),
    ]));

    // ML-DSA-65 signs the issuerAuth COSE `Sig_structure`.
    let protected = mldsa_protected_header();
    let sig_struct = sig_structure(&protected, &mso);
    let signature = issuer_sk.sign(&sig_struct);
    let sig_bytes: EncodedSignature<MlDsa65> = signature.encode();
    let issuer_signature = sig_bytes.to_vec();

    let issuer_auth = Value::Array(vec![
        Value::Bytes(protected.clone()),
        Value::Map(vec![("issuerKey".into(), mldsa_cose_key(&issuer_pk))]),
        Value::Bytes(mso.clone()),
        Value::Bytes(issuer_signature.clone()),
    ]);

    let document = encode_value(Value::Map(vec![
        ("docType".into(), PID_DOCTYPE.into()),
        (
            "issuerSigned".into(),
            Value::Map(vec![
                (
                    "nameSpaces".into(),
                    Value::Map(vec![(PID_NAMESPACE.into(), Value::Array(namespace_items))]),
                ),
                ("issuerAuth".into(), issuer_auth),
            ]),
        ),
        (
            "deviceSigned".into(),
            Value::Map(vec![(
                "deviceAuth".into(),
                Value::Map(vec![("deviceSignature".into(), device_cose_sign1)]),
            )]),
        ),
    ]));

    IssuerSignedDocument {
        document,
        mso,
        issuer_pk,
        issuer_sig_structure: sig_struct,
        issuer_signature,
    }
}

/// Complete data for the all-ML-DSA-65 mdoc fixture.
/// Each role includes its public key and signed message.
/// Issuer and device roles sign a `Sig_structure`.
/// The revocation role signs the message from [`mldsa_revocation_fixture`].
pub struct MldsaIdentityFixture {
    /// Encoded PID mdoc document (top-level `Value::Map`).
    pub document: Vec<u8>,
    /// Exact issuer-authenticated MobileSecurityObject payload.
    pub mso: Vec<u8>,
    /// Issuer ML-DSA-65 public key, encoded (`PK_BYTES` = 1952 bytes).
    pub issuer_pk: Vec<u8>,
    /// The COSE `Sig_structure` the issuer signed (payload = MSO).
    pub issuer_sig_structure: Vec<u8>,
    /// The ML-DSA-65 issuer signature (`SIG_BYTES` = 3309 bytes).
    pub issuer_signature: Vec<u8>,
    /// Device ML-DSA-65 public key, encoded (`PK_BYTES` = 1952 bytes).
    pub device_pk: Vec<u8>,
    /// The COSE `Sig_structure` the device signed (payload =
    /// DeviceAuthentication bytes).
    pub device_sig_structure: Vec<u8>,
    /// The ML-DSA-65 device signature (`SIG_BYTES` = 3309 bytes).
    pub device_signature: Vec<u8>,
    /// Revocation-authority ML-DSA-65 public key. It corresponds to the signing
    /// key used by [`mldsa_revocation_fixture`].
    pub revocation_pk: Vec<u8>,
}

/// PID fixture with the demo session transcript.
/// The issuer and device use ML-DSA-65.
/// The MSO contains an AKP device key.
pub fn mldsa_identity_fixture() -> MldsaIdentityFixture {
    mldsa_realistic_pid_fixture_with_age_over_18(&eu_id_prover::mdoc::openid4vp_session_transcript(
        b"session-transcript-123",
    ))
}

/// Build the canonical Boolean claim with a selected digest identifier.
pub fn mldsa_age_over_18_fixture_with_digest_id(
    session_transcript: &[u8],
    digest_id: u64,
    random_fill: u8,
) -> MldsaIdentityFixture {
    mldsa_identity_fixture_with_transcript_and_attributes(
        session_transcript,
        vec![(
            digest_id,
            "age_over_18",
            Value::Bool(true),
            vec![random_fill; 32],
        )],
    )
}

/// Seven-attribute PID fixture for TS13 tests.
///
/// The fixture uses deterministic RustCrypto keys.
/// Each item uses a 32-byte random value.
/// The TS13 request proves only the `age_over_18` equality item.
pub fn mldsa_realistic_pid_fixture_with_age_over_18(
    session_transcript: &[u8],
) -> MldsaIdentityFixture {
    mldsa_identity_fixture_with_profile(
        session_transcript,
        MLDSA_DEVICE_SEED,
        vec![
            (
                1,
                "given_name",
                Value::Text("Erika".to_string()),
                vec![1; 32],
            ),
            (2, "nationality", Value::Text("DE".to_string()), vec![2; 32]),
            (
                3,
                "family_name",
                Value::Text("Mustermann".to_string()),
                vec![3; 32],
            ),
            (
                4,
                "birth_date",
                Value::Text("1985-05-05".to_string()),
                vec![4; 32],
            ),
            (
                5,
                "issuance_date",
                Value::Text("2026-01-01".to_string()),
                vec![5; 32],
            ),
            (
                6,
                "expiry_date",
                Value::Text("2030-01-01".to_string()),
                vec![6; 32],
            ),
            (17, "age_over_18", Value::Bool(true), vec![17; 32]),
        ],
        "2026-01-01T00:00:00Z",
        "2026-01-01T00:00:00Z",
        "2030-01-01T00:00:00Z",
    )
}

/// Credential A for the fixed A1/A2/B public-input unlinkability test.
///
/// Calling this with two fresh transcripts changes only request-bound device
/// authentication. The issuer-authenticated MSO and device key stay identical.
#[allow(dead_code)]
pub fn mldsa_ts13_credential_a_with_transcript(session_transcript: &[u8]) -> MldsaIdentityFixture {
    mldsa_realistic_pid_fixture_with_age_over_18(session_transcript)
}

/// Independently issued, shape-identical credential B for the fixed
/// public-input unlinkability test.
///
/// Credential B changes each credential-stable private class.
/// It changes the device key, MSO facts, randomizers, and digest identifiers.
/// It also changes attribute data and validity times.
/// These changes produce different signatures and a different revocation ID.
#[allow(dead_code)]
pub fn mldsa_ts13_credential_b_with_transcript(session_transcript: &[u8]) -> MldsaIdentityFixture {
    mldsa_identity_fixture_with_profile(
        session_transcript,
        MLDSA_DEVICE_B_SEED,
        vec![
            (
                7,
                "given_name",
                Value::Text("Alice".to_string()),
                vec![0x81; 32],
            ),
            (
                8,
                "nationality",
                Value::Text("FR".to_string()),
                vec![0x82; 32],
            ),
            (
                9,
                "family_name",
                Value::Text("Beispielxx".to_string()),
                vec![0x83; 32],
            ),
            (
                10,
                "birth_date",
                Value::Text("1988-08-08".to_string()),
                vec![0x84; 32],
            ),
            (
                11,
                "issuance_date",
                Value::Text("2025-06-01".to_string()),
                vec![0x85; 32],
            ),
            (
                12,
                "expiry_date",
                Value::Text("2029-12-31".to_string()),
                vec![0x86; 32],
            ),
            (18, "age_over_18", Value::Bool(true), vec![0x92; 32]),
        ],
        "2025-06-01T00:00:00Z",
        "2025-06-01T00:00:00Z",
        "2029-12-31T00:00:00Z",
    )
}

fn mldsa_identity_fixture_with_transcript_and_attributes(
    session_transcript: &[u8],
    attributes: Vec<(u64, &str, Value, Vec<u8>)>,
) -> MldsaIdentityFixture {
    mldsa_identity_fixture_with_profile(
        session_transcript,
        MLDSA_DEVICE_SEED,
        attributes,
        "2026-01-01T00:00:00Z",
        "2026-01-01T00:00:00Z",
        "2030-01-01T00:00:00Z",
    )
}

fn mldsa_identity_fixture_with_profile(
    session_transcript: &[u8],
    device_seed: [u8; 32],
    attributes: Vec<(u64, &str, Value, Vec<u8>)>,
    signed: &str,
    valid_from: &str,
    valid_until: &str,
) -> MldsaIdentityFixture {
    // A deterministic seed makes the device key pair reproducible.
    let device_sk = SigningKey::<MlDsa65>::from_seed(&device_seed.into());
    let device_pk_bytes: EncodedVerifyingKey<MlDsa65> = device_sk.verifying_key().encode();
    let device_pk = device_pk_bytes.to_vec();

    // ML-DSA-65 signs the device COSE `Sig_structure`.
    let protected = mldsa_protected_header();
    let device_payload =
        eu_id_prover::mdoc::device_authentication_bytes(session_transcript, PID_DOCTYPE)
            .expect("device authentication payload builds");
    let device_sig_structure = sig_structure(&protected, &device_payload);
    let signature = device_sk.sign(&device_sig_structure);
    let sig_bytes: EncodedSignature<MlDsa65> = signature.encode();
    let device_signature = sig_bytes.to_vec();
    let device_cose_sign1 = Value::Array(vec![
        Value::Bytes(protected),
        Value::Map(Vec::new()),
        Value::Bytes(device_payload),
        Value::Bytes(device_signature.clone()),
    ]);

    let built = build_pid_document_with_attributes(
        mldsa_cose_key(&device_pk),
        device_cose_sign1,
        attributes,
        signed,
        valid_from,
        valid_until,
    );
    let revocation_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_REVOCATION_SEED.into());
    let revocation_pk_bytes: EncodedVerifyingKey<MlDsa65> = revocation_sk.verifying_key().encode();

    MldsaIdentityFixture {
        document: built.document,
        mso: built.mso,
        issuer_pk: built.issuer_pk,
        issuer_sig_structure: built.issuer_sig_structure,
        issuer_signature: built.issuer_signature,
        device_pk,
        device_sig_structure,
        device_signature,
        revocation_pk: revocation_pk_bytes.to_vec(),
    }
}

/// Create an ML-DSA-65 signature over the canonical revocation message.
/// Return `(public_key, signature)`.
/// The values contain 1,952 and 3,309 bytes.
/// The third fixture seed makes the result deterministic.
pub fn mldsa_revocation_fixture(id_lo: u64, id_hi: u64, epoch: u32) -> (Vec<u8>, Vec<u8>) {
    let sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_REVOCATION_SEED.into());
    let pk_bytes: EncodedVerifyingKey<MlDsa65> = sk.verifying_key().encode();
    let message = eu_id_prover::ts13::ts13_revocation_message(id_lo, id_hi, epoch);
    let signature = sk.sign(&message);
    let sig_bytes: EncodedSignature<MlDsa65> = signature.encode();
    (pk_bytes.to_vec(), sig_bytes.to_vec())
}
