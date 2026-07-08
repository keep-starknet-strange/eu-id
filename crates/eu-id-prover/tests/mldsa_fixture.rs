//! ML-DSA-65-signed mdoc fixture (milestone M1).
//!
//! Builds the same synthetic PID mdoc structure the P-256 demo fixture emits
//! (`crates/eu-id-prover/src/mdoc.rs::demo_mdoc_document`), but with an
//! `issuerAuth` `COSE_Sign1` whose protected header carries the ML-DSA-65 COSE
//! `alg` id and whose signature is ML-DSA-65 over the standard `Sig_structure`.
//! The issuer key is an `ml-dsa` (oracle) keypair; the device key stays P-256.
//!
//! This is additive fixture support — the shipping mdoc proving/statement path
//! is untouched (that swap is M7). The fixture exists so M2+ can parse it and
//! diff a witness against the native `stwo-mldsa` reference verdict.
//!
//! Structure mirrors the P-256 demo exactly except for the two issuer-signature
//! carriers (the `issuerAuth` protected header and the signature bytes) and the
//! issuer COSE key type. Rebuilt here with `ciborium::Value` directly rather
//! than reaching into private `mdoc.rs` helpers.

use ciborium::value::Value;
use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use p256::ecdsa::{Signature as P256Signature, SigningKey as P256SigningKey};
use sha2::{Digest, Sha256};

use stwo_mldsa::constants::{COSE_ALG_ML_DSA_65, COSE_KTY_AKP};
use stwo_mldsa::reference::verify::verify_internals;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const MDOC_PROFILE_VERSION: &str = "2.0";
const CBOR_TAG_ENCODED_CBOR: u64 = 24;

/// Deterministic ML-DSA-65 issuer seed for the fixture (distinct from the P-256
/// demo issuer). Fixed so `mldsa_pid_fixture()` is reproducible.
const MLDSA_ISSUER_SEED: [u8; 32] = [0x5au8; 32];
/// The demo device signing key seed (P-256), matching the P-256 fixtures.
const DEVICE_SEED: [u8; 32] = [11u8; 32];

/// Everything a consumer of the ML-DSA mdoc fixture needs: the full mdoc
/// document bytes, the raw issuer public key (1952 bytes, for `verify_internals`),
/// and the `Sig_structure` preimage that was signed plus its ML-DSA signature.
pub struct MldsaPidFixture {
    /// Encoded PID mdoc document (top-level `Value::Map`).
    pub document: Vec<u8>,
    /// Issuer ML-DSA-65 public key, encoded (`PK_BYTES` = 1952 bytes).
    pub issuer_pk: Vec<u8>,
    /// The COSE `Sig_structure` the issuer signed (`Signature1 ‖ protected ‖
    /// external_aad(empty) ‖ payload(MSO)`).
    pub sig_structure: Vec<u8>,
    /// The ML-DSA-65 signature over `sig_structure` (`SIG_BYTES` = 3309 bytes).
    pub issuer_signature: Vec<u8>,
}

fn encode_value(value: Value) -> Vec<u8> {
    let mut out = Vec::new();
    ciborium::ser::into_writer(&value, &mut out).expect("CBOR serialization");
    out
}

/// COSE `protected` header for ML-DSA-65: `{1: alg}` serialized to a bstr.
/// (`ES256` uses `{1: -7}` = `A1 01 26`; here `alg = COSE_ALG_ML_DSA_65`.)
fn mldsa_protected_header() -> Vec<u8> {
    encode_value(Value::Map(vec![(
        Value::from(1),
        Value::from(COSE_ALG_ML_DSA_65),
    )]))
}

/// COSE `Sig_structure` (RFC 9052 §4.4): `["Signature1", protected, ext_aad,
/// payload]`, identical layout to the P-256 path.
fn sig_structure(protected: &[u8], payload: &[u8]) -> Vec<u8> {
    encode_value(Value::Array(vec![
        Value::Text("Signature1".to_string()),
        Value::Bytes(protected.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(payload.to_vec()),
    ]))
}

/// A P-256 device COSE_Key (`kty EC2`, `alg ES256`), matching the demo fixture.
fn device_cose_key(signing_key: &P256SigningKey) -> Value {
    let encoded = signing_key.verifying_key().to_encoded_point(false);
    let x: [u8; 32] = encoded.x().expect("x")[..].try_into().expect("x len");
    let y: [u8; 32] = encoded.y().expect("y")[..].try_into().expect("y len");
    Value::Map(vec![
        (Value::from(1), Value::from(2)),  // kty: EC2
        (Value::from(3), Value::from(-7)), // alg: ES256
        (Value::from(-1), Value::from(1)), // crv: P-256
        (Value::from(-2), Value::Bytes(x.to_vec())),
        (Value::from(-3), Value::Bytes(y.to_vec())),
    ])
}

/// An issuer ML-DSA COSE_Key: AKP key type carrying the raw public key.
/// (`kty = COSE_KTY_AKP`, `alg = COSE_ALG_ML_DSA_65`, public key in label -1.)
fn issuer_mldsa_cose_key(pk: &[u8]) -> Value {
    Value::Map(vec![
        (Value::from(1), Value::from(COSE_KTY_AKP)),
        (Value::from(3), Value::from(COSE_ALG_ML_DSA_65)),
        (Value::from(-1), Value::Bytes(pk.to_vec())),
    ])
}

/// Build a profile-v2 `IssuerSignedItemBytes` (tag-24-wrapped canonical item).
fn issuer_signed_item(digest_id: u64, element: &str, value: Value, random: Vec<u8>) -> Vec<u8> {
    let item = Value::Map(vec![
        (Value::Text("random".into()), Value::Bytes(random)),
        (Value::Text("digestID".into()), Value::from(digest_id)),
        (Value::Text("elementValue".into()), value),
        (Value::Text("elementIdentifier".into()), element.into()),
    ]);
    encode_value(Value::Tag(
        CBOR_TAG_ENCODED_CBOR,
        Box::new(Value::Bytes(encode_value(item))),
    ))
}

fn tdate(text: &str) -> Value {
    Value::Tag(0, Box::new(text.into()))
}

/// The ML-DSA-65-signed PID mdoc fixture with the demo session transcript —
/// extractable by `extract_pid_mdoc` with `MdocPidRequest::eudi_pid`.
pub fn mldsa_pid_fixture() -> MldsaPidFixture {
    mldsa_pid_fixture_with_transcript(&eu_id_prover::mdoc::openid4vp_session_transcript(
        b"session-transcript-123",
    ))
}

/// The ML-DSA-65-signed PID mdoc fixture. Exported for M2+/M7 tests.
pub fn mldsa_pid_fixture_with_transcript(session_transcript: &[u8]) -> MldsaPidFixture {
    // Issuer ML-DSA-65 keypair (deterministic seed → reproducible fixture).
    let issuer_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_ISSUER_SEED.into());
    let issuer_vk = issuer_sk.verifying_key();
    let issuer_pk_bytes: EncodedVerifyingKey<MlDsa65> = issuer_vk.encode();
    let issuer_pk = issuer_pk_bytes.to_vec();

    // Device P-256 key (unchanged from the demo fixture).
    let device_sk = P256SigningKey::from_bytes((&DEVICE_SEED).into()).expect("device key");
    let device_key = device_cose_key(&device_sk);

    // Namespace items + value digests (same two attributes as the demo).
    let birth_date_item = issuer_signed_item(
        7,
        "birth_date",
        Value::Text("1990-07-15".to_string()),
        vec![7; 16],
    );
    let nationality_item =
        issuer_signed_item(9, "nationality", Value::Text("DE".to_string()), vec![9; 16]);
    let birth_digest: [u8; 32] = Sha256::digest(&birth_date_item).into();
    let nat_digest: [u8; 32] = Sha256::digest(&nationality_item).into();

    let mso = encode_value(Value::Map(vec![
        ("version".into(), MDOC_PROFILE_VERSION.into()),
        ("docType".into(), PID_DOCTYPE.into()),
        ("digestAlgorithm".into(), "SHA-256".into()),
        (
            "valueDigests".into(),
            Value::Map(vec![(
                PID_NAMESPACE.into(),
                Value::Map(vec![
                    (Value::from(7), Value::Bytes(birth_digest.to_vec())),
                    (Value::from(9), Value::Bytes(nat_digest.to_vec())),
                ]),
            )]),
        ),
        (
            "deviceKeyInfo".into(),
            Value::Map(vec![("deviceKey".into(), device_key)]),
        ),
        (
            "validityInfo".into(),
            Value::Map(vec![
                ("signed".into(), tdate("2026-01-01T00:00:00Z")),
                ("validFrom".into(), tdate("2026-01-01T00:00:00Z")),
                ("validUntil".into(), tdate("2030-01-01T00:00:00Z")),
            ]),
        ),
    ]));

    // issuerAuth COSE_Sign1 signed with ML-DSA-65 over the Sig_structure.
    let protected = mldsa_protected_header();
    let sig_struct = sig_structure(&protected, &mso);
    let signature = issuer_sk.sign(&sig_struct);
    let sig_bytes: EncodedSignature<MlDsa65> = signature.encode();
    let issuer_signature = sig_bytes.to_vec();

    let issuer_auth = Value::Array(vec![
        Value::Bytes(protected.clone()),
        Value::Map(vec![("issuerKey".into(), issuer_mldsa_cose_key(&issuer_pk))]),
        Value::Bytes(mso.clone()),
        Value::Bytes(issuer_signature.clone()),
    ]);

    // Device signature stays P-256 over the (empty) device-namespaces payload.
    // Disambiguate the `Signer` trait — the ml-dsa oracle pulls in a second
    // `signature` crate version whose `Signer` also matches by name.
    use ecdsa::signature::Signer as _;
    let device_payload =
        eu_id_prover::mdoc::device_authentication_bytes(session_transcript, PID_DOCTYPE)
            .expect("device authentication payload builds");
    let device_sig_struct = sig_structure(&[0xA1, 0x01, 0x26], &device_payload);
    let device_signature: P256Signature = device_sk.sign(&device_sig_struct);
    let mut device_compact = Vec::with_capacity(64);
    device_compact.extend_from_slice(&device_signature.r().to_bytes());
    device_compact.extend_from_slice(&device_signature.s().to_bytes());
    let device_cose_sign1 = Value::Array(vec![
        Value::Bytes(vec![0xA1, 0x01, 0x26]),
        Value::Map(Vec::new()),
        Value::Bytes(device_payload),
        Value::Bytes(device_compact),
    ]);

    let document = encode_value(Value::Map(vec![
        ("docType".into(), PID_DOCTYPE.into()),
        (
            "issuerSigned".into(),
            Value::Map(vec![
                (
                    "nameSpaces".into(),
                    Value::Map(vec![(
                        PID_NAMESPACE.into(),
                        Value::Array(vec![
                            Value::Bytes(birth_date_item),
                            Value::Bytes(nationality_item),
                        ]),
                    )]),
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

    MldsaPidFixture {
        document,
        issuer_pk,
        sig_structure: sig_struct,
        issuer_signature,
    }
}

#[test]
fn mldsa_fixture_issuer_auth_verifies_natively() {
    let fx = mldsa_pid_fixture();
    assert_eq!(fx.issuer_pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(
        fx.issuer_signature.len(),
        stwo_mldsa::constants::SIG_BYTES
    );

    // The native stwo-mldsa reference must accept the fixture's issuer signature
    // over the exact Sig_structure preimage.
    let trace = verify_internals(&fx.issuer_pk, &fx.sig_structure, &fx.issuer_signature)
        .expect("issuer signature decodes");
    assert!(
        trace.accepted,
        "ML-DSA issuer signature must verify natively: {:?}",
        trace.reason
    );
}

#[test]
fn mldsa_fixture_parses_as_cbor_with_mldsa_alg() {
    let fx = mldsa_pid_fixture();
    // Round-trips as CBOR.
    let doc: Value = ciborium::de::from_reader(fx.document.as_slice()).expect("document is CBOR");
    assert!(matches!(doc, Value::Map(_)));

    // The issuerAuth protected header advertises the ML-DSA-65 alg id.
    let protected = mldsa_protected_header();
    let hdr: Value = ciborium::de::from_reader(protected.as_slice()).unwrap();
    let Value::Map(entries) = hdr else {
        panic!("protected header is a map")
    };
    let (_, alg) = &entries[0];
    assert_eq!(*alg, Value::from(COSE_ALG_ML_DSA_65));
}

#[test]
fn mldsa_fixture_rejects_tampered_issuer_signature() {
    let mut fx = mldsa_pid_fixture();
    // Flip a byte in the z region (past the 48-byte c̃) — must reject.
    let z_off = stwo_mldsa::constants::C_TILDE_BYTES + 200;
    fx.issuer_signature[z_off] ^= 0x01;
    let rejected = match verify_internals(&fx.issuer_pk, &fx.sig_structure, &fx.issuer_signature) {
        Ok(trace) => !trace.accepted,
        Err(_) => true,
    };
    assert!(rejected, "tampered issuer signature must not verify");
}

#[test]
fn mldsa_fixture_is_deterministic() {
    let a = mldsa_pid_fixture();
    let b = mldsa_pid_fixture();
    assert_eq!(a.document, b.document);
    assert_eq!(a.issuer_pk, b.issuer_pk);
}
