//! ML-DSA-65-signed mdoc fixture (milestone M1).
//!
//! Builds the same synthetic PID mdoc structure the P-256 demo fixture emits
//! (`crates/eu-id-prover/src/mdoc.rs::demo_mdoc_document`), but with an
//! `issuerAuth` `COSE_Sign1` whose protected header carries the ML-DSA-65 COSE
//! `alg` id and whose signature is ML-DSA-65 over the standard `Sig_structure`.
//! The issuer key is an `ml-dsa` (oracle) keypair; the device key stays P-256.
//!
//! `mldsa_full_pq_fixture()` additionally builds the fully post-quantum
//! variant (spec §2a/§4 G1): the device key is an AKP COSE_Key carrying an
//! ML-DSA-65 public key and the `deviceSignature` is a pure ML-DSA-65
//! COSE_Sign1; `mldsa_revocation_fixture()` signs the raw 20-byte TS13
//! revocation message with a third deterministic ML-DSA key (no prehash).
//!
//! This is additive fixture support — the shipping mdoc proving/statement path
//! is untouched (that swap is M7). The fixture exists so M2+ can parse it and
//! diff a witness against the native `stwo-mldsa` reference verdict.
//!
//! Structure mirrors the P-256 demo exactly except for the two issuer-signature
//! carriers (the `issuerAuth` protected header and the signature bytes) and the
//! issuer COSE key type. Rebuilt here with `ciborium::Value` directly rather
//! than reaching into private `mdoc.rs` helpers.
#![cfg(feature = "ml-dsa")]

use ciborium::value::Value;
use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
#[cfg(feature = "p256")]
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
/// Deterministic ML-DSA-65 device seed for the fully-PQ fixture (distinct
/// from the issuer and revocation seeds).
const MLDSA_DEVICE_SEED: [u8; 32] = [0x6du8; 32];
/// Deterministic ML-DSA-65 revocation-authority seed (third fixture seed).
const MLDSA_REVOCATION_SEED: [u8; 32] = [0x7eu8; 32];
/// The demo device signing key seed (P-256), matching the P-256 fixtures.
#[cfg(feature = "p256")]
const DEVICE_SEED: [u8; 32] = [11u8; 32];

/// Everything a consumer of the ML-DSA mdoc fixture needs: the full mdoc
/// document bytes, the raw issuer public key (1952 bytes, for `verify_internals`),
/// and the `Sig_structure` preimage that was signed plus its ML-DSA signature.
#[cfg(feature = "p256")]
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
#[cfg(feature = "p256")]
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

/// An ML-DSA COSE_Key: AKP key type carrying the raw public key.
/// (`kty = COSE_KTY_AKP`, `alg = COSE_ALG_ML_DSA_65`, public key in label -1.)
/// Used for both the issuer header key and the fully-PQ device key.
fn mldsa_cose_key(pk: &[u8]) -> Value {
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
#[cfg(feature = "p256")]
pub fn mldsa_pid_fixture() -> MldsaPidFixture {
    mldsa_pid_fixture_with_transcript(&eu_id_prover::mdoc::openid4vp_session_transcript(
        b"session-transcript-123",
    ))
}

/// The issuer-signed pieces `build_pid_document` produces around a device arm.
struct IssuerSignedDocument {
    document: Vec<u8>,
    issuer_pk: Vec<u8>,
    issuer_sig_structure: Vec<u8>,
    issuer_signature: Vec<u8>,
}

/// Assemble the PID mdoc document (namespace items, MSO, ML-DSA-65-signed
/// `issuerAuth`) around the given device COSE_Key and `deviceSignature`
/// COSE_Sign1. Shared by the device-P256 and fully-PQ fixture builders.
fn build_pid_document(device_key: Value, device_cose_sign1: Value) -> IssuerSignedDocument {
    // Issuer ML-DSA-65 keypair (deterministic seed → reproducible fixture).
    let issuer_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_ISSUER_SEED.into());
    let issuer_vk = issuer_sk.verifying_key();
    let issuer_pk_bytes: EncodedVerifyingKey<MlDsa65> = issuer_vk.encode();
    let issuer_pk = issuer_pk_bytes.to_vec();

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

    IssuerSignedDocument {
        document,
        issuer_pk,
        issuer_sig_structure: sig_struct,
        issuer_signature,
    }
}

/// The ML-DSA-65-signed PID mdoc fixture. Exported for M2+/M7 tests.
#[cfg(feature = "p256")]
pub fn mldsa_pid_fixture_with_transcript(session_transcript: &[u8]) -> MldsaPidFixture {
    // Device P-256 key (unchanged from the demo fixture), signing the (empty)
    // device-namespaces payload. Disambiguate the `Signer` trait — the ml-dsa
    // oracle pulls in a second `signature` crate version whose `Signer` also
    // matches by name.
    use ecdsa::signature::Signer as _;
    let device_sk = P256SigningKey::from_bytes((&DEVICE_SEED).into()).expect("device key");
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

    let built = build_pid_document(device_cose_key(&device_sk), device_cose_sign1);
    MldsaPidFixture {
        document: built.document,
        issuer_pk: built.issuer_pk,
        sig_structure: built.issuer_sig_structure,
        issuer_signature: built.issuer_signature,
    }
}

/// Everything a consumer of the fully post-quantum mdoc fixture needs: the
/// document plus, per role, the public key and the exact signed preimage
/// (`Sig_structure` for issuer/device; revocation signs the raw 20-byte
/// message, see [`mldsa_revocation_fixture`]).
pub struct MldsaFullPqFixture {
    /// Encoded PID mdoc document (top-level `Value::Map`).
    pub document: Vec<u8>,
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
    /// Revocation-authority ML-DSA-65 public key (same key
    /// [`mldsa_revocation_fixture`] signs with).
    pub revocation_pk: Vec<u8>,
}

/// The fully post-quantum PID mdoc fixture with the demo session transcript:
/// ML-DSA-65 issuer AND ML-DSA-65 device (AKP deviceKey, pure ML-DSA
/// `deviceSignature`).
pub fn mldsa_full_pq_fixture() -> MldsaFullPqFixture {
    mldsa_full_pq_fixture_with_transcript(&eu_id_prover::mdoc::openid4vp_session_transcript(
        b"session-transcript-123",
    ))
}

/// The fully post-quantum PID mdoc fixture (spec §2a). The MSO `deviceKey` is
/// an AKP COSE_Key (`{1: 7, 3: -49, -1: pk}`) and `deviceSignature` is a
/// COSE_Sign1 with protected header `A1 01 38 30` whose signature is pure
/// ML-DSA-65 over the standard `Sig_structure` — mirroring the issuer arm.
pub fn mldsa_full_pq_fixture_with_transcript(session_transcript: &[u8]) -> MldsaFullPqFixture {
    // Device ML-DSA-65 keypair (deterministic seed → reproducible fixture).
    let device_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_DEVICE_SEED.into());
    let device_pk_bytes: EncodedVerifyingKey<MlDsa65> = device_sk.verifying_key().encode();
    let device_pk = device_pk_bytes.to_vec();

    // deviceSignature COSE_Sign1 signed with ML-DSA-65 over the Sig_structure
    // (same detached DeviceAuthentication payload as the P-256 device arm).
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

    let built = build_pid_document(mldsa_cose_key(&device_pk), device_cose_sign1);
    let revocation_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_REVOCATION_SEED.into());
    let revocation_pk_bytes: EncodedVerifyingKey<MlDsa65> = revocation_sk.verifying_key().encode();

    MldsaFullPqFixture {
        document: built.document,
        issuer_pk: built.issuer_pk,
        issuer_sig_structure: built.issuer_sig_structure,
        issuer_signature: built.issuer_signature,
        device_pk,
        device_sig_structure,
        device_signature,
        revocation_pk: revocation_pk_bytes.to_vec(),
    }
}

/// The raw TS13 revocation message: `LE64(id_lo) ‖ LE64(id_hi) ‖ LE32(epoch)`
/// (20 bytes). This is what the ML-DSA revocation authority signs — pure
/// ML-DSA, no SHA-256 prehash (spec §1b/§2a).
pub fn revocation_message(id_lo: u64, id_hi: u64, epoch: u32) -> [u8; 20] {
    let mut msg = [0u8; 20];
    msg[..8].copy_from_slice(&id_lo.to_le_bytes());
    msg[8..16].copy_from_slice(&id_hi.to_le_bytes());
    msg[16..].copy_from_slice(&epoch.to_le_bytes());
    msg
}

/// An ML-DSA-65 revocation-authority signature over the raw 20-byte message
/// [`revocation_message`]. Returns `(public_key, signature)` — 1952 and 3309
/// bytes respectively. Deterministic (third fixture seed).
pub fn mldsa_revocation_fixture(id_lo: u64, id_hi: u64, epoch: u32) -> (Vec<u8>, Vec<u8>) {
    let sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_REVOCATION_SEED.into());
    let pk_bytes: EncodedVerifyingKey<MlDsa65> = sk.verifying_key().encode();
    let signature = sk.sign(&revocation_message(id_lo, id_hi, epoch));
    let sig_bytes: EncodedSignature<MlDsa65> = signature.encode();
    (pk_bytes.to_vec(), sig_bytes.to_vec())
}

/// A minimal PID mdoc whose `issuerAuth` advertises COSE ES256 (P-256, alg -7).
/// Used only by the `not(feature = "p256")` clean-error test below: parsing must
/// reject it with `UnsupportedIssuerAlg` before any signature check, because the
/// issuer P-256 proving path is not compiled in.
#[cfg(not(feature = "p256"))]
fn es256_issuer_document() -> Vec<u8> {
    // ES256 protected header `{1: -7}` = `A1 01 26`. The unprotected map, MSO
    // payload and signature bytes are placeholders — the parser errors on the
    // issuer alg before it reads any of them.
    let es256_protected = vec![0xA1u8, 0x01, 0x26];
    let issuer_auth = Value::Array(vec![
        Value::Bytes(es256_protected),
        Value::Map(vec![("issuerKey".into(), Value::Map(Vec::new()))]),
        Value::Bytes(vec![0u8; 8]),
        Value::Bytes(vec![0u8; 64]),
    ]);
    encode_value(Value::Map(vec![
        ("docType".into(), PID_DOCTYPE.into()),
        (
            "issuerSigned".into(),
            Value::Map(vec![
                (
                    "nameSpaces".into(),
                    Value::Map(vec![(PID_NAMESPACE.into(), Value::Array(Vec::new()))]),
                ),
                ("issuerAuth".into(), issuer_auth),
            ]),
        ),
        (
            "deviceSigned".into(),
            Value::Map(vec![(
                "deviceAuth".into(),
                Value::Map(vec![("deviceSignature".into(), Value::Array(Vec::new()))]),
            )]),
        ),
    ]))
}

/// Without the `p256` feature, an ES256 (P-256) issuer must be rejected with a
/// clean `UnsupportedIssuerAlg` error naming the missing feature — never a panic.
#[cfg(not(feature = "p256"))]
#[test]
fn es256_issuer_rejected_without_p256_feature() {
    use eu_id_prover::mdoc::{extract_pid_mdoc, MdocError, MdocPidRequest};
    let request = MdocPidRequest::eudi_pid(eu_id_prover::mdoc::openid4vp_session_transcript(
        b"session-transcript-123",
    ));
    let err = extract_pid_mdoc(&es256_issuer_document(), &request)
        .expect_err("ES256 issuer must be rejected without the p256 feature");
    match err {
        MdocError::UnsupportedIssuerAlg(msg) => {
            assert!(
                msg.contains("p256"),
                "message should name the feature: {msg}"
            );
        }
        other => panic!("expected UnsupportedIssuerAlg, got {other:?}"),
    }
}

#[cfg(feature = "p256")]
#[test]
fn mldsa_fixture_issuer_auth_verifies_natively() {
    let fx = mldsa_pid_fixture();
    assert_eq!(fx.issuer_pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(fx.issuer_signature.len(), stwo_mldsa::constants::SIG_BYTES);

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

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
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

#[cfg(feature = "p256")]
#[test]
fn mldsa_fixture_is_deterministic() {
    let a = mldsa_pid_fixture();
    let b = mldsa_pid_fixture();
    assert_eq!(a.document, b.document);
    assert_eq!(a.issuer_pk, b.issuer_pk);
}

/// Rejected iff the reference verifier errors on decode or traces `accepted == false`.
fn rejects(pk: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    match verify_internals(pk, msg, sig) {
        Ok(trace) => !trace.accepted,
        Err(_) => true,
    }
}

#[test]
fn full_pq_fixture_issuer_and_device_verify_natively() {
    let fx = mldsa_full_pq_fixture();
    assert_eq!(fx.issuer_pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(fx.device_pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(fx.issuer_signature.len(), stwo_mldsa::constants::SIG_BYTES);
    assert_eq!(fx.device_signature.len(), stwo_mldsa::constants::SIG_BYTES);

    let issuer = verify_internals(
        &fx.issuer_pk,
        &fx.issuer_sig_structure,
        &fx.issuer_signature,
    )
    .expect("issuer signature decodes");
    assert!(
        issuer.accepted,
        "ML-DSA issuer signature must verify natively: {:?}",
        issuer.reason
    );
    let device = verify_internals(
        &fx.device_pk,
        &fx.device_sig_structure,
        &fx.device_signature,
    )
    .expect("device signature decodes");
    assert!(
        device.accepted,
        "ML-DSA device signature must verify natively: {:?}",
        device.reason
    );
}

#[test]
fn full_pq_fixture_device_key_is_akp_with_anchor() {
    // The ML-DSA protected header is exactly `{1: -49}` = `A1 01 38 30`.
    assert_eq!(mldsa_protected_header(), [0xA1, 0x01, 0x38, 0x30]);

    // The document embeds the AKP deviceKey with the CBOR anchor: label `-1`
    // (`20`) followed by the 1952-byte bstr header (`59 07 A0`) and the raw
    // device public key (spec §2b).
    let fx = mldsa_full_pq_fixture();
    let mut anchored = vec![0x20, 0x59, 0x07, 0xA0];
    anchored.extend_from_slice(&fx.device_pk);
    assert!(
        fx.document
            .windows(anchored.len())
            .any(|window| window == anchored),
        "document must contain `20 59 07 A0 ‖ device_pk`"
    );
}

#[test]
fn full_pq_fixture_rejects_tampered_issuer_signature() {
    let mut fx = mldsa_full_pq_fixture();
    // Flip a byte in the z region (past the 48-byte c̃) — must reject.
    fx.issuer_signature[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 0x01;
    assert!(
        rejects(
            &fx.issuer_pk,
            &fx.issuer_sig_structure,
            &fx.issuer_signature
        ),
        "tampered issuer signature must not verify"
    );
}

#[test]
fn full_pq_fixture_rejects_tampered_device_signature() {
    let mut fx = mldsa_full_pq_fixture();
    fx.device_signature[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 0x01;
    assert!(
        rejects(
            &fx.device_pk,
            &fx.device_sig_structure,
            &fx.device_signature
        ),
        "tampered device signature must not verify"
    );
}

#[test]
fn full_pq_fixture_is_deterministic() {
    let a = mldsa_full_pq_fixture();
    let b = mldsa_full_pq_fixture();
    assert_eq!(a.document, b.document);
    assert_eq!(a.device_pk, b.device_pk);
    assert_eq!(a.revocation_pk, b.revocation_pk);
}

#[test]
fn revocation_fixture_verifies_and_rejects_tamper() {
    let (pk, sig) = mldsa_revocation_fixture(41, 4141, 7);
    assert_eq!(pk.len(), stwo_mldsa::constants::PK_BYTES);
    assert_eq!(sig.len(), stwo_mldsa::constants::SIG_BYTES);
    assert_eq!(pk, mldsa_full_pq_fixture().revocation_pk);

    let msg = revocation_message(41, 4141, 7);
    let trace = verify_internals(&pk, &msg, &sig).expect("revocation signature decodes");
    assert!(
        trace.accepted,
        "ML-DSA revocation signature must verify natively: {:?}",
        trace.reason
    );

    // Tampered signature must reject.
    let mut bad_sig = sig.clone();
    bad_sig[stwo_mldsa::constants::C_TILDE_BYTES + 200] ^= 0x01;
    assert!(
        rejects(&pk, &msg, &bad_sig),
        "tampered revocation signature must not verify"
    );
    // A different message (wrong epoch) must reject too — no prehash to hide it.
    assert!(
        rejects(&pk, &revocation_message(41, 4141, 8), &sig),
        "revocation signature must be bound to the exact 20-byte message"
    );
}
