//! Fully post-quantum ML-DSA-65 mdoc fixture.
//!
//! The issuer, device, and TS13 revocation authority all use deterministic
//! ML-DSA-65 keys. Issuer and device authentication sign their standard COSE
//! `Sig_structure`; revocation signs the raw 20-byte message.

use ciborium::value::Value;
use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use sha2::{Digest, Sha256};

use stwo_mldsa::constants::{COSE_ALG_ML_DSA_65, COSE_KTY_AKP};
use stwo_mldsa::reference::verify::verify_internals;

const PID_DOCTYPE: &str = "eu.europa.ec.eudi.pid.1";
const PID_NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const MDOC_PROFILE_VERSION: &str = "2.0";
const CBOR_TAG_ENCODED_CBOR: u64 = 24;

/// Deterministic ML-DSA-65 issuer seed.
const MLDSA_ISSUER_SEED: [u8; 32] = [0x5au8; 32];
/// Deterministic ML-DSA-65 device seed.
const MLDSA_DEVICE_SEED: [u8; 32] = [0x6du8; 32];
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

/// The issuer-signed pieces produced around a device-authentication arm.
struct IssuerSignedDocument {
    document: Vec<u8>,
    issuer_pk: Vec<u8>,
    issuer_sig_structure: Vec<u8>,
    issuer_signature: Vec<u8>,
}

/// Assemble a PID mdoc with an exact caller-selected set of issuer-signed
/// attributes. This keeps TS13's equality fixture independent from the
/// product birth-date/nationality profile.
fn build_pid_document_with_attributes(
    device_key: Value,
    device_cose_sign1: Value,
    attributes: Vec<(u64, &str, Value, Vec<u8>)>,
) -> IssuerSignedDocument {
    // Issuer ML-DSA-65 keypair (deterministic seed → reproducible fixture).
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
            Value::Map(vec![(PID_NAMESPACE.into(), Value::Map(value_digests))]),
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
        issuer_pk,
        issuer_sig_structure: sig_struct,
        issuer_signature,
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
    mldsa_full_pq_fixture_with_transcript_and_nationality(
        session_transcript,
        Value::Text("DE".to_string()),
    )
}

/// Fixture variant with a definite, canonical nationality array.  Its first
/// member is intentionally not policy-accepted, exercising the selected-index
/// stride rather than just a one-member array.
pub fn mldsa_full_pq_fixture_with_nationality_array(
    session_transcript: &[u8],
) -> MldsaFullPqFixture {
    mldsa_full_pq_fixture_with_transcript_and_nationality(
        session_transcript,
        Value::Array(vec![
            Value::Text("FR".to_string()),
            Value::Text("DE".to_string()),
        ]),
    )
}

/// A TS13-specific fully-PQ fixture with one equality-disclosed Boolean
/// attribute. It intentionally does not include product-profile attributes.
pub fn mldsa_full_pq_fixture_with_attribute(
    session_transcript: &[u8],
    element: &str,
    value: Value,
) -> MldsaFullPqFixture {
    mldsa_full_pq_fixture_with_transcript_and_attributes(
        session_transcript,
        vec![(17, element, value, vec![17; 16])],
    )
}

fn mldsa_full_pq_fixture_with_transcript_and_nationality(
    session_transcript: &[u8],
    nationality_value: Value,
) -> MldsaFullPqFixture {
    mldsa_full_pq_fixture_with_transcript_and_attributes(
        session_transcript,
        vec![
            (
                7,
                "birth_date",
                Value::Text("1990-07-15".to_string()),
                vec![7; 16],
            ),
            (9, "nationality", nationality_value, vec![9; 16]),
        ],
    )
}

fn mldsa_full_pq_fixture_with_transcript_and_attributes(
    session_transcript: &[u8],
    attributes: Vec<(u64, &str, Value, Vec<u8>)>,
) -> MldsaFullPqFixture {
    // Device ML-DSA-65 keypair (deterministic seed → reproducible fixture).
    let device_sk = SigningKey::<MlDsa65>::from_seed(&MLDSA_DEVICE_SEED.into());
    let device_pk_bytes: EncodedVerifyingKey<MlDsa65> = device_sk.verifying_key().encode();
    let device_pk = device_pk_bytes.to_vec();

    // deviceSignature COSE_Sign1 signed with ML-DSA-65 over the Sig_structure.
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
    );
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
