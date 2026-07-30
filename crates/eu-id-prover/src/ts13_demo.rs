//! Frozen public-context primitives for the TS13 unlinkable age-over-18 demo.
//!
//! This module deliberately does not route the demo profile into the mdoc
//! prover yet. It owns only the deterministic public derivation and the
//! zero-column transcript component which the final composition will insert at
//! frozen module slot 4.

use std::cmp::Ordering;

use air_core::{Air, AirProver, TreeLayout};
use ciborium::value::Value;
use sha2::{Digest, Sha256};
use stwo::core::air::Component;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::{ComponentProver, TreeBuilder};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::TraceLocationAllocator;

const CONTEXT_LABEL: &str = "EUDI-TS13-DEMO-CONTEXT-V1";
const SYSTEM_NAME: &str = "stwo-euid-ts13-demo-v1";
const PUBLIC_CONTEXT_TRANSCRIPT_DOMAIN: &[u8] = b"EUDI-TS13-PUBLIC-CONTEXT-V1";
const DOCUMENT_TYPE: &str = "eu.europa.ec.eudi.pid.1";
const NAMESPACE: &str = "eu.europa.ec.eudi.pid.1";
const ELEMENT_IDENTIFIER: &str = "age_over_18";
const EXPECTED_VALUE_CBOR: &[u8] = &[0xf5];
const ML_DSA_65_PROTECTED_HEADER: &[u8] = &[0xa1, 0x01, 0x38, 0x30];
const REQUEST_CONTEXT_CORPUS_LABEL: &str = "EUDI-TS13-REQUEST-CONTEXT-CORPUS-V1";
const REQUEST_CONTEXT_CAPACITY_HEADROOM: usize = 128;
const OPENID4VP_CORPUS_LABEL: &str = "official-openid4vp-1.0";
const ISO_QR_CORPUS_LABEL: &str = "iso18013-5-qr-ble-both-p256";
const ISO_NFC_STATIC_CORPUS_LABEL: &str = "iso18013-5-nfc-static-ble-both-p256";
const NDEF_DEVICE_ENGAGEMENT_TYPE: &[u8] = b"iso.org:18013:deviceengagement";
const NDEF_BLE_OOB_TYPE: &[u8] = b"application/vnd.bluetooth.le.oob";
const CORPUS_BLE_UUID: [u8; 16] = [
    0xb3, 0xd5, 0x2a, 0xc4, 0xa1, 0xb6, 0x4b, 0x51, 0xa2, 0x2e, 0x78, 0xee, 0x55, 0xef, 0x6e, 0xb6,
];
const CORPUS_DEVICE_KEY_X: [u8; 32] = [
    0x71, 0x04, 0xf7, 0xe2, 0xc2, 0xe9, 0x5c, 0xa7, 0x64, 0x82, 0xc0, 0xc9, 0x63, 0xd4, 0x54, 0xb7,
    0xe5, 0xd0, 0x53, 0xc5, 0xb5, 0x9c, 0xe8, 0x9d, 0x00, 0xff, 0x7c, 0x7d, 0x7a, 0xb6, 0xff, 0x7d,
];
const CORPUS_DEVICE_KEY_Y: [u8; 32] = [
    0xf4, 0x42, 0x82, 0x12, 0x92, 0xc2, 0x45, 0x3e, 0xc6, 0x7c, 0x75, 0x23, 0x3e, 0xa5, 0x6e, 0x17,
    0x34, 0xc2, 0x11, 0xae, 0x26, 0xb2, 0x59, 0xfd, 0xf2, 0x32, 0xb5, 0xb3, 0xd8, 0x2b, 0x1b, 0xa2,
];
const CORPUS_READER_KEY_X: [u8; 32] = [
    0xdb, 0x1b, 0x6d, 0x2c, 0xc5, 0xe6, 0xba, 0xeb, 0xd1, 0x2f, 0xb7, 0x6d, 0x4f, 0xa4, 0x09, 0x57,
    0x65, 0x98, 0x32, 0xe4, 0x1c, 0xad, 0xe1, 0x5d, 0xb9, 0x03, 0x8f, 0x37, 0xef, 0x5b, 0xa3, 0x21,
];
const CORPUS_READER_KEY_Y: [u8; 32] = [
    0xb0, 0x36, 0x1e, 0x20, 0x84, 0x71, 0xbb, 0x94, 0xa6, 0x87, 0x08, 0x9c, 0x49, 0x57, 0xfc, 0x4d,
    0x99, 0x83, 0xab, 0xe0, 0x4c, 0xde, 0xeb, 0x15, 0x5b, 0xcd, 0x69, 0x06, 0x40, 0x13, 0x77, 0x27,
];
const OPENID4VP_HANDOVER_INFO_SHA256: [u8; 32] = [
    0x04, 0x8b, 0xc0, 0x53, 0xc0, 0x04, 0x42, 0xaf, 0x9b, 0x8e, 0xed, 0x49, 0x4c, 0xef, 0xdd, 0x9d,
    0x95, 0x24, 0x0d, 0x25, 0x4b, 0x04, 0x6b, 0x11, 0xb6, 0x80, 0x13, 0x72, 0x2a, 0xad, 0x38, 0xac,
];

/// FIPS 204 ML-DSA-65 `pkEncode` byte length.
pub const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1_952;

/// Public values needed to derive the frozen TS13 request context.
///
/// `zk_system_id` is the relying-party-local request identifier. The fixed
/// proof-system name is a separate constant in the canonical context array.
#[derive(Clone, Copy, Debug)]
pub struct Ts13DemoPublicContextInput<'a> {
    pub circuit_hash: &'a [u8; 32],
    pub zk_system_id: &'a str,
    pub document_type: &'a str,
    pub namespace: &'a str,
    pub element_identifier: &'a str,
    pub expected_value_cbor: &'a [u8],
    pub timestamp_epoch_seconds: i64,
    pub session_transcript: &'a [u8],
    pub trusted_issuer_public_key: &'a [u8],
    pub revocation_public_key: &'a [u8],
    pub revocation_epoch: u32,
}

/// All verifier-derived public bytes consumed by the final TS13 composition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13DemoDerivedContext {
    pub canonical_session_transcript: Vec<u8>,
    pub device_authentication_bytes: Vec<u8>,
    pub device_cose_sig_structure: Vec<u8>,
    pub canonical_context_cbor: Vec<u8>,
    pub request_context_digest: [u8; 32],
}

/// Deterministic ISO device-authentication bytes derived from one request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13DemoDerivedDeviceAuthentication {
    pub canonical_session_transcript: Vec<u8>,
    pub device_authentication_bytes: Vec<u8>,
    pub device_cose_sig_structure: Vec<u8>,
}

/// One captured request shape used to freeze the device-message capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13DemoRequestContextCorpusEntry {
    pub label: &'static str,
    pub canonical_session_transcript: Vec<u8>,
    pub device_cose_sig_structure: Vec<u8>,
}

/// Evidence committed to the later shape manifest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ts13DemoRequestContextMeasurement {
    pub corpus_sha256: [u8; 32],
    pub observed_max_device_cose_sig_structure_bytes: u32,
    pub device_sig_structure_capacity: u32,
}

/// Privacy-safe failures from deterministic TS13 public-context construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ts13DemoContextError {
    MalformedSessionTranscript,
    InvalidPublicContext,
}

impl std::fmt::Display for Ts13DemoContextError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::MalformedSessionTranscript => "malformed session transcript",
            Self::InvalidPublicContext => "invalid public context",
        })
    }
}

impl std::error::Error for Ts13DemoContextError {}

fn push_argument(out: &mut Vec<u8>, major: u8, value: u64) {
    let prefix = major << 5;
    match value {
        0..=23 => out.push(prefix | value as u8),
        24..=0xff => out.extend_from_slice(&[prefix | 24, value as u8]),
        0x100..=0xffff => {
            out.push(prefix | 25);
            out.extend_from_slice(&(value as u16).to_be_bytes());
        }
        0x1_0000..=0xffff_ffff => {
            out.push(prefix | 26);
            out.extend_from_slice(&(value as u32).to_be_bytes());
        }
        _ => {
            out.push(prefix | 27);
            out.extend_from_slice(&value.to_be_bytes());
        }
    }
}

fn push_len(out: &mut Vec<u8>, major: u8, len: usize) {
    push_argument(out, major, len as u64);
}

fn canonical_key_cmp(left: &[u8], right: &[u8]) -> Ordering {
    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
}

fn encode_canonical_value(value: &Value, out: &mut Vec<u8>) -> Result<(), Ts13DemoContextError> {
    match value {
        Value::Integer(integer) => {
            let integer = i128::from(*integer);
            if integer >= 0 {
                push_argument(out, 0, integer as u64);
            } else {
                push_argument(out, 1, (-1 - integer) as u64);
            }
        }
        Value::Bytes(bytes) => {
            push_len(out, 2, bytes.len());
            out.extend_from_slice(bytes);
        }
        Value::Text(text) => {
            push_len(out, 3, text.len());
            out.extend_from_slice(text.as_bytes());
        }
        Value::Array(items) => {
            push_len(out, 4, items.len());
            for item in items {
                encode_canonical_value(item, out)?;
            }
        }
        Value::Map(entries) => {
            let mut encoded_entries = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                let mut encoded_key = Vec::new();
                encode_canonical_value(key, &mut encoded_key)?;
                encoded_entries.push((encoded_key, value));
            }
            encoded_entries.sort_by(|left, right| canonical_key_cmp(&left.0, &right.0));
            if encoded_entries
                .windows(2)
                .any(|pair| pair[0].0 == pair[1].0)
            {
                return Err(Ts13DemoContextError::MalformedSessionTranscript);
            }
            push_len(out, 5, encoded_entries.len());
            for (encoded_key, value) in encoded_entries {
                out.extend_from_slice(&encoded_key);
                encode_canonical_value(value, out)?;
            }
        }
        Value::Tag(tag, item) => {
            push_argument(out, 6, *tag);
            encode_canonical_value(item, out)?;
        }
        Value::Float(value) if value.is_nan() => {
            // RFC 8949 preferred serialization fixes every NaN to half-precision
            // quiet NaN 0x7e00, independent of its input payload or width.
            out.extend_from_slice(&[0xf9, 0x7e, 0x00]);
        }
        Value::Float(value) => {
            // Ciborium's low-level float header selects the shortest exact
            // f16/f32/f64 representation for all non-NaN values, including
            // signed zero and infinities.
            ciborium::ser::into_writer(&Value::Float(*value), out)
                .map_err(|_| Ts13DemoContextError::InvalidPublicContext)?;
        }
        Value::Bool(false) => out.push(0xf4),
        Value::Bool(true) => out.push(0xf5),
        Value::Null => out.push(0xf6),
        _ => return Err(Ts13DemoContextError::MalformedSessionTranscript),
    }
    Ok(())
}

fn canonical_cbor(value: &Value) -> Result<Vec<u8>, Ts13DemoContextError> {
    let mut out = Vec::new();
    encode_canonical_value(value, &mut out)?;
    Ok(out)
}

fn read_preferred_argument(
    bytes: &[u8],
    position: &mut usize,
    additional: u8,
) -> Result<u64, Ts13DemoContextError> {
    let read = |position: &mut usize, count: usize| {
        let end = position
            .checked_add(count)
            .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
        let value = bytes
            .get(*position..end)
            .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
        *position = end;
        Ok(value)
    };
    match additional {
        value @ 0..=23 => Ok(u64::from(value)),
        24 => {
            let value = u64::from(read(position, 1)?[0]);
            (value >= 24)
                .then_some(value)
                .ok_or(Ts13DemoContextError::MalformedSessionTranscript)
        }
        25 => {
            let value = u64::from(u16::from_be_bytes(
                read(position, 2)?
                    .try_into()
                    .map_err(|_| Ts13DemoContextError::MalformedSessionTranscript)?,
            ));
            (value > u64::from(u8::MAX))
                .then_some(value)
                .ok_or(Ts13DemoContextError::MalformedSessionTranscript)
        }
        26 => {
            let value = u64::from(u32::from_be_bytes(
                read(position, 4)?
                    .try_into()
                    .map_err(|_| Ts13DemoContextError::MalformedSessionTranscript)?,
            ));
            (value > u64::from(u16::MAX))
                .then_some(value)
                .ok_or(Ts13DemoContextError::MalformedSessionTranscript)
        }
        27 => {
            let value = u64::from_be_bytes(
                read(position, 8)?
                    .try_into()
                    .map_err(|_| Ts13DemoContextError::MalformedSessionTranscript)?,
            );
            (value > u64::from(u32::MAX))
                .then_some(value)
                .ok_or(Ts13DemoContextError::MalformedSessionTranscript)
        }
        _ => Err(Ts13DemoContextError::MalformedSessionTranscript),
    }
}

fn validate_preferred_float(encoded: &[u8]) -> Result<(), Ts13DemoContextError> {
    let value: Value = ciborium::de::from_reader(encoded)
        .map_err(|_| Ts13DemoContextError::MalformedSessionTranscript)?;
    if !matches!(value, Value::Float(_))
        || canonical_cbor(&value).map_err(|_| Ts13DemoContextError::MalformedSessionTranscript)?
            != encoded
    {
        return Err(Ts13DemoContextError::MalformedSessionTranscript);
    }
    Ok(())
}

enum CborFrame {
    Tag,
    Array {
        remaining: u64,
    },
    Map {
        remaining: u64,
        expecting_key: bool,
        key_start: usize,
        previous_key: Option<(usize, usize)>,
    },
}

fn finish_canonical_item(
    bytes: &[u8],
    end: usize,
    stack: &mut Vec<CborFrame>,
) -> Result<bool, Ts13DemoContextError> {
    loop {
        let Some(frame) = stack.last_mut() else {
            return Ok(true);
        };
        match frame {
            CborFrame::Tag => {
                stack.pop();
            }
            CborFrame::Array { remaining } => {
                *remaining -= 1;
                if *remaining == 0 {
                    stack.pop();
                } else {
                    return Ok(false);
                }
            }
            CborFrame::Map {
                remaining,
                expecting_key,
                key_start,
                previous_key,
            } => {
                if *expecting_key {
                    let key = bytes
                        .get(*key_start..end)
                        .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
                    if previous_key.is_some_and(|(start, previous_end)| {
                        canonical_key_cmp(&bytes[start..previous_end], key) != Ordering::Less
                    }) {
                        return Err(Ts13DemoContextError::MalformedSessionTranscript);
                    }
                    *previous_key = Some((*key_start, end));
                    *expecting_key = false;
                    return Ok(false);
                }
                *remaining -= 1;
                if *remaining == 0 {
                    stack.pop();
                } else {
                    *expecting_key = true;
                    *key_start = end;
                    return Ok(false);
                }
            }
        }
    }
}

fn validate_canonical_cbor(bytes: &[u8]) -> Result<usize, Ts13DemoContextError> {
    let mut stack = Vec::new();
    let mut position = 0usize;
    loop {
        let start = position;
        let initial = *bytes
            .get(position)
            .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
        position += 1;
        let major = initial >> 5;
        let additional = initial & 0x1f;
        let item_is_complete = match major {
            0 | 1 => {
                read_preferred_argument(bytes, &mut position, additional)?;
                true
            }
            2 | 3 => {
                let len =
                    usize::try_from(read_preferred_argument(bytes, &mut position, additional)?)
                        .map_err(|_| Ts13DemoContextError::MalformedSessionTranscript)?;
                let end = position
                    .checked_add(len)
                    .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
                let value = bytes
                    .get(position..end)
                    .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
                if major == 3 && std::str::from_utf8(value).is_err() {
                    return Err(Ts13DemoContextError::MalformedSessionTranscript);
                }
                position = end;
                true
            }
            4 => {
                let count = read_preferred_argument(bytes, &mut position, additional)?;
                if count == 0 {
                    true
                } else {
                    stack.push(CborFrame::Array { remaining: count });
                    false
                }
            }
            5 => {
                let count = read_preferred_argument(bytes, &mut position, additional)?;
                if count == 0 {
                    true
                } else {
                    stack.push(CborFrame::Map {
                        remaining: count,
                        expecting_key: true,
                        key_start: position,
                        previous_key: None,
                    });
                    false
                }
            }
            6 => {
                read_preferred_argument(bytes, &mut position, additional)?;
                stack.push(CborFrame::Tag);
                false
            }
            7 => {
                match additional {
                    0..=23 => {}
                    24 => {
                        let simple = *bytes
                            .get(position)
                            .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
                        if simple < 32 {
                            return Err(Ts13DemoContextError::MalformedSessionTranscript);
                        }
                        position += 1;
                    }
                    width @ 25..=27 => {
                        let len = 1usize << (width - 24);
                        let end = position
                            .checked_add(len)
                            .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
                        bytes
                            .get(position..end)
                            .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?;
                        validate_preferred_float(
                            bytes
                                .get(start..end)
                                .ok_or(Ts13DemoContextError::MalformedSessionTranscript)?,
                        )?;
                        position = end;
                    }
                    _ => return Err(Ts13DemoContextError::MalformedSessionTranscript),
                }
                true
            }
            _ => return Err(Ts13DemoContextError::MalformedSessionTranscript),
        };

        if item_is_complete && finish_canonical_item(bytes, position, &mut stack)? {
            return Ok(position);
        }
    }
}

/// Fully consume and validate the deterministic RFC 8949 encoding of a
/// SessionTranscript. Token-level validation keeps canonical simple values,
/// NaN, and infinities which `ciborium::Value` cannot round-trip losslessly.
pub fn canonical_session_transcript(bytes: &[u8]) -> Result<Vec<u8>, Ts13DemoContextError> {
    if bytes.first().map(|byte| byte >> 5) != Some(4)
        || validate_canonical_cbor(bytes)? != bytes.len()
    {
        return Err(Ts13DemoContextError::MalformedSessionTranscript);
    }
    Ok(bytes.to_vec())
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn p256_cose_key(x: &[u8; 32], y: &[u8; 32]) -> Result<Vec<u8>, Ts13DemoContextError> {
    canonical_cbor(&Value::Map(vec![
        (Value::Integer(1.into()), Value::Integer(2.into())),
        (Value::Integer((-1).into()), Value::Integer(1.into())),
        (Value::Integer((-2).into()), Value::Bytes(x.to_vec())),
        (Value::Integer((-3).into()), Value::Bytes(y.to_vec())),
    ]))
}

fn tagged_encoded_cbor(encoded: Vec<u8>) -> Value {
    Value::Tag(24, Box::new(Value::Bytes(encoded)))
}

fn corpus_device_engagement(
    include_qr_retrieval_methods: bool,
) -> Result<Vec<u8>, Ts13DemoContextError> {
    let device_key = p256_cose_key(&CORPUS_DEVICE_KEY_X, &CORPUS_DEVICE_KEY_Y)?;
    let mut entries = vec![
        (Value::Integer(0.into()), Value::Text("1.0".to_string())),
        (
            Value::Integer(1.into()),
            Value::Array(vec![
                Value::Integer(1.into()),
                tagged_encoded_cbor(device_key),
            ]),
        ),
    ];
    if include_qr_retrieval_methods {
        let central_client = Value::Array(vec![
            Value::Integer(2.into()),
            Value::Integer(1.into()),
            Value::Map(vec![
                (Value::Integer(0.into()), Value::Bool(false)),
                (Value::Integer(1.into()), Value::Bool(true)),
                (
                    Value::Integer(11.into()),
                    Value::Bytes(CORPUS_BLE_UUID.to_vec()),
                ),
            ]),
        ]);
        let peripheral_server = Value::Array(vec![
            Value::Integer(2.into()),
            Value::Integer(1.into()),
            Value::Map(vec![
                (Value::Integer(0.into()), Value::Bool(true)),
                (Value::Integer(1.into()), Value::Bool(false)),
                (
                    Value::Integer(10.into()),
                    Value::Bytes(CORPUS_BLE_UUID.to_vec()),
                ),
            ]),
        ]);
        entries.push((
            Value::Integer(2.into()),
            Value::Array(vec![central_client, peripheral_server]),
        ));
    }
    canonical_cbor(&Value::Map(entries))
}

fn corpus_nfc_static_handover(device_engagement: &[u8]) -> Result<Value, Ts13DemoContextError> {
    let engagement_len = u8::try_from(device_engagement.len())
        .map_err(|_| Ts13DemoContextError::InvalidPublicContext)?;
    let engagement_type_len = u8::try_from(NDEF_DEVICE_ENGAGEMENT_TYPE.len())
        .map_err(|_| Ts13DemoContextError::InvalidPublicContext)?;
    let ble_type_len = u8::try_from(NDEF_BLE_OOB_TYPE.len())
        .map_err(|_| Ts13DemoContextError::InvalidPublicContext)?;

    // NFC Forum Connection Handover 1.5, one active BLE carrier, and the
    // auxiliary ISO DeviceEngagement record used by the wallet's static path.
    let mut handover_select = vec![
        0x91,
        0x02,
        0x0f,
        b'H',
        b's',
        0x15,
        0xd1,
        0x02,
        0x09,
        b'a',
        b'c',
        0x01,
        0x01,
        b'0',
        0x01,
        0x04,
        b'm',
        b'd',
        b'o',
        b'c',
        0x1c,
        engagement_type_len,
        engagement_len,
        0x04,
    ];
    handover_select.extend_from_slice(NDEF_DEVICE_ENGAGEMENT_TYPE);
    handover_select.extend_from_slice(b"mdoc");
    handover_select.extend_from_slice(device_engagement);

    handover_select.extend_from_slice(&[0x5a, ble_type_len, 0x15, 0x01]);
    handover_select.extend_from_slice(NDEF_BLE_OOB_TYPE);
    handover_select.push(b'0');
    handover_select.extend_from_slice(&[0x02, 0x1c, 0x03, 0x11, 0x07]);
    handover_select.extend(CORPUS_BLE_UUID[8..].iter().rev());
    handover_select.extend(CORPUS_BLE_UUID[..8].iter().rev());

    Ok(Value::Array(vec![
        Value::Bytes(handover_select),
        Value::Null,
    ]))
}

fn corpus_session_transcripts() -> Result<Vec<(&'static str, Vec<u8>)>, Ts13DemoContextError> {
    let openid4vp = canonical_cbor(&Value::Array(vec![
        Value::Null,
        Value::Null,
        Value::Array(vec![
            Value::Text("OpenID4VPHandover".to_string()),
            Value::Bytes(OPENID4VP_HANDOVER_INFO_SHA256.to_vec()),
        ]),
    ]))?;

    let reader_key = p256_cose_key(&CORPUS_READER_KEY_X, &CORPUS_READER_KEY_Y)?;
    let qr_device_engagement = corpus_device_engagement(true)?;
    let qr = canonical_cbor(&Value::Array(vec![
        tagged_encoded_cbor(qr_device_engagement),
        tagged_encoded_cbor(reader_key.clone()),
        Value::Null,
    ]))?;

    let nfc_device_engagement = corpus_device_engagement(false)?;
    let nfc_handover = corpus_nfc_static_handover(&nfc_device_engagement)?;
    let nfc_static = canonical_cbor(&Value::Array(vec![
        tagged_encoded_cbor(nfc_device_engagement),
        tagged_encoded_cbor(reader_key),
        nfc_handover,
    ]))?;

    Ok(vec![
        (OPENID4VP_CORPUS_LABEL, openid4vp),
        (ISO_QR_CORPUS_LABEL, qr),
        (ISO_NFC_STATIC_CORPUS_LABEL, nfc_static),
    ])
}

/// Derive the exact ISO DeviceAuthentication and full COSE `Sig_structure`
/// from one canonical SessionTranscript.
pub fn derive_device_authentication(
    session_transcript: &[u8],
) -> Result<Ts13DemoDerivedDeviceAuthentication, Ts13DemoContextError> {
    let canonical_session_transcript = canonical_session_transcript(session_transcript)?;
    let empty_device_namespaces = canonical_cbor(&Value::Map(Vec::new()))?;
    let mut device_authentication = Vec::new();
    push_argument(&mut device_authentication, 4, 4);
    encode_canonical_value(
        &Value::Text("DeviceAuthentication".to_string()),
        &mut device_authentication,
    )?;
    device_authentication.extend_from_slice(&canonical_session_transcript);
    encode_canonical_value(
        &Value::Text(DOCUMENT_TYPE.to_string()),
        &mut device_authentication,
    )?;
    encode_canonical_value(
        &Value::Tag(24, Box::new(Value::Bytes(empty_device_namespaces))),
        &mut device_authentication,
    )?;
    let device_authentication_bytes = canonical_cbor(&Value::Tag(
        24,
        Box::new(Value::Bytes(device_authentication)),
    ))?;
    let device_cose_sig_structure = canonical_cbor(&Value::Array(vec![
        Value::Text("Signature1".to_string()),
        Value::Bytes(ML_DSA_65_PROTECTED_HEADER.to_vec()),
        Value::Bytes(Vec::new()),
        Value::Bytes(device_authentication_bytes.clone()),
    ]))?;

    Ok(Ts13DemoDerivedDeviceAuthentication {
        canonical_session_transcript,
        device_authentication_bytes,
        device_cose_sig_structure,
    })
}

/// Deterministic request corpus shared by capacity measurement and artifact
/// generation. Entries contain both the captured transcript and its full
/// derived device COSE message.
pub fn request_context_corpus(
) -> Result<Vec<Ts13DemoRequestContextCorpusEntry>, Ts13DemoContextError> {
    corpus_session_transcripts()?
        .into_iter()
        .map(|(label, transcript)| {
            let derived = derive_device_authentication(&transcript)?;
            Ok(Ts13DemoRequestContextCorpusEntry {
                label,
                canonical_session_transcript: derived.canonical_session_transcript,
                device_cose_sig_structure: derived.device_cose_sig_structure,
            })
        })
        .collect()
}

fn canonical_request_context_corpus(
    corpus: &[Ts13DemoRequestContextCorpusEntry],
) -> Result<Vec<u8>, Ts13DemoContextError> {
    canonical_cbor(&Value::Array(vec![
        Value::Text(REQUEST_CONTEXT_CORPUS_LABEL.to_string()),
        Value::Array(
            corpus
                .iter()
                .map(|entry| {
                    Value::Array(vec![
                        Value::Text(entry.label.to_string()),
                        Value::Bytes(entry.canonical_session_transcript.clone()),
                        Value::Bytes(entry.device_cose_sig_structure.clone()),
                    ])
                })
                .collect(),
        ),
    ]))
}

/// Measure the supported request corpus and select the frozen power-of-two
/// message capacity with the specification's 128-byte headroom.
pub fn measure_request_context_corpus(
) -> Result<Ts13DemoRequestContextMeasurement, Ts13DemoContextError> {
    let corpus = request_context_corpus()?;
    let observed_max = corpus
        .iter()
        .map(|entry| entry.device_cose_sig_structure.len())
        .max()
        .ok_or(Ts13DemoContextError::InvalidPublicContext)?;
    let capacity = observed_max
        .checked_add(REQUEST_CONTEXT_CAPACITY_HEADROOM)
        .and_then(usize::checked_next_power_of_two)
        .ok_or(Ts13DemoContextError::InvalidPublicContext)?;

    Ok(Ts13DemoRequestContextMeasurement {
        corpus_sha256: sha256(&canonical_request_context_corpus(&corpus)?),
        observed_max_device_cose_sig_structure_bytes: u32::try_from(observed_max)
            .map_err(|_| Ts13DemoContextError::InvalidPublicContext)?,
        device_sig_structure_capacity: u32::try_from(capacity)
            .map_err(|_| Ts13DemoContextError::InvalidPublicContext)?,
    })
}

/// Reject a request message which cannot fit the artifact's fixed geometry.
pub fn ensure_device_cose_sig_structure_capacity(
    device_cose_sig_structure: &[u8],
    capacity: u32,
) -> Result<(), Ts13DemoContextError> {
    let capacity =
        usize::try_from(capacity).map_err(|_| Ts13DemoContextError::InvalidPublicContext)?;
    if capacity == 0 || !capacity.is_power_of_two() || device_cose_sig_structure.len() > capacity {
        return Err(Ts13DemoContextError::InvalidPublicContext);
    }
    Ok(())
}

/// Derive the exact ISO DeviceAuthentication, COSE Sig_structure, and TS13
/// canonical request context from verifier-authoritative public inputs.
pub fn derive_public_context(
    input: Ts13DemoPublicContextInput<'_>,
) -> Result<Ts13DemoDerivedContext, Ts13DemoContextError> {
    if input.document_type != DOCUMENT_TYPE
        || input.namespace != NAMESPACE
        || input.element_identifier != ELEMENT_IDENTIFIER
        || input.expected_value_cbor != EXPECTED_VALUE_CBOR
        || input.trusted_issuer_public_key.len() != ML_DSA_65_PUBLIC_KEY_BYTES
        || input.revocation_public_key.len() != ML_DSA_65_PUBLIC_KEY_BYTES
    {
        return Err(Ts13DemoContextError::InvalidPublicContext);
    }

    let derived_device = derive_device_authentication(input.session_transcript)?;
    let canonical_session_transcript = derived_device.canonical_session_transcript;
    let device_authentication_bytes = derived_device.device_authentication_bytes;
    let device_cose_sig_structure = derived_device.device_cose_sig_structure;

    let canonical_context_cbor = canonical_cbor(&Value::Array(vec![
        Value::Text(CONTEXT_LABEL.to_string()),
        Value::Text(SYSTEM_NAME.to_string()),
        Value::Text(input.zk_system_id.to_string()),
        Value::Bytes(input.circuit_hash.to_vec()),
        Value::Text(DOCUMENT_TYPE.to_string()),
        Value::Text(NAMESPACE.to_string()),
        Value::Text(ELEMENT_IDENTIFIER.to_string()),
        Value::Bytes(EXPECTED_VALUE_CBOR.to_vec()),
        Value::Integer(input.timestamp_epoch_seconds.into()),
        Value::Bytes(sha256(&canonical_session_transcript).to_vec()),
        Value::Bytes(sha256(&device_cose_sig_structure).to_vec()),
        Value::Bytes(sha256(input.trusted_issuer_public_key).to_vec()),
        Value::Bytes(sha256(input.revocation_public_key).to_vec()),
        Value::Integer(input.revocation_epoch.into()),
    ]))?;
    let request_context_digest = sha256(&canonical_context_cbor);

    Ok(Ts13DemoDerivedContext {
        canonical_session_transcript,
        device_authentication_bytes,
        device_cose_sig_structure,
        canonical_context_cbor,
        request_context_digest,
    })
}

/// Frozen zero-column AIR module which binds the TS13 request theorem before
/// relation challenges are drawn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ts13PublicContextBindV1 {
    request_context_digest: [u8; 32],
    circuit_hash: [u8; 32],
}

impl Ts13PublicContextBindV1 {
    pub const fn new(request_context_digest: [u8; 32], circuit_hash: [u8; 32]) -> Self {
        Self {
            request_context_digest,
            circuit_hash,
        }
    }
}

impl Air for Ts13PublicContextBindV1 {
    fn mix_public(&self, channel: &mut Blake2sChannel) {
        for &byte in PUBLIC_CONTEXT_TRANSCRIPT_DOMAIN
            .iter()
            .chain(&self.request_context_digest)
            .chain(&self.circuit_hash)
        {
            channel.mix_u64(u64::from(byte));
        }
    }

    fn draw_relations(&mut self, _channel: &mut Blake2sChannel) {}

    fn layout(&self) -> TreeLayout {
        TreeLayout {
            preprocessed: Vec::new(),
            trace: Vec::new(),
            interaction: Vec::new(),
        }
    }

    fn claimed_sums(&self) -> Vec<QM31> {
        Vec::new()
    }

    fn preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        Vec::new()
    }

    fn build_components(&mut self, _allocator: &mut TraceLocationAllocator) {}

    fn components(&self) -> Vec<&dyn Component> {
        Vec::new()
    }
}

impl AirProver for Ts13PublicContextBindV1 {
    fn max_log_size(&self) -> u32 {
        0
    }

    fn write_preprocessed(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_trace(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn write_interaction(&mut self, _tb: &mut TreeBuilder<SimdBackend, air_core::Mc>) {}

    fn prover_components(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn sample_input<'a>(
        circuit_hash: &'a [u8; 32],
        transcript: &'a [u8],
        issuer_key: &'a [u8],
        revocation_key: &'a [u8],
    ) -> Ts13DemoPublicContextInput<'a> {
        Ts13DemoPublicContextInput {
            circuit_hash,
            zk_system_id: "rp-demo",
            document_type: DOCUMENT_TYPE,
            namespace: NAMESPACE,
            element_identifier: ELEMENT_IDENTIFIER,
            expected_value_cbor: EXPECTED_VALUE_CBOR,
            timestamp_epoch_seconds: 1_735_689_600,
            session_transcript: transcript,
            trusted_issuer_public_key: issuer_key,
            revocation_public_key: revocation_key,
            revocation_epoch: 7,
        }
    }

    #[test]
    fn canonical_session_transcript_accepts_preferred_float_encodings() {
        for canonical in [
            &[0x81, 0xf9, 0x7e, 0x00][..],
            &[0x81, 0xf9, 0x7c, 0x00],
            &[0x81, 0xf9, 0xfc, 0x00],
            &[0x81, 0xfa, 0x47, 0xc3, 0x50, 0x00],
        ] {
            assert_eq!(
                canonical_session_transcript(canonical).as_deref(),
                Ok(canonical)
            );
        }
    }

    #[test]
    fn canonical_session_transcript_accepts_unrestricted_canonical_items() {
        for canonical in [
            &[0x81, 0xf7][..],
            &[0x81, 0xf8, 0x20],
            &[0x81, 0xd8, 0x18, 0x41, 0xa0],
        ] {
            assert_eq!(
                canonical_session_transcript(canonical).as_deref(),
                Ok(canonical)
            );
        }
    }

    #[test]
    fn canonical_session_transcript_rejects_noncanonical_or_malformed_cbor() {
        for malformed in [
            &[0x81, 0xa2, 0x61, b'b', 0x01, 0x61, b'a', 0x02][..],
            &[0x81, 0xa2, 0x61, b'a', 0x01, 0x61, b'a', 0x02],
            &[0x9f, 0x01, 0xff],
            &[0x81, 0x18, 0x01],
            &[0x81, 0xf9, 0x7e, 0x01],
            &[0x81, 0xfa, 0x7f, 0x80, 0x00, 0x00],
            &[0x81, 0xfa, 0xff, 0x80, 0x00, 0x00],
            &[0x81, 0xfa, 0x3f, 0x80, 0x00, 0x00],
            &[0x81, 0xfb, 0x7f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            &[0x81, 0xf8, 0x17],
            &[0x81, 0xd8, 0x01, 0xf6],
            &[0x81, 0x61, 0xff],
            &[0x81, 0x5f, 0x40, 0xff],
            &[0x81, 0x01, 0x02],
            &[0x01],
            &[],
        ] {
            assert_eq!(
                canonical_session_transcript(malformed),
                Err(Ts13DemoContextError::MalformedSessionTranscript),
                "accepted malformed transcript {}",
                hex(malformed)
            );
        }
    }

    #[test]
    fn canonical_session_transcript_accepts_deep_canonical_nesting() {
        let mut nested = vec![0x81; 1_024];
        nested.push(0xf6);
        let canonical = canonical_session_transcript(&nested);
        assert_eq!(canonical, Ok(nested));
    }

    #[test]
    fn canonical_session_transcript_accepts_canonical_map_order() {
        let canonical = [0x81, 0xa3, 0x01, 0x01, 0x20, 0x02, 0x18, 0x18, 0x03];
        assert_eq!(
            canonical_session_transcript(&canonical),
            Ok(canonical.to_vec())
        );
    }

    #[test]
    fn exact_device_authentication_cose_and_context_are_stable() {
        let circuit_hash = [0x11; 32];
        let transcript = [0x83, 0xf6, 0xf6, 0x81, 0x01];
        let issuer_key = [0x22; ML_DSA_65_PUBLIC_KEY_BYTES];
        let revocation_key = [0x33; ML_DSA_65_PUBLIC_KEY_BYTES];
        let derived = derive_public_context(sample_input(
            &circuit_hash,
            &transcript,
            &issuer_key,
            &revocation_key,
        ))
        .unwrap();

        assert_eq!(derived.canonical_session_transcript, transcript);
        assert_eq!(
            hex(&derived.device_authentication_bytes),
            "d8185837847444657669636541757468656e7469636174696f6e83f6f681017765752e6575726f70612e65632e657564692e7069642e31d81841a0"
        );
        assert_eq!(
            hex(&derived.device_cose_sig_structure),
            "846a5369676e61747572653144a101383040583bd8185837847444657669636541757468656e7469636174696f6e83f6f681017765752e6575726f70612e65632e657564692e7069642e31d81841a0"
        );
        assert_eq!(
            hex(&derived.canonical_context_cbor),
            "8e7819455544492d545331332d44454d4f2d434f4e544558542d5631767374776f2d657569642d747331332d64656d6f2d76316772702d64656d6f582011111111111111111111111111111111111111111111111111111111111111117765752e6575726f70612e65632e657564692e7069642e317765752e6575726f70612e65632e657564692e7069642e316b6167655f6f7665725f313841f51a677485805820711fe8362af74f1b03b190df7d5c421aa0443f24f32b7cc559049db85923a4455820f8b7f020bb89e3e3335973c9dfa44308521281bcb6a2b3cfaf6e516869ff268c5820ba118867d8dae627389f32117ee64b1515713965e5694250971804293345354d58209ad608ed47497e04b6d0b209bb4d5fd020cfff8afa7a1855f00a3abf94bfc10307"
        );
        assert_eq!(
            hex(&derived.request_context_digest),
            "c9ec6eb138da43f3f278000d9b8a4ab9188904ef53c12f1df503bcd972a04fc4"
        );
    }

    #[test]
    fn request_context_corpus_and_capacity_are_stable() {
        let corpus = request_context_corpus().unwrap();
        assert_eq!(
            corpus.iter().map(|entry| entry.label).collect::<Vec<_>>(),
            vec![
                OPENID4VP_CORPUS_LABEL,
                ISO_QR_CORPUS_LABEL,
                ISO_NFC_STATIC_CORPUS_LABEL
            ]
        );
        assert_eq!(
            hex(&corpus[0].canonical_session_transcript),
            "83f6f682714f70656e494434565048616e646f7665725820048bc053c00442af9b8eed494cefdd9d95240d254b046b11b68013722aad38ac"
        );
        let expected_shapes = [
            (
                56,
                "5892c5070e68b42fc23d2931e581e3f668bb409814a242d520a86b1e225d28eb",
                130,
            ),
            (
                227,
                "2e4cb873aea91825efcbc539e057a5a4325691e4f54330a7f16f4bbc51da5733",
                303,
            ),
            (
                380,
                "307b69873c6ecf00a8303a18ee44b59e75ef35792ae47a9d7ae1df37aa63856c",
                456,
            ),
        ];
        for (entry, (transcript_len, transcript_sha256, cose_len)) in
            corpus.iter().zip(expected_shapes)
        {
            assert_eq!(
                canonical_session_transcript(&entry.canonical_session_transcript).unwrap(),
                entry.canonical_session_transcript
            );
            assert_eq!(
                derive_device_authentication(&entry.canonical_session_transcript)
                    .unwrap()
                    .device_cose_sig_structure,
                entry.device_cose_sig_structure
            );
            assert_eq!(entry.canonical_session_transcript.len(), transcript_len);
            assert_eq!(
                hex(&sha256(&entry.canonical_session_transcript)),
                transcript_sha256
            );
            assert_eq!(entry.device_cose_sig_structure.len(), cose_len);
        }

        let measurement = measure_request_context_corpus().unwrap();
        assert_eq!(
            hex(&measurement.corpus_sha256),
            "2ba3208731e3eb7b67ef54e0683f28dcb81d1b3811c0d2a1ce1d187ee9c3d77c"
        );
        assert_eq!(
            measurement.observed_max_device_cose_sig_structure_bytes,
            456
        );
        assert_eq!(measurement.device_sig_structure_capacity, 1_024);

        let capacity = usize::try_from(measurement.device_sig_structure_capacity).unwrap();
        let largest = corpus
            .iter()
            .max_by_key(|entry| entry.device_cose_sig_structure.len())
            .unwrap();
        assert_eq!(
            ensure_device_cose_sig_structure_capacity(
                &largest.device_cose_sig_structure,
                measurement.device_sig_structure_capacity
            ),
            Ok(())
        );
        assert_eq!(
            ensure_device_cose_sig_structure_capacity(
                &vec![0; capacity + 1],
                measurement.device_sig_structure_capacity
            ),
            Err(Ts13DemoContextError::InvalidPublicContext)
        );
    }

    #[test]
    fn public_context_rejects_profile_or_key_shape_drift() {
        let circuit_hash = [0x11; 32];
        let transcript = [0x80];
        let issuer_key = [0x22; ML_DSA_65_PUBLIC_KEY_BYTES];
        let revocation_key = [0x33; ML_DSA_65_PUBLIC_KEY_BYTES];

        let mut input = sample_input(&circuit_hash, &transcript, &issuer_key, &revocation_key);
        input.element_identifier = "birth_date";
        assert_eq!(
            derive_public_context(input),
            Err(Ts13DemoContextError::InvalidPublicContext)
        );

        let short_key = [0x22; ML_DSA_65_PUBLIC_KEY_BYTES - 1];
        let input = sample_input(&circuit_hash, &transcript, &short_key, &revocation_key);
        assert_eq!(
            derive_public_context(input),
            Err(Ts13DemoContextError::InvalidPublicContext)
        );
    }

    #[test]
    fn context_bind_has_no_columns_and_mixes_exact_frozen_bytes() {
        let bind = Ts13PublicContextBindV1::new([0x44; 32], [0x55; 32]);
        let mut channel = Blake2sChannel::default();
        bind.mix_public(&mut channel);

        assert_eq!(
            hex(channel.digest().as_ref()),
            "d19ae85694b5d299e32b1b61ff5051331cfba6b4e58e81365b63144f51eb4ef2"
        );
        assert_eq!(bind.layout().preprocessed, Vec::<u32>::new());
        assert_eq!(bind.layout().trace, Vec::<u32>::new());
        assert_eq!(bind.layout().interaction, Vec::<u32>::new());
        assert!(bind.claimed_sums().is_empty());
        assert_eq!(bind.max_log_size(), 0);
    }

    #[test]
    fn context_bind_changes_for_each_bound_input_class() {
        let digest = |request_context_digest, circuit_hash| {
            let bind = Ts13PublicContextBindV1::new(request_context_digest, circuit_hash);
            let mut channel = Blake2sChannel::default();
            bind.mix_public(&mut channel);
            channel.digest()
        };
        let baseline = digest([0x44; 32], [0x55; 32]);
        assert_ne!(baseline, digest([0x45; 32], [0x55; 32]));
        assert_ne!(baseline, digest([0x44; 32], [0x56; 32]));
    }
}
