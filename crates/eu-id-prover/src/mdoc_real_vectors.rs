//! Fixed third-party mdoc vectors shared by strict-parser unit tests.

use std::io::Cursor;

use ciborium::value::Value;

pub(crate) const PYMDOC_ITEM_KEY_ORDER: [&str; 4] =
    ["random", "digestID", "elementValue", "elementIdentifier"];
pub(crate) const LONGFELLOW_ITEM_KEY_ORDER: [&str; 4] =
    ["digestID", "random", "elementIdentifier", "elementValue"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RealMdocNamespace {
    pub(crate) name: String,
    pub(crate) digest_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RealIssuerSignedItem {
    pub(crate) namespace: String,
    pub(crate) outer: Vec<u8>,
    pub(crate) inner: Vec<u8>,
    pub(crate) digest_id: u32,
    pub(crate) key_order: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RealMdocVector {
    pub(crate) source: &'static str,
    pub(crate) version: String,
    pub(crate) mso: Vec<u8>,
    pub(crate) namespaces: Vec<RealMdocNamespace>,
    pub(crate) items: Vec<RealIssuerSignedItem>,
}

const PID_PYMDOC_SOURCE: &str =
    "crates/eu-id-prover/tests/vectors/pid_pymdoc_v1/issuer_signed.cbor";
const LONGFELLOW_MDL3_SOURCE: &str = "crates/eu-id-prover/tests/vectors/longfellow_mdl3/mdoc.cbor";
const LONGFELLOW_EUAV11_SOURCE: &str =
    "crates/eu-id-prover/tests/vectors/longfellow_euav11/mdoc.cbor";

const PID_PYMDOC_BYTES: &[u8] = include_bytes!("../tests/vectors/pid_pymdoc_v1/issuer_signed.cbor");
const LONGFELLOW_MDL3_BYTES: &[u8] = include_bytes!("../tests/vectors/longfellow_mdl3/mdoc.cbor");
const LONGFELLOW_EUAV11_BYTES: &[u8] =
    include_bytes!("../tests/vectors/longfellow_euav11/mdoc.cbor");

const PID_NAMESPACES: &[(&str, usize)] = &[("eu.europa.ec.eudi.pid.1", 6)];
const MDL3_NAMESPACES: &[(&str, usize)] =
    &[("org.iso.18013.5.1", 34), ("org.iso.18013.5.1.aamva", 6)];
const EUAV11_NAMESPACES: &[(&str, usize)] = &[("eu.europa.ec.av.1", 5)];

const PID_ITEM_LENGTHS: &[(usize, usize)] = &[
    (104, 100),
    (102, 98),
    (110, 106),
    (112, 108),
    (115, 111),
    (113, 109),
];
const MDL3_ITEM_LENGTHS: &[(usize, usize)] = &[(94, 90), (95, 91), (95, 91), (79, 75), (83, 79)];
const EUAV11_ITEM_LENGTHS: &[(usize, usize)] = &[(100, 96)];

struct FixtureSpec {
    source: &'static str,
    bytes: &'static [u8],
    mso_len: usize,
    namespaces: &'static [(&'static str, usize)],
    item_lengths: &'static [(usize, usize)],
    item_key_order: &'static [&'static str; 4],
}

const FIXTURES: [FixtureSpec; 3] = [
    FixtureSpec {
        source: PID_PYMDOC_SOURCE,
        bytes: PID_PYMDOC_BYTES,
        mso_len: 526,
        namespaces: PID_NAMESPACES,
        item_lengths: PID_ITEM_LENGTHS,
        item_key_order: &PYMDOC_ITEM_KEY_ORDER,
    },
    FixtureSpec {
        source: LONGFELLOW_MDL3_SOURCE,
        bytes: LONGFELLOW_MDL3_BYTES,
        mso_len: 1_750,
        namespaces: MDL3_NAMESPACES,
        item_lengths: MDL3_ITEM_LENGTHS,
        item_key_order: &LONGFELLOW_ITEM_KEY_ORDER,
    },
    FixtureSpec {
        source: LONGFELLOW_EUAV11_SOURCE,
        bytes: LONGFELLOW_EUAV11_BYTES,
        mso_len: 479,
        namespaces: EUAV11_NAMESPACES,
        item_lengths: EUAV11_ITEM_LENGTHS,
        item_key_order: &LONGFELLOW_ITEM_KEY_ORDER,
    },
];

pub(crate) fn real_mdoc_vectors() -> Vec<RealMdocVector> {
    FIXTURES.iter().map(load_fixture).collect()
}

fn load_fixture(spec: &FixtureSpec) -> RealMdocVector {
    let root = decode_exact(spec.bytes, spec.source);
    let issuer_signed = issuer_signed(&root, spec.source);
    let issuer_signed_map = as_map(issuer_signed, "issuerSigned", spec.source);

    let issuer_auth = map_get(issuer_signed_map, "issuerAuth", spec.source);
    let issuer_auth = match issuer_auth {
        Value::Tag(18, inner) => inner.as_ref(),
        value => value,
    };
    let issuer_auth = as_array(issuer_auth, "issuerAuth", spec.source);
    assert_eq!(
        issuer_auth.len(),
        4,
        "{}: issuerAuth is not a four-element COSE_Sign1",
        spec.source
    );
    let payload = as_bytes(&issuer_auth[2], "issuerAuth payload", spec.source);
    let payload = decode_exact(payload, "issuerAuth payload");
    let mso = match payload {
        Value::Tag(24, inner) => {
            as_bytes(&inner, "MobileSecurityObjectBytes", spec.source).to_vec()
        }
        _ => panic!(
            "{}: issuerAuth payload is not tag-24 MSO bytes",
            spec.source
        ),
    };
    let mso_value = decode_exact(&mso, "MobileSecurityObject");
    let mso_map = as_map(&mso_value, "MobileSecurityObject", spec.source);
    let version = as_text(
        map_get(mso_map, "version", spec.source),
        "MSO version",
        spec.source,
    )
    .to_string();

    let value_digests = as_map(
        map_get(mso_map, "valueDigests", spec.source),
        "MSO valueDigests",
        spec.source,
    );
    let namespaces = value_digests
        .iter()
        .map(|(name, digests)| RealMdocNamespace {
            name: as_text(name, "valueDigests namespace", spec.source).to_string(),
            digest_count: as_map(digests, "namespace digests", spec.source).len(),
        })
        .collect::<Vec<_>>();

    let item_namespaces = as_map(
        map_get(issuer_signed_map, "nameSpaces", spec.source),
        "issuerSigned nameSpaces",
        spec.source,
    );
    let mut items = Vec::new();
    for (namespace, namespace_items) in item_namespaces {
        let namespace = as_text(namespace, "item namespace", spec.source);
        for item in as_array(namespace_items, "namespace items", spec.source) {
            items.push(load_item(spec, namespace, item));
        }
    }

    assert_eq!(
        version, "1.0",
        "{}: unexpected profile version",
        spec.source
    );
    assert_eq!(
        mso.len(),
        spec.mso_len,
        "{}: MSO length changed",
        spec.source
    );
    assert_eq!(
        namespaces
            .iter()
            .map(|namespace| (namespace.name.as_str(), namespace.digest_count))
            .collect::<Vec<_>>(),
        spec.namespaces,
        "{}: valueDigests namespace census changed",
        spec.source
    );
    assert_eq!(
        items
            .iter()
            .map(|item| (item.outer.len(), item.inner.len()))
            .collect::<Vec<_>>(),
        spec.item_lengths,
        "{}: IssuerSignedItem lengths changed",
        spec.source
    );
    assert!(
        items.iter().all(|item| {
            item.key_order
                .iter()
                .map(String::as_str)
                .eq(spec.item_key_order.iter().copied())
        }),
        "{}: IssuerSignedItem key order changed",
        spec.source
    );

    RealMdocVector {
        source: spec.source,
        version,
        mso,
        namespaces,
        items,
    }
}

fn load_item(spec: &FixtureSpec, namespace: &str, item: &Value) -> RealIssuerSignedItem {
    let outer = match item {
        Value::Tag(24, inner) if matches!(inner.as_ref(), Value::Bytes(_)) => encode_value(item),
        Value::Bytes(bytes) => bytes.clone(),
        _ => panic!(
            "{}: namespace {namespace} contains a non-IssuerSignedItemBytes value",
            spec.source
        ),
    };
    assert_subslice_once(spec.bytes, &outer, spec.source);

    let outer_value = decode_exact(&outer, "IssuerSignedItemBytes");
    assert_eq!(
        encode_value(&outer_value),
        outer,
        "{}: IssuerSignedItem wrapper is not canonical",
        spec.source
    );
    let inner = match outer_value {
        Value::Tag(24, inner) => as_bytes(&inner, "IssuerSignedItemBytes", spec.source).to_vec(),
        _ => panic!("{}: IssuerSignedItemBytes is not tag 24", spec.source),
    };
    assert!(
        outer.starts_with(&[0xd8, 0x18, 0x58])
            && outer.get(3).copied() == u8::try_from(inner.len()).ok()
            && outer.len() == inner.len() + 4,
        "{}: IssuerSignedItemBytes does not use the exact tag24/bstr8 wrapper",
        spec.source
    );

    let inner_value = decode_exact(&inner, "IssuerSignedItem");
    let inner_map = as_map(&inner_value, "IssuerSignedItem", spec.source);
    let key_order = inner_map
        .iter()
        .map(|(key, _)| as_text(key, "IssuerSignedItem key", spec.source).to_string())
        .collect();
    let digest_id = as_u32(
        map_get(inner_map, "digestID", spec.source),
        "IssuerSignedItem digestID",
        spec.source,
    );

    RealIssuerSignedItem {
        namespace: namespace.to_string(),
        outer,
        inner,
        digest_id,
        key_order,
    }
}

fn issuer_signed<'a>(root: &'a Value, source: &str) -> &'a Value {
    let root_map = as_map(root, "vector root", source);
    if map_get_opt(root_map, "issuerAuth").is_some() {
        return root;
    }
    let documents = as_array(
        map_get(root_map, "documents", source),
        "DeviceResponse documents",
        source,
    );
    let document = documents
        .first()
        .unwrap_or_else(|| panic!("{source}: DeviceResponse has no documents"));
    map_get(
        as_map(document, "DeviceResponse document", source),
        "issuerSigned",
        source,
    )
}

fn decode_exact(bytes: &[u8], context: &str) -> Value {
    let mut reader = Cursor::new(bytes);
    let value = ciborium::de::from_reader(&mut reader)
        .unwrap_or_else(|error| panic!("{context}: CBOR decode failed: {error}"));
    assert_eq!(
        reader.position() as usize,
        bytes.len(),
        "{context}: trailing CBOR bytes"
    );
    value
}

fn encode_value(value: &Value) -> Vec<u8> {
    let mut bytes = Vec::new();
    ciborium::ser::into_writer(value, &mut bytes).expect("Value serialization into Vec");
    bytes
}

fn map_get_opt<'a>(map: &'a [(Value, Value)], key: &str) -> Option<&'a Value> {
    map.iter().find_map(|(candidate, value)| {
        matches!(candidate, Value::Text(text) if text == key).then_some(value)
    })
}

fn map_get<'a>(map: &'a [(Value, Value)], key: &str, source: &str) -> &'a Value {
    map_get_opt(map, key).unwrap_or_else(|| panic!("{source}: missing map field {key}"))
}

fn as_map<'a>(value: &'a Value, context: &str, source: &str) -> &'a [(Value, Value)] {
    match value {
        Value::Map(entries) => entries,
        _ => panic!("{source}: {context} is not a map"),
    }
}

fn as_array<'a>(value: &'a Value, context: &str, source: &str) -> &'a [Value] {
    match value {
        Value::Array(items) => items,
        _ => panic!("{source}: {context} is not an array"),
    }
}

fn as_bytes<'a>(value: &'a Value, context: &str, source: &str) -> &'a [u8] {
    match value {
        Value::Bytes(bytes) => bytes,
        _ => panic!("{source}: {context} is not a byte string"),
    }
}

fn as_text<'a>(value: &'a Value, context: &str, source: &str) -> &'a str {
    match value {
        Value::Text(text) => text,
        _ => panic!("{source}: {context} is not text"),
    }
}

fn as_u32(value: &Value, context: &str, source: &str) -> u32 {
    let Value::Integer(value) = value else {
        panic!("{source}: {context} is not an integer");
    };
    u32::try_from(i128::from(*value))
        .unwrap_or_else(|_| panic!("{source}: {context} is outside u32"))
}

fn assert_subslice_once(haystack: &[u8], needle: &[u8], source: &str) {
    let count = haystack
        .windows(needle.len())
        .filter(|candidate| *candidate == needle)
        .count();
    assert_eq!(
        count, 1,
        "{source}: reconstructed IssuerSignedItem occurs {count} times in the fixed bytes"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loads_all_fixed_vector_shapes() {
        let vectors = real_mdoc_vectors();
        assert_eq!(vectors.len(), 3);
        assert_eq!(
            vectors
                .iter()
                .map(|vector| vector.source)
                .collect::<Vec<_>>(),
            [
                PID_PYMDOC_SOURCE,
                LONGFELLOW_MDL3_SOURCE,
                LONGFELLOW_EUAV11_SOURCE,
            ]
        );
        assert_eq!(
            vectors
                .iter()
                .map(|vector| vector.items.len())
                .collect::<Vec<_>>(),
            [6, 5, 1]
        );
    }

    #[test]
    fn keeps_exact_tag24_item_bytes() {
        for vector in real_mdoc_vectors() {
            for item in vector.items {
                let decoded = decode_exact(&item.outer, "returned IssuerSignedItemBytes");
                let Value::Tag(24, inner) = decoded else {
                    panic!("{}: returned item is not tag 24", vector.source);
                };
                assert_eq!(
                    as_bytes(&inner, "returned IssuerSignedItemBytes", vector.source),
                    item.inner
                );
                assert_eq!(item.outer.len(), item.inner.len() + 4);
                assert_eq!(item.key_order.len(), 4);
            }
        }
    }
}
