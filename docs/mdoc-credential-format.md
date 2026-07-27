# EUID mdoc Credential Format (v1 + v2)

> **Product mdoc proof contract.** The implementation lives in
> `crates/eu-id-prover/src/mdoc.rs` and is exported through
> `eu_id_prover::{prove_mdoc, verify_mdoc}`. The older 11-byte credential proof
> remains separate as the POC benchmark path. The current SDK
> `proveIdentity`/`verifyIdentity` FFI contract is explicitly non-revocation:
> it rejects a proof carrying any TS13 revocation inputs because its public
> statement does not yet expose the authority key and epoch.

## Purpose & Scope

The EUID mdoc profile is the constrained ISO/IEC 18013-5-shaped credential
format accepted by the product mdoc proof path. Profile v1 (packed `bstr`
values, `"1.0"`) and profile v2 (canonical CBOR, text values, `"2.0"`) are both
accepted; v2 is what real wallets emit. It proves:

- issuer COSE_Sign1 ES256 signature over the Mobile Security Object,
- device-auth COSE_Sign1 ES256 signature over the requested
  `DeviceAuthenticationBytes`,
- SHA-256 digests for disclosed issuer-signed items,
- age and nationality predicates bound to disclosed item bytes.

The circuit parses the exact profile CBOR streams and proves their semantic
scope, including the selected item identifiers, digest membership, validity
fields, and device key. It does not perform x509 chain validation or support
SD-JWT / `zk-jwt`; those requests are rejected fail-closed at the TS13 entry
point. x5chain validation is host-side against verifier-supplied trusted roots.

TS13 sorted-pair non-revocation is supported end-to-end for the MSO-derived
identifier `id = LE64(SHA-256(MSO bytes)[0..8])`: the strict
`id_lo < id < id_hi` range check, the id-to-MSO-SHA digest binding, the
MSO-SHA-preimage-to-issuerAuth-payload linkage, and the revocation-authority
P-256 sorted-pair signature over `SHA-256(LE64(id_lo) || LE64(id_hi) ||
LE32(epoch))` are all part of the mdoc proof when the TS13 revocation layout is
enabled. Under the default `ec-coprocessor` feature the signature check rides
the P4b coprocessor bundle as a third ECDSA instance set. Its message hash and
signature remain private: fixed MAC relations join the hidden coprocessor
instance to the in-STARK revocation-SHA digest, while the verifier supplies and
checks the public revocation key. The non-coprocessor build keeps the
in-STARK P-256 AIR instance. The public statement carries only the revocation
public key, epoch, and a range-layout flag; `id`, `id_lo`, `id_hi`, the
revocation message hash, and the signature stay witness.

This optional relation is currently available through the lower-level
`mdoc::prove_mdoc_circuit` path after augmenting the circuit statement with
`with_ts13_revocation*`, plus the corresponding circuit/public verifier. The
top-level `eu_id_prover::prove_mdoc` and SDK FFI do not yet construct those
inputs; `verifyIdentity` rejects them fail-closed until `ZkPublicStatement`
and `ZkMdocWitness` carry the complete verifier and prover revocation inputs.
The published TS13 circuit hash and preprocessed root pin the default
`ec-coprocessor` composition only. A no-default build is not a published TS13
profile and canonical artifact verification there fails closed.

Zero-knowledge privacy masking is implemented in the product mdoc proof path
(P4c Classes A–E: perfectly masked blind-row cells, MAC/SHA decoys, 1-active-row
predicate layouts, Class-D reserved-dummy-key range/SHA tables, and committed
per-proof cyclic masks for every private LogUp claimed sum). The mask columns
are committed before a fresh transcript challenge is drawn; their target sums
cancel globally and are never serialized as proof metadata. The
classification, simulator sketch, and executable guards are in
`tasks/p4c-leakage-table.md`.
This document states what is implemented; it does not itself assert external
TS13 compatibility — that claim gates on the release signoff recorded in
`tasks/audits/2026-07-07-ts13-evidence.md`.

The old 11-byte proof-of-concept credential path is intentionally separate and
keeps its nonce module for parity benchmarks.

## Document Shape

The top-level document is a CBOR map with:

- `docType`
- `issuerSigned`
- `deviceSigned`

`issuerSigned` contains `nameSpaces` and `issuerAuth`. The only accepted PID
namespace is `eu.europa.ec.eudi.pid.1`, and it must equal the requested
namespace. Extra namespace items are allowed.

`deviceSigned.deviceAuth.deviceSignature` is a COSE_Sign1 over
`DeviceAuthenticationBytes = #6.24(bstr .cbor DeviceAuthentication)`, where
`DeviceAuthentication = ["DeviceAuthentication", SessionTranscript, docType,
DeviceNameSpacesBytes]`. The verifier recomputes that payload from its own
session transcript and docType.

## IssuerSignedItemBytes

Each disclosed item is encoded as ISO-correct tag 24 over a byte string:

```text
#6.24(bstr .cbor IssuerSignedItem)
```

The SHA-256 digest is computed over the full received `IssuerSignedItemBytes`
encoding, including the tag-24 and bstr headers. The circuit witness keeps these
full bytes.

Profile v1 accepts the legacy `IssuerSignedItem` key order:

```text
elementValue, digestID, random, elementIdentifier
```

Profile v2 emits and requires the RFC 8949 core-deterministic (canonical) order:

```text
random, digestID, elementValue, elementIdentifier
```

Both profiles require the exact four-key set; only v2 rejects non-canonical
ordering.
`random` is a byte string of at least 16 bytes. `digestID` must fit in `u32`.

The item-map ordering profile and the element-value encoding are independent.
The circuit-admissible values are:

- `birth_date`: either a packed `bstr` `[year_hi, year_lo, month, day]` or a
  `tstr` `YYYY-MM-DD`. The exposed window is 4 or 10 bytes respectively
  and is bound to the age predicate.
- `nationality`: either a `bstr` of ISO-3166-1 numeric big-endian bytes or a
  `tstr` ISO 3166-1 alpha-2 code. The nationality predicate runs in the
  matching (numeric or alpha-2) code space.

A window straddling a 64-byte SHA-256 block boundary is admitted (Phase A
multi-block field exposure); the host only checks byte-equality at the
prover-supplied offset.

## COSE_Sign1

Both issuer and device signatures use:

```text
[protected bstr, unprotected map, payload bstr, signature bstr]
```

The protected header must be exactly `a1 01 26`, the CBOR encoding of
`{1: -7}` for ES256. The signature is exactly 64 compact bytes `r || s`.

The signed structure is:

```text
cbor(["Signature1", protected, b"", payload])
```

The issuer key is either carried directly in
`issuerAuth.unprotected["issuerKey"]` or extracted host-side from
`issuerAuth.unprotected[33]` (`x5chain`) after the chain verifies to a
verifier-supplied trusted root. The device key is carried in
`MobileSecurityObject.deviceKeyInfo.deviceKey`. Both keys are strict ES256
P-256 COSE keys with `1:2`, `-1:1`, `-2:x`, and `-3:y`; `3:-7` is accepted
when present.

## Mobile Security Object

The issuerAuth payload is a CBOR Mobile Security Object with:

- `version`: `"1.0"` (v1) or `"2.0"` (v2); any other value is rejected
- `docType`: equal to the requested document type
- `digestAlgorithm`: exactly `"SHA-256"`
- `valueDigests`
- `deviceKeyInfo.deviceKey`
- `validityInfo.signed`
- `validityInfo.validFrom`
- `validityInfo.validUntil`

Each validity value is CBOR tag 0 over an exact 20-character UTC timestamp:

```text
YYYY-MM-DDTHH:MM:SSZ
```

The statement builder checks `validFrom <= policy.current_date <= validUntil`
using date-only comparison. `signed` is parsed and stored for review but is not
policy-checked.

## Statement Invariants

`MdocCircuitStatement::from_extracted` is the circuit-admissibility gate. It
rejects extracted data unless:

- the extracted birth-date bytes equal the received item bytes at the recorded
  offset,
- the extracted nationality bytes equal the received item bytes at the recorded
  offset,
- the credential validity window includes the policy date,
- the disclosed item digest IDs resolve to MSO digests, and each digest / the
  validity date / device-key coordinate is locatable as a contiguous window in
  the issuer `Sig_structure` preimage.

## In-circuit semantic bindings (Phase D)

The item digests and device key are **not** public inputs. `MdocCborStream`
proves the exact accepted CBOR grammar and `MdocScope` follows the parsed
structure rather than trusting prover-supplied byte offsets:

- **D1 — element identifier:** the requested `elementIdentifier` is parsed at
  the correct `IssuerSignedItem` map key and pinned byte-for-byte to the public
  request.
- **D2 — digest membership:** the parsed `digestID` selects the matching
  `valueDigests[namespace][digestID]` entry in the MSO, whose 32 bytes equal the
  selected item's SHA-256 digest.
- **D3 — device-key origin:** the parsed MSO `deviceKey` coordinates equal the
  device signature's public key `(qx, qy)` proven by the EC path.
- **Validity:** the parsed `validFrom` and `validUntil` dates are consumed by
  the validity AIR and compared with the public policy date.
- **Revocation:** when enabled, the normalized MSO payload is bound as the
  exact SHA-256 preimage used to derive the private revocation identifier.

Consequently the public statement carries the issuer key or trusted-root
anchored issuer key, policy, session transcript, requested semantic scope, and
the two public-path `(r, s)` signatures. Everything else is witness, including
item digests, MSO bytes, disclosed item bytes, parsed dates, and the device
key.
