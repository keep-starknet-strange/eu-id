# EUID mdoc Credential Format v1

> **Frozen isolated profile contract.** This document mirrors
> `tasks/mdoc-credential-format-spec.md` sections 1-3. The implementation lives
> in `crates/eu-id-prover/src/mdoc.rs`. The profile is intentionally isolated
> from the current simplified identity full flow until mdoc integration is
> explicitly started.

## Purpose & Scope

The EUID mdoc profile v1 is the constrained ISO/IEC 18013-5-shaped credential
format accepted by the isolated mdoc proof path. It proves:

- issuer COSE_Sign1 ES256 signature over the Mobile Security Object,
- device-auth COSE_Sign1 ES256 signature over the requested session transcript,
- SHA-256 digests for disclosed issuer-signed items,
- age and nationality predicates bound to disclosed item bytes.

This profile does not add identity/FFI wiring, in-circuit CBOR parsing,
in-circuit text parsing, x5chain validation, revocation, SD-JWT support, or the
old 11-byte proof-of-concept credential path.

## Document Shape

The top-level document is a CBOR map with:

- `docType`
- `issuerSigned`
- `deviceSigned`

`issuerSigned` contains `nameSpaces` and `issuerAuth`. The only accepted PID
namespace is `eu.europa.ec.eudi.pid.1`, and it must equal the requested
namespace. Extra namespace items are allowed.

`deviceSigned.deviceAuth.deviceSignature` is a COSE_Sign1 whose payload must be
byte-equal to the request session transcript.

## IssuerSignedItemBytes

Each disclosed item is encoded as ISO-correct tag 24 over a byte string:

```text
#6.24(bstr .cbor IssuerSignedItem)
```

The SHA-256 digest is computed over the full received `IssuerSignedItemBytes`
encoding, including the tag-24 and bstr headers. The circuit witness keeps these
full bytes.

The `IssuerSignedItem` map uses the profile order:

```text
elementValue, digestID, random, elementIdentifier
```

`random` is a byte string of at least 16 bytes. `digestID` must fit in `u32`.

The circuit-admissible values are:

- `birth_date`: byte string exactly `[year_hi, year_lo, month, day]`
- `nationality`: byte string exactly ISO-3166-1 numeric big-endian bytes

Text values remain accepted for host-side display/review extraction, but
`MdocCircuitStatement::from_extracted` rejects them because the predicate bytes
cannot be proven equal to the received CBOR value bytes.

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

The issuer key is carried in `issuerAuth.unprotected["issuerKey"]`; the device
key is carried in `MobileSecurityObject.deviceKeyInfo.deviceKey`. Both are
strict ES256 P-256 COSE keys with `1:2`, `3:-7`, `-1:1`, `-2:x`, and `-3:y`.

## Mobile Security Object

The issuerAuth payload is a CBOR Mobile Security Object with:

- `version`: exactly `"1.0"`
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

The isolated statement builder checks `validFrom <= policy.current_date <=
validUntil` using date-only comparison. `signed` is parsed and stored for
review but is not policy-checked.

## Statement Invariants

`MdocCircuitStatement::from_extracted` is the circuit-admissibility gate. It
rejects extracted data unless:

- the extracted birth-date bytes equal the received item bytes at the recorded
  offset,
- the extracted nationality bytes equal the received item bytes at the recorded
  offset,
- both value windows end in the first SHA-256 block,
- the credential validity window includes the policy date,
- the disclosed item digest IDs resolve to MSO digests.
