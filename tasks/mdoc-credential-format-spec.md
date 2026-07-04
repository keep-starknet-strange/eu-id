# EUID mdoc Credential Format v1 — Implementation Spec

Scope for promoting the isolated mdoc support (`crates/eu-id-prover/src/mdoc.rs`)
from "parses whatever the fixture emits" to a **frozen, enforced credential
profile**. Self-contained: implement from this document alone.

**In scope:** the normative profile below, early enforcement of every circuit
prerequisite in `MdocCircuitStatement::from_extracted`, MSO realism
(version / docType / validityInfo), ISO-correct tag-24 item wrapping, fixtures,
tests, and the prose contract doc.

**Out of scope (do NOT touch):** wiring mdoc into `prove_identity` /
`verify_identity` / FFI; in-circuit CBOR parsing; text→packed date transcoding
in-circuit; x5chain issuer keys; in-circuit validity checks; revocation;
hiding `r`/`s` or the item digests (they are public in v1 — known privacy
caveat, separate work); SD-JWT; the 11-byte POC path (leave untouched).

---

## 1. Normative profile ("EUID mdoc profile v1")

A constrained subset of ISO/IEC 18013-5. A document outside this profile MUST
be rejected host-side with the exact error named in §3 — never by a LogUp
imbalance at prove time.

All hashing/signing is over **received bytes**. Nothing is ever re-serialized;
byte offsets refer to positions inside received encodings. There is therefore
no canonical-CBOR requirement beyond the explicit ordering rules below.

### 1.1 Document (CBOR map, top level)

```
{
  "docType":      tstr = "eu.europa.ec.eudi.pid.1",   ; must equal request.doctype
  "issuerSigned": {
    "nameSpaces": { NAMESPACE: [ IssuerSignedItemBytes, ... ] },
    "issuerAuth": COSE_Sign1                           ; §1.4, payload = MSO bytes
  },
  "deviceSigned": {
    "deviceAuth": { "deviceSignature": COSE_Sign1 }    ; §1.4, payload = session transcript
  }
}
```

- `NAMESPACE` = `"eu.europa.ec.eudi.pid.1"` (must equal `request.namespace`).
- The namespace array MUST contain items with `elementIdentifier`
  `"birth_date"` and `"nationality"`. Extra items are allowed and ignored.
- Device auth payload MUST byte-equal `request.session_transcript`
  (profile deviation from ISO's detached-payload `DeviceAuthentication`; kept).

### 1.2 IssuerSignedItemBytes

ISO-correct tag-24-over-bstr (this is a **change** from the current code,
which uses `Tag(24, Map)` — see §4 item 1):

```
IssuerSignedItemBytes = #6.24( bstr .cbor IssuerSignedItem )

IssuerSignedItem = {              ; keys in EXACTLY this order:
  "elementValue":      <value>,   ; FIRST — see block-0 rule below
  "digestID":          uint,      ; must fit u32
  "random":            bstr,      ; len >= 16
  "elementIdentifier": tstr,
}
```

- **Key order is normative.** The circuit's SHA field-exposure only reaches
  the first 64-byte SHA block of a preimage
  (`crates/stwo-sha256/src/field_exposure.rs` asserts `offset < 64`).
  `elementValue` first keeps the value window inside block 0. This deviates
  from ISO canonical map ordering; documented, revisit with multi-block
  exposure.
- `SHA-256(IssuerSignedItemBytes)` (the full received encoding, tag and bstr
  header included) MUST equal `MSO.valueDigests[NAMESPACE][digestID]`.

### 1.3 Circuit-provable element values

The in-circuit binding recomposes raw bytes big-endian (no digit arithmetic),
so the provable encodings are:

| element       | required `elementValue`      | packed meaning                          |
|---------------|------------------------------|-----------------------------------------|
| `birth_date`  | `bstr` of exactly 4 bytes    | `year_hi, year_lo, month, day`          |
| `nationality` | `bstr` of exactly 2 bytes    | ISO-3166-1 numeric, big-endian          |

`tstr` forms (full-date `"YYYY-MM-DD"`, alpha-2 `"DE"`) remain accepted by
`extract_pid_mdoc` for host-side display/review, but MUST be rejected by
`MdocCircuitStatement::from_extracted` (§2.2) — their bytes at the value
offset do not recompose to the packed attribute.

### 1.4 COSE_Sign1 (both issuer and device)

```
[ protected: bstr, unprotected: map, payload: bstr, signature: bstr ]
```

- `protected` MUST be exactly the bytes `a1 01 26` (the encoded map `{1: -7}`,
  ES256). Reject anything else.
- `signature` MUST be 64 bytes, compact `r ‖ s`, each 32 bytes big-endian.
- Signed bytes: `Sig_structure = cbor(["Signature1", protected, b"", payload])`
  (empty `external_aad`).
- Issuer key transport: `unprotected["issuerKey"]` as a COSE_Key
  (`{1:2, 3:-7, -1:1, -2: x bstr(32), -3: y bstr(32)}`) — profile deviation
  from ISO x5chain; kept for v1.
- Curve/hash: P-256 + SHA-256 only.

### 1.5 MobileSecurityObject (issuerAuth payload)

Extend the currently-parsed shape with the three starred fields (all REQUIRED):

```
MSO = {
  "version":         tstr = "1.0",                       ; * must equal
  "docType":         tstr,                               ; * must equal request.doctype
  "digestAlgorithm": tstr = "SHA-256",
  "valueDigests":    { NAMESPACE: { uint => bstr(32) } },
  "deviceKeyInfo":   { "deviceKey": COSE_Key },
  "validityInfo": {                                      ; *
    "signed":     tdate,
    "validFrom":  tdate,
    "validUntil": tdate,
  },
}
```

- `tdate` = `#6.0( tstr "YYYY-MM-DDTHH:MM:SSZ" )` — CBOR Tag 0 over exactly
  that 20-char form. Parse with manual digit parsing (like
  `parse_birth_date_text`); no new dependencies, no timezone offsets, no
  fractional seconds. Reject anything else.
- Validity semantics (checked in `from_extracted`, §2.2): compare **date parts
  only**, inclusive on both ends:
  `validFrom.date <= policy.current_date <= validUntil.date`.
  `signed` is parsed and stored but not policy-checked in v1.

---

## 2. Circuit statement contract

### 2.1 Public vs witness (unchanged mechanics, restated so nobody "fixes" it)

| datum | visibility |
|---|---|
| issuer key `Q`, issuer `(r, s)` | public (`MdocCircuitStatement.issuer_input`) |
| device key, device `(r, s)` | public (`device_input`) |
| `z_issuer`, `z_device` | NOT public — proven `= SHA-256(sig_structure)` via digest-bind bridges |
| `birth_date_digest`, `nationality_digest` (salted item digests) | public — v1 caveat |
| value offsets, policy | public |
| item bytes, MSO bytes, sig_structure bytes, DOB, nationality | witness |

### 2.2 Invariants `MdocCircuitStatement::from_extracted` MUST enforce

Each with the exact error from §3; all currently missing unless noted:

1. `birth_date_item[offset .. offset+4] == birth_date_bytes` and
   `nationality_item[offset .. offset+2] == nationality_bytes`
   (kills tstr-form values and any offset drift in one check).
2. `offset + window_len <= 64` for both windows (block-0 exposure rule).
3. Validity window vs `policy.current_date` (§1.5).
4. Digest lookups (already present — keep).

`prove_mdoc_circuit`'s existing statement/extracted cross-checks stay as-is.

---

## 3. Error variants

Extend `MdocError` (exhaustive list of new variants; reuse existing ones where
named):

| condition | error |
|---|---|
| MSO missing version/docType/validityInfo | `MissingField("...")` (existing variant) |
| MSO `version != "1.0"` | `UnsupportedMsoVersion(String)` (new) |
| MSO `docType` mismatch | `DoctypeMismatch` (existing) |
| tdate malformed / not Tag 0 / bad form | `InvalidTdate(&'static str)` (new) |
| `current_date < validFrom` | `CredentialNotYetValid` (new) |
| `current_date > validUntil` | `CredentialExpired` (new) |
| salt `len < 16` | `SaltTooShort { len: usize }` (new) |
| protected header ≠ `a1 01 26` | `InvalidCoseSign1("protected header must be ES256")` (existing variant) |
| tag 24 content not bstr | `WrongType("IssuerSignedItemBytes")` (existing variant) |
| §2.2 window-bytes mismatch | `UnsupportedCircuitValue("element value bytes at offset")` (existing variant) |
| §2.2 window past block 0 | `UnsupportedCircuitValue("value window must lie in first SHA-256 block")` |
| digestID > u32::MAX | `WrongType("digestID")` (existing variant) |

---

## 4. Work items (in order)

All in `crates/eu-id-prover` unless stated.

1. **`src/mdoc.rs` — tag-24 wrapping.** Change item decode (the
   `Value::Tag(24, inner)` match, ~line 464) to require
   `Tag(24, Bytes(inner_bytes))` and decode `IssuerSignedItem` from
   `inner_bytes`. `ParsedItem.bytes` stays the FULL received
   `IssuerSignedItemBytes` encoding (digests and offsets are over it).
2. **`src/mdoc.rs` — COSE strictness.** Enforce protected == `a1 01 26` and
   64-byte compact signature in `parse_cose_sign1`.
3. **`src/mdoc.rs` — MSO fields.** Extend `parse_mso` / `ParsedMso` with
   `version`, `docType`, `validityInfo` per §1.5 (manual tdate parser).
   Store parsed validity dates on `ExtractedPidMdoc`
   (`valid_from: (u16,u8,u8)`, `valid_until: (u16,u8,u8)`,
   `signed_at: (u16,u8,u8)`). Check `docType`/`version` in
   `extract_pid_mdoc`; salt length check in item parsing.
4. **`src/mdoc.rs` — `from_extracted` invariants** per §2.2.
5. **`tests/mdoc_support.rs` — fixture generator.** Update in place (do not
   move it): tag-24-bstr wrapping, MSO version/docType/validityInfo
   (default window: signed/validFrom `2026-01-01T00:00:00Z`, validUntil
   `2030-01-01T00:00:00Z`), keep key order `elementValue` first. Add knobs to
   `fixture_with_values` (or small wrapper fns) for: validity override, salt
   override, key-order flip (value last), protected-header override.
6. **Tests** — §5.
7. **Docs.** New `docs/mdoc-credential-format.md` = §1–§3 of this spec as the
   frozen contract (mirror the style of `docs/credential-format.md`). Add one
   pointer line to `docs/credential-format.md` ("superseded for the mdoc path
   by …"). Update the module doc of `src/mdoc.rs` to name the profile.

## 5. Acceptance tests

Fast (default `cargo test -p eu-id-prover --test mdoc_support`), all against
the fixture generator; existing 4 tests keep passing (updated fixtures):

- `extracts_pid_items_mso_device_key_and_signatures` — extend asserts:
  validity dates extracted.
- Existing rejects: digest mismatch, wrong transcript, wrong doctype.
- New host rejects (one test each, assert the exact §3 error):
  `rejects_non_bstr_tag24`, `rejects_bad_protected_header`,
  `rejects_short_salt`, `rejects_missing_validity_info`,
  `rejects_malformed_tdate`, `rejects_mso_doctype_mismatch`,
  `rejects_mso_version_mismatch`.
- New `from_extracted` rejects: `statement_rejects_expired_credential`,
  `statement_rejects_not_yet_valid_credential`,
  `statement_rejects_text_birth_date` (tstr fixture),
  `statement_rejects_text_nationality`,
  `statement_rejects_value_window_past_first_block` (key-order-flipped
  fixture).

Slow (`#[ignore]`, release):

- `isolated_mdoc_circuit_profile_proves_and_verifies` — keeps passing with the
  v1-profile fixture (this is the gate that the format changes didn't break
  the circuit path).

Commands (run all before done):

```
rtk proxy cargo test -p eu-id-prover --test mdoc_support
rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies --release -- --ignored
rtk cargo clippy -p eu-id-prover
rtk proxy cargo fmt --check
```

## 6. Freeze rule

After this lands, §1–§3 are the frozen v1 contract (same status as the POC
credential layout): consumers key off the key order, the block-0 window rule,
and the packed value encodings. Any change bumps the profile version and MSO
`version` handling — never silently.
