# Quantum-safe TS13 public-input-unlinkable age-over-18 demo profile

Status: implemented demo protocol.

This document specifies the canonical TS13 identity proof.
It specifies the application `proveIdentity` and `verifyIdentity` boundary.
It also specifies the opaque TS13 `ZkDocument.proof` bytes.
It does not specify wallet or application integration.

The specification uses these pinned sources:

- [EUDI ARF Technical Specification 13 at commit
  `230cd75d9`](https://github.com/eu-digital-identity-wallet/eudi-doc-architecture-and-reference-framework/blob/230cd75d9c243e6b4c7b35f3f2bf73f9dff20cdc/docs/technical-specifications/ts13-zksnarks.md).
- [`feat/quantum-safe` at commit
  `20f9d7a8`](https://github.com/keep-starknet-strange/eu-id/commit/20f9d7a86bac57286ff9ea4a328956f25f5d1ac8).

The words **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are normative.
Code comments are not evidence of conformance.
Executable constraints and adversarial tests are evidence of conformance.
Transcript construction and serialization are also evidence of conformance.

## Terminology

- **AAD**: additional authenticated data.
- **AIR**: algebraic intermediate representation.
- **AKP**: asymmetric key pair, the COSE key type used for ML-DSA.
- **CBOR**: Concise Binary Object Representation.
- **COSE**: CBOR Object Signing and Encryption.
- **DCQL**: Digital Credentials Query Language.
- **FRI**: Fast Reed-Solomon Interactive Oracle Proof of Proximity.
- **GKR**: Goldwasser-Kalai-Rothblum protocol.
- **ML-DSA**: Module-Lattice-Based Digital Signature Algorithm.
- **MSO**: MobileSecurityObject.
- **NDEF**: NFC Data Exchange Format.
- **NFC**: near-field communication.
- **PCS**: polynomial commitment scheme.
- **PID**: person identification data.
- **PKI**: public key infrastructure.
- **RP**: relying party.
- **STARK**: scalable transparent argument of knowledge.
- **UTC**: Coordinated Universal Time.

## 1. Objective

The circuit proves these facts together:

- A trusted issuer issued the PID.
- The PID contains `age_over_18 = true`.
- The PID is valid at the specified second.
- The holder authenticated the presentation with the bound device key.
- The PID is not revoked in the specified epoch.

The application calls:

```kotlin
val proof: ByteArray = proveIdentity(statement, witness)
```

The returned bytes are the opaque `ZkDocument.proof` value.
The EUDI presentation layer constructs the surrounding `ZkDocument`.

This profile is for a demonstration.
It supports one claim and one credential shape.
It uses post-quantum authentication for all signatures.
It uses the STARK parameters in the source-bound circuit artifact.
It makes no claim of 128-bit post-quantum security.

## 2. Privacy claim and limitation

This profile provides public-input unlinkability:

- Credentials from one issuer use one credential-independent public theorem.
- The verifier uses a fresh request context for each presentation.
- All statement fields remain public.
- A credential-stable value cannot select the circuit.
- A credential-stable value cannot select the trace layout.
- A credential-stable value cannot change the identity-proof envelope length.
- A credential-stable value cannot change the public preprocessing root.

STWO is transparent and is not zero knowledge.
STWO can expose witness-derived data in the proof transcript.
This profile does not claim transcript unlinkability.

Use this exact description:

```text
public-input unlinkable; transcript zero knowledge pending
```

Documentation MUST NOT claim complete unlinkability or zero knowledge for this
profile.

## 3. Fixed profile

The profile identifier is:

```text
ts13-pid-age-over-18-unlinkable-demo-v1
```

The `ZkSystemSpec.system` value is:

```text
stwo-euid-ts13-demo-v1
```

The profile has these fixed parameters:

| Parameter | Value |
| --- | --- |
| credential format | `mso_mdoc_zk` |
| document type | `eu.europa.ec.eudi.pid.1` |
| namespace | `eu.europa.ec.eudi.pid.1` |
| requested element | `age_over_18` |
| comparison | equality |
| public result | CBOR `true` (`0xf5`) |
| issuer authentication | FIPS 204 ML-DSA-65 |
| device authentication | FIPS 204 ML-DSA-44 |
| device COSE algorithm | `-48` |
| device protected header | `h'a101382f'` |
| device public key | 1,312 bytes |
| device signature | 2,420 bytes |
| revocation authentication | FIPS 204 ML-DSA-65 |
| digest algorithm | SHA-256 |
| device authentication profile | ISO 18013-5 `DeviceAuthentication` |
| trusted issuer keys per proof | one |
| disclosed attributes | one |
| revocation | mandatory |
| timestamp precision | one UTC Unix second |

The issuer signature authenticates an MSO that commits to the
`age_over_18 = true` item.
The circuit does not calculate age from a birth date.
The implementation MUST NOT substitute a birth-date predicate.

The profile MUST reject these inputs:

- an additional requested claim;
- another namespace;
- another document type;
- an extension claim;
- optional revocation;
- another algorithm;
- another credential shape.

### 3.1 Credential shape

The profile has these fixed shape values:

| Value | Size |
| --- | ---: |
| issuer COSE `Sig_structure` | 1,894 bytes |
| MSO payload | 1,873 bytes |
| padded `IssuerSignedItemBytes` | 128 bytes |
| device COSE `Sig_structure` capacity | 1,024 bytes |
| digest-identifier CBOR integer encoding | 1, 2, or 3 bytes |

Each `digestID` MUST use a canonical CBOR unsigned-integer encoding.
The complete encoding MUST use 1, 2, or 3 bytes.
The implementation MUST reject a 5-byte encoding.
The shape-manifest value `credentialShape.digestIdentifierIntegerWidths` MUST
be `[1, 2, 3]`.

The shape manifest contains the numeric constants that select the circuit
shape.
The circuit artifact commits to the shape manifest.
Each demo credential MUST match the manifest.

These values are also fixed profile constants:

- CBOR integer-width classes for digest identifiers;
- trace log sizes;
- row counts;
- stream identifiers;
- relation counts;
- the maximum Keccak schedule.

The trace always allocates the full device-message capacity.
The verifier supplies the active device-message length.
The AIR constrains the SHAKE padding position from that length.
The AIR constrains all inactive bytes to their canonical values.
The AIR constrains all unused permutation rows to their canonical values.

The active length is public request context.
It MUST NOT change the trace geometry.
It MUST NOT change the tree-zero root.
It MUST NOT change the circuit hash.
It MUST NOT change the identity-proof envelope length.

`proveIdentity` MUST return `InvalidPublicContext` for a larger device message.
A different capacity requires a different circuit hash.

Two unlinkability fixtures MUST have different credential data.
The different data MUST include:

- MSO bytes;
- device public keys;
- item randomizers;
- digest identifiers;
- issuer signatures;
- device signatures;
- revocation signatures;
- revocation identifiers.

The fixtures SHOULD also use different signed gap witnesses.

`proveIdentity` MUST return `UnsupportedCredentialShape` for another shape.
It MUST NOT select a different length bucket.
It MUST reject values that do not match the required profile strings.

## 4. Threat model

The construction protects against these actions:

- A holder proves a false claim.
- A prover uses a consistent but unauthenticated witness.
- A verifier relabels a proof for another relying party.
- A verifier relabels a proof for another session or timestamp.
- A verifier relabels a proof for another trust policy.
- A verifier relabels a proof for another revocation epoch.
- Relying parties compare clear public surfaces.

The clear public surfaces include:

- semantic statements;
- circuit choices;
- public preprocessing roots;
- envelope headers;
- envelope lengths.

The transcript limitation in Section 2 applies to the STARK body.

The construction uses these assumptions:

- The verifier policy supplies the issuer public key.
- The verifier policy supplies the revocation public key.
- Proof bytes do not supply a trusted key.
- The issuer emits the fixed canonical CBOR shape.
- The verifier supplies or validates a fresh timestamp.
- The SessionTranscript contains a fresh verifier challenge.
- The relying party enforces its replay policy.
- ML-DSA-44 and ML-DSA-65 are secure.
- SHA-256 is collision-resistant.
- The STARK is sound.

The circuit selects each ML-DSA profile.
The witness cannot select a profile.
The issuer and revocation instances use ML-DSA-65.
The device instance uses ML-DSA-44.

The ML-DSA-44 SampleInBall cap can reject an honest signature with negligible
probability.
Section 8.3 specifies this completeness limit.

The issuer key partitions the anonymity set.
The profile and claim also partition the anonymity set.
The revocation epoch also partitions the anonymity set.
The privacy claim applies only inside one partition.

## 5. Public and private data

### 5.1 Public inputs

The verifier policy supplies these semantic public values:

| Public value | Purpose |
| --- | --- |
| actual circuit hash | select the circuit |
| RP-local `zkSystemId` | bind the request |
| document type | select the credential type |
| namespace | select the claim scope |
| element identifier | select the claim |
| expected CBOR value `true` | define the disclosed result |
| canonical SessionTranscript bytes | bind the presentation |
| exact verification Unix second | check validity |
| trusted issuer ML-DSA-65 public key | define issuer trust |
| revocation ML-DSA-65 public key | define revocation trust |
| revocation epoch | define freshness and partition |

The verifier MUST treat these keys as authoritative.
The verifier MUST NOT trust a key from the proof envelope.

The circuit derives only these additional public values:

- `SHA-256(canonicalSessionTranscript)`;
- the canonical device COSE `Sig_structure`;
- the device COSE `Sig_structure` length;
- `SHA-256(deviceCoseSigStructure)`;
- the canonical UTC RFC 3339 verification time;
- the request-context digest from Section 6.

The prover and verifier derive these values from the semantic statement.
The caller cannot supply an independent derived value.

The identity-proof envelope header contains only these values:

- the fixed magic;
- the envelope version;
- the circuit hash;
- the fixed proof-body capacity.

These universal circuit values are public:

- profile strings;
- the shape manifest;
- trace geometry;
- cryptographic parameters;
- the device-message capacity.

### 5.2 Witness-only values

These values are witness-only:

| Witness value | Proof use |
| --- | --- |
| issuer COSE `Sig_structure` | authenticate the issuer message |
| MSO payload | authenticate and parse the credential |
| issuer signature | authenticate the issuer |
| MSO `validFrom` and `validUntil` | check exact validity |
| MSO device key | bind the device key |
| device key `rho`, `t1`, and `tr` | verify ML-DSA |
| device signature | authenticate the holder |
| selected `IssuerSignedItemBytes` | prove the claim |
| item randomizer | calculate the item digest |
| digest identifier and its CBOR width | select `valueDigests` |
| private offsets, parser state, and active lengths | parse private CBOR |
| MSO digest | derive the revocation identifier |
| revocation identifier | prove non-revocation |
| revocation interval and signature | prove non-revocation |

These values MUST be absent as clear fields from:

- the semantic statement;
- the envelope header;
- public preprocessing;
- the verifier API.

Credential and certificate serial numbers MUST NOT be explicit statement
fields, circuit selectors, or preprocessing inputs.
If the credential contains a serial number, that number is unselected witness
data.

STWO can expose information derived from these values in the proof transcript.
This profile does not guarantee proof-body confidentiality.

The device COSE `Sig_structure` can remain public.
It is request data and is not credential-stable.
Its active length can also remain public.
Universal shape constants can remain public.

### 5.3 Exact public statement

The native verifier input has this conceptual form:

```rust
pub struct IdentityStatement {
    pub circuit_hash: Vec<u8>,
    pub zk_system_id: String,
    pub document_type: String,
    pub namespace: String,
    pub element_identifier: String,
    pub expected_value_cbor: Vec<u8>,
    pub timestamp_epoch_seconds: i64,
    pub session_transcript: Vec<u8>,
    pub trusted_issuer_public_key: Vec<u8>,
    pub revocation_public_key: Vec<u8>,
    pub revocation_epoch: u32,
}
```

The circuit hash MUST contain 32 bytes.
The trusted issuer public key MUST contain 1,952 bytes.
The revocation public key MUST contain 1,952 bytes.

The implementation MUST use the exact profile and proof-system strings in
Section 3. It MUST compare each caller-supplied document type, namespace, and
element identifier with its exact required string.
The verifier MUST validate all caller-supplied values.

The verifier controls `timestamp_epoch_seconds`.
The proof and witness cannot change this value.
The application MUST apply its clock policy before it creates the statement.
The timestamp MUST be in this inclusive range:
`2020-01-01T00:00:00Z` through `2099-12-31T23:59:59Z`.

The statement has none of these fields:

- `current_date_epoch_day`;
- a trusted-key list;
- a resource-cap field;
- a credential length;
- a digest identifier;
- a device key;
- a prover-supplied request-binding hash.

This specification keeps four separate public allowlists:

1. semantic statement fields;
2. derived circuit values;
3. identity-proof envelope header fields;
4. universal circuit constants.

Schema tests MUST destructure all typed fields without `..`.
Artifact drift tests MUST cover universal constants.
The union of the four allowlists defines the complete clear public surface.
A privacy review MUST approve each new field.

## 6. Presentation context

### 6.1 Canonical context

The prover and verifier independently encode this CBOR array:

```text
[
  "EUDI-TS13-DEMO-CONTEXT-V1",
  "stwo-euid-ts13-demo-v1",
  zkSystemId,
  circuitHashBytes,
  "eu.europa.ec.eudi.pid.1",
  "eu.europa.ec.eudi.pid.1",
  "age_over_18",
  h'f5',
  timestampEpochSeconds,
  SHA-256(canonicalSessionTranscriptBytes),
  SHA-256(deviceCoseSigStructureBytes),
  SHA-256(trustedIssuerPublicKey),
  SHA-256(revocationPublicKey),
  revocationEpoch
]
```

The encoder MUST use deterministic CBOR from RFC 8949.
It MUST use definite lengths.
It MUST use the shortest integer encodings.
It MUST use the UTF-8 strings shown above.
It MUST encode each digest as a 32-byte byte string.
It MUST encode `circuitHashBytes` as a 32-byte byte string.
It MUST encode `h'f5'` as a one-byte byte string.
It MUST NOT encode `h'f5'` as a Boolean.
It MUST use signed Unix time in whole seconds.
It MUST NOT add trailing bytes.

The request-context digest is:

```text
SHA-256(canonicalContextCbor)
```

### 6.2 STARK transcript binding

`Ts13PublicContextBind` has zero trace columns.
It MUST call `mix_u64` once for each byte in this order:

1. ASCII `EUDI-TS13-PUBLIC-CONTEXT-V1`;
2. the 32 request-context digest bytes;
3. the 32 circuit-hash bytes.

The prover and verifier MUST use the same mixing operation.
They MUST mix the bytes before a challenge can affect the proof.
The circuit artifact fixes the component order.

The verifier calculates the digest from its expected statement.
The envelope MUST NOT supply an authoritative digest.
The identity-proof envelope MUST NOT contain a diagnostic digest copy.

A context change MUST invalidate the proof.
This rule includes a change to:

- `zkSystemId`;
- SessionTranscript;
- timestamp;
- issuer key;
- revocation key;
- revocation epoch;
- claim;
- profile.

### 6.3 Device authentication

The public statement contains the canonical SessionTranscript bytes.
The statement builder MUST consume all supplied CBOR bytes.
It MUST encode the decoded value again.
It MUST reject a noncanonical original encoding.

The verifier MUST reconstruct the ISO 18013-5
`DeviceAuthenticationBytes`.
The reconstruction uses:

- the decoded SessionTranscript;
- the fixed document type;
- fixed empty device namespaces;
- the fixed ISO 18013-5 profile.

The construction is:

```text
emptyDeviceNamespacesBytes = CBOR({})
deviceAuthentication = [
  "DeviceAuthentication",
  decodedCanonicalSessionTranscript,
  "eu.europa.ec.eudi.pid.1",
  tag24(bstr(emptyDeviceNamespacesBytes))
]
DeviceAuthenticationBytes = CBOR(tag24(bstr(CBOR(deviceAuthentication))))
```

The encoder MUST embed the SessionTranscript as its decoded CBOR value.
It MUST NOT embed the SessionTranscript as a byte string.
It MUST use both tag-24 wrappers.
It MUST use `0xa0` for the canonical empty map.

The verifier then constructs:

```text
deviceCoseSigStructure = CBOR([
  "Signature1",
  h'a101382f',
  h'',
  deviceAuthenticationBytes
])
```

The protected header is `{ 1: -48 }`.
The external AAD is empty.
The complete `Sig_structure` is the public ML-DSA message.
The request-context digest also binds this complete message.

The prover MUST NOT supply an authoritative derived value.
The implementation MUST derive the device-authentication bytes and the COSE
`Sig_structure` from the statement.
The API MUST NOT accept an authoritative copy of either value.

## 7. Circuit theorem

A proof is valid only if all requirements in this section are true.

### 7.1 Issuer authentication

The circuit proves these facts:

1. The private issuer COSE `Sig_structure` has the fixed shape.
2. The protected algorithm is ML-DSA-65.
3. The external AAD is empty.
4. The private payload is the private MSO used by all other components.
5. The issuer signature verifies with the trusted issuer key.
6. An unprotected credential key cannot replace verifier trust.

### 7.2 Private MSO facts

The circuit proves these private MSO facts:

1. `docType == "eu.europa.ec.eudi.pid.1"`.
2. `digestAlgorithm == "SHA-256"`.
3. `validFrom < timestamp < validUntil`.
4. `deviceKeyInfo` contains the canonical private device key.
5. The fixed namespace contains the selected item digest.
6. The private digest identifier selects that digest.

The validity limits are exclusive.
Equality with either limit MUST fail.

The private MSO validity component parses each private tag-0 UTC value.
Each value has the exact form `YYYY-MM-DDTHH:MM:SSZ`.
The parser MUST check all digits and separators.
It MUST check Gregorian month, day, and leap-year rules.
It MUST require `hour < 24`.
It MUST require `minute < 60`.
It MUST require `second < 60`.
It MUST require a year in `2020..=2099`.

The component converts both private times to Unix seconds.
It uses range-checked integer limbs.
The verifier converts the public time to the same form.
The AIR proves both nonzero slacks:

```text
timestamp - validFrom >= 1
validUntil - timestamp >= 1
```

The inclusive epoch-day comparator is not valid for this profile.
Host parsing can reject malformed input early.
Host parsing MUST NOT be the only check for a security fact.

### 7.3 Requested item

The MSO `version` value MUST be `1.0`.
The circuit MUST NOT accept another MSO version.

The circuit parses one tag-24 `IssuerSignedItemBytes` value.
The inner map MUST contain these four unique keys:

- `digestID`;
- `random`;
- `elementIdentifier`;
- `elementValue`.

The keys MAY occur in any map order.
The circuit hashes and binds the exact received tagged-CBOR bytes.
It MUST NOT re-encode the item before it calculates the digest.

The circuit proves these facts:

1. The namespace is the fixed PID namespace.
2. `elementIdentifier == "age_over_18"`.
3. `elementValue` is canonical CBOR `true`.
4. The randomizer is private.
5. The digest identifier is private.
6. SHA-256 of the signed item equals the selected MSO digest.
7. The item and MSO use the same digest-identifier cells.

`ZkDocumentData` contains the public result `true`.
The verifier MUST accept that result only after proof verification.

### 7.4 Device authentication

The circuit proves these facts:

1. The private device key is the key in the authenticated MSO.
2. The private device signature is a valid ML-DSA-44 signature.
3. The signed message is the message from Section 6.3.
4. ML-DSA uses the key that the MSO contains.

The private device `pkEncode` MUST contain 1,312 bytes.
The private device signature MUST contain 2,420 bytes.
The device profile MUST use COSE algorithm `-48`.

The proof MUST include the complete chain for matrix expansion, private-key
evaluation, key hashing, ML-DSA verification, and MSO key binding.
A private key hash alone is not sufficient.
The verifier MUST NOT supply `rho`, `t1`, `tr`, or a native key fold.

### 7.5 Revocation

The private revocation identifier is:

```text
id = LE64(SHA-256(privateMsoPayload)[0..8])
```

The fixture issuer MUST reject identifier `0`.
It MUST reject identifier `2^64 - 1`.
It MUST reject a collision in the demo issuance set.

The circuit proves:

```text
idLo < id < idHi
```

It verifies a private ML-DSA-65 signature on:

```text
LE64(idLo) || LE64(idHi) || LE32(revocationEpoch)
```

The verifier supplies the revocation public key.
The circuit binds the public epoch.
The identifier, interval, MSO digest, and signature are witness-only.
They are absent from the clear statement and envelope header.

This identifier derivation applies only to the controlled demo set.

## 8. AIR composition

These fixed components bind the private theorem:

- private issuer-message provider;
- private MSO binder;
- complete padded MSO SHA-256 binding;
- strict private item CBOR parser;
- private item binder;
- private `valueDigests` scanner;
- exact-second MSO validity;
- private device-key derivation and binding;
- private revocation range and signature.

The Keccak service MUST bind its round GKR output claim to the global LogUp sum
and the committed trace.

### 8.1 Private `rho` and matrix expansion

The matrix-expansion component derives the ML-DSA matrix from private `rho`.
The verifier MUST NOT supply a matrix coefficient.

The component uses:

- 16 row-major SHAKE-128 jobs for `rho || j || i`;
- six squeeze blocks for each job;
- the FIPS rejection sampler;
- three-byte candidates;
- acceptance only for values below `q = 8,380,417`;
- exactly 256 accepted coefficients for each polynomial.

The component MUST fail if six blocks do not supply enough coefficients.
It emits canonical stage-zero `NttCell` tuples.

These values are circuit constants:

- stream count;
- stream order;
- domains;
- candidate schedule;
- relation multiplicities.

The six-block cap is a profile constant.

### 8.2 Private A and t1 evaluation

The private key-evaluation constraints MUST remove all verifier-native uses of
the device key.
These constraints use the inverse-Horner construction.

The private key-evaluation constraints MUST:

- consume the stage-zero matrix cells from the matrix-expansion component;
- perform all eight inverse-butterfly stages;
- apply `256^-1 mod q = 8,347,681`;
- constrain each butterfly twiddle;
- constrain each modular add and subtract reduction;
- constrain each quotient;
- constrain each output to `[0,q)`;
- evaluate all 16 active A polynomials at `(r,s)`;
- decode and scale the four private `t1` polynomials by `2^13`;
- evaluate all four active scaled `t1` polynomials at `(r,s)`;
- keep the fixed coefficient identifiers `0..29`;
- keep the fixed A identifiers `30..59`;
- keep the fixed t1 identifiers `60..65`;
- serialize the fixed `[coeff 30, A 30, t1 6]` vector.

The private evaluation vector always contains 66 slots.
ML-DSA-44 uses these coefficient slots:

```text
z_0..z_3       = 0..3
w_0..w_3       = 5..8
e_0..e_3       = 11..14
v_0..v_3       = 17..20
c               = 23
C_0..C_3       = 24..27
```

The coefficient slots `4`, `9`, `10`, `15`, `16`, `21`, `22`, `28`, and `29`
MUST equal canonical zero.
The active A slots are `30..45`.
The A tail slots `46..59` MUST equal canonical zero.
The active scaled-t1 slots are `60..63`.
The t1 tail slots `64..65` MUST equal canonical zero.

The AIR MUST constrain each inactive trace to zero.
It MUST also emit the zero evaluation for the slot relation.
The fold MUST consume every identifier in `0..65` exactly once.
This rule binds the canonical zero tails to the fixed 66-slot proof shape.

The transcript derives `(r,s)` after the prover commits the witness columns.
The private A and t1 evaluation and the device fold use the same `(r,s)` pair.
They are contiguous parts of one private-device ML-DSA AIR.
The implementation MUST NOT use a second challenge pair.

The canonical t1 split is:

```text
t1 = lo9 + 512 * hi1
```

The AIR MUST range-check `lo9` to nine bits.
It MUST constrain `hi1` as a Boolean.
The key-evaluation constraints emit `T1Cell(i,m,lo9,hi1)` for the device-key
binder.
A byte lookup alone is not sufficient.

For each coefficient, the key-evaluation constraints prove:

```text
2^13 * t1 = d0 + 512*d1 + 512^2*d2
```

Each `d + 256` value has a nine-bit range check.
The permitted range prevents an M31 alias.

The key-evaluation constraints emit A and scaled-t1 `EvalAtRs` tuples.
Each emitted tuple has negative multiplicity.
The device fold consumes all 66 evaluations.
Each consumed evaluation has positive multiplicity.

The active ML-DSA-44 fold uses these groups in order:

```text
[z_0..z_3,w_0..w_3,e_0..e_3,v_0..v_3,c,C_0..C_3]
```

The 16 active A groups follow these groups.
The four active scaled-t1 groups follow the A groups.
The fixed zero tails remain in their slots.

The fold MUST constrain this complete identity:

```text
sum_{i=0..3} rhoRlc^i * (
    sum_{j=0..3} AHat[i][j] * zHat[j]
    - cHat * scaledT1Hat[i]
    - wHat[i]
    - (r^256 + 1) * vHat[i]
    - qHat(s) * eHat[i]
    - (s - B) * carryHat[i]
) = 0

qHat(s) = 1 - 16*s + 32*s^2
B = 512
scaledT1 = 2^13 * t1
```

Each hat is a balanced-radix-512 evaluation at `(r,s)`.
`rhoRlc` is the independent row-folding challenge.
It is not the private ML-DSA seed `rho`.

The AIR MUST construct `qHat(s)` from `[1,-16,32]`.
The witness and verifier MUST NOT supply `qHat(s)`.
The signs and correction factors are normative.
All four active `v`, `e`, and carry evaluations are normative.
A bare congruence modulo `q` is not sufficient.

No verifier-native A, t1, `qHat`, or key-fold value can remain.

### 8.3 Private key hashing and device ML-DSA

The private device ML-DSA component takes the device message as a public input.
The device public key is witness-only.

The component MUST constrain:

```text
tr = SHAKE256(pkEncode, 64 bytes)
mu = SHAKE256(tr || 0x00 || 0x00 || deviceCoseSigStructure, 64 bytes)
```

The component connects these values to:

- c-tilde;
- w1 encoding;
- SampleInBall.

The private ML-DSA mode MUST mix:

- an explicit private-key mode tag;
- the public device message;
- the public device-message length;
- the fixed namespace;
- the fixed stream base.

It MUST NOT mix or serialize:

- the private key;
- `rho`;
- `t1`;
- `tr`.

The fixed bridge order is:

```text
[pk_tr, tr_mu, mu_ct, w1enc, ct_sib]
```

The ML-DSA-44 device instance sets `tau = 39`.
Its SampleInBall squeeze cap is one SHAKE-256 rate block of 136 bytes.
The first eight bytes supply the sign bits.
The remaining 128 bytes supply the placement candidates.

The sampler MUST place all 39 coefficients in that block.
If it cannot do this, witness generation MUST return the typed
`SampleInBallExhausted` error.
It MUST NOT squeeze a second block.
It MUST NOT select another circuit shape.

The estimated exhaustion probability is about `2^-202.929`.
The cap therefore creates a negligible honest-prover failure mode.
This limit affects completeness.
It does not weaken soundness for a proof that the verifier accepts.
The demo accepts this tradeoff to keep the device proof shape fixed.

The issuer and revocation instances remain ML-DSA-65.
Their selected SampleInBall cap is five SHAKE-256 rate blocks.

The verifier MUST NOT construct a placeholder key.
The ML-DSA verifier receives no device-key bytes.

### 8.4 Private key and MSO binding

The device-key binder binds the 1,312-byte FIPS `pkEncode` to the private COSE
key.
The authenticated MSO contains that COSE key.

The fixed COSE key is:

```text
kty = 7
alg = -48
label -1 = 1,312-byte ML-DSA-44 pkEncode
```

The circuit artifact contains this canonical MSO prefix:

```text
6d 64 65 76 69 63 65 4b 65 79 49 6e 66 6f
a1 69 64 65 76 69 63 65 4b 65 79
a3 01 07 03 38 2f 20 59 05 20
```

The binder uses 288 active rows.
The first 32 rows contain `rho`.
Each of the four `t1` polynomials uses 64 five-byte groups.

For bytes `b0..b4`, the binder proves:

```text
b1 = l2 + 4*h6
b2 = l4 + 16*h4
b3 = l6 + 64*h2

u0 = b0 + 256*l2
u1 = h6 + 64*l4
u2 = h4 + 16*l6
u3 = h2 + 4*b4
```

The binder range-checks each byte to eight bits.
It enforces these exact fragment widths:

```text
l2 < 2^2   h6 < 2^6
l4 < 2^4   h4 < 2^4
l6 < 2^6   h2 < 2^2
```

Linear reconstruction alone is not sufficient.
Each `u` uses the same `hi1` and `lo9` form as the private t1 evaluation.
The first 32 bytes consume `RhoCell` tuples from the matrix-expansion
component.
The binder emits one normalized private 1,312-byte field for the private device
ML-DSA component.

The fixed binder lookup census is:

- 1,312 normalized device-key byte uses;
- 32 `RhoCell` uses;
- 1,024 `T1Cell` uses;
- one device-key-start use;
- 544 eight-bit range uses;
- 1,024 nine-bit range uses;
- zero seven-bit range uses.

A change to any bound key value MUST invalidate the proof.
This rule includes:

- a key byte;
- a start offset;
- a packed fragment;
- a `rho` cell;
- a `t1` cell.

### 8.5 Module and transcript order

The prover and verifier MUST use this order:

1. shared SHA-256 tables;
2. shared ML-DSA and range tables;
3. shared Keccak service;
4. `Ts13PublicContextBind`;
5. private issuer-message provider;
6. issuer private-message ML-DSA;
7. requested-item SHA-256;
8. complete private MSO SHA-256;
9. private item CBOR parsers;
10. private item binder;
11. private MSO binder;
12. private MSO validity component;
13. private `valueDigests` scanner;
14. private matrix-expansion component;
15. private device-key binder and normalizer;
16. one private-device ML-DSA AIR with key evaluation and hashing;
17. private revocation range;
18. private revocation ML-DSA;
19. public revocation key and epoch binding.

The circuit artifact fixes:

- relation handles;
- claim order;
- tree placement;
- challenge order;
- component geometry;
- public-mix order.

The prover and verifier MUST share one profile definition.
They MUST NOT use separate hand-built orders.

The lookup graph is normative:

| Tuple | Owner | Producer | Consumer |
| --- | --- | --- | --- |
| issuer `FieldBytes(field,index,byte)` | issuer-message provider | provider `-m` | each user `+1`; checked sum is `m` |
| device key `FieldBytes(1,index,byte)` | issuer `FieldBytes` owner | device-key binder `-1` | device ML-DSA `+1` for 1,312 bytes |
| `RhoCell(position,byte)` | matrix expansion | matrix expansion `+1` | device-key binder `-1` for 32 bytes |
| `NttCell(poly,stage,index,l0,l1,l2)` | matrix expansion | 16 active matrix polynomials and key-evaluation stages `+1` | prior key-evaluation stage or Horner evaluation `-1` |
| `T1Cell(poly,index,lo9,hi1)` | device-key binder | private t1 evaluation `+1` | device-key binder `-1` for 1,024 coefficients |
| `EvalAtRs(poly,e0,e1,e2,e3)` | device ML-DSA AIR | identifiers `0..65`, each `-1`; inactive tails contain canonical zero | device fold `+1` for all 66 values |
| `MdocDevicePkStart(start)` | private MSO binder | MSO binder `-1` | device-key binder `+1` |

The device-key binder draws the `T1Cell` challenge before the device AIR.
LogUp cancellation does not require producer-first order.
The implementation MUST NOT add a balancing component.

## 9. Circuit identity

TS13 `circuitHash` commits to the circuit.
The profile uses `circuit-artifact-v1.cbor`.

The artifact contains:

- profile and constraint-system versions;
- the ordered component list;
- ordered column geometry and component masks;
- log sizes and active row counts;
- relation names, tuple shapes, and signs;
- transcript mix order;
- challenge order;
- claim order;
- fixed vector lengths;
- fixed profile constants;
- fixed CBOR prefixes;
- fixed hash-stream constants;
- fixed range-table constants;
- the SHA-256 digest of this normative specification;
- the shape-manifest digest;
- the tree-zero root derivation;
- the proof-system field;
- PCS, FRI, query, and proof-of-work parameters;
- proof and envelope versions;
- enabled Cargo features;
- the `Cargo.lock` digest;
- the Rust toolchain;
- the soundness source-tree digest.

The source-tree digest covers:

- the workspace `Cargo.toml`;
- this normative specification;
- `air-core`;
- `stwo-sha256`;
- `stwo-keccak`;
- `stwo-mldsa`;
- `eu-id-prover`;
- `sdk`.

The digest input is a sorted path and SHA-256 manifest.
The generator encodes the manifest deterministically.
The generator MUST reject generation-input bytes that differ from the audited source hash.

The generator excludes build output such as `target/`.
It also excludes three recursive generated files:

- the shape manifest;
- the circuit artifact;
- the circuit-hash source file.

The generator MUST use a closed exclusion allowlist.
It MUST NOT use an ignore glob.
A new local soundness package MUST enter the source-tree digest.

The circuit hash is:

```text
SHA-256(circuitArtifactBytes)
```

The identity-proof envelope header and context digest use the raw 32 bytes.

A soundness change MUST change the artifact and circuit hash.
This rule includes a change to:

- constraint code;
- layout;
- relations;
- transcript construction;
- constants;
- proof parameters;
- public statements;
- canonical context;
- envelopes;
- the `proveIdentity` API;
- the `verifyIdentity` API.

CI MUST regenerate the artifact and reject drift.
A human-selected tuple is not a valid circuit hash.

## 10. Native API and proof envelope

### 10.1 API

The exported prover is:

```rust
pub fn prove_identity(
    statement: IdentityStatement,
    witness: IdentityWitness,
) -> Result<Vec<u8>, IdentityError>;

pub struct IdentityWitness {
    pub document: Vec<u8>,
    pub revocation_id_lo: u64,
    pub revocation_id_hi: u64,
    pub revocation_signature: Vec<u8>,
}
```

UniFFI exports:

```kotlin
fun proveIdentity(
    statement: IdentityStatement,
    witness: IdentityWitness,
): ByteArray
```

The statement contains the public values from Section 5.3.
The statement contains the issuer and revocation public keys.
The verifier controls both keys.

`witness.document` contains the canonical private mdoc data.
The witness contains the private revocation interval and signature.
It MUST NOT contain a trust key or trust-key hash.

UniFFI also exports:

```kotlin
fun verifyIdentity(
    statement: IdentityStatement,
    proof: ByteArray,
): Unit
```

The function returns only after the complete identity theorem verifies.
Malformed input returns a typed `IdentityError`.
UniFFI exports only `proveIdentity` and `verifyIdentity`.

### 10.2 Identity-proof envelope

The proof uses this fixed binary envelope:

```text
offset  size       field
0       8          ASCII "EUIDTS13"
8       2          little-endian version 4
10      32         raw circuit hash
42      4          little-endian body capacity P
46      P          canonical proof and zero padding
```

For this circuit, `P` is 1,507,328 bytes.
The total envelope is 1,507,374 bytes.

`P` is a circuit-artifact constant.
It is not the used proof length.
The artifact derives `P` from the maximum serialized proof size.
The derivation uses the fixed query and column parameters.
`P` MUST be the smallest sufficient multiple of 65,536 bytes.

The canonical proof prefix can have a variable length.
Challenge-derived query positions cause this variation.
The encoder writes the canonical prefix.
It fills the remainder with `0x00`.
It MUST NOT serialize the used prefix length.

The decoder MUST reject:

- another magic value;
- another version;
- an unknown circuit hash;
- another capacity;
- another total length;
- another claim shape;
- another vector shape;
- an envelope that does not start with the identity-proof header.

The decoder MUST decode one bounded proof prefix.
It MUST record the consumed cursor position.
It MUST encode the decoded proof again.
The new bytes MUST equal the consumed prefix.
All remaining bytes MUST equal `0x00`.

The identity-proof envelope MUST NOT contain:

- a semantic statement;
- a request-binding hash;
- a device key;
- an MSO;
- a digest identifier;
- a credential-selected shape.

The proof is not compressed.
Data-dependent compression length can reveal metadata.
The application MUST disable transport compression.
Alternatively, transport MUST add independent fixed-size padding.

The variable prefix length is challenge-dependent.
It is inside the transparent proof body.
Section 2 gives the privacy limitation for that body.

### 10.3 Errors

The API distinguishes these errors:

- `UnsupportedCircuitHash`;
- `UnsupportedCredentialShape`;
- `MalformedSessionTranscript`;
- `InvalidPublicContext`;
- `InvalidPrivateCredential`;
- `InvalidRevocationWitness`;
- `ProofGenerationFailed`;
- `MalformedProofEnvelope`;
- `ProofVerificationFailed`.

An error MUST NOT contain private data.
Private data includes:

- credential bytes;
- keys;
- signatures;
- offsets;
- revocation values.

## 11. Acceptance tests

### 11.1 Three presentations

The required fixtures are:

- **A1:** credential A with fresh context 1;
- **A2:** credential A with fresh context 2;
- **B:** credential B with fresh context 3.

Credentials A and B use the same issuer.
They use the same profile and claim.
They use the same revocation policy.
They have different private values.
The different values include:

- MSOs;
- item randomizers;
- digest identifiers;
- device keys;
- signatures;
- revocation identifiers;
- credential data;
- validity limits.

The validity values use the same encoded width.
Both credentials are valid at the test time.

Contexts 1 and 2 use different RP-identifier lengths.
They also use different SessionTranscript lengths.
Both lengths remain within the fixed capacity.

The test MUST confirm:

```text
MSO(A1) == MSO(A2)
MSO(A1) != MSO(B)
deviceKey(A1) == deviceKey(A2)
deviceKey(A1) != deviceKey(B)
```

All three proofs MUST verify.

The test replaces only fresh request fields with a marker.
After replacement, it MUST confirm:

- the semantic public statements are identical;
- the circuit hashes are identical;
- the required profile strings are identical;
- the tree-zero roots are identical;
- the envelope lengths are identical;
- no identity-proof header field distinguishes A from B.

The test does not require equal proof-body bytes.

### 11.2 Exact public schema

`ts13_public_schema_is_exact` MUST:

1. destructure every semantic statement field without `..`;
2. destructure every derived context field without `..`;
3. destructure every circuit public-input field without `..`;
4. destructure every private witness field without `..`;
5. fail to compile when an unreviewed field appears.

Integration tests MUST inspect semantic statements for forbidden markers.
Integration tests MUST also inspect identity-proof headers for forbidden markers.

Typed-field inspection is authoritative.
Byte-run tests MUST use high-entropy sentinels.
A sentinel MUST NOT plausibly collide with a public key.

Tests MUST NOT scan a one-byte identifier by itself.
Tests MUST NOT scan a two-byte length by itself.
Tests MUST NOT scan an offset or bucket by itself.

The forbidden semantic set includes:

- full or partial MSO runs;
- issuer signatures;
- device signatures;
- full device keys;
- `rho`, `t1`, or `tr`;
- digest identifiers with selected digest context;
- item randomizers;
- private item encodings;
- validity timestamps;
- private offsets;
- private length buckets;
- revocation identifiers;
- revocation endpoints;
- MSO digests;
- revocation signatures;
- certificate serial numbers;
- credential serial numbers.

The test MUST NOT scan the STARK body for zero-knowledge evidence.

### 11.3 Context relabeling

The public-input relabeling test MUST:

1. create and verify one proof;
2. retain the identity-proof envelope;
3. change the RP-local identifier and require failure;
4. change the timestamp by one second on the same UTC day;
5. require verification failure for the changed timestamp;
6. change the SessionTranscript and require failure;
7. change issuer policy and require failure;
8. change revocation policy and require failure;
9. derive all public circuit bytes again after each change.

The test MUST reach proof verification.
A header-only failure is not sufficient evidence.

### 11.4 Theorem negative tests

Proof verification MUST fail for these changes:

| Area | Change |
| --- | --- |
| issuer | signature, key, algorithm, or payload binding |
| MSO | document type, digest algorithm, key window, or payload start |
| validity | expired, not valid, boundary, adjacent second, or malformed UTC |
| item | namespace, element, value, randomizer, or item bytes |
| digest | identifier, map key, selected digest, or scanner position |
| device context | transcript, document type, namespaces, algorithm, AAD, or payload |
| device signature | profile, protected algorithm, exact wire length, encoding, or value |
| revocation | identifier, endpoint, strictness, signature, or epoch |
| role separation | swapped issuer, device, or revocation role |
| shape | wrong fixed length, capacity overflow, or extra CBOR |

### 11.5 Private device-key negative tests

The proof MUST reject:

- an ML-DSA-65 protected header or profile tag in the device role;
- a 1,952-byte device public key;
- a 3,309-byte device signature;
- a wrong matrix seed `rho`;
- a wrong `(j,i)` domain;
- an ExpandA stream count other than 16;
- a wrong ExpandA stream order;
- a wrong squeeze block;
- candidate `q` as an accepted value;
- a rejected valid candidate;
- an accepted candidate after coefficient 256;
- a forged A coefficient;
- a forged inverse-butterfly stage;
- a wrong inverse normalization;
- a forged A or t1 evaluation;
- an inverse-NTT modular alias;
- a wrong t1 scaling digit;
- a forged scaling carry;
- a changed `v`, `e`, or carry evaluation;
- an omitted correction term;
- a sign change in the integer-lift fold;
- witness-supplied `qHat`;
- a wrong `[1,-16,32]` coefficient;
- a wrong `(r^256 + 1)` factor;
- a wrong `(s - 512)` factor;
- a reordered private evaluation vector;
- a wrong private evaluation vector length;
- a nonzero inactive coefficient slot in `4`, `9`, `10`, `15`, `16`, `21`,
  `22`, `28`, or `29`;
- a nonzero inactive A slot in `46..59`;
- a nonzero inactive t1 slot in `64..65`;
- a missing or extra relation counterpart for an inactive evaluation slot;
- a substituted device key;
- a wrong device-key start or field identifier;
- a wrong device-key byte position or fragment;
- a wrong device-key high bit;
- a wrong `RhoCell` or `T1Cell`;
- an alternate device-key decomposition;
- a wrong `pkEncode`-to-`tr` binding;
- a wrong `tr`-to-`mu` binding;
- a wrong `mu`-to-`c-tilde` binding;
- a wrong `w1` binding;
- a wrong `c-tilde`-to-`SampleInBall` binding;
- a missing relation counterpart;
- an extra relation counterpart;
- a wrong claimed sum.

A resource-cap test MUST force ML-DSA-44 SampleInBall exhaustion after one
block.
It MUST require the typed `SampleInBallExhausted` error.
It MUST confirm that the prover does not add a second block or select another
shape.

This substitution MUST fail:

> The device signature uses key K2, but the authenticated MSO contains key K1.

The substitution MUST fail when all K2 witness values are consistent.

### 11.6 Proof format

Tests MUST prove these conditions:

- An envelope without the identity-proof header fails.
- An unknown circuit hash fails before body decoding.
- A wrong capacity fails.
- A nonzero padding byte fails.
- A noncanonical proof prefix fails.
- A truncated envelope fails.
- A trailing byte fails.
- The statement defines one public equality claim.

### 11.7 Resource evidence

Functional acceptance requires a successful proof and verification.
It also requires the exact 1,507,374-byte identity-proof envelope.

Performance is not a conformance requirement.
Benchmark reports MUST record:

- the commit;
- the circuit hash;
- the fixture;
- the PCS configuration;
- the feature set;
- the thread count;
- the device;
- the operating system;
- proof time;
- verification time;
- envelope size;
- peak resident memory.

This historical physical-device report is not evidence for the current
circuit artifact:

```text
tasks/bench-results/ts13-mobile-firebase-20260730/README.md
```

## 12. Non-goals

This demo does not include:

- STWO proof masking;
- a general zero-knowledge compiler;
- generic DCQL predicates;
- multiple claims;
- arbitrary PID or mdoc shapes;
- runtime length buckets;
- a hidden issuer;
- a hidden requested claim;
- a hidden profile;
- a hidden revocation epoch;
- production PKI;
- `x5chain` validation;
- certificate validation;
- issuance;
- trust-list distribution;
- a production revocation database;
- a collision registry;
- revocation epoch rollover;
- wallet integration;
- application integration;
- secure-key-store integration;
- platform integration;
- a 128-bit post-quantum security claim.

## 13. Conformance

An implementation conforms only if:

1. `proveIdentity` returns a fixed-size identity-proof envelope.
2. `verifyIdentity` verifies the complete theorem.
3. The circuit constrains every fact in Section 7.
4. The public allowlists in Section 5 are exhaustive.
5. The A1, A2, and B test passes.
6. A context relabeling invalidates the proof.
7. A device-key substitution invalidates the proof.
8. The circuit artifact determines the circuit hash.
9. All negative tests pass.
10. All API and envelope tests pass.
11. All fixed-shape tests pass.
12. The benchmark records include peak resident memory.
13. Documentation uses the exact privacy description from Section 2.
