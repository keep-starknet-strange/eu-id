# Quantum-Safe Mdoc — Clean-Scheme Spec (feat/mldsa-claude)

Status: implementation spec, 2026-07-09. Independent implementation (bake-off
branch); designed from committed `ac0d1cb1` + first principles.

## 0. Goal and claim

`quantum-safe-mdoc` is one uniform mode with **no classical public-key
assumption anywhere in the verification chain**:

- issuer authentication: ML-DSA-65 (committed, M7–M9);
- device/holder authentication: ML-DSA-65 (this work);
- TS13 revocation-authority authentication: ML-DSA-65 (this work);
- issuer trust: verifier-supplied ML-DSA public-key pins (no x5chain — a
  PQ PKI profile does not exist yet in 18013-5/ARF; pins match the EUDI
  trusted-list distribution model). A self-carried AKP header key is never
  a trust decision.
- proof system: hash-based (Blake2s Merkle / SHAKE / SHA-256) — Grover-only.

Mixed signature modes fail closed in both directions, at extraction, at
statement validation, at prove, and at verify.

Known v1 limitation (documented, not fixed here): in ML-DSA mode the issuer
`Sig_structure` and signature are public statement inputs, so presentations
of the same credential are linkable. The P-256 mode retains the hiding
property. PQ unlinkability is follow-up work (private-message issuer mode —
the same mechanism revocation uses below, plus salted-digest-only disclosure).

Security claim wording: "no classical public-key assumption in the
quantum-safe path". Do NOT claim a NIST level for the composed proof until
the QROM accounting of the PCS/FS/grinding closes.

## 1. stwo-mldsa: multi-instance hosting

The committed crate supports ONE hosted instance per proof. Three collision
axes were analyzed; only one is real:

- Preprocessed column ids are global. air-core tree-0 dedups by id
  (first-writer-wins), so a second instance would silently alias the first
  instance's **witness-dependent** columns (SIB schedule) and
  **shape-dependent** columns (bridge/sink). REAL — must namespace.
- Keccak stream ids / perm-id plan: NOT a collision. Each module instance
  draws its own `KeccakRelations` in `draw_relations_common` (module-local
  randomness), so LogUp terms cannot cancel across instances.
- `HOSTED_MSG_FIELD_ID = 0`: NOT a collision. Each instance consumes its own
  `SharedFieldRelation` handle (issuer_field / device_field / revocation
  field), which are independently drawn relations.

### 1a. `with_instance_namespace(&'static str)`

On `MlDsaProver` and `MlDsaVerifier` (both sides must agree):

1. Prefix the namespace onto the ids of every **sib** preprocessed column
   (witness-dependent schedule) and every **bridge/sink** preprocessed column
   (message-length-dependent), by prefixing the descriptor `tag`s and the sib
   id strings: `"msg"` → `"<ns>/msg"`. Fixed-content columns (coeffs/decomp
   layout + all rc value tables + keccak tables) keep global ids so tree-0
   dedup shares one copy across instances — sharing is intentional and safe
   because their content is a protocol constant.
2. Mix the namespace bytes into `mix_public` (role/domain separation): a
   device claim tree cannot be replayed against the revocation slot even with
   a compatible shape, because the transcripts diverge at mix time.

### 1b. Private-message hosted mode

`with_private_message()` on both sides. Purpose: the TS13 revocation message
is `LE64(id_lo) ‖ LE64(id_hi) ‖ LE32(epoch)` where the bounds are PRIVATE
witness data; the P-256 path hides them behind a SHA-256 prehash, a pure
ML-DSA signature has no prehash, so the message itself must stay private.

Verified against committed code: the verifier uses `input.message` CONTENT
only in `mix_public` (`compute_public_evals` reads rho/t1/z/c̃/hint;
`LayoutCtx`/shapes/bridges read `message.len()` only). Therefore:

- private mode mixes `message.len()` (and the namespace) but NOT the bytes;
- the verifier-side `MlDsaVerifyInput.message` carries zeroed bytes of the
  correct length (never serialized as real data);
- soundness: the μ-absorb bytes flow exclusively through the host's
  `FieldBytesRelation` (yielded by a host module that constrains them
  in-AIR — for revocation: the SHA exposure module + `MdocRevocationRangeBind`
  over the same field id), exactly like the already-private c̃/µ streams
  ("they flow only through HashIo"). FS binding of the message is inherited
  from the host module's own claims; the ML-DSA circuit enforces
  c̃ = SHAKE(μ ‖ w1Encode) and μ = SHAKE(tr ‖ M_private) in-circuit.

### 1c. Two-instance gate (stwo-mldsa/tests/hosted.rs)

- two hosted instances, distinct namespaces, different signatures/messages →
  proves and verifies;
- swapped claim vectors between the two instances → reject;
- same-shape different-witness instances → distinct preprocessed roots
  (regression for the dedup-alias failure mode).

## 2. eu-id-prover: scheme-tagged device + revocation

### 2a. Data model

- Reuse the committed issuer enum for the device: rename conceptually to
  "auth input", keep `IssuerAuthInput` as an alias. `ExtractedPidMdoc` and
  `MdocCircuitStatement.device_input` become the enum (`Ecdsa(EcdsaVerifyInput)`
  / `MlDsa(Box<MlDsaVerifyInput>)`).
- Device COSE key in the MSO: AKP COSE_Key (`kty: 7`, `alg: -49`, pub bytes
  in label `-1`, 1,952 bytes). Parser accepts it only under `ml-dsa` and only
  when the issuer is ML-DSA (fail-closed match on
  `(device_key_scheme, device_signature.alg, issuer_scheme)`).
- Device signature: COSE_Sign1 detached-payload with `MLDSA_PROTECTED_HEADER`;
  native pre-check via `stwo_mldsa::reference::verify::verify_internals` at
  extraction (mirror of the issuer arm).
- TS13 revocation: scheme-tagged key + signature on
  `Ts13RevocationStatement`/`Ts13RevocationWitness`; ML-DSA arm signs the raw
  20-byte message (pure, no prehash); native `verify_witness` via the
  reference verifier.

### 2b. Device-key ↔ MSO binding (ML-DSA)

The P-256 path pins two 32-byte coordinate windows into the issuer MSO via
`MdocWindowBind`. A 1,952-byte key does not fit that shape — and does not
need it: in ML-DSA mode the issuer `Sig_structure` (containing the MSO) and
the device public key are both PUBLIC statement inputs, already mixed into
Fiat-Shamir and bound in-circuit by the issuer instance's μ-absorption. So
the binding is a canonical byte equality enforced host-side ON BOTH PROVE AND
VERIFY, before STARK verification:

- statement carries `mso_device_key_akp_offset`;
- check `issuer_message[off .. off+1952] == pk_encode(device_pk)` plus the
  CBOR anchor prefix (`-1` key + 1952-byte bstr header `20 59 07 A0`) at
  `off - 3`;
- widening the 32-byte window AIR to 1,952 columns would prove an equality
  already fixed by the public transcript — rejected.

### 2c. Prove/verify wiring (non-coprocessor, `ml-dsa`)

Scheme = ML-DSA swaps, per role:

| role | P-256 modules (dropped) | ML-DSA module (added) |
|---|---|---|
| device | `device_p256` + `device_bridge` | `device_mldsa = MlDsaProver::hosted(w, in, device_field).with_instance_namespace("mdoc/device")` |
| revocation | `revocation_p256` + `revocation_bridge` | `revocation_mldsa = …(revocation_field).with_instance_namespace("mdoc/ts13/revocation").with_private_message()` |

- `device_sha` / `revocation_sha` stay as the byte-exposure providers (no
  digest handle in ML-DSA mode, mirroring the committed `issuer_sha`
  treatment); `MdocRevocationRangeBind` keeps consuming the same 20-byte
  field id — the bounds check never moves host-side.
- Module order: each mldsa instance composes immediately after its provider
  SHA module (host handle must be set before `draw_relations`). Issuer
  instance keeps default namespace ("" / `"mdoc/issuer"` — pick one and mix
  it; a bare default that matches the standalone crate tests is acceptable
  only if the role tag is still mixed).
- Proof struct: `device_mldsa: Option<MdocMlDsaClaims>`,
  `revocation_mldsa: Option<MdocMlDsaClaims>`; shape gates per role mirroring
  the committed issuer gate (n_group_evals / hosted_claimed_sums_len) BEFORE
  `Claims::from_flat`.
- Verify fail-closed: claim presence must biconditionally match the statement
  scheme per role; scheme uniformity across roles checked once at statement
  validation.

## 3. Features / SDK / FFI

- `quantum-safe-mdoc = ["ml-dsa"]` alias on eu-id-prover, sdk, eu-id-ffi.
- P-256 isolation: `stwo-p256`, `p256`, `ecdsa` become optional deps reachable
  only from `p256`/`ec-coprocessor` features; device/revocation P-256 code
  paths gated `#[cfg(feature = "p256")]`. Acceptance:
  `cargo tree -p eu-id-prover --no-default-features --features quantum-safe-mdoc -e normal`
  contains no p256 / ecdsa / elliptic-curve / primeorder / sec1 / rfc6979 /
  stwo-p256 / eu-id-ec-coprocessor.
- `MdocPidRequest.trusted_mldsa_issuer_public_keys: Vec<Vec<u8>>` (1,952-byte
  encoded pks); an ML-DSA issuer REQUIRES a non-empty pin list and the header
  AKP key must be a member (fail-closed; self-carried keys never trusted).
- SDK: the ML-DSA path is unreachable through the SDK today (SDK is
  coprocessor-shaped). Phase-3 item; the prover-level API is the product
  surface for this bake-off round. FFI: passthrough features only.

## 3a. As-built decisions (2026-07-10)

- Enum named `MdocAuthInput`, aliases `IssuerAuthInput`/`DeviceAuthInput`.
- D2 binding: **no offset fields exist at all** — canonical CBOR navigation
  (`Sig_structure[3]` → MSO → `deviceKeyInfo.deviceKey` → AKP `-1` bytes)
  against `pk_encode(statement device pk)`, identical helper at prove and
  verify. The offset-tamper class of the P-256 window binding does not apply.
- Proof claims: issuer stays `mldsa`; added `device_mldsa`, `revocation_mldsa`
  (all `Option`, presence biconditional with the statement arm per role;
  shape-gated before claim-tree construction). Device/revocation P-256 claims
  became `Option` accordingly.
- Namespaces: `mdoc/issuer`, `mdoc/device`, `mdoc/ts13/revocation` on both
  sides (issuer explicitly namespaced too).
- Hosted ML-DSA binds ρ/t1/tr/message in the transcript; c̃/z/hint are private
  witness (mirrors the committed issuer path). Tampered-signature negatives
  live at the native/prove layer; verify-side public-binding negatives tamper
  the transcript-mixed key bytes.
- Revocation: `MdocRevocationKey`/`MdocRevocationSignature` enums shared by
  mdoc.rs/ts13.rs; verify-side revocation input rebuilt from public pk/sig
  with `message = [0u8; 20]`, `tr = SHAKE-256(pk)`.
- Measured (single-thread, issuer+device+revocation ML-DSA, default
  PcsConfig): **prove 72.68 s, verify 372.7 ms, proof 34,424,854 bytes**
  (vs ~2.9 s / ~4.5 MB for the P-256 mode). Keccak-heavy triple instance;
  perf work (shared Keccak lanes across instances, PcsConfig tuning,
  compression) is explicitly follow-up, not part of the soundness scheme.

## 4. Executable gates

- [x] G1 native: fixture signs issuer + device + revocation with ML-DSA-65;
      per-role tamper negatives reject at extraction.
- [x] G2 e2e: one root-pinned STARK proving issuer + device + revocation
      ML-DSA + attribute policy; serialization round-trip.
- [x] G3 role replay: device↔revocation claim swap rejects; device↔issuer
      input swap rejects.
- [x] G4 mixed-mode: ML-DSA issuer + ES256 device rejects; ES256 issuer +
      ML-DSA device rejects; ML-DSA mode + P-256 revocation key rejects.
- [x] G5 MSO binding: device-key offset tamper and anchor tamper reject on
      both prove and verify sides.
- [x] G6 revocation: out-of-range id / wrong epoch / tampered signature /
      tampered bounds reject; the serialized statement/proof contains no
      id_lo/id_hi bytes (privacy assert).
- [x] G7 preprocessed-root: two different device signatures ⇒ different
      pinned roots; per-signature pin regression across all three roles.
- [ ] G8 quantum-only dependency-tree gate + feature-matrix build checks.
- [x] G9 P-256 regression suites unchanged
      (compose_p256_sha, credential_pipeline, e2e_soundness, identity_api,
      nonce_signature, mdoc_support suites).
- [x] G10 perf: single-thread prove/verify/proof-size for the all-ML-DSA
      composition (named numbers in this file when measured).

## 5. Implementation order

1. stwo-mldsa: namespacing + private-message mode + two-instance tests (§1).
2. Test fixture: ML-DSA device + revocation signing (RustCrypto `ml-dsa`
   dev-oracle) + AKP deviceKey credential builder.
3. Prover data model (§2a) + extraction fail-closed guards.
4. Wiring (§2c) + MSO binding (§2b).
5. Negatives (G3–G7).
6. Features/SDK isolation (§3, G8).
7. Full gate run + perf (G10) + commit.
