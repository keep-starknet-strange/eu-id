# EUDI TS13 Full Compatibility Gap Specification

Date: 2026-07-07
Baseline commit: `79ae3916` on `feat/proof-reductions`. "At baseline" below
always means this commit. If HEAD has moved, re-verify the "Current status"
column and the baseline-pass claims before executing any work order.

This is the authoritative spec for everything still missing before this repo can
claim full compatibility with the EUDI TS13 arithmetic-circuit ZKP path: the
TS13 statement, wire formats, and negotiation, with our own `ZkSystem` id.
"TS13-compatible" here NEVER means emitting `longfellow-libzk-v1` proofs — see
decision D-TS13-SYS in WO-TS13-2.

## Execution Rules (read before running any acceptance block)

1. **A test filter that matches zero tests is a FAILURE.** `cargo test` exits 0
   when the filter matches nothing. For every acceptance command, the output
   must show each named required test in the pass list. `running 0 tests` or
   `0 passed` means the work order is NOT done, even though the exit code is 0.
2. **Tests marked (NEW) do not exist at the baseline commit.** Creating them is
   part of the work order. Do not rename them; the exact function names below
   are the acceptance contract. If a name must change, update this spec in the
   same commit.
3. **Commands marked "regression guard" already pass at baseline.** They prove
   nothing about completion; they only prove you did not break existing
   behavior. Completion evidence is exclusively the (NEW) tests and named
   artifacts.
4. Run every heavy (`--release --ignored`) command with `RAYON_NUM_THREADS=1`
   as written; multi-threaded runs can deadlock under cross-session contention.

## Scope

This document covers the product mdoc proof path:

- `crates/eu-id-prover/src/mdoc.rs`
- `crates/eu-id-prover/src/mdoc_mac.rs`
- `crates/eu-id-prover/tests/mdoc_support.rs`
- `crates/eu-id-ec-coprocessor/src/ecdsa.rs`
- `crates/sdk/src/lib.rs`

It does not cover the older 11-byte POC credential path except when that path
is used as a benchmark or regression guard. It also does not require TS14/BBS+
support; TS14 is a separate multi-message-signature architecture that requires
issuer cryptography changes.

## Compatibility Definition

The repo is TS13-compatible when all required rows in the compatibility matrix
below are green for at least one published circuit parameter tuple and the SDK
can consume and emit the TS13 presentation-layer formats for that tuple.

The first required published tuple is:

```text
system: stwo-euid-v1 advertised via TS13 ZkSystemSpec negotiation
        (NOT longfellow-libzk-v1 — see decision D-TS13-SYS in WO-TS13-2)
credential: ISO/IEC 18013-5 mdoc PID / mDL shaped DeviceResponse
proof: one verifier-facing zero-knowledge proof artifact
attributes: one disclosed TS13 equality attribute, age_over_18
soundness: at least 100 statistical bits after composed-system accounting
device binding: ISO DeviceAuthenticationBytes over verifier session transcript
issuer signature: ES256/P-256 issuerAuth over MSO
revocation: TS13 sorted-pair non-revocation
presentation: ISO ZkRequest/ZkDocument plus OpenID4VP DCQL mso_mdoc_zk
circuit identity: pinned circuit_hash derived from canonical circuit config
```

Additional supported tuples may include the current two-attribute PID profile
(`birth_date` age predicate plus nationality set predicate), but those are
extensions. The TS13 claim must stand on the one-attribute equality tuple first.

## Current Baseline

The repo already has substantial TS13-shaped functionality:

- mdoc extraction and statement construction for real vectors, including
  Longfellow mDL and EUAV vectors.
- issuer and device ES256/P-256 verification paths.
- SHA-256 digest membership and item binding through anchored mdoc windows.
- validity-window checks over `validFrom`, `validUntil`, and verifier policy date.
- device-key binding from MSO to device authentication.
- ValueEquality mode for TS13-style disclosed attributes.
- `AgeOver` and `Alpha2Set` predicate modes as product extensions.
- Longfellow GF(2^128) MAC binding work in the P4b track.
- focused real-vector and negative tests in `crates/eu-id-prover/tests/mdoc_support.rs`.

The repo must not claim full TS13 compatibility yet. The missing required work
is concentrated in zero-knowledge masking completion, revocation, presentation
formats, circuit parameterization/hash publication, and formal verification
evidence.

## Compatibility Matrix

| Area | TS13 requirement | Current status | Required work |
|---|---|---|---|
| Issuer signature | Prove an issuer ES256 signature over the MSO hash. | Mostly present through the mdoc issuer P-256 path. | Keep in the final TS13 tuple and re-run after P4/P5 repinning. |
| Device binding | Prove the device-auth ES256 signature over session-bound `DeviceAuthenticationBytes`. | Present, with ISO and Longfellow legacy profiles. | Publish the exact TS13 tuple profile and reject unsupported profiles at the TS13 entry point. |
| mdoc digest binding | Prove disclosed item preimages hash to MSO `valueDigests`. | Present through `MdocWindowBind` and anchored offsets. | Preserve negative gates for digest/member/window tampering. |
| Attribute disclosure | Public requested `(namespace, name, value)` attributes. | `ValueEquality` exists; current product default also supports computed predicates. | TS13 tuple must use `ValueEquality` for `age_over_18`; computed predicates must be documented as extensions. |
| Validity | Prove `validFrom <= now <= validUntil`. | Present for anchored date windows. | Keep policy date caller-bound in SDK and presentation formats. |
| Zero knowledge | Hide witness mdoc bytes, signatures, device key, digests, and unused statement data. | P4a/P4b in progress; P4c masking/leakage proof still open. | Complete P4c masking, leakage table, simulator sketch, and composed-ZK verification. |
| Soundness | Document at least 100 statistical bits for the full composed system. | Individual proof configs expose security bits; no final tuple table. | Add a circuit tuple soundness table covering Ligero, sumcheck, Fiat-Shamir, STARK/FRI, and union bounds. |
| Non-revocation | TS13 sorted-pair revocation proof for a credential identifier and epoch. | Missing entirely. | Implement WO-TS13-1 after the credential-id product decision. |
| Presentation | ISO ZkRequest/ZkDocument and OpenID4VP DCQL `mso_mdoc_zk`; reject unsupported `zk-jwt` until implemented. | SDK uses a bespoke `stwo-euid-v1` envelope. | Implement WO-TS13-2 in `crates/sdk/src/presentation.rs` or the established SDK module layout. |
| ZK system id | `longfellow-libzk-v1`. | SDK contract currently exposes `stwo-euid-v1`. | See D-TS13-SYS in WO-TS13-2: `longfellow-libzk-v1` denotes libzk proof bytes per `draft-google-cfrg-libzk`; stwo proofs MUST NOT carry that id. Register our own `ZkSystem` value; reject `longfellow-libzk-v1` requests fail-closed. |
| Circuit identity | `circuit_hash` over canonical circuit parameters. | SDK has a string key only; no published hash family. | Implement WO-TS13-3 with golden circuit hashes and fail-closed verification. |
| Circuit parameters | Tuple includes document size, attribute count, max attribute size, and issuer-set size. | Current mdoc path is partially parameterized, with fixed product defaults and N=1/N=3 tests. | Publish supported tuples and pin proof/preprocessed roots per tuple. |
| Real-vector conformance | TS13/Longfellow examples prove and verify. | Extraction and slow end-to-end tests exist for vendored Longfellow vectors. | Promote the TS13 tuple tests to the release gate after P4c and parameter repinning. |
| Documentation contracts | Product docs must not describe TS13-required behavior as unsupported once the tuple is published. | `docs/mdoc-credential-format.md` still excludes revocation, SD-JWT, x509-in-circuit validation, and privacy masking. | Update docs during the evidence pack so exclusions match the supported TS13 tuple and optional variants. |
| Issuer privacy | Optional TS13 enhanced variant: hide issuer key by proving Access CA signature in-circuit. | Not implemented; issuer public key is public/host-trusted. | Optional WO-TS13-4 only after product approval. Baseline TS13 compatibility does not require it. |
| Proof size/performance | Longfellow parity target for product viability. | Active parity work exists; current numbers are not final. | Not a strict conformance blocker, but must be tracked before external compatibility claims. |

## Required Work Orders

### WO-TS13-0: Finish Zero-Knowledge Compatibility Gate

Owner: P4/P5 mdoc proof track.

Required before any compatibility claim:

1. Complete P4c masking for the product mdoc proof path.
2. Classify every public value and proof opening as public-by-design, perfectly
   masked, statistically masked, or rejected by the TS13 entry point.
3. Add the P4c leakage table named in `tasks/p4c-masking-note.md`.
4. Add the circle-code rank check and bit-decoy numerical bound required by the
   masking note.
5. Add a simulator sketch for the published tuple.
6. Re-run the Longfellow vector proof gates under the zero-knowledge config.

Completion evidence (all four commands in the block below already pass at
baseline `79ae3916` WITHOUT any P4c work — they are regression guards only):

- (NEW) test `mdoc_zk_masking_classification_complete`: walks every public
  value and proof opening in the tuple proof and asserts each carries one of
  the four classifications from item 2; fails if any is unclassified.
- (NEW) test `mdoc_zk_circle_code_rank_check`: the rank check and bit-decoy
  numerical bound from `tasks/p4c-masking-note.md`, as an executable assert.
- (NEW) artifact: leakage table committed at the location named in
  `tasks/p4c-masking-note.md` (if the note names none, `tasks/p4c-leakage-table.md`).
- (NEW) artifact: simulator sketch for the published tuple, in the same file
  or a sibling `tasks/` doc.

Acceptance (regression guards plus the NEW tests above):

```bash
rtk proxy cargo test -p eu-id-prover mdoc_zk_ -- --nocapture
rtk proxy cargo test -p eu-id-prover --test mdoc_support
rtk proxy env RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release --features ec-coprocessor mdoc_coprocessor_rejects_required_negative_mutations -- --ignored --exact --nocapture
rtk proxy env RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release --test mdoc_support longfellow_mdl3_n1_age_over_18_end_to_end -- --ignored --exact --nocapture
rtk proxy env RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release --test mdoc_support longfellow_euav11_age_over_18_end_to_end -- --ignored --exact --nocapture
```

The first command must show both `mdoc_zk_` tests passing (Execution Rule 1).
The review report must include proof bytes, prove time, verify time, and the
composed security-bit table for the tuple.

### WO-TS13-1: Add Sorted-Pair Non-Revocation

Owner: mdoc proof path plus EC coprocessor.

TS13 uses a revocation authority that publishes signatures over consecutive
identifier pairs and an epoch. A non-revoked credential proves that its private
identifier lies strictly between a signed pair.

Required design:

1. Add a revocation statement containing public revocation key `rpk` and public
   epoch `ep`.
2. Add witness values `id`, `id_lo`, `id_hi`, and the revocation signature.
3. Prove `verify_p256(rpk, SHA-256(encode(id_lo, id_hi, ep)), signature)`.
4. Prove `id_lo < id < id_hi`.
5. Bind `id`, `id_lo`, `id_hi`, and `ep` to the hashed revocation message.
6. Bind `id` to the credential identifier source selected by product decision
   D-TS13-ID below.
7. Add the revocation proof to the same verifier-facing TS13 proof artifact.

Decision D-TS13-ID (RESOLVED 2026-07-07 — derived identifier from MSO bytes):

TS13 only states "it is assumed that an issued credential has a unique
identifier"; it does not define where it lives in the mdoc. Our profile:

```text
id = LE64( SHA-256( MSO bytes )[0..8] )
```

where "MSO bytes" is the same MobileSecurityObjectBytes payload the circuit
already binds through the issuerAuth signature.

Rationale, in force:

- MUST NOT derive from issuerAuth signature bytes: ECDSA is malleable —
  (r, s) and (r, n−s) are both valid signatures, so a holder could flip `s`
  to change their derived id and escape revocation. The MSO bytes are the
  SIGNED payload: changing any bit breaks the issuer signature.
- No issuer change needed; works for the vendored Longfellow mDL/EUAV real
  vectors today, and the issuer/revoker can compute the id from its records.
- The id derivation MUST happen in-circuit from the already-bound MSO window
  (the mdoc path already proves SHA-256 over these bytes), not be supplied as
  a free witness.
- Collision policy: 64-bit truncation gives birthday collision probability
  ≈ n²/2⁶⁵; at 10⁸ credentials that is ≈ 2⁻¹²; a collision revokes an extra
  credential (availability, not soundness). Record this in the evidence pack.
- Upgrade path: if a signed `credential_id` attribute is later standardized,
  add it as a second identifier source behind the same statement field;
  do not remove the MSO-derived mode.

Decision D-TS13-BOUNDARY (RESOLVED 2026-07-07 — sentinel pairs):

TS13 defines only interior pairs and strict `id_lo < id < id_hi`; it is silent
on `id < first` and `id > last`. Our revocation-authority profile (we also
build the revoker tooling, so this is ours to define until ETSI standardizes):

- The revoker always prepends sentinel `0` and appends sentinel
  `2^64 − 1` to the sorted revoked list before signing consecutive pairs.
- An empty revocation list is published as the single signed pair
  `(0, 2^64 − 1, ep)`.
- The circuit constraint stays strict `id_lo < id < id_hi` with no special
  cases. Credentials whose derived id is `0` or `2^64 − 1` (probability
  ≈ 2⁻⁶³) are rejected at issuance and reissued; the circuit does not handle
  them.
- Signed message encoding per TS13: `LE64(id_lo) || LE64(id_hi) || LE32(ep)`,
  hashed with SHA-256, signed with ECDSA P-256.

Acceptance:

```bash
rtk proxy cargo test -p eu-id-prover --test mdoc_support ts13_revocation
rtk proxy env RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release --features ec-coprocessor ts13_revocation_non_revoked_end_to_end -- --ignored --exact --nocapture
```

At baseline the filter `ts13_revocation` matches ZERO tests. The first command
passes acceptance only when its output lists all seven (NEW) tests below.

Required tests, all (NEW):

- `ts13_revocation_non_revoked_end_to_end` — the positive path.
- `ts13_revocation_sentinel_pair_end_to_end` — positive path against the
  empty-list pair `(0, 2^64 − 1, ep)` per D-TS13-BOUNDARY (also covers
  `id < first` / `id > last`, which use the sentinel pairs identically).
- `ts13_revocation_rejects_id_equal_lo` — `id == id_lo` rejects.
- `ts13_revocation_rejects_id_equal_hi` — `id == id_hi` rejects.
- `ts13_revocation_rejects_forged_pair_signature` — forged revocation pair
  signature rejects.
- `ts13_revocation_rejects_stale_epoch` — stale epoch rejects.
- `ts13_revocation_rejects_missing_caller_binding` — statement `rpk` or `ep`
  not supplied by caller rejects.

### WO-TS13-2: Add TS13 Presentation Layer

Owner: SDK.

Implement TS13 presentation compatibility without changing circuit arithmetic.
Use the existing SDK module layout unless a new `crates/sdk/src/presentation.rs`
is cleaner.

Required formats:

1. ISO `ZkRequest` under DeviceRequest requestInfo.
2. ISO `ZkDocument` / `ZkDocumentData(Bytes)` in DeviceResponse.
3. OpenID4VP DCQL credential format `mso_mdoc_zk`.
4. `zk-jwt` parser stub that rejects unsupported requests with a precise error
   until an SD-JWT tuple is implemented.
5. `zkSystemId` / `ZkSystemSpec` negotiation per decision D-TS13-SYS below.
6. `params.circuit_hash` fail-closed matching against the pinned tuple.
7. Caller-bound policy fields: doctype, namespace, requested attributes, session
   transcript, trusted issuer set, revocation key, epoch, and current date.

Decision D-TS13-SYS (RESOLVED — this is the implementation rule):

TS13's `system: "longfellow-libzk-v1"` identifies Google's libzk proof system;
its proof and circuit serialization are pinned by IETF `draft-google-cfrg-libzk`
(TS13 §out-of-scope defers to it explicitly). Our stwo-based proofs are a
different proof system that proves the same TS13 statement. Therefore:

- stwo proofs MUST NOT be emitted under `system: "longfellow-libzk-v1"`. A
  relying party resolving that id to a libzk verifier would reject them; a
  relying party accepting them under that id has a broken verifier.
- The TS13 entry points use TS13's own negotiation mechanism: advertise and
  accept our own `ZkSystem` value (`stwo-euid-v1`) inside standard
  `ZkSystemSpec` / DCQL `zk_system_type` structures. Wire formats are TS13;
  the system id is ours.
- Requests offering ONLY `longfellow-libzk-v1` are rejected fail-closed with a
  distinct unsupported-system error (see the negative test below). Do not
  implement a libzk-compatible proof backend under this spec; that would be a
  separate work order requiring an explicit product decision.

Current SDK compatibility note:

`crates/sdk/src/lib.rs` exposes `stwo-euid-v1` and a bespoke bincode proof
envelope. The bespoke envelope may remain for the existing apps, but TS13
entry points emit CBOR `ZkDocument` and must not silently accept or emit the
`longfellow-libzk-v1` identifier for stwo proofs.

Acceptance:

```bash
rtk proxy cargo test -p sdk ts13_presentation
rtk proxy cargo test -p sdk mdoc
rtk proxy cargo test -p eu-id-prover --test mdoc_support
```

At baseline the filter `ts13_presentation` matches ZERO tests (and so did the
old `presentation` filter). The first command passes acceptance only when its
output lists all seven (NEW) tests below; the other two are regression guards.

Required tests, all (NEW), named `ts13_presentation_*`:

- `ts13_presentation_round_trip` — ZkRequest in, ZkDocument out, DCQL
  `mso_mdoc_zk` accepted, for the pinned tuple.
- `ts13_presentation_rejects_unknown_zk_system_id` — a `system` value that is
  neither `stwo-euid-v1` nor otherwise supported rejects.
- `ts13_presentation_rejects_longfellow_only_request` — a request whose
  `zk_system_type` list contains ONLY `longfellow-libzk-v1` rejects with the
  distinct unsupported-system error from D-TS13-SYS; a stwo proof is never
  emitted or accepted under the `longfellow-libzk-v1` id.
- `ts13_presentation_rejects_unknown_circuit_hash`.
- `ts13_presentation_rejects_tuple_mismatch` — request/proof tuple mismatch
  rejects.
- `ts13_presentation_rejects_caller_policy_drift` — rejects even if the proof
  envelope claims otherwise.
- `ts13_presentation_rejects_zk_jwt_unsupported` — `zk-jwt` rejects with a
  specific unsupported-format error variant, not a generic parse error.

### WO-TS13-3: Publish Circuit Parameter Tuples and Hashes

Owner: prover plus SDK contract.

Required tuple fields:

- max mdoc byte length;
- number of disclosed attributes;
- max disclosed attribute byte length;
- number of potential issuers or issuer-public-key policy mode;
- revocation enabled flag and identifier width;
- device-auth profile;
- PCS/security config;
- preprocessed root / fixed table fingerprints;
- proof system id.

Required outputs:

1. Canonical serialization for the tuple.
2. SHA-256 `circuit_hash` golden files.
3. SDK lookup table from request tuple to hash.
4. Verifier fail-closed check that proof tuple, request tuple, hash, and pinned
   preprocessed roots all match.
5. Security-bit table per tuple.

Acceptance:

```bash
rtk proxy cargo test -p eu-id-prover circuit_hash
rtk proxy cargo test -p sdk circuit_hash
rtk proxy cargo test -p eu-id-prover --release shape_dump -- --ignored --nocapture
```

At baseline the filter `circuit_hash` matches ZERO tests in both crates. The
first two commands pass acceptance only when their output lists the four (NEW)
tests below; `shape_dump` is a regression guard.

Required tests, all (NEW):

- `circuit_hash_golden_matches_canonical_serialization` — recomputes the
  golden `circuit_hash` from the canonical tuple serialization and compares
  against the committed golden file. Any serialization change fails this test
  until the golden file is deliberately regenerated in the same commit.
- `circuit_hash_rejects_cross_tuple_proof` — hash from tuple A rejects a proof
  for tuple B.
- `circuit_hash_rejects_stale_preprocessed_root` — proof with a stale
  preprocessed root rejects.
- `circuit_hash_sdk_lookup_fail_closed` (in `-p sdk`) — a request tuple with
  no lookup-table entry rejects; it must not fall through to any default hash.

### WO-TS13-4: Normalize Attribute Semantics

Owner: mdoc statement builder and SDK request mapping.

The current product API supports computed predicates. TS13 compatibility needs
the equality-disclosure path to be first-class and unambiguous.

Required behavior:

1. The published TS13 age tuple requests `age_over_18` as a disclosed
   `ValueEquality(true)` attribute when the credential carries that attribute.
   Status at baseline: ALREADY DONE — `longfellow_mdl3_n1_age_over_18_end_to_end`
   uses `MdocDisclosureMode::ValueEquality` (see
   `crates/eu-id-prover/tests/mdoc_support.rs`, around line 2017). Do not
   re-implement; verify and move on.
2. `AgeOver` from `birth_date` and `Alpha2Set` remain product extensions, not
   the baseline TS13 tuple.
3. SDK presentation metadata labels extension predicates distinctly so relying
   parties do not confuse them with TS13 equality attributes. Status at
   baseline: MISSING — this is part of the work of this WO.
4. The equality tuple is REACHABLE THROUGH THE FFI. Status at baseline:
   MISSING — this is the other part. At baseline the uniffi surface cannot
   request it at all: `expected_mdoc_attributes()` in `crates/sdk/src/lib.rs`
   hardcodes `birth_date → AgeOver` and `nationality → Alpha2Set`, and
   `PredicateMode` (`Age`/`Nat`/`And`/`Or`) has no equality variant. The
   prover-level `MdocDisclosureMode::ValueEquality` exists but is unreachable
   from the app. Extend the exported request types so a caller can request
   `age_over_18` as a disclosed `ValueEquality(true)` attribute, keeping the
   existing hardcoded profile as the default for the current apps.
5. Longfellow mDL and EUAV vectors cover the equality tuple.

Completion evidence:

- (NEW) test `ts13_sdk_labels_extension_predicates` (in `-p sdk`) — SDK
  presentation metadata marks `AgeOver` and `Alpha2Set` requests as
  extensions and `ValueEquality` requests as TS13 equality attributes; an
  extension predicate must never serialize with the TS13 equality label.
- (NEW) test `ts13_sdk_value_equality_request_maps_to_prover` (in `-p sdk`) —
  a statement built through the exported FFI types requesting `age_over_18`
  equality produces an `MdocPidRequest` whose attribute list contains
  `MdocDisclosureMode::ValueEquality` for `age_over_18` (and no `AgeOver`
  entry); the default two-attribute product profile is unchanged when the
  caller does not opt in.

Acceptance (third command is a regression guard — it already passes at
baseline):

```bash
rtk proxy cargo test -p sdk ts13_sdk_labels_extension_predicates
rtk proxy cargo test -p sdk ts13_sdk_value_equality_request_maps_to_prover
rtk proxy env RAYON_NUM_THREADS=1 cargo test -p eu-id-prover --release --test mdoc_support longfellow_mdl3_n1_age_over_18_end_to_end -- --ignored --exact --nocapture
```

### WO-TS13-5: Verification Evidence Pack

Owner: release/documentation.

Before an external TS13-compatible claim, produce one evidence file under
`tasks/audits/` for the tuple.

Required contents:

- exact commit hash;
- exact supported tuple serialization;
- circuit hash;
- verifier-facing public statement fields;
- hidden witness fields;
- soundness-bit accounting;
- zero-knowledge leakage table;
- real-vector fixture list;
- proof bytes;
- prove/verify time and hardware;
- all commands run and pass/fail status.
- documentation diff showing `docs/mdoc-credential-format.md`, SDK docs, and
  public README text no longer contradict the supported tuple.

Acceptance (all four commands are regression guards; the deliverable is the
evidence file itself under `tasks/audits/`, containing every required item
above — a green run with no evidence file is NOT completion):

```bash
rtk proxy cargo fmt --check
rtk proxy cargo test -p eu-id-prover --test mdoc_support
rtk proxy cargo test -p sdk
rtk proxy make check
```

If `make check` has an unrelated known failure, the evidence file must name the
failing target and include the narrower green gates that cover the TS13 tuple.

## Optional Work

### WO-TS13-6: Hide Issuer Key Through Access-CA Verification

This is an optional privacy upgrade, not a blocker for baseline compatibility.

Design:

1. Make the issuer public key witness-private.
2. Add an in-circuit ES256 verification for the DS certificate signed by a
   public Access CA / IACA key.
3. Bind issuer key bytes to the TBSCertificate window.
4. Parameterize the circuit by potential issuer count / trust-anchor policy.

Do not start this work without a product decision. It changes the public
statement and trust model.

### WO-TS13-7: Longfellow Performance Parity

This is a product-readiness track, not a strict compatibility blocker.

Continue tracking it in `tasks/longfellow-parity-plan.md` and
`tasks/remaining-work-orders-2026-07-06.md`. Any public compatibility statement
should still include current proof size and proving time because TS13 adoption
will be judged against the Longfellow reference implementation.

## Sequencing

1. Finish P4c zero-knowledge masking and leakage evidence.
2. Implement TS13 presentation layer in the SDK; this can proceed in parallel
   with proof work if it owns only SDK files.
3. Publish circuit parameter tuples and hashes after P4c because proof shape and
   fixed roots will be repinned.
4. Implement revocation per the resolved D-TS13-ID (MSO-derived id) and
   D-TS13-BOUNDARY (sentinel pairs) decisions in WO-TS13-1.
5. Run the verification evidence pack.
6. Decide separately whether issuer-key privacy and performance parity are
   needed before external launch.

## Review Checklist

- No TS13 compatibility claim is allowed while non-revocation is missing.
- No TS13 compatibility claim is allowed while any stwo proof is emitted or
  accepted under the `longfellow-libzk-v1` system id (D-TS13-SYS), or while
  `longfellow-libzk-v1`-only requests are answered instead of rejected.
- No TS13 compatibility claim is allowed without a published `circuit_hash`.
- No TS13 compatibility claim is allowed without P4c zero-knowledge evidence.
- Computed predicates may be advertised as extensions only after the equality
  tuple is green.
